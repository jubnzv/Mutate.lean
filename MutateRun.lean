import Lean
open Lean Elab Parser Command

def swaps : List (Name × String) :=
  [(`«term_-_»,"+"),(`«term_+_»,"-"),(`«term_*_»,"/"),(`«term_/_»,"*"),
   (`«term_<_»,"≤"),(`«term_≤_»,"<"),(`«term_>_»,"≥"),(`«term_≥_»,">"),(`«term_==_»,"!="),
   (`«term_=_»,"≠"),(`«term_≠_»,"="),
   (`«term_∧_»,"∨"),
   (`«term_&&&_»,"|||"),(`«term_|||_»,"&&&"),(`«term_^^^_»,"&&&"),
   (`«term_<<<_»,">>>"),(`«term_>>>_»,"<<<")]

def identSwaps : List (Name × String) :=
  [(`min,"max"),(`max,"min"),(`Nat.min,"Nat.max"),(`Nat.max,"Nat.min"),
   (`true,"false"),(`false,"true"),
   (`sub?,"add?"),(`mod?,"div?")]

partial def collect (src : String) (s : Syntax) : Array (String.Pos.Raw × String.Pos.Raw × String) := Id.run do
  let mut acc := #[]
  for a in s.getArgs do acc := acc ++ collect src a
  if let some (_, r) := swaps.find? (·.1 == s.getKind) then
    if s.getArgs.size > 1 then
      if let (some p, some q) := (s.getArgs[1]!.getPos?, s.getArgs[1]!.getTailPos?) then
        acc := acc.push (p, q, r)
  else if let some n := s.isNatLit? then
    if let (some p, some q) := (s.getPos?, s.getTailPos?) then
      acc := acc.push (p, q, toString (n + 1))
  else if s.isIdent then
    if let some (_, r) := identSwaps.find? (·.1 == s.getId) then
      if let (some p, some q) := (s.getPos?, s.getTailPos?) then
        acc := acc.push (p, q, r)
  else if s.isOfKind ``Lean.Parser.Term.app then
    let fn := s.getArg 0
    let args := (s.getArg 1).getArgs
    if fn.isIdent && fn.getId == `flip && args.size ≥ 1 then
      if let (some p, some pa, some qa) := (fn.getPos?, args[0]!.getPos?, args[0]!.getTailPos?) then
        acc := acc.push (p, qa, String.Pos.Raw.extract src pa qa)
    if h : args.size ≥ 2 then
      let a := args[args.size - 2]; let b := args[args.size - 1]
      -- named args are position-independent -> swap is a no-op, fakes a survived
      let named (x : Syntax) := x.isOfKind ``Lean.Parser.Term.namedArgument
      if !named a && !named b then
        if let (some pa, some qa, some pb, some qb) :=
            (a.getPos?, a.getTailPos?, b.getPos?, b.getTailPos?) then
          let ta := String.Pos.Raw.extract src pa qa
          let tb := String.Pos.Raw.extract src pb qb
          if ta != tb then  -- f x x, same reason
            acc := acc.push (pa, qb, tb ++ " " ++ ta)
  return acc

def isDef (c : Syntax) : Bool :=
  (c.find? (fun s => s.isOfKind ``Lean.Parser.Command.definition ||
    s.isOfKind ``Lean.Parser.Command.instance ||
    s.isOfKind ``Lean.Parser.Command.abbrev)).isSome

-- mutate bodies only, never signatures: mutating types is spec mutation and fakes
-- survived when both variants elaborate (e.g. swapping `Coe A B` args with A defeq B)
partial def bodies (s : Syntax) : Array Syntax := Id.run do
  if s.isOfKind ``Lean.Parser.Command.declValSimple ||
     s.isOfKind ``Lean.Parser.Command.declValEqns ||
     s.isOfKind ``Lean.Parser.Command.whereStructInst then
    return #[s]
  let mut acc := #[]
  for a in s.getArgs do acc := acc ++ bodies a
  return acc
def isSpec (c : Syntax) : Bool :=
  (c.find? (fun s => s.isOfKind ``Lean.Parser.Term.prop || (s.isIdent && s.getId == `Prop))).isSome
def cName (c : Syntax) : String :=
  match c.find? (·.isOfKind ``Lean.Parser.Command.declId) with
  | some d => (d.getArg 0).getId.toString | none => "?"

partial def parseAll (ic : InputContext) (pm : ParserModuleContext)
    (st : ModuleParserState) (ms : MessageLog) (acc : Array Syntax) : Array Syntax :=
  let (c, st', ms') := parseCommand ic pm st ms
  if c.isOfKind ``Lean.Parser.Command.eoi then acc else parseAll ic pm st' ms' (acc.push c)

def whoKilled (nm : String) (cmds : Array Syntax) (fm : FileMap) (ml : MessageLog) : String := Id.run do
  for m in ml.toList do
    if m.severity == .error then
      let ep := fm.ofPosition m.pos
      for c in cmds do
        if let (some a, some b) := (c.getPos?, c.getTailPos?) then
          if a ≤ ep && ep ≤ b then
            let tag := if cName c == nm then "stillborn" else "killed"
            return tag ++ "  " ++ cName c
      return "killed  ?"
  return "killed  ?"

def modOf (p : String) : String :=
  ((p.replace "./" "").replace ".lean" "").replace "/" "."

def modPath (m : String) : String :=
  m.replace "." "/" ++ ".lean"

def importsOf (h : String) : List String :=
  (h.splitOn "\n").filterMap fun l =>
    if l.startsWith "import " then some (String.Pos.Raw.extract l ⟨7⟩ l.rawEndPos) else none

partial def gather (m : String)
    (st : List String × List (String × String × List String)) :
    IO (List String × List (String × String × List String)) := do
  if st.1.contains m then return st
  let path := modPath m
  if !(← System.FilePath.pathExists path) then return (m :: st.1, st.2)
  let s ← IO.FS.readFile path
  let (hdr, _, _) ← Parser.parseHeader (Parser.mkInputContext s path)
  let he := hdr.raw.getTailPos?.getD ⟨0⟩
  let body := String.Pos.Raw.extract s he s.rawEndPos
  let imps := importsOf (String.Pos.Raw.extract s ⟨0⟩ he)
  let mut st := (m :: st.1, (m, body, imps) :: st.2)
  for i in imps do st ← gather i st
  return st

def reachT (g : List (String × String × List String)) (t : String) : List String := Id.run do
  let mut r := [t]
  for _ in [0:g.length + 1] do
    for e in g do
      if !r.contains e.1 && e.2.2.any (fun i => r.contains i) then r := e.1 :: r
  return r

def topo (g : List (String × String × List String)) (ns : List String) : List String := Id.run do
  let mut out : List String := []
  for _ in [0:ns.length + 1] do
    for e in g do
      if ns.contains e.1 && !out.contains e.1 &&
         (e.2.2.filter (fun i => ns.contains i)).all (fun i => out.contains i) then
        out := out ++ [e.1]
  return out

unsafe def main (args : List String) : IO Unit := do
  Lean.enableInitializersExecution
  if args.isEmpty then throw <| IO.userError "usage: MutateRun.lean <target> [killer...]"
  let seeds := args.map modOf
  let t := seeds.head!
  let (_, g) ← seeds.foldlM (fun st m => gather m st)
    (([], []) : List String × List (String × String × List String))
  let inSet := (reachT g t ++ seeds).foldl (fun a m => if a.contains m then a else a ++ [m]) []
  let ord := t :: (topo g inSet).filter (· != t)
  let bodyOf := fun m => ((g.find? (·.1 == m)).map (·.2.1)).getD ""
  let imps := (g.foldl (fun a e => a ++ e.2.2) []).foldl
    (fun a m => if a.contains m || inSet.contains m then a else a ++ [m]) []
  let header := String.join (imps.map fun m => s!"import {m}\n")
  let tBody := bodyOf t
  let src := header ++ tBody ++ String.join ((ord.drop 1).map fun m => "\n" ++ bodyOf m)
  let fEnd := (header ++ tBody).rawEndPos
  let name := args.head!
  let ic := Parser.mkInputContext src name
  let (hdr, mpst, ms) ← Parser.parseHeader ic
  let (env, ms) ← processHeader hdr {} ms ic
  if ms.hasErrors then
    for m in ms.toList do IO.eprintln (← m.toString)
    throw <| IO.userError "header import failed"
  let pm : ParserModuleContext := { env := env, options := {} }
  let cmds := parseAll ic pm mpst ms #[]
  let mut sites := #[]
  for c in cmds do
    if isDef c && !isSpec c then
      if let some cp := c.getPos? then
        if cp ≤ fEnd then
          for b in bodies c do for s in collect src b do sites := sites.push (cName c, s)
  IO.println s!"{sites.size} AST sites in def bodies\n"
  let mut k := 0; let mut sv := 0; let mut sb := 0
  for (nm, p, q, r) in sites do
    let msrc := String.Pos.Raw.extract src ⟨0⟩ p ++ r ++ String.Pos.Raw.extract src q src.rawEndPos
    let ic2 := Parser.mkInputContext msrc name
    let cs := Command.mkState env {} {}
    let fs ← IO.processCommands ic2 mpst cs
    let ml := fs.commandState.messages
    if ml.hasErrors then
      let verdict := whoKilled nm (parseAll ic2 pm mpst {} #[]) ic2.fileMap ml
      if verdict.startsWith "killed" then k := k+1 else sb := sb+1
      IO.println s!"  {nm}  {r}  {verdict}"
    else
      sv := sv+1
      IO.println s!"  {nm}  -> {r}  survived"
  IO.println s!"\nkilled={k}  survived={sv}  stillborn={sb}"
