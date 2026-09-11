import Lean
open Lean Elab Parser Command

def swaps : List (Name × String × List String) :=
  [(`«term_+_»,"+",["-","*"]),(`«term_-_»,"-",["+","/"]),(`«term_*_»,"*",["+","/"]),
   (`«term_/_»,"/",["%","*"]),(`«term_%_»,"%",["/","+"]),
   (`«term_<_»,"<",["≤","=",">"]),(`«term_≤_»,"≤",["<",">"]),
   (`«term_>_»,">",["≥","=","<"]),(`«term_≥_»,"≥",[">","<"]),
   (`«term_==_»,"==",["!="]),(`«term_!=_»,"!=",["=="]),
   (`«term_=_»,"=",["≠"]),(`«term_≠_»,"≠",["="]),
   (`«term_∧_»,"∧",["∨"]),(`«term_∨_»,"∨",["∧"]),
   (`«term_&&_»,"&&",["||"]),(`«term_||_»,"||",["&&"]),
   (`«term_&&&_»,"&&&",["|||","^^^"]),(`«term_|||_»,"|||",["&&&","^^^"]),(`«term_^^^_»,"^^^",["&&&","|||"]),
   (`«term_<<<_»,"<<<",[">>>"]),(`«term_>>>_»,">>>",["<<<"])]

-- every mutation site carries an op tag so `--ops`/`--no-ops` can select classes
def opTags : List String :=
  (swaps.map (·.2.1)) ++ ["lit","ident","flip","args","body"]

def identSwaps : List (Name × String) :=
  [(`min,"max"),(`max,"min"),(`Nat.min,"Nat.max"),(`Nat.max,"Nat.min"),
   (`true,"false"),(`false,"true"),
   (`sub?,"add?"),(`mod?,"div?")]

partial def collect (src : String) (s : Syntax) : Array (String × String.Pos.Raw × String.Pos.Raw × String) := Id.run do
  let mut acc := #[]
  for a in s.getArgs do acc := acc ++ collect src a
  if let some (_, tag, rs) := swaps.find? (·.1 == s.getKind) then
    if s.getArgs.size > 1 then
      if let (some p, some q) := (s.getArgs[1]!.getPos?, s.getArgs[1]!.getTailPos?) then
        for r in rs do acc := acc.push (tag, p, q, r)
  else if let some n := s.isNatLit? then
    if let (some p, some q) := (s.getPos?, s.getTailPos?) then
      acc := acc.push ("lit", p, q, toString (n + 1))
  else if s.isIdent then
    if let some (_, r) := identSwaps.find? (·.1 == s.getId) then
      if let (some p, some q) := (s.getPos?, s.getTailPos?) then
        acc := acc.push ("ident", p, q, r)
  else if s.isOfKind ``Lean.Parser.Term.app then
    let fn := s.getArg 0
    let args := (s.getArg 1).getArgs
    if fn.isIdent && fn.getId == `flip && args.size ≥ 1 then
      if let (some p, some pa, some qa) := (fn.getPos?, args[0]!.getPos?, args[0]!.getTailPos?) then
        acc := acc.push ("flip", p, qa, String.Pos.Raw.extract src pa qa)
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
            acc := acc.push ("args", pa, qb, tb ++ " " ++ ta)
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

def vals : List String := ["default","0","1","true","false"]

-- whole-body -> constant; ill-typed swaps become stillborn, never fatal
def bodyVals (src : String) (b : Syntax) : Array (String × String.Pos.Raw × String.Pos.Raw × String) := Id.run do
  let mut acc := #[]
  if b.isOfKind ``Lean.Parser.Command.declValSimple then
    let t := b.getArg 1
    if let (some p, some q) := (t.getPos?, t.getTailPos?) then
      let orig := String.Pos.Raw.extract src p q
      for c in vals do if c != orig then acc := acc.push ("body", p, q, c)
  else if b.isOfKind ``Lean.Parser.Command.declValEqns then
    if let (some p, some q) := (b.getPos?, b.getTailPos?) then
      for c in vals do acc := acc.push ("body", p, q, ":= " ++ c)
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

def splitPats (s : String) : List String := (s.splitOn ",").filter (· != "")

def hasSub (pat nm : String) : Bool := pat != "" && (nm.splitOn pat).length > 1

structure Opts where
  verbose : Bool := false
  incl : List String := []
  excl : List String := []
  ops : List String := []
  noOps : List String := []
  sample : Nat := 0
  seed : Nat := 0
  files : List String := []

partial def parseArgs (as : List String) (o : Opts) : Opts :=
  match as with
  | [] => o
  | a :: t =>
    if a == "-v" || a == "--verbose" then parseArgs t { o with verbose := true }
    else if a.startsWith "--include-def=" then parseArgs t { o with incl := o.incl ++ splitPats (a.drop 14).toString }
    else if a.startsWith "--exclude-def=" then parseArgs t { o with excl := o.excl ++ splitPats (a.drop 14).toString }
    else if a == "--include-def" then
      match t with
      | p :: t' => parseArgs t' { o with incl := o.incl ++ splitPats p }
      | [] => o
    else if a == "--exclude-def" then
      match t with
      | p :: t' => parseArgs t' { o with excl := o.excl ++ splitPats p }
      | [] => o
    else if a.startsWith "--ops=" then parseArgs t { o with ops := o.ops ++ splitPats (a.drop 6).toString }
    else if a.startsWith "--no-ops=" then parseArgs t { o with noOps := o.noOps ++ splitPats (a.drop 9).toString }
    else if a == "--ops" then
      match t with
      | p :: t' => parseArgs t' { o with ops := o.ops ++ splitPats p }
      | [] => o
    else if a == "--no-ops" then
      match t with
      | p :: t' => parseArgs t' { o with noOps := o.noOps ++ splitPats p }
      | [] => o
    else if a.startsWith "--sample=" then parseArgs t { o with sample := (a.drop 9).toString.toNat! }
    else if a.startsWith "--seed=" then parseArgs t { o with seed := (a.drop 7).toString.toNat! }
    else if a == "--sample" then
      match t with
      | p :: t' => parseArgs t' { o with sample := p.toNat! }
      | [] => o
    else if a == "--seed" then
      match t with
      | p :: t' => parseArgs t' { o with seed := p.toNat! }
      | [] => o
    else parseArgs t { o with files := o.files ++ [a] }

-- substring match on the declaration name; include (if any) must match, exclude wins
def keepDef (o : Opts) (nm : String) : Bool :=
  (o.incl.isEmpty || o.incl.any (hasSub · nm)) && !o.excl.any (hasSub · nm)

-- deterministic subset: partial Fisher-Yates driven by an LCG. Same --sample/--seed
-- always selects the same sites, so a sampled run is reproducible.
def sampleSites {α : Type} (n seed : Nat) (a : Array α) : Array α := Id.run do
  if n == 0 || n >= a.size then return a
  let mut arr := a
  let mut st := seed * 2654435761 + 12345
  for i in [0:n] do
    st := (st * 1103515245 + 12345) % 2147483648
    let j := i + st % (arr.size - i)
    arr := arr.swapIfInBounds i j
  return arr.take n

-- exact match on the op tag; `--ops` (if any) must match, `--no-ops` wins
def keepOp (o : Opts) (tag : String) : Bool :=
  (o.ops.isEmpty || o.ops.contains tag) && !o.noOps.contains tag

-- elaborate only until the first error
partial def processUntilError : Frontend.FrontendM Unit := do
  let done ← Frontend.processCommand
  if done then return
  if (← get).commandState.messages.hasErrors then return
  processUntilError

def processEarly (ic : Parser.InputContext) (ps : Parser.ModuleParserState)
    (cs : Command.State) : IO Frontend.State := do
  let (_, st) ← (processUntilError.run { inputCtx := ic }).run
    { commandState := cs, parserState := ps, cmdPos := ps.pos }
  return st

unsafe def main (args : List String) : IO Unit := do
  Lean.enableInitializersExecution
  let o := parseArgs args {}
  let verbose := o.verbose
  let files := o.files
  if files.isEmpty then
    throw <| IO.userError
      "usage: Mutate.lean [-v] [--include-def P,..] [--exclude-def P,..] [--ops O,..] [--no-ops O,..] [--sample N] [--seed S] <target> [killer...]"
  -- Validate only the files named on the command line
  for f in files do
    let fp := modPath (modOf f)
    if !(← System.FilePath.pathExists fp) then
      throw <| IO.userError s!"no such file: {fp}"
  for t in o.ops ++ o.noOps do
    if !opTags.contains t then
      throw <| IO.userError s!"unknown op {t}; known: {String.intercalate "," opTags}"
  let seeds := files.map modOf
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
  let name := files.head!
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
    if isDef c && !isSpec c && keepDef o (cName c) then
      if let some cp := c.getPos? then
        if cp ≤ fEnd then
          for b in bodies c do
            for s in collect src b do
              if keepOp o s.1 then sites := sites.push (cName c, s)
            for s in bodyVals src b do
              if keepOp o s.1 then sites := sites.push (cName c, s)
  let total := sites.size
  sites := sampleSites o.sample o.seed sites
  if verbose then
    if sites.size != total then
      IO.println s!"{sites.size} AST sites in def bodies (sample of {total}, seed {o.seed})\n"
    else IO.println s!"{sites.size} AST sites in def bodies\n"
  if sites.isEmpty then
    throw <| IO.userError "no mutation sites -- did --include-def/--exclude-def/--ops/--no-ops filter everything out?"
  -- Baseline check: refuse to run when the unmutated source does not elaborate.
  (← IO.getStdout).flush
  let t0 ← IO.monoMsNow
  let baseFs ← IO.processCommands ic mpst (Command.mkState env {} {})
  let baseMs := (← IO.monoMsNow) - t0
  if baseFs.commandState.messages.hasErrors then
    IO.eprintln "baseline does not elaborate -- every mutant would be reported `killed`:"
    for m in baseFs.commandState.messages.toList do
      if m.severity == .error then IO.eprintln (← m.toString)
    throw <| IO.userError "refusing to run: fix the baseline first"
  if verbose then
    IO.println s!"baseline elaborates in {baseMs}ms ({sites.size} mutants ~ {(baseMs * sites.size) / 60000}min serial)\n"
    (← IO.getStdout).flush
  let mut k := 0; let mut sv := 0; let mut sb := 0
  let mut i := 0
  let tStart ← IO.monoMsNow
  let n := sites.size
  for (nm, _op, p, q, r) in sites do
    i := i + 1
    let msrc := String.Pos.Raw.extract src ⟨0⟩ p ++ r ++ String.Pos.Raw.extract src q src.rawEndPos
    let ic2 := Parser.mkInputContext msrc name
    let cs := Command.mkState env {} {}
    let fs ← processEarly ic2 mpst cs
    let ml := fs.commandState.messages
    if ml.hasErrors then
      let verdict := whoKilled nm (parseAll ic2 pm mpst {} #[]) ic2.fileMap ml
      if verdict.startsWith "killed" then k := k+1 else sb := sb+1
      if verbose then IO.println s!"[{i}/{n}] {nm}  {r}  {verdict}"
      else IO.println s!"  {nm}  {r}  {verdict}"
    else
      sv := sv+1
      if verbose then IO.println s!"[{i}/{n}] {nm}  -> {r}  survived"
      else IO.println s!"  {nm}  -> {r}  survived"
    -- U1: flush every line so redirected output is live, and report progress
    -- periodically with a measured ETA. A long run is otherwise indistinguishable
    -- from a hung one -- the only way to tell used to be `ps` on the CPU time.
    (← IO.getStdout).flush
    if verbose && (i % 25 == 0 || i == n) then
      let el := (← IO.monoMsNow) - tStart
      let eta := if i == 0 then 0 else (el / i) * (n - i)
      IO.println s!"  -- {i}/{n} ({(100*i)/n}%)  killed={k} survived={sv} stillborn={sb}  elapsed={el/60000}m  eta~{eta/60000}m"
      (← IO.getStdout).flush
  if sites.size != total then
    IO.println s!"\nkilled={k}  survived={sv}  stillborn={sb}  (sample of {total}, seed {o.seed})"
  else IO.println s!"\nkilled={k}  survived={sv}  stillborn={sb}"
  (← IO.getStdout).flush
