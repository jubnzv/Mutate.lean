import Lean
open Lean

namespace Mutate

structure Op where
  name    : String
  cls     : String
  applies : Syntax → Bool
  rewrite : Syntax → Syntax

def infixSwap (k k' : Name) (a cls : String) : Op where
  name    := s!"{k} → {k'}"
  cls     := cls
  applies := (·.getKind == k)
  rewrite := fun s => match s with
    | .node info _ args => .node info k' (args.set! 1 (mkAtom a))
    | s => s

def identSwap (f t : Name) (cls : String) : Op where
  name    := s!"{f} → {t}"
  cls     := cls
  applies := fun s => s.isIdent && s.getId == f
  rewrite := fun s => mkIdentFrom s t

def lib : List Op := [
  infixSwap `«term_-_» `«term_+_» "+" "arith",
  infixSwap `«term_+_» `«term_-_» "-" "arith",
  infixSwap `«term_*_» `«term_/_» "/" "arith",
  infixSwap `«term_/_» `«term_*_» "*" "arith",
  infixSwap `«term_<_» `«term_≤_» "≤" "cmp",
  infixSwap `«term_≤_» `«term_<_» "<" "cmp",
  infixSwap `«term_>_» `«term_≥_» "≥" "cmp",
  infixSwap `«term_≥_» `«term_>_» ">" "cmp",
  infixSwap `«term_==_» `«term_!=_» "!=" "cmp",
  infixSwap `«term_=_» `«term_≠_» "≠" "cmp",
  infixSwap `«term_≠_» `«term_=_» "=" "cmp",
  identSwap `min `max "clamp",
  identSwap `max `min "clamp",
  identSwap `Nat.min `Nat.max "clamp",
  identSwap `Nat.max `Nat.min "clamp",
  identSwap `true `false "bool",
  identSwap `false `true "bool",
  infixSwap `«term_&&&_» `«term_|||_» "|||" "bit",
  infixSwap `«term_|||_» `«term_&&&_» "&&&" "bit",
  infixSwap `«term_^^^_» `«term_&&&_» "&&&" "bit",
  infixSwap `«term_<<<_» `«term_>>>_» ">>>" "bit",
  infixSwap `«term_>>>_» `«term_<<<_» "<<<" "bit",
  identSwap `sub? `add? "abort",
  identSwap `ssub `sadd "abort" ]

partial def countSites (op : Op) (s : Syntax) : Nat :=
  (if op.applies s then 1 else 0) + s.getArgs.foldl (fun n a => n + countSites op a) 0

partial def mutNth (op : Op) (tgt : Nat) (s : Syntax) : StateM Nat Syntax := do
  if op.applies s then
    let i ← getModify (· + 1)
    if i == tgt then return op.rewrite s
  match s with
  | .node info k args => return .node info k (← args.mapM (mutNth op tgt))
  | _ => return s

def ofOp (op : Op) (s : Syntax) : List (String × Nat × Syntax) :=
  (List.range (countSites op s)).map fun i => (op.name, i, (mutNth op i s).run' 0)

def all (s : Syntax) : List (String × Nat × Syntax) := lib.flatMap (ofOp · s)

end Mutate

open Mutate Lean Elab Command in
elab "#count " e:term : command => do
  logInfo s!"{(all e.raw).length} mutants from {lib.length} ops"
  for (nm, i, _) in all e.raw do logInfo s!"  {nm}  site#{i}"
