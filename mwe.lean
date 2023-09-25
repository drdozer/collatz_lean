import Mathlib.Tactic
import Lean

open Lean.Parser.Tactic.Conv
open Lean.Elab.Tactic.Conv
open Lean Elab Term Meta

def elabConvRewrite (e : Expr) (stx : TSyntax `conv) : TermElabM (Expr × Expr) := do
  let (rhs, eq) ← mkConvGoalFor e

  let goals ← Tactic.run eq.mvarId! do
    let (lhsNew, proof) ← convert e (Tactic.evalTactic stx)
    updateLhs lhsNew proof
    return ()

  if goals.length = 0 then
    throwError "this is a bug in rewriteByConv"

  if goals.length > 1 then
    throwError s!"error in `rewriteByConv`, unsolved goals {← goals.mapM (fun g => do ppExpr (← g.getType))}"

  (goals.get! 0).refl

  return (← instantiateMVars rhs, ← instantiateMVars eq)

def rewriteByConv (e : Expr) (stx : TSyntax `conv) : MetaM (Expr × Expr) := do
  let (r,_) ← (elabConvRewrite e stx).run {} {}
  return r

syntax:1 term "rewrite_by" convSeq : term

elab_rules : term
| `($x:term rewrite_by $rw:convSeq) => do
  let x ← elabTerm x none
  let (x',_eq) ← elabConvRewrite x (← `(conv| ($rw)))
  return x'



inductive ColN where
    | zero      : ColN
    | even_of   : ColN → ColN
    | odd_of    : ColN → ColN
deriving Repr

@[simp]
def ColN.eval (cn: ColN) (n : ℕ) : ℕ := match cn with
| ColN.zero => n
| ColN.even_of cm => 2 * (ColN.eval cm n)
| ColN.odd_of cm => 2 * (ColN.eval cm n) + 1

def z10 := ColN.even_of $ ColN.odd_of ColN.zero

#reduce z10.eval
#check z10.eval rewrite_by simp ; ring_nf

def z10eval := (z10.eval rewrite_by simp ; ring_nf)

#reduce z10eval
#check z10eval