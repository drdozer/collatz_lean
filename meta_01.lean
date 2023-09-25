import Lean

macro x:ident ":" t:term " ↦ " y:term : term => do
  `(fun $x : $t => $y)

#eval (x : Nat ↦x + 2) 2

macro x:ident " ↦ " y:term : term => do
  `(fun $x => $y)

#eval (x ↦ x + 2) 2

elab "#assertType " termStx:term " : " typeStx:term : command =>
  open Lean Lean.Elab Command Term in
  liftTermElabM
    try
      let tp ←elabType typeStx
      discard $ elabTermEnsuringType termStx tp
      synthesizeSyntheticMVarsNoPostponing
      logInfo "success"
    catch | _ => throwError "failure"

#assertType 5 : Nat

#assertType [] : Nat


inductive Arith : Type where
  | add : Arith → Arith → Arith -- e + f
  | mul : Arith → Arith → Arith -- e * f
  | nat : Nat → Arith           -- constant
  | var : String → Arith        -- variable

declare_syntax_cat arith
syntax num : arith
syntax str : arith
syntax:50 arith:50 " + " arith:51 : arith
syntax:60 arith:60 " * " arith:61 : arith
syntax " ( " arith " ) " : arith

syntax " ⟪ " arith " ⟫ " : term

macro_rules
  | `(⟪ $s:str ⟫) => `(Arith.var $s)
  | `(⟪ $n:num ⟫) => `(Arith.nat $n)
  | `(⟪ $x:arith + $y:arith ⟫) => `(Arith.add ⟪ $x ⟫ ⟪ $y ⟫)
  | `(⟪ $x:arith * $y:arith ⟫) => `(Arith.mul ⟪ $x ⟫ ⟪ $y ⟫)
  | `(⟪ ( $x ) ⟫) => `( ⟪ $x ⟫ )

#check ⟪ "x" * "y" ⟫
#check ⟪ "x" + "y" ⟫
#check ⟪ "x" + 20 ⟫
#check ⟪ "x" + "y" * "z" ⟫
#check ⟪ ("x" + "y") * "y" ⟫

open Lean Meta Elab Tactic Term in
elab "suppose " n:ident " : " t:term : tactic => do
  let n : Name := n.getId
  let mvarId ← getMainGoal
  mvarId.withContext do
    let t ← elabType t
    let p ← mkFreshExprMVar t MetavarKind.syntheticOpaque n
    let (_, mvarIdNew) ← MVarId.intro1P $ ← mvarId.assert n t p
    replaceMainGoal [p.mvarId!, mvarIdNew]
  evalTactic $ ← `(tactic|rotate_left)

example : 0 + a = a := by
  suppose add_comm : 0 + a = a + 0
  rw [add_comm]; rfl
  rw [Nat.zero_add, Nat.add_zero]

