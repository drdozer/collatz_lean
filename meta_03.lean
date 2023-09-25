import Lean

namespace Playground

inductive Expr where
  | bvar    : Nat → Expr
  | fvar    : FVarId → Expr
  | mvar    : MVarId → Expr
  | sort    : Level → Expr
  | const   : Name → List Level → Expr
  | app     : Expr → Expr → Expr
  | lam     : Name → Expr → Expr → BinderInfo → Expr
  | forallE : Name → Expr → Expr → BinderInfo → Expr
  | letE    : Name → Expr → Expr → Bool → Expr
  | lit     : Literal → Expr
  | mdata   : MData → Expr → Expr
  | proj    : Name → Nat → Expr → Expr

end Playground

open Lean

def z' := Expr.const `Nat.zero []
#eval z'

def z := Expr.const ``Nat.zero []
#eval z

open Nat

-- unhygenic as `zero` may or may not bind in a given expansion context
def z₁ := Expr.const `zero []
#eval z₁

-- hygenic, as the double backtick fully resolves `zero` to `Nat.zero`
def z₂ := Expr.const ``zero []
#eval z₂

def one := Expr.app (.const ``Nat.succ []) z
#eval one

def natExpr : Nat → Expr
| 0 => z
| succ n => .app (.const ``Nat.succ []) (natExpr n)

#eval natExpr 0
#eval natExpr 1
#eval natExpr 2

def sumExpr : Nat → Nat → Expr
| n, m => mkAppN (.const ``Nat.add []) #[natExpr n, natExpr m]

#eval sumExpr 0 1

def constZero : Expr :=
  .lam `x (.const ``Nat []) (.const ``Nat.zero []) BinderInfo.default

#eval constZero

def nat : Expr := .const ``Nat []

def addOne : Expr :=
  .lam `x nat
    (mkAppN (.const ``Nat.add []) #[.bvar 0, mkNatLit 1])
    BinderInfo.default

def mapAddOneNil : Expr :=
  mkAppN (.const ``List.map [levelOne, levelOne])
    #[nat, nat, addOne, .app (.const ``List.nil [levelOne]) nat]

elab "mapAddOneNil" : term => return mapAddOneNil

#check mapAddOneNil

#reduce mapAddOneNil

#check Expr.app (Expr.app (.const ``Nat.add []) (natExpr 1)) (natExpr 2)
#check Lean.mkAppN (.const ``Nat.add []) #[natExpr 1, natExpr 2]
