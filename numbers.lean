import Mathlib.Tactic

/-!
# Introduction

This is an attempt to explore the collatz conjecture by translating the problem into a series of
number-like data structures, and operations over these.

The collatz function is:

```
def collatz(n : ℕ) : ℕ := if Even n then n/2 else n*3+1 
```

The accompanying collatz conjecture is that for all `n>0`, repeatedly applying the collatz function
will eventually reach 1.

## Evenness and oddness as a numeral

The collatz function behaves differently, depending on if it is applied to an odd or an even number.
Let's say we know we're applying collatz to `Even n`.
We then know that it will be able to take the `n/2` path.
As `Even n₁` can be represented as `2*n₂`, we could represent this as a type constructor,
`even_of n₂` which evaluates to `2*n₂`.
Once this even number has been processed by collatz, we're left with `n₂`.
Let's imagine that it happens to be odd.
So `Odd n₂` implies that there is some `n₃` such that `2*n₃+1 = n₂`.
We could represent this as another constructor, `odd_of n₃`.
Our full number is now `even_of (odd_of n₃)`.
When this is processed by collatz,
it will first divide by 2 stripping off the outer `even_of` constructor.
Then it will calculate `3 * (2*n₃ + 1) + 1 = 6*n₃+4`, which is even, so reduce that to `3*n₃ + 2`.
We can continue to add "facts" about how our number was constructed from nested even and odd terms,
which will then drive the collatz function further and further.
Finally, we can terminate our number with a zero, which indicates STOP!

The three constructors, `zero`, `even_of` and `odd_of` represent leaving a number unchanged,
doubling it, and doubling it plus 1.
These seem a lot like binary operations.
Doubling is a bitshift.
Doubling add 1 is a bitshift plus 1.
So in a sense, `even_of` is a zero bit, and `odd_of` is a one bit.
The `zero` terminal ends the binary numeral.
However, the outermost constructor is the least significant, making the zero the most significant.
So we have, in effect, got a backwards binary numeral.

Where this differs from binary is that we can substitute the `zero` terminal with any `n₀`,
making the evaluation of these numerals equivalent to computing a linear function of `n₀`,
equal to the corresponding binary numeral when `n₀=0`.
-/

/--!
A collatz numeral.
-/
inductive ColN where
    | zero      : ColN          -- zero, also leading zero
    | even_of   : ColN → ColN   -- the even number that is twice the previous
    | odd_of    : ColN → ColN   -- the odd number that is one more than twice the previous
deriving Repr

instance : Zero ColN where zero := ColN.zero
instance : One ColN where one := ColN.odd_of 0

/-!
The z10 numeral is equivalent to 2.
-/
def z10 := ColN.even_of $ ColN.odd_of ColN.zero

/-!
The evaluation of a collatz numeral is straightforward from its defnition.
The `zero` constructor returns whatver it was given.
The `even_of` constructor doubles what follows, and the `odd_of` constructor doubles and adds 1.
-/

/--!
Evaluate a ColN, as an equation.

Evaluation at 0 recovers the natural number equivalent to the binary representation.
-/ 

@[simp]
def ColN.eval {α : Type} [HMul ℕ α α] [HAdd ℕ α α] (cn: ColN) (n : α) : α := match cn with
| ColN.zero => n
| ColN.even_of cm => 2 * (ColN.eval cm n)
| ColN.odd_of cm => 1 + 2 * (ColN.eval cm n)

/-!
It behaves as expected:
-/

#eval ColN.eval 0 1
#eval ColN.eval 0 2

#eval ColN.eval 1 0
#eval ColN.eval 1 1
#eval ColN.eval 1 2

#eval z10.eval 0
#eval z10.eval 1
#eval z10.eval 2

/-!
Yikes! The partially applied form is horrific.
-/
#reduce z10.eval

/-!
But that form is equivalent to a neat and tidy linear function.
-/
example (n : ℕ): z10.eval n = 4 * n + 2 := by
    simp [z10]
    ring

/-!
In the hopes of working with neat functions rather than eye-watering lambdas,
we will start by modelling a simple linear equation with a factor and a constant.

To avoid needing to make eager decisions, we'll leavel the type of numbers we're using until later.
-/

/--! A linear equation, of the form `y = m*x+c` -/
@[ext]
structure LinEq (α : Type) :=
  (m : α)
  (c : α)
deriving Repr

@[simp, simps]
instance {α : Type} [HMul α α α]: HMul α (LinEq α) (LinEq α) where
  hMul a b := ⟨a * b.m, a * b.c⟩

@[simp, simps]
instance : HMul ℕ (LinEq ℚ) (LinEq ℚ) where
  hMul a b := (a : ℚ) * b

@[simp, simps]
instance {α : Type} [HAdd α α α]: HAdd α (LinEq α) (LinEq α) where
  hAdd a b := ⟨b.m, a + b.c⟩

@[simp, simps]
instance : HAdd ℕ (LinEq ℚ) (LinEq ℚ) where
  hAdd a b := (a : ℚ) + b

@[simp, simps]
instance {α : Type} [HDiv α α α]: HDiv (LinEq α) α (LinEq α) where
  hDiv a b := LinEq.mk (a.m / b) (a.c / b)

@[simp, simps]
instance : HDiv (LinEq ℚ) ℕ (LinEq ℚ) where
  hDiv a b := a / (b : ℚ)

@[simp] def n_0 {α : Type} [Zero α] [One α] : LinEq α := (LinEq.mk 0 0)
@[simp] def n_0_ℕ := @n_0 ℕ _ _
@[simp] def n_0_ℚ := @n_0 ℚ _ _


@[simp] def n_1 {α : Type} [Zero α] [One α] : LinEq α := (LinEq.mk 1 0)
@[simp] def n_1_ℕ := @n_1 ℕ _ _
@[simp] def n_1_ℚ := @n_1 ℚ _ _

#eval z10.eval n_1_ℕ

example (n : LinEq ℕ): z10.eval n = (2 + 4*n) := by
  simp
  ring


/--! Evaluate a linear equation at some number. -/
@[simp]
def LinEq.eval {α} [Semiring α] (le : LinEq α) (n : α) : α := le.m * n + le.c

/-! It appears to work, as seen here: -/
#eval (0 : ColN).eval n_1_ℕ 
#eval ((0 : ColN).eval n_1_ℕ).eval 0
#eval ((0 : ColN).eval n_1_ℕ).eval 1
#eval ((0 : ColN).eval n_1_ℕ).eval 2
#eval (1 : ColN).eval n_1_ℕ
#eval ((1 : ColN).eval n_1_ℕ).eval 0
#eval ((1 : ColN).eval n_1_ℕ).eval 1
#eval ((1 : ColN).eval n_1_ℕ).eval 2
#eval z10.eval n_1_ℕ 
#eval (z10.eval n_1_ℕ).eval 0
#eval (z10.eval n_1_ℕ).eval 1
#eval (z10.eval n_1_ℕ).eval 2

/-!
Obviously, it should be true that `ColN.eval` applied to a natural number is equal to `ColN.eval`
applied to the unit linear equation at this same natural number.

Best check though.
-/
theorem eval_nat_eq_eval_lineq1 (n : ℕ) (cn : ColN): ColN.eval cn n = (cn.eval n_1_ℕ).eval n := by
    induction cn with
    | zero =>
        simp
    | even_of cm h =>
        simp
        rw [h]
        simp
        ring
    | odd_of cm h =>
        simp
        rw [h]
        simp
        ring

/-! And with that, we're done representing the numerals that will be inputs to the collatz function.

What has all this work bought us?
Well, appart from the inherrent beauty of it, we've also derived something rather special.
A given collatz numeral allows us to compute a linear equation that identifies every single place
in the numberline that a particular sequence of collatz steps fits.
The `z10` numeral is every single place where collatz will reduce an even number to an odd number.
The next step is to see if we can perform the same magic we just performed over the inputs to the
collatz function to something similar over the collatz chains themselves.
-/

/-!
## Sequences of collatz application as numerals.

Repeated application of the collatz function results in a sequence of step_up (`3n+1`),
and a step_down (`n/2`) steps.
In keeping with the previous section, let's represent this explicitly,
treat it a bit like a number and see what happens this time.

We will use `zero` to represent the end of a sequence.
It is probably mis-named, but we'll stick with it for now.
Then the `step_up` and `step_down` constructors represent the obvious.
-/
inductive ColS where
| zero : ColS
| step_up : ColS → ColS    -- the rising collatz step, applied at odd numbers
| step_down : ColS → ColS  -- the falling collatz step, applied at even numbers
deriving Repr

/-! It is evaluated in the obvious way.
This time, we need to compute within the rational numbers, as we are dividing.
When the `step_up` and `step_down` operations are applied correctly to a natural number,
they will, of course, always produce whole-number results.
However, without that context of if we are applying them to an odd or even number,
it is easier to do things with fractions.
-/
@[simp]
def ColS.eval {α : Type} [HMul ℕ α α] [HAdd ℕ α α] [HDiv α ℕ α](cs: ColS) (n :α) : α := match cs with
| ColS.zero => n
| ColS.step_up ds => 1 + 3 * (ds.eval n)
| ColS.step_down ds => (ds.eval n) / 2

/-! And we can see that they behave pretty much how we would expect, computing collatz chains. -/
#eval ColS.zero.eval 1
#eval (ColS.step_up $ ColS.zero).eval 1
#eval (ColS.step_down $ ColS.step_up $ ColS.zero).eval 1
#eval (ColS.step_down $ ColS.step_down $ ColS.step_up $ ColS.zero).eval 1

#eval (ColS.step_up $ ColS.zero).eval 3
#eval (ColS.step_down $ ColS.step_up $ ColS.zero).eval 3
#eval (ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero).eval 3
#eval (ColS.step_down $ ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero).eval 3
#eval (ColS.step_down $ ColS.step_down $ ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero).eval 3
#eval (ColS.step_down $ ColS.step_down $ ColS.step_down $ ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero).eval 3
#eval (ColS.step_down $ ColS.step_down $ ColS.step_down $ ColS.step_down $ ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero).eval 3

@[simp] instance : HMul ℕ ℚ ℚ where
  hMul a b := (a : ℚ) * b 
@[simp] instance : HAdd ℕ ℚ ℚ where
  hAdd a b := (a : ℚ) + b
@[simp] instance : HDiv ℚ ℕ ℚ where
  hDiv a b := a / (b : ℚ)

/-!
Again, we would like to be confident that the two ways of evaluating a ColS numeral are equivalent.
So let's check that.
-/
theorem cols_eval_eq_to_lf_eval (cs : ColS) (n : ℚ): cs.eval n = (cs.eval n_1_ℚ).eval n := by
  induction cs with
  | zero =>
    simp only [ColS.eval, LinEq.eval, n_1_ℚ, n_1, one_mul, add_zero]
  | step_up ds h =>
    simp only [ColS.eval, instHAddNatRat, instHMulNatRat, instHDivRatNat, h, LinEq.eval, instHMulNatLinEqRat,
      instHMulLinEq, instHAddNatLinEqRat, instHAddLinEq, instHDivLinEqRatNat, instHDivLinEq, n_1_ℚ, n_1, Nat.cast_ofNat,
      Nat.cast_one, instHMulNatLinEqRat_hMul, instHAddNatLinEqRat_hAdd]
    ring
  | step_down ds h =>
    simp only [ColS.eval, h, LinEq.eval, instHMulLinEq, instHAddLinEq, n_1_ℕ, n_1]
    field_simp

/-!
And now we can look at some examples of what collatz sequence numerals look like in practice.
-/

def cn3 := (ColN.odd_of $ ColN.odd_of ColN.zero).eval n_1_ℚ

#eval ColS.zero.eval n_1_ℚ 
#eval ColS.zero.eval 1

#eval ColS.zero.eval cn3

#eval ((ColS.step_up $ ColS.zero).eval n_1_ℚ)
#eval ((ColS.step_up $ ColS.zero).eval n_1_ℚ).eval 3
#eval ((ColS.step_up $ ColS.zero).eval cn3)


#eval (ColS.step_down $ ColS.step_up $ ColS.zero).eval n_1_ℚ
#eval (ColS.step_down $ ColS.step_down $ ColS.step_up $ ColS.zero).eval n_1_ℚ
#eval (ColS.step_down $ ColS.step_up $ ColS.zero).eval cn3

#eval ((ColS.step_up $ ColS.zero).eval n_1_ℚ)
#eval ((ColS.step_up $ ColS.zero).eval n_1_ℚ).eval 3
#eval ((ColS.step_up $ ColS.zero).eval cn3)

#eval ((ColS.step_down $ ColS.step_up $ ColS.zero).eval n_1_ℚ)
#eval ((ColS.step_down $ ColS.step_up $ ColS.zero).eval n_1_ℚ).eval 3
#eval ((ColS.step_down $ ColS.step_up $ ColS.zero).eval cn3)

#eval ((ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero).eval n_1_ℚ)
#eval ((ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero).eval n_1_ℚ).eval 3
#eval ((ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero).eval cn3)

#eval ((ColS.step_down $ ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero).eval n_1_ℚ)
#eval ((ColS.step_down $ ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero).eval n_1_ℚ).eval 3
#eval ((ColS.step_down $ ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero).eval cn3)

#eval ((ColS.step_down $ ColS.step_down $ ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero).eval n_1_ℚ)
#eval ((ColS.step_down $ ColS.step_down $ ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero).eval n_1_ℚ).eval 3
#eval ((ColS.step_down $ ColS.step_down $ ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero).eval cn3)

#eval ((ColS.step_down $ ColS.step_down $ ColS.step_down $ ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero).eval n_1_ℚ)
#eval ((ColS.step_down $ ColS.step_down $ ColS.step_down $ ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero).eval n_1_ℚ).eval 3
#eval ((ColS.step_down $ ColS.step_down $ ColS.step_down $ ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero).eval cn3)

#eval ((ColS.step_down $ ColS.step_down $ ColS.step_down $ ColS.step_down $ ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero).eval n_1_ℚ)
#eval ((ColS.step_down $ ColS.step_down $ ColS.step_down $ ColS.step_down $ ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero).eval n_1_ℚ).eval 3
#eval ((ColS.step_down $ ColS.step_down $ ColS.step_down $ ColS.step_down $ ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero).eval cn3)



/-!
Where as ColN was intimately related to binary,
it looks like ColS is in turn intimiately related to dyadic rational.
All the terms are of the form `a/2^b`.


-/
