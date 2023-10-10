import Mathlib.Tactic
import Mathlib

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

A simple way to write these numerals is in the form `z10` where `z` represents the terminal `zero`,
1 represents an `odd_of` and 0 represents an `even_of`, applying the constructors to the left.

The length of the number is the count of `even_of` and `odd_of` constructors.
So the length of `z10` is 2.

Where this differs from binary is that we can substitute the `zero` terminal with any `n₀`,
making the evaluation of these numerals equivalent to computing a linear function of `n₀`.
This evaluates to the corresponding binary numeral when `n₀=0`.
For a collatz numeral `z n₀` for the numeral rewritten in this manner, and `z 0` for the corresponding numeric value.
More generally, a z digit is the class `(z n₀) mod (2^p) = (z 0) ` where `p` is the length of the numeral.

This means that our collatz numerals differ from normal binary numerals, in that leading zeros are significant.
`z1` is a different numeral from `z01`, as `z1` is the numbers `2n+1`, where as `z01` is the numbers `4n+1`.
-/

/--!
A collatz numeral.
-/
inductive ColN where
    | zero      : ColN          -- zero, most-significant-figure terminal
    | even_of   : ColN → ColN   -- the even number that is twice the previous
    | odd_of    : ColN → ColN   -- the odd number that is one more than twice the previous
deriving Repr

-- The z0 numeral is equivalent to 0.
def z0 := ColN.zero

def z0' := ColN.even_of ColN.zero

-- The z1 numeral is equvalent to 1.
def z1 := ColN.odd_of ColN.zero

-- The z10 numeral is equivalent to 2.
def z10 := ColN.even_of $ ColN.odd_of ColN.zero

-- The z11 numeral is equivalent to 3.
def z11 := ColN.odd_of $ ColN.odd_of ColN.zero

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

@[simp]
theorem coln_eval_zero : ColN.zero.eval = id := rfl

@[simp]
theorem coln_eval_even_of_zero : (ColN.even_of ColN.zero).eval = (2 * .) := rfl

@[simp]
def append (a b : ColN) : ColN := match b with
| ColN.zero => a
| ColN.even_of c => ColN.even_of (append a c)
| ColN.odd_of c => ColN.odd_of (append a c)

@[simp]
theorem eval_append {a b : ColN} {n : ℕ}: (append a b).eval n = b.eval (a.eval n) := by
  induction b with
  | zero => rfl
  | even_of cn h =>
    simp
    assumption
  | odd_of cn h =>
    simp
    assumption


@[simp]
theorem eval_absorb_even_of_zero : cm = append (ColN.even_of ColN.zero) f → cm.eval 0 = f.eval 0 := by
  rintro hcm
  rw [hcm]
  simp

@[simp]
theorem eval_eq {α : Type} [HMul ℕ α α] [HAdd ℕ α α] (a: ColN) (i j : α) : i = j → a.eval i = a.eval j := by
  induction a with
  | zero => simp
  | even_of a h =>
    intro ij_eq
    have hij := h ij_eq
    simp [hij]
  | odd_of a h =>
    intro ij_eq
    have hij := h ij_eq
    simp [hij]


@[simp]
theorem eval_even_of_zeros_eq_zero {p: ℕ} : ((Nat.iterate ColN.even_of p) ColN.zero).eval 0 = 0 := by
  induction p with
  | zero => rfl
  | succ n h =>
    rw [Function.iterate_succ_apply' ColN.even_of n ColN.zero]
    simp
    assumption

theorem leading_zeros_same_c {cn : ColN} {p: ℕ} :
  (append (ColN.even_of^[p] ColN.zero) cn).eval 0 = cn.eval 0 := by
  simp


/-!
It behaves as expected:
-/

#eval z0.eval 0
#eval z0.eval 1
#eval z0.eval 2

#eval z1.eval 0
#eval z1.eval 1
#eval z1.eval 2

#eval z10.eval 0
#eval z10.eval 1
#eval z10.eval 2

#eval z11.eval 0
#eval z11.eval 1
#eval z11.eval 2

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

/--!
We can manipulate `LinEq` values directly, but it would be far more convenient if we could apply
scalar addition, multiplication and division to them with the normal syntax.
This is supported by providing instances of the `HAdd`, `HMul` and `HDiv` classes.
-/

@[simp, simps]
instance {α : Type} [HMul α α α]: HMul α (LinEq α) (LinEq α) where
  hMul a b := ⟨a * b.m, a * b.c⟩

@[simp, simps]
instance : HMul ℕ (LinEq ℚ) (LinEq ℚ) where
  hMul a b := (Rat.ofInt $ Int.ofNat a) * b

@[simp, simps]
instance {α : Type} [HAdd α α α]: HAdd α (LinEq α) (LinEq α) where
  hAdd a b := ⟨b.m, a + b.c⟩

@[simp, simps]
instance : HAdd ℕ (LinEq ℚ) (LinEq ℚ) where
  hAdd a b := (Rat.ofInt $ Int.ofNat a) + b

@[simp, simps]
instance {α : Type} [HDiv α α α]: HDiv (LinEq α) α (LinEq α) where
  hDiv a b := LinEq.mk (a.m / b) (a.c / b)

@[simp, simps]
instance : HDiv (LinEq ℚ) ℕ (LinEq ℚ) where
  hDiv a b := a / (Rat.ofInt $ Int.ofNat b)

@[simp] def le_0 {α : Type} [Zero α] [One α] : LinEq α := (LinEq.mk 0 0)
@[simp] def le_0_ℕ := @le_0 ℕ _ _
@[simp] def le_0_ℚ := @le_0 ℚ _ _


@[simp] def le_1 {α : Type} [Zero α] [One α] : LinEq α := (LinEq.mk 1 0)
@[simp] def le_1_ℕ := @le_1 ℕ _ _
@[simp] def le_1_ℚ := @le_1 ℚ _ _

#eval z10.eval le_1_ℕ

example (n : LinEq ℕ): z10.eval n = (2 + 4*n) := by
  simp
  ring


/--! Evaluate a linear equation at some number. -/
@[simp]
def LinEq.eval {α} [Semiring α] (le : LinEq α) (n : α) : α := le.m * n + le.c

/-! It appears to work, as seen here: -/
#eval z0.eval le_1_ℕ 
#eval (z0.eval le_1_ℕ).eval 0
#eval (z0.eval le_1_ℕ).eval 1
#eval (z0.eval le_1_ℕ).eval 2
#eval z1.eval le_1_ℕ
#eval (z1.eval le_1_ℕ).eval 0
#eval (z1.eval le_1_ℕ).eval 1
#eval (z1.eval le_1_ℕ).eval 2
#eval z10.eval le_1_ℕ 
#eval (z10.eval le_1_ℕ).eval 0
#eval (z10.eval le_1_ℕ).eval 1
#eval (z10.eval le_1_ℕ).eval 2
#eval z11.eval le_1_ℕ 
#eval (z11.eval le_1_ℕ).eval 0
#eval (z11.eval le_1_ℕ).eval 1
#eval (z11.eval le_1_ℕ).eval 2

/-!
Obviously, it should be true that `ColN.eval` applied to a natural number is equal to `ColN.eval`
applied to the unit linear equation at this same natural number.

Best check though.
-/
theorem eval_nat_eq_eval_lineq1 (n : ℕ) (cn : ColN): ColN.eval cn n = (cn.eval le_1_ℕ).eval n := by
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

/-!
Lastly, we should be able to convert a natural number into an equivalant collatz number.
-/
def ColN.ofNat (n : ℕ) : ColN :=
if n_is_zero : n = 0 then ColN.zero
else
  let l := n % 2 = 0
  let r := n / 2
  if l then ColN.even_of $ ColN.ofNat r
  else ColN.odd_of $ ColN.ofNat r
decreasing_by
  simp_wf
  exact Nat.bitwise_rec_lemma n_is_zero

theorem ofNat_evals_to_nat_zero: (ColN.ofNat 0).eval 0 = 0 := by simp

theorem ofnat_evals_to_nat_even(n : ℕ) (nz : ¬n=0) (nh : (ColN.ofNat n).eval 0 = n): (ColN.ofNat $ 2 * n).eval 0 = 2*n := by
  rw [ColN.ofNat]
  simp [nz, nh]

theorem ofnat_evals_to_nat_odd(n : ℕ) (nh : (ColN.ofNat n).eval 0 = n) : (ColN.ofNat $ 2*n+1).eval 0 = 2*n+1 := by
  rw [ColN.ofNat]
  rw [Nat.odd_iff.mp]
  simp [ColN.eval, Nat.add_comm, Nat.add_mul_div_left, Nat.div_eq_of_lt]
  assumption
  exact odd_two_mul_add_one n

example (a b : ℕ) (ha : 0 < a) (hab : (a = 2*b)): (0 < b) := by
  simp_all only [gt_iff_lt, zero_lt_mul_left]

example (a b : ℕ) (ha : ¬ a = 0) (hab : (a = 2*b)): ¬ b = 0 := by
  simp_all only [mul_eq_zero, false_or, not_false_eq_true]

example (a : ℕ)(ha : ¬ a = 0) : 0 < a := by exact Nat.pos_of_ne_zero ha

example (a b : ℕ)(ha : ¬ a = 0) (hab : (a = 2*b)) : b < a := by
  have pa := Nat.pos_of_ne_zero ha
  simp_all only [mul_eq_zero, false_or, gt_iff_lt, zero_lt_mul_left, lt_mul_iff_one_lt_left]

theorem two_m_helper (m : ℕ) : m < 2 * m + 1 := by
  have mle : m ≤ 2 * m := by
    apply Nat.le_mul_of_pos_left
    simp
  exact Nat.lt_succ.mpr mle

theorem ofNat_evals_to_nat(n : ℕ) : (ColN.ofNat n).eval 0 = n :=
if nz : n = 0 then
  by
    simp [nz]
else by cases (Nat.even_or_odd n) with
  | inl even_n =>
    have ⟨ m, hm ⟩ := even_n
    have m2 : m + m = 2*m := by ring
    have mnz : ¬ m = 0 := by simp_all only [mul_eq_zero, false_or, not_false_eq_true]
    have mev := ofnat_evals_to_nat_even m mnz (ofNat_evals_to_nat m)
    simp_all
  | inr odd_n =>
    have ⟨ m, hm ⟩ := odd_n
    have mov := ofnat_evals_to_nat_odd m (ofNat_evals_to_nat m)
    simp_all
decreasing_by
  have npos := Nat.pos_of_ne_zero nz
  simp_wf
  simp_all only [mul_eq_zero, false_or, gt_iff_lt, zero_lt_mul_left, lt_mul_iff_one_lt_left, two_m_helper]
  
  
#exit

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

/-!
This gets verbose quickly, so we will make some shorthand.
-/

def cs_u := ColS.step_up $ ColS.zero
def cs_ud := ColS.step_down $ ColS.step_up $ ColS.zero
def cs_udu := ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero
def cs_udud := ColS.step_down $ ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero
def cs_ududd := ColS.step_down $ ColS.step_down $ ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero
def cs_ududdd := ColS.step_down $ ColS.step_down $ ColS.step_down $ ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero
def cs_ududddd := ColS.step_down $ ColS.step_down $ ColS.step_down $ ColS.step_down $ ColS.step_up $ ColS.step_down $ ColS.step_up $ ColS.zero

#eval cs_u.eval 3
#eval cs_ud.eval 3
#eval cs_udu.eval 3
#eval cs_udud.eval 3
#eval cs_ududd.eval 3
#eval cs_ududdd.eval 3
#eval cs_ududddd.eval 3

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
theorem cols_eval_eq_to_lf_eval (cs : ColS) (n : ℚ): cs.eval n = (cs.eval le_1_ℚ).eval n := by
  induction cs with
  | zero =>
    simp
  | step_up ds h =>
    simp [h]
    ring
  | step_down ds h =>
    simp [h]
    field_simp

/-!
And now we can look at some examples of what collatz sequence numerals look like in practice.
-/

-- The linear equation in ℚ for z11 (=3).
def cn3 := z11.eval le_1_ℚ
#eval cn3

#eval ColS.zero.eval le_1_ℚ 
#eval ColS.zero.eval 1

#eval ColS.zero.eval cn3

#eval (cs_u.eval le_1_ℚ)
#eval (cs_u.eval le_1_ℚ).eval 3
#eval (cs_u.eval cn3)


#eval (cs_ud.eval le_1_ℚ)
#eval (cs_ud.eval le_1_ℚ).eval 3
#eval cs_ud.eval cn3

#eval (cs_u.eval le_1_ℚ)
#eval (cs_u.eval le_1_ℚ).eval 3
#eval (cs_u.eval cn3)

#eval (cs_ud.eval le_1_ℚ)
#eval (cs_ud.eval le_1_ℚ).eval 3
#eval (cs_ud.eval cn3)

#eval (cs_udu.eval le_1_ℚ)
#eval (cs_udu.eval le_1_ℚ).eval 3
#eval (cs_udu.eval cn3)

#eval (cs_udud.eval le_1_ℚ)
#eval (cs_udud.eval le_1_ℚ).eval 3
#eval (cs_udud.eval cn3)

#eval (cs_ududd.eval le_1_ℚ)
#eval (cs_ududd.eval le_1_ℚ).eval 3
#eval (cs_ududd.eval cn3)

#eval (cs_ududdd.eval le_1_ℚ)
#eval (cs_ududdd.eval le_1_ℚ).eval 3
#eval (cs_ududdd.eval cn3)

#eval (cs_ududddd.eval le_1_ℚ)
#eval (cs_ududddd.eval le_1_ℚ).eval 3
#eval (cs_ududddd.eval cn3)



/-!
Where as ColN was intimately related to binary,
it looks like ColS is in turn intimiately related to dyadic rational.
All the terms are of the form `a/2^b`.

A closer look at the equational solutions show something odd.
The equational form of the ColS expression quite quicly is able to generate non-whole numbers.
Let's look at the first example, where we've gone `3 ↦ 10 ↦ 5`.
-/

def le_5 : LinEq ℚ := { m := (3 : Rat)/2, c := (1 : Rat)/2 }

#eval le_5.eval 0
#eval le_5.eval 1
#eval le_5.eval 2
#eval le_5.eval 3

/-!
We can see that every even-numbered solution is not a whole number.
What this means is that the collatz function only reduces using the `down` step here when the `n`
is odd.
This is due to the way that you can't apply the `up` or `down` step of the collatz function for all `n`.
The `up` step only works where `n` is odd, and the down step only works where `n` is even.

As it happens, this is fine for `n` in the equation for 3, so the evaluation gives:
`{ m := 6, c := 5 }`.
So using `n` for 3, all the solutions at this point are whole numbers.

If we move on through the calculation, we reach a step where `n` for 3 no longer always gives whole-number results.
At `3 ↦ 10 ↦ 5 ↦ 16 ↦ 8 ↦ 4`, we reach the ColS equation:
`{ m := (9 : Rat)/8, c := (5 : Rat)/8 }` and the corresponding equation for `n=3` of
`{ m := (9 : Rat)/2, c := 4 }`
-/

def le_4 : LinEq ℚ := { m := (9 : Rat)/2, c := 4 }
#eval le_4.eval 0
#eval le_4.eval 1
#eval le_4.eval 2
#eval le_4.eval 3

/-!
Again, we see that this doesn't have a whole-number solution for all choices of `n`.
This is because to reduce from 8 to 4, we need the `n` to be even.
That is, it's only defined for `n=3, Even n`.
We can represent this directly by rewriting the expression for tree from `z11` to `z011`.
The leading zero is saying that `n` is guaranteed even.
-/

def z011 := append z0' z11
def cn03 := z011.eval le_1_ℚ
/-!
And just to check that z011 is another way to write 3, here it is.
-/
#eval z011.eval 0

/-!
If we plug this into the expression above, we now get:
-/

#eval (cs_ududd.eval cn03)
#eval (cs_ududdd.eval cn03)
#eval (cs_ududddd.eval cn03)

/-!
Again, we see that while it fixes the problem with the 4 case, we now have issues at the 2 and 1 cases.
More leading evens (zeros) will fix that though.
-/

def z0011 := append z0' z011
def cn003 := z0011.eval le_1_ℚ

#eval (cs_ududd.eval cn003)
#eval (cs_ududdd.eval cn003)
#eval (cs_ududddd.eval cn003)


def z00011 := append z0' z0011
def cn0003 := z00011.eval le_1_ℚ

#eval z11
#eval z011
#eval z0011
#eval z00011


#eval cn3
#eval cn03
#eval cn003
#eval cn0003



#eval z11.eval le_0_ℚ
#eval z011.eval le_0_ℚ
#eval z0011.eval le_0_ℚ
#eval z00011.eval le_0_ℚ

#eval (cs_ududd.eval cn0003)
#eval (cs_ududdd.eval cn0003)
#eval (cs_ududddd.eval cn0003)

/-!
And we're done.

So, the collatz numeral `z00011` gives us an equation for all valid collatz chains where the smallest
example is the chain from 3 to 1.
More generally, it is the function:

`32n+15 ↦ 
-/

def three_chain (n : ℚ) : ℚ × ℚ := ⟨ (z00011.eval n), (cs_ududddd.eval cn0003).eval n ⟩


#eval three_chain 0
#eval three_chain 1
#eval three_chain 2
#eval three_chain 3
#eval three_chain 4
#eval three_chain 5