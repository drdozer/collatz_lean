import Mathlib.Tactic



namespace Rat

/--!
Some theorems describing cases where ℚ corresponds to ℤ.
-/

theorem isInt_ofInt (i : ℤ) : (Rat.ofInt i).isInt = true := by
    simp only [Rat.isInt, Rat.ofInt]

theorem floor_eq_self_if_isInt (a : ℚ) : a.isInt → a.floor = a := by
    simp only [Rat.isInt, Nat.beq_eq_true_eq, Rat.floor, Int.cast_ite]
    intro ha1
    simp [ha1, ←den_eq_one_iff a]

theorem ceil_eq_self_if_isInt (a : ℚ) : a.isInt → a.ceil = a := by
    simp only [Rat.isInt, Nat.beq_eq_true_eq, Rat.ceil, Int.cast_ite, Int.cast_add, Int.cast_one]
    intro ha1
    simp [ha1, ← den_eq_one_iff a]

theorem sum_isInt (a b : ℚ) : a.isInt → b.isInt → (a + b).isInt := by
    simp only [Rat.isInt, Nat.beq_eq_true_eq, Rat.add_def]
    intro ha hb
    simp only [hb, Nat.cast_one, mul_one, ha]
    simp [Rat.normalize]

theorem sub_isInt (a b : ℚ) : a.isInt → b.isInt → (a - b).isInt := by
    simp only [Rat.isInt, Nat.beq_eq_true_eq, Rat.sub_def]
    intro ha hb
    simp only [hb, Nat.cast_one, mul_one, ha]
    simp [Rat.normalize]

theorem mul_isInt (a b : ℚ) : a.isInt → b.isInt → (a * b).isInt := by
    simp only [Rat.isInt, Nat.beq_eq_true_eq, Rat.mul_def]
    intro ha hb
    simp only [ha, hb, mul_one]
    simp [Rat.normalize]

end Rat
-- attribute [local simp] parity_simps

variable (n : Nat)
variable (a b c : Nat)
variable (i j k p q : Nat)
-- variable (f : Nat → Nat)

attribute [-simp] Nat.odd_iff_not_even -- this simp yecks things up

-- we should really be grabbing everything in the partiy_simps set, but that's not supported
attribute [simp] Nat.even_add
attribute [simp] Nat.even_mul

@[simp] theorem iff_even_given_odd : Odd n -> (if Even n then x else y) = y := by
    intro hon
    have h : ¬ Even n := by exact Iff.mp Nat.odd_iff_not_even hon
    simp [h]

/-!
# The collatz conjecture

So far, the 3n+1 problem, or collatz conjecture, is unsolved.
Take the following function:
-/


def collatz := if Even n then n / 2 else 3 * n + 1

/-!
Now pick any whole number greater than zero.
Apply the collatz function to that.
And again.
And again.
This will generate an unending sequence of whole numbers.
You will eventually hit the number 1.
-/

-- For a given positive integer, within a finite number of steps it will hit 1.
def collatz_conjecture_n n := n > 0 -> ∃ p, Nat.iterate collatz p n = 1

-- For all integers, within a finite number of steps, they will hit 1.
def collatz_conjecture := ∀ n, collatz_conjecture_n n

/-!
We can double-check that the collatz function doesn't reach zero, and was not reached from zero.
-/

@[simp] theorem collatz_nonzero : collatz n > 0 ↔ n > 0 := by
    simp only[collatz]
    split
    case inl h =>   -- even case
        obtain ⟨ i, hn ⟩ := h
        rw [←Nat.two_mul] at hn
        simp [*]
    case inr nh =>  -- odd case
        obtain ⟨ i, rfl ⟩ := Iff.mpr Nat.odd_iff_not_even nh
        simp

/-!
We can also observe that if we take the collatz of any odd number, the result is guaranteed to be an even number.
-/

theorem collatz_odd_to_even : Odd n -> Even (collatz n) := by
    intro hon
    have h : ¬ Even n := by exact Iff.mp Nat.odd_iff_not_even hon
    rw [collatz, if_neg h]
    obtain ⟨ x, rfl ⟩ := hon
    use 3*x+2
    ring    


/-!
If we have a starting number, and apply collatz, and that new number reaches 1, then our starting number also reaches 1.
-/

@[simp] theorem collatz_induct :
        0 < n ->
        collatz_conjecture_n (collatz n) ->
        collatz_conjecture_n n := by
    intro ngzero
    simp [*, collatz_conjecture_n]
    intros q cq
    use (Nat.succ q)
    assumption



/-!
It is useful to think of sequences made by repeatedly applying the collatz function.
These are entirely defined by their starting (left) number, and their ending (right) number.
They have a length, which is how many times collatz must be applied to get from left to right.
It is convenient to carry around a proof that `left` and `right` really are `length` applications of collatz appart.
-/

structure CollatzSequence where
    left: Nat
    right: Nat
    length: Nat
    is_valid : Nat.iterate collatz length left = right
deriving Repr

/-!
If we have two collatz sequences that "touch", so that the right of one is the left of the other, we can always join them into a larger sequence.
-/

def join (ls rs : CollatzSequence) (touch: ls.right = rs.left): CollatzSequence :=
    { left := ls.left, right := rs.right , length := rs.length + ls.length, is_valid := by
        have lh := ls.is_valid
        have rh := rs.is_valid
        rw [touch] at lh
        rw [←lh] at rh
        have cmp := Function.iterate_add_apply collatz rs.length ls.length ls.left
        simp [←cmp] at rh
        assumption
    }

/-!
There are two special sequences, the one that follows a single application of collatz starting from an even number, and an odd number, respecrively.
-/
def even_1 (a : Nat) : CollatzSequence :=
    {
        left := 2*a
        right := a
        length := 1
        is_valid := by
            simp [collatz]
    }

def odd_1 (a : Nat) : CollatzSequence :=
    {
        left := 2*a+1
        right := 6*a + 4
        length := 1
        is_valid := by
            have nel := by exact Iff.mp Nat.odd_iff_not_even (odd_two_mul_add_one a)
            simp [*, collatz]
            ring
    }


/-!
Just to double-check, the left-hand value of the even case is even,
the left-hand value of the odd case is odd and the right-hand value of the odd case is even.
-/
example : Even (even_1 a).left := by simp [even_1]
example : Odd (odd_1 a).left := by simp [odd_1]
example : Even (odd_1 a).right := by simp [odd_1]

structure LF :=
    (m : ℕ)
    (c : ℚ)
    (m_gt_zero : 0 < m)

def LF.app (lf : LF) (n : ℚ) : ℚ := lf.m * n + lf.c

def whole_number_solutions (lf : LF) := ∀ n, Rat.isInt n -> Rat.isInt (lf.app n)

theorem solution_is_a_whole_number_if_c_is_a_whole_number (lf : LF) : Rat.isInt (lf.c) → whole_number_solutions lf := by
    simp only [Rat.isInt, Nat.beq_eq_true_eq, whole_number_solutions, LF.app]
    rintro c_wn n n_wn
    

def solutions (lf₁ lf₂ : LF) : LF×LF := 
    let mgcd := Nat.gcd lf₁.m lf₂.m
    let lfL := {
        m := lf₂.m / mgcd
        c := lf₂.c / lf₁.m
        m_gt_zero := by 
            exact Nat.div_gcd_pos_of_pos_right lf₁.m lf₂.m_gt_zero
    }
    let lfR := {
        m := lf₁.m / mgcd
        c := lf₁.c / lf₂.m
        m_gt_zero := by
            exact Nat.div_gcd_pos_of_pos_left lf₂.m lf₁.m_gt_zero
    }
    ⟨ lfL, lfR ⟩


theorem solutions_valid (lf₁ lf₂ : LF) : (⟨sL, sR⟩ = solutions lf₁ lf₂) → 
        ∀ n , lf₁.app (sL.app n) = lf₂.app (sR.app n) := by
    simp only [solutions, Prod.mk.injEq, and_imp]
    rintro hsL hsR n
    simp only [LF.app, hsL, Nat.isUnit_iff, hsR]
    have lf₁nz : (lf₁.m : ℚ) ≠ 0 := Iff.mpr Nat.cast_ne_zero $ Nat.pos_iff_ne_zero.mp lf₁.m_gt_zero
    have lf₂nz : (lf₂.m : ℚ) ≠ 0 := Iff.mpr Nat.cast_ne_zero $ Nat.pos_iff_ne_zero.mp lf₂.m_gt_zero

    simp only [Nat.isUnit_iff, mul_add]
    simp only [Nat.isUnit_iff, mul_div_cancel' lf₂.c lf₁nz, mul_div_cancel' lf₁.c lf₂nz]
    simp only [Nat.isUnit_iff, Nat.gcd_dvd_right, ne_eq, Nat.cast_eq_zero, Nat.cast_div_charZero, Nat.gcd_dvd_left]
    ring


