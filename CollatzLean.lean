import Mathlib.Tactic

variable (n : Nat)
variable (a b c : Nat)
variable (i j k p : Nat)

theorem mod21 {n: Nat} : n%2=1 → 0 < n := by
    induction n
    simp
    simp
        


def is_even a := ∃ b, 2*b = a

def gen_even a := 2*a

def is_odd a := ∃ b, 1 + 2*b = a

def gen_odd a := 2*a + 1

def collatz := if n % 2 == 0 then n / 2 else 3 * n + 1

theorem collatz_odd_to_even : is_odd n -> is_even (collatz n) := by
    rintro ⟨i, rfl⟩
    use 3 * i + 2
    simp [collatz]
    simp [mul_add]
    simp [add_comm 3]
    simp [← mul_assoc]

@[simp] theorem collatz_nonzero : collatz n > 0 ↔ n > 0 := by
    simp [collatz]
    split
    case inl h =>
        obtain ⟨i, rfl⟩ := Nat.dvd_of_mod_eq_zero h
        simp
    case inr nh =>
        simp
        simp [Nat.mul_mod_left] at nh
        exact mod21 nh
        


def collatz_conjecture_n n := n > 0 -> ∃ p, Nat.iterate collatz p n = 1

def collatz_conjecture := ∀ n, collatz_conjecture_n n

theorem C1 : collatz_conjecture_n 1 := by
    simp [collatz_conjecture_n]
    use 0 -- p=0
    simp

theorem C2_calc : collatz_conjecture_n 2 := by
    simp [collatz_conjecture_n]
    use 1
    simp

theorem C4_calc : collatz_conjecture_n 4 := by
    simp [collatz_conjecture_n]
    use 2
    simp

@[simp] theorem collatz_induct :    0 < n ->
                            collatz_conjecture_n (collatz n) ->
                            collatz_conjecture_n n := by
    intro ngzero
    simp [*, collatz_conjecture_n]
    intros q cq
    use (Nat.succ q)
    assumption


