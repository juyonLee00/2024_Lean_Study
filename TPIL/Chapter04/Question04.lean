def solve_even (n : Nat) : Prop := ∃ k, n = 2 * k

def solve_prime (n : Nat) : Prop := 1 < n ∧ ∀ m : Nat, m ∣ n → m = 1 ∨ m = n

def solve_infinitely_many_primes : Prop := ∀ n : Nat, ∃ p : Nat, solve_prime p ∧ p > n

def solve_Fermat_prime (n : Nat) : Prop := ∃ k : Nat, n = 2 ^ (2 ^ k) + 1 ∧ solve_prime n

def solve_infinitely_many_Fermat_primes : Prop := ∀ n : Nat, ∃ p : Nat, solve_Fermat_prime p ∧ p > n

def solve_goldbach_conjecture : Prop := ∀ n : Nat, solve_even n ∧ 2 < n → ∃ a b : Nat, solve_prime a ∧ solve_prime b ∧ n = a + b

def solve_Goldbach's_weak_conjecture : Prop := ∀ n : Nat, n > 5 ∧ ¬ solve_even n → ∃ a b c : Nat, solve_prime a ∧ solve_prime b ∧ solve_prime c ∧ n = a + b + c

def solve_Fermat's_last_theorem_pos : Prop :=
  ∀ (n x y z : Nat),
    n ≥ 3 →
    1 ≤ x →
    1 ≤ y →
    1 ≤ z →
    x ^ n + y ^ n ≠ z ^ n

/-
Bulhwi: please restate Fermat's Last Theorem.
theorem not_flt : ¬Fermat's_last_theorem := by
  intro h
  have hne : 0 ^ 3 + 0 ^ 3 ≠ 0 ^ 3 := h 3 0 0 0 (Nat.le_refl 3)
  simp at hne
-/
