def even (n : Nat) : Prop := ∃ k, n = 2 * k

def prime (n : Nat) : Prop := 1 < n ∧ ∀ m : Nat, m ∣ n → m = 1 ∨ m = n

def infinitely_many_primes : Prop := ∀ n : Nat, ∃ p : Nat, prime p ∧ p > n

def Fermat_prime (n : Nat) : Prop := ∃ k : Nat, n = 2 ^ (2 ^ k) + 1 ∧ prime n

def infinitely_many_Fermat_primes : Prop := ∀ n : Nat, ∃ p : Nat, Fermat_prime p ∧ p > n

def goldbach_conjecture : Prop := ∀ n : Nat, even n ∧ 2 < n → ∃ a b : Nat, prime a ∧ prime b ∧ n = a + b

def Goldbach's_weak_conjecture : Prop := ∀ n : Nat, n > 5 ∧ ¬ even n → ∃ a b c : Nat, prime a ∧ prime b ∧ prime c ∧ n = a + b + c

def Fermat's_last_theorem : Prop := ∀ n x y z : Nat, n ≥ 3 → x ^ n + y ^ n ≠ z ^ n

/-- Bulhwi: please restate Fermat's Last Theorem. -/
theorem not_flt : ¬Fermat's_last_theorem := by
  intro h
  have hne : 0 ^ 3 + 0 ^ 3 ≠ 0 ^ 3 := h 3 0 0 0 (Nat.le_refl 3)
  simp at hne
