variable (p q : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  rw [and_comm]

example : p ∨ q ↔ q ∨ p := by
  rw [or_comm]


-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  rw [and_assoc]

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  rw [or_assoc]


-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  simp

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  simp


-- other properties
example : (p → q → r) ↔ (p ∧ q → r) := by
  rw [and_imp]
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  rw [or_imp]

example : ¬ (p ∨ q) ↔ ¬p ∧ ¬q := by
  simp

example : ¬p ∨ ¬q → ¬ (p ∧ q) := by
  rintro (hnp | hnq) ⟨hp, hq⟩
  · exact hnp hp
  · exact hnq hq

example : ¬ (p ∧ ¬p) := by
  intro ⟨hp, hnp⟩
  exact hnp hp

example : p ∧ ¬q → ¬(p → q) := by
  rintro ⟨hp, hnq⟩ hpq
  exact hnq (hpq hp)

example : ¬p → (p → q) := by
  intro hnp hp
  contradiction

example : (¬p ∨ q) → (p → q) := by
  intro h hp
  cases h with
  | inl hnp =>
    contradiction
  | inr hq =>
    exact hq

example : p ∨ False ↔ p := by
  simp

example : p ∧ False ↔ False := by
  simp

example : (p → q) → (¬q → ¬p) := by
  rintro hpq hnq hp
  exact hnq (hpq hp)
