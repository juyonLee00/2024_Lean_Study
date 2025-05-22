variable (p q : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  rw [and_comm]

example : p ∨ q ↔ q ∨ p := by
  rw [or_comm]

section

variable (r : Prop)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  rw [and_assoc]

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  rw [or_assoc]


-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · rintro ⟨hp, (hq | hr)⟩
    · exact Or.inl ⟨hp, hq⟩
    · exact Or.inr ⟨hp, hr⟩
  · rintro (⟨hp, hq⟩ | ⟨hp, hr⟩)
    · exact ⟨hp, Or.inl hq⟩
    · exact ⟨hp, Or.inr hr⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  · intro h
    match h with
    | Or.inl hp => exact ⟨Or.inl hp, Or.inl hp⟩
    | Or.inr ⟨hq, hr⟩ => exact ⟨Or.inr hq, Or.inr hr⟩
  · intro ⟨hpq, hpr⟩
    match hpq, hpr with
    | Or.inl hp, _ => exact Or.inl hp
    | _, Or.inl hp => exact Or.inl hp
    | Or.inr hq, Or.inr hr => exact Or.inr ⟨hq, hr⟩


-- other properties
example : (p → q → r) ↔ (p ∧ q → r) := by
  rw [and_imp]

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  rw [or_imp]

end

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
  intro ⟨hp, hnq⟩ hpq
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
  intro hpq hnq hp
  exact hnq (hpq hp)
