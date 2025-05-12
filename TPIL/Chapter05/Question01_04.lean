variable {α : Type} (p q : α → Prop)
open Classical

-- 1.
example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  simp

example : (∀ x, p x → q x) → (∀ x, p x) → ∀ x, q x := by
  rintro h₁ h₂ x
  exact h₁ x (h₂ x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  rintro (hp | hq) x
  · exact Or.inl (hp x)
  · exact Or.inr (hq x)


-- 2.
example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  rw [forall_and]

section

variable (r : Prop)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  apply Iff.intro
  · intro h; by_cases hr : r
    · right; exact hr
    · left; intro x; cases h x with
      | inl hp => exact hp
      | inr hr' => contradiction
  · rintro (hp | hr) x
    · exact Or.inl (hp x)
    · exact Or.inr hr

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  apply Iff.intro
  · intro h hr x; exact h x hr
  · intro h x hr; exact h hr x

end

-- 3.
