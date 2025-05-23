set_option linter.unusedVariables false

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := fun ⟨_, hr⟩ => hr

example (a : α) : r → (∃ x : α, r) := fun hr => ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun ⟨x, ⟨hpx, hr⟩⟩ => ⟨⟨x, hpx⟩, hr⟩)
    (fun ⟨⟨x, hpx⟩, hr⟩ => ⟨x, ⟨hpx, hr⟩⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨x, hpq⟩ =>
      Or.elim hpq
        (fun hp => Or.inl ⟨x, hp⟩)
        (fun hq => Or.inr ⟨x, hq⟩))
    (fun h =>
      Or.elim h
        (fun ⟨x, hp⟩ => ⟨x, Or.inl hp⟩)
        (fun ⟨x, hq⟩ => ⟨x, Or.inr hq⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h ⟨x, hnp⟩ => hnp (h x))
    (fun h x =>
      byContradiction (fun hnp => h ⟨x, hnp⟩))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (fun ⟨x, px⟩ h => h x px)
    (fun h =>
      byContradiction
        (fun h' => h (fun x px => h' ⟨x, px⟩)))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (fun h x hp => h ⟨x, hp⟩)
    (fun h ⟨x, hp⟩ => h x hp)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h => byContradiction (fun h' => h (fun x => byContradiction (fun hpx => h' ⟨x, hpx⟩))))
    (fun ⟨x, hnp⟩ h => hnp (h x))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (fun h ⟨x, hp⟩ => h x hp)
    (fun h x hp => h ⟨x, hp⟩)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨x, hpxr⟩ hpx => hpxr (hpx x))
    (fun h =>
      byCases
        (fun hpx : ∀ x, p x => ⟨a, fun _ => h hpx⟩)
        (fun hnp => byContradiction (fun h' =>
          let contra := fun x => byContradiction (fun hpx => h' ⟨x, fun _ => absurd ‹_› hpx⟩)
          hnp contra)))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (fun ⟨x, hx⟩ hr => ⟨x, hx hr⟩)
    (fun h =>
      byCases
        (fun hr : r => sorry)
        (fun hnr : ¬r => sorry))
