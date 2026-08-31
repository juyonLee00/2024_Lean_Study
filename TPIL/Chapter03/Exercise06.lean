example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    -- 첫 번째 방향: p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r)
    (fun h : p ∨ (q ∧ r) =>
      And.intro
        (h.elim
          (fun hp : p => show p ∨ q from Or.inl hp)
          (fun hqr : q ∧ r => show p ∨ q from Or.inr hqr.left))
        (h.elim
          (fun hp : p => show p ∨ r from Or.inl hp)
          (fun hqr : q ∧ r => show p ∨ r from Or.inr hqr.right)))
    -- 두 번째 방향: (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r)
    (fun h : (p ∨ q) ∧ (p ∨ r) =>
      h.left.elim
        (fun hp : p => show p ∨ (q ∧ r) from Or.inl hp)
        (fun hq : q =>
          h.right.elim
            (fun hp : p => show p ∨ (q ∧ r) from Or.inl hp)
            (fun hr : r => show p ∨ (q ∧ r) from Or.inr ⟨hq, hr⟩)))
