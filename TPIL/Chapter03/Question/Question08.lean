example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h : (p ∨ q) → r =>
      And.intro
        (fun hp : p => h (Or.inl hp))
        (fun hq : q => h (Or.inr hq)))
    (fun h : (p → r) ∧ (q → r) =>
      fun hpq : p ∨ q =>
        hpq.elim
          (fun hp : p => h.left hp)
          (fun hq : q => h.right hq))
