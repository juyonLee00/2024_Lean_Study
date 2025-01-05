example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q =>
      h.elim (fun hp : p => Or.inr hp) (fun hq : q => Or.inl hq))
    (fun h : q ∨ p =>
      h.elim (fun hq : q => Or.inr hq) (fun hp : p => Or.inl hp))
