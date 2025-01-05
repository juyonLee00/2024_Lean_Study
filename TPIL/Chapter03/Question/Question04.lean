example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r =>
      h.elim
        (fun hpq : p ∨ q => hpq.elim (fun hp : p => Or.inl hp) (fun hq : q => Or.inr (Or.inl hq)))
        (fun hr : r => Or.inr (Or.inr hr)))
    (fun h : p ∨ (q ∨ r) =>
      h.elim
        (fun hp : p => Or.inl (Or.inl hp))
        (fun hqr : q ∨ r => hqr.elim (fun hq : q => Or.inl (Or.inr hq)) (fun hr : r => Or.inr hr)))
