example (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h : ¬(p ∨ q) =>
      ⟨fun hp : p => h (Or.inl hp),  -- ¬p
      fun hq : q => h (Or.inr hq)⟩) -- ¬q

    (fun h : ¬p ∧ ¬q =>
      fun h_or : p ∨ q =>
        h_or.elim h.1 h.2)  -- p가 참이면 ¬p에 모순, q가 참이면 ¬q에 모순
