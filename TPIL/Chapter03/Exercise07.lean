example (p q r : Prop) : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun h : p → (q → r) =>
      fun h_and : p ∧ q =>
        h h_and.1 h_and.2)
    (fun h : p ∧ q → r =>
      fun hp : p =>
        fun hq : q =>
          h ⟨hp, hq⟩)
