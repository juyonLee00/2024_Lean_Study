example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
      And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
      And.intro (And.right h) (And.left h))
