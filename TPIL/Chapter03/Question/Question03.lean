example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r =>
      And.intro (And.left (And.left h)) (And.intro (And.right (And.left h)) (And.right h)))
    (fun h : p ∧ (q ∧ r) =>
      And.intro (And.intro (And.left h) (And.left (And.right h))) (And.right (And.right h)))
