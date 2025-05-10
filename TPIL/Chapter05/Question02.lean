example (p q r : Prop) (hp : p)
  : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat constructor;
  all_goals ( first
    | exact Or.inl      hp
    | exact Or.inr (Or.inl hp)
    | exact Or.inr (Or.inr hp) )
