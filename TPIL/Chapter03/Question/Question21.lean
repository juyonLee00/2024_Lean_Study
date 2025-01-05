open Classical

variable (p q r : Prop)

example : (p → q) → (¬p ∨ q) :=
  fun h : p → q =>
    byCases
      (fun hp : p => Or.inr (h hp))
      (fun hnp : ¬p => Or.inl hnp)
