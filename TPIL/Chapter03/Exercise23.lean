open Classical

variable (p q r : Prop)

example : p ∨ ¬p :=
  byCases
    (fun hp : p => Or.inl hp)
    (fun hnp : ¬p => Or.inr hnp)
