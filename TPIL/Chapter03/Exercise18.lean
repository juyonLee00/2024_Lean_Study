open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun h : p → q ∨ r =>
    byCases
      (fun hp : p =>
        (h hp).elim
          (fun hq : q => Or.inl (fun _ => hq))
          (fun hr : r => Or.inr (fun _ => hr)))
      (fun hnp : ¬p => Or.inl (fun hp => False.elim (hnp hp))) --p가 거짓이면 p→q는 항상 성립.
