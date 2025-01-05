open Classical

variable (p q r : Prop)

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun h : ¬(p ∧ q) =>
    byCases
      (fun hp : p =>
        byCases
          (fun hq : q => False.elim (h ⟨hp, hq⟩)) --p∧q가 참이면 모순
          (fun hnq : ¬q => Or.inr hnq))
      (fun hnp : ¬p => Or.inl hnp)
