open Classical

variable (p q r : Prop)

example : ¬(p → q) → p ∧ ¬q :=
  fun h : ¬(p → q) =>
    byCases
      (fun hp : p =>
        byCases
          (fun hq : q => False.elim (h (fun _ => hq))) --p→q가 참이면 모순
          (fun hnq : ¬q => ⟨hp, hnq⟩)) --q가 거짓이면 p∧¬q 반환
      (fun hnp : ¬p =>False.elim (h (fun hp => False.elim (hnp hp)))) -- p가 거짓이면 p→q는 참
