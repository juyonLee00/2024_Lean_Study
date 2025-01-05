example : p ∨ False ↔ p :=
  Iff.intro
    (fun h : p ∨ False =>
      h.elim
        (fun hp : p => hp) --p참이면 p반환
        (fun hf : False => False.elim hf)) --false면 모순 유도
    (fun hp : p =>
      Or.inl hp) -- p로 p∨False를 구성
