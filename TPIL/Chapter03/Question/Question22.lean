open Classical

variable (p q r : Prop)

example : (¬q → ¬p) → (p → q) :=
  fun h : ¬q → ¬p =>
    fun hp : p =>
      byCases
        (fun hq : q => hq) -- q가 참이면 반환
        (fun hnq : ¬q => False.elim (h hnq hp)) -- ¬q가 참이면 모순 유도
