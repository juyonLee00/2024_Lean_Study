example : (¬p ∨ q) → (p → q) :=
  fun h : ¬p ∨ q =>
    fun hp : p =>
      h.elim
        (fun hnp : ¬p => absurd hp hnp) -- np가 참일 경우
        (fun hq : q => hq) -- q가 참일 경우
