example (p q : Prop) : ¬p → (p → q) :=
  fun hnp : ¬p =>
    fun hp : p =>
      absurd hp hnp --hp가 모순이므로 가설은 참.
