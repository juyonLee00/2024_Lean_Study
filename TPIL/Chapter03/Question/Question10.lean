example (p q : Prop) : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun h : ¬p ∨ ¬q =>
    fun hpq : p ∧ q =>
      h.elim
        (fun hnp : ¬p => hnp hpq.left)   -- 첫 번째 경우: ¬p가 참이라면 모순 발생
        (fun hnq : ¬q => hnq hpq.right)  -- 두 번째 경우: ¬q가 참이라면 모순 발생
