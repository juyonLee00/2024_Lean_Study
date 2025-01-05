example : p ∧ ¬q → ¬(p → q) :=
  fun h : p ∧ ¬q =>
    fun hpq : p → q =>
      h.right (hpq h.left)
