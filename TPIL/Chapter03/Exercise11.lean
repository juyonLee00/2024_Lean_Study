example (p : Prop) : ¬(p ∧ ¬p) :=
  fun h : p ∧ ¬p =>
    h.2 h.1 --¬p면 p는 거짓이지만 p는 h.1에 의해 참
