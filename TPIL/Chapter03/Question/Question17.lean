example : (p → q) → (¬q → ¬p) :=
  fun hpq : p → q => --p가 참이면 q도 참임을 가정
    fun hnq : ¬q => --¬q, p가 주어졌을 때 모순 유도
      fun hp : p =>
        hnq (hpq hp)
