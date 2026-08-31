namespace Hidden

-- 명제식 자료형 정의
inductive Formular where
  | truth : Formular -- 참 명제
  | falsity : Formular -- 거짓 명제
  | atom (n : Nat) : Formular -- 원자 명제 (명제 구별용 Nat)
  | neg (p : Formular) : Formular -- 받은 명제의 부정 명제
  | andF (p q : Formular) : Formular -- 받은 명제들의 AND 명제
  | orF (p q : Formular) : Formular -- 받은 명제들의 OR 명제
  | implF (p q : Formular) : Formular -- 받은 명제들의 Impl 명제
  | iffF (p q : Formular) : Formular -- 받은 명제들이 동치라는 명제

-- 입력값에 따른 명제 계산
def eval (assign : Nat -> Bool) (p : Formular) : Bool :=
  match p with
  | Formular.truth => true -- 항상 참
  | Formular.falsity => false -- 항상 거짓
  | Formular.atom n => assign n -- n번 명제의 assign값 계산
  | Formular.neg p => !(eval assign p) -- 명제 참 거짓 여부 판단 후 결과 반전
  | Formular.andF p q => (eval assign p) && (eval assign q)
  | Formular.orF p q => (eval assign p) || (eval assign q)
  | Formular.implF p q => !(eval assign p) || (eval assign q)
  | Formular.iffF p q => (eval assign p) == (eval assign q)

-- 명제식의 복잡도 측정
-- 식 내부 구성 요소 개수 판단
def complexity (p : Formular) : Nat :=
  match p with
  | Formular.truth => 0
  | Formular.falsity => 0
  | Formular.atom _ => 0
  | Formular.neg p => Nat.succ (complexity p)
  | Formular.andF p q => Nat.succ (complexity p + complexity q)
  | Formular.orF p q => Nat.succ (complexity p + complexity q)
  | Formular.implF p q => Nat.succ (complexity p + complexity q)
  | Formular.iffF p q => Nat.succ (complexity p + complexity q)


def Formular.subst (n : Nat) (B A : Formular) : Formular :=
  match A with
  | truth => Formular.truth
  | falsity => Formular.falsity
  | atom m =>
      if m = n then B else A
  | neg p =>
      neg (subst n B p)
  | andF p q =>
      andF (subst n B p) (subst n B q)
  | orF p q =>
      orF (subst n B p) (subst n B q)
  | implF p q =>
      orF (subst n B p) (subst n B q)
  | iffF p q =>
      orF (subst n B p) (subst n B q)

-- def pqr : Formular := Formular.andF (Formular.andF p q) r



end Hidden
