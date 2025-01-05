/-
## Question 1
-/

/-(1)-/
  def TwoPlusThreeIsFive : Prop := 2 + 3 = 5
  theorem twoPlusThreeIsFive : TwoPlusThreeIsFive := rfl

/-(2)-/
  def FifteenMinusEightIsSeven : Prop := 15 - 8 = 7
  theorem fifteenMinusEightIsSeven : FifteenMinusEightIsSeven := rfl

/-(3)-/
    def HelloAppendWorldIsHelloworld : Prop := "Hello, ".append "world" = "Hello, world"
  theorem helloAppendWorldIsHelloworld : HelloAppendWorldIsHelloworld := rfl

/-(4)-/
/-5 < 18 은 비교가 포함된 명제이기 때문에 두 값이 같은지 확인하는 rfl을 사용하면 오류가 발생한다.-/
