# Chapter 3 Quiz

## Question 1
\(1\) 
```lean
  def TwoPlusThreeIsFive : Prop := 2 + 3 = 5
  theorem twoPlusThreeIsFive : TwoPlusThreeIsFive := rfl
```
\(2\) 
```lean
  def FifteenMinusEightIsSeven : Prop := 15 - 8 = 7
  theorem fifteenMinusEightIsSeven : FifteenMinusEightIsSeven := rfl
```
\(3\)
```lean
  def HelloAppendWorldIsHelloworld : Prop := "Hello, ".append "world" = "Hello, world"
  theorem helloAppendWorldIsHelloworld : HelloAppendWorldIsHelloworld := rfl
```
\(4\) `5 < 18` 은 비교가 포함된 명제이기 때문에 두 값이 같은지 확인하는 rfl을 사용하면 오류가 발생한다.

## Question 2
\(1\)
```lean
  theorem twoPlusThreeIsFive : 2 + 3 = 5 := by simp
```
\(2\) 
```lean
  theorem fifteenMinusEightIsSeven : 15 - 8 = 7 := by simp
```
\(3\)
```lean
  theorem helloAppendWorldIsHelloworld : "Hello, "++ "world" = "Hello, world" := by simp
```
\(4\)
```lean
  theorem eighteenIsBiggerThanFive : 5 < 18 := by simp
```

## Question 3
```lean
  def GetFifthValueInList {α : Type} (datas : list α) (IsSafe : datas.lenth >= 5) : α := datas.nth_le 4 IsSafe

```
