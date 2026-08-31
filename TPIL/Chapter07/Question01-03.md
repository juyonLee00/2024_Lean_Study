# 7장 퀴즈

## 문제 1

\(a\) `Bool` 유형의 도입 규칙과 제거 규칙은 무엇인가? \

도입 규칙
true : Bool
false : Bool

제거 규칙
Bool.rec, Bool.casesOn이 표준 제거자이다.
즉, 어떤 타입 α로의 함수 f : Bool → α 는 f true, f false만 정하면 결정된다.

\(b\) `Bool` 유형의 구성자와 재귀자는 무엇인가?
구성자 : true, false
재귀자 : Bool.rec(or Bool.casesOn)

## 문제 2

`DayOfWeek` 이름 공간 안의 두 함수 `DayOrEnd`와 `listDayOrEnd`를 정의하라.

```lean
namespace Question02

/-- An inductive type with a finite, enumerated list of days of the week. -/
inductive DayOfWeek where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
deriving Repr

namespace DayOfWeek

/-- If `d` is a weekday, `DayOrEnd d` is the type of vectors with five days of the week; otherwise,
it's the type of vectors with two days of the week. -/
def DayOrEnd (d : DayOfWeek) : Type :=
  match d with
  | sunday    => Vector DayOfWeek 2
  | monday    => Vector DayOfWeek 5
  | tuesday   => Vector DayOfWeek 5
  | wednesday => Vector DayOfWeek 5
  | thursday  => Vector DayOfWeek 5
  | friday    => Vector DayOfWeek 5
  | saturday  => Vector DayOfWeek 2

/-- If `d` is a weekday, `listDayOrEnd d` is the vector with weekdays; otherwise, it's the vector
with the days in the weekend. -/
def listDayOrEnd (d : DayOfWeek) : DayOrEnd d :=
  match d with
  | sunday    => #v[sunday, saturday]
  | monday    => #v[monday, tuesday, wednesday, thursday, friday]
  | tuesday   => #v[monday, tuesday, wednesday, thursday, friday]
  | wednesday => #v[monday, tuesday, wednesday, thursday, friday]
  | thursday  => #v[monday, tuesday, wednesday, thursday, friday]
  | friday    => #v[monday, tuesday, wednesday, thursday, friday]
  | saturday  => #v[sunday, saturday]

end DayOfWeek

end Question02
```

## 문제 3

`Bool` 유형에 대한 불 연산 `and`, `or`, `not`을 정의하고, 아래 나열된 두 항등식을 검증하라.

```lean
namespace Question03

namespace Bool

/-- Boolean “or”, also known as disjunction. -/
def or (a b : Bool) : Bool :=
  match a, b with
  | true,  _     => true
  | false, true  => true
  | false, false => false

/-- Boolean “and”, also known as conjunction. -/
def and (a b : Bool) : Bool :=
  match a, b with
  | true,  true  => true
  | _,     _     => false

/-- Boolean negation, also known as Boolean complement. -/
def not (a : Bool) : Bool :=
  match a with
  | true  => false
  | false => true

/-- `Bool.not_not`. -/
theorem not_involutive (a : Bool) : not (not a) = a := a
| true  => rfl
| false => rfl

/-- `Bool.and_comm`. -/
theorem and_commutative (a b : Bool) : and a b = and b a :=
| true,  true  => rfl
| true,  false => rfl
| false, true  => rfl
| false, false => rfl

end Bool

end Question03
```

