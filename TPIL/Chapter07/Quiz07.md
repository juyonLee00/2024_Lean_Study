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

## 문제 4

`α`에서 `β`로의 그리고 `β`에서 `γ`로의 부분 함수의 합성 개념을 정의하라. 그러고 나서, 이 개념이 우리가 예상한 대로 작동함을 보여라.

```
namespace Question04

def PFun (α β : Type) := α → Option β

namespace PFun

def comp {α β γ : Type} (g : PFun β γ) (f : PFun α β) : PFun α γ :=
  fun x => Option.bind (f x) g

def pid (α : Type) : PFun α α :=
  fun x => some x

theorem comp_id {α β} (f : PFun α β) : comp (pid β) f = f :=
  funext (fun x =>
    show (f x).bind (pid β) = f x from
    match f x with
    | none   => rfl
    | some b => rfl)

theorem id_comp {α β} (g : PFun α β) : comp g (pid α) = g :=
  funext (fun x => rfl)

theorem comp_assoc {α β γ δ}
  (h : PFun γ δ) (g : PFun β γ) (f : PFun α β) :
  comp h (comp g f) = comp (comp h g) f := by
  funext x
  unfold comp
  cases f x with
  | none   => rfl
  | some b => rfl

end PFun

end Question04
```

## 문제 5

두 유형 `Bool`과 `Nat`에 거주자가 있고, 거주자가 있는 두 유형의 곱에도 거주자가 있으며, 거주자가 있는 유형으로의 함수의 유형에도 거주자가 있음을 보여라.

```
namespace Question05

example : Inhabited Bool := sorry
example : Inhabited Nat := sorry

instance instInhabitedProd {α β} [Inhabited α] [Inhabited β] : Inhabited (α × β) :=
  ⟨(default, default)⟩

instance instInhabitedArrow {α β} [Inhabited β] : Inhabited (α → β) :=
  ⟨fun _ => default⟩

def pickPair {α β} [Inhabited α] [Inhabited β] : α × β := default
def pickFun  {α β} [Inhabited β] : α → β := default

end Question05

```

## 문제 6

`Subtype`을 이용해 홀수의 유형을 정의하라.

```
namespace Question06

def OddNat : Type := { n : Nat }

namespace OddNat

def val (x : OddNat) : Nat := x.val
def one : OddNat := ⟨1, by exact Nat.odd_1⟩

end OddNat

end Question06
```
