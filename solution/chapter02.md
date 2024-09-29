# Chapter 2 Quiz

## Question 1
\(a\) `Int`\
\(b\) `Float`\
\(c\) `Char`\
\(d\) `String` \
\(e\) `List Nat`\
\(f\) `Prop`

## Question 2
\(a\) `-1`\
\(b\) `0.000000`\
\(c\) `76`\
\(d\) `4`\
\(e\) `[1, 2]`\
\(f\) `true`

## Question 3
```lean
namespace Question03

def f (x : Nat) := 2 * x - 1
#eval f 1

end Question03
```

## Question 4
\(a\) `Bool → Bool` 
```
def q04a : Bool -> Bool := fun x : Bool => x
```
\(b\) `(Bool → Bool) → Bool` 
```
def q04b : (Bool -> Bool) -> Bool := fun f => f true
```
\(c\) `Bool → (Bool → Bool)` 
```
def q04c : Bool -> (Bool -> Bool) := fun x => fun y => x && y
```
\(d\) `Bool → Bool → Bool`
```
def q04d : Bool -> Bool -> Bool := fun x => fun y => x || y
```

## Question 5
\(a\) `(true, false)` \
\(b\) `((true, false), true)` \
\(c\) `(true, (true, false))` \
\(d\) `(false, true, false)`

## Question 6
\(a\) `1` \
\(b\) `10` \
\(c\) `'L'` \
\(d\) `4`

## Question 7
\(a\) `Bool → Bool` 
* 함수 타입으로, Bool값을 받아 Bool값을 반환하는 함수이다.

\(b\) `Bool × Bool`
* Cartesian product 타입으로, 2개의 Bool값을 갖는 튜플이다.

## Question 8
* 유형을 입력받아 유형을 반환하는 함수이므로 Type.id가 Nat을 받을 경우 Nat을 반환한다.
* Nat의 유형은 Type이므로, 정답은 Type이다.

## Question 9

Define a constant of each type listed below.

\(a\) `(Nat, Type 0)` \
\(b\) `fun (f : Type 2) => List f`

## Question 10
```
namespace Question10

def f.{u, v, w} : Type u -> Type v -> Type w -> Type (max u v w) :=
  fun (α : Type u) (β : Type v) (γ : Type w) => α × (β × γ)
def g.{u, v, w} : Type u -> Type v -> Type w -> Type (max u v w) :=
  fun (α : Type u) (β : Type v) (γ : Type w) => (α -> β) -> γ

end Question10
```

## Question 11
* universe-polymorphic하지 않다. 8번의 함수는 유형을 입력받아 유형을 반환하는데, 그 정의역과 공역 모두 고정된 유형 세계이기 때문이다.

## Question 12

\(a\) `(Nat, Type 0)` 
* universe-polymorphic하지 않다. Nat과 Type 0 둘 다 고정된 유형 세계에 속하기 때문이다.
  
\(b\) `fun (f : Type 2) => List f`
* universe-polymorphic하지 않다. 고정된 Type 2와 Type 3 사이에서만 동작하고, 함수는 Type 2에서 Type 3로 가는 것이기 때문이다.

## Question 13
`-1`.

## Question 14
```
def q014 (n : Nat) : Bool :=
  if n = 0 the false else true
```
## Question 15
* constant function이 아니다. 입력값에 따라 출력값이 달라지기 때문이다.
  
## Question 16
* identity function이 아니다. identity function은 입력값을 그대로 반환해야 하는데 입력값과 상관없이 0을 반환하기 때문이다.

## Question 17
```lean
def q17 (f : List Char → Nat) (g : (List Char → Nat) → (String → Nat)) (s : String) : Nat :=
  g f s
```

## Question 18
* 변수 이름이 달라도 함수의 의미는 동일하므로 alpha-equivalence이다.

## Question 19
* f, g가 alpha-equivalance하다.

## Question 20
```
def q20 (a b : Nat) : Nat :=
  if a <= b then a else b
```

## Question 21
* `foo`는 `a`의 타입이 고정되어 있어서 함수 `x`의 타입 체크를 통과한다. `bar`는 `a`의 타입을 받아서 인자로 전달한다. 그러나 함수 내 `x+2`는 `Nat`에만 적용이 가능한데 `a`는 제약 없는 임의의 타입이기 때문에 `a`의 타입이 `Nat`이 아닐 수도 있기 때문에 타입 체크를 통과하지 못한다.

## Question 22
```
def compose : (α β γ : Type) → (β → γ) → (α → β) → α → γ :=
fun α β γ g f x => g (f x)

def doTwice : (α : Type) → (α → α) → α → α :=
fun α h x => h (h x)

def doThrice : (α : Type) → (α → α) → α → α :=
fun α h x => h (h (h x))
```

## Question 23
```
def compose {α : Type} (g : List α → List α) (f : List α → List α) (x : List α) : List α :=
  g (f x)
```

## Question 24
\(a\) `[0, 1, 2, 3]`\
\(b\) `[true]`\
\(c\) `["Lean", "4"]`

## Question 25
\(a\) `True`\
\(b\) `True`\
\(c\) `False`\
\(d\) `False`

## Question 26
\(a\) `False`\
(b\) `False`\
\(c\) `False` 

## Question 27
\(a\) `True`\
\(b\) `False`\
\(c\) `False`\
\(d\) `False`\
\(e\) `False`

## Question 28
* `dependent function type`이다. 그 이유는 `β a`가 `a`에 의존하고, `β`의 타입이 `α`에 의존하기 때문이다.

## Question 29
* `dependent product type`이다. 그 이유는 `β a`가 `a`에 의존하기 때문이다.

## Question 30
* `Sigma type`이다. 그 이유는 `Σ (a : α), β a`에서 시그마 타입이라고 명시되어 있기 때문이다.

## Question 31
* 같은 타입이다. 그 이유는 둘 다 첫 번째 요소의 타입이 `α`이고, 두 번째 요소의 타입이 첫 번째 요소에 의존하는 `β a`인 쌍을 나타낸다는 의미는 동일하기 때문이다.

## Question 32
* `dependent function type`이 아니다. 그 이유는 리턴 타입이 `Prop`로 고정되어 있어 입력값 `α`에 의존하지 않기 때문이다.

## Question 33
* `dependent product type`이 아니다. 그 이유는 `α`에 관계없이 `Prop`이 항상 명제이기 때문이다.

## Question 34
```
namespace Question34

universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ (a : α), β a :=
  ⟨a, b⟩

end Question34
```

## Question 35
\(a\) `1`\
\(b\) `-1`

## Question 36
\(a\) `[]`, `List Nat`\
\(b\) `[0, 1, 2, 3]`, `List Nat`

## Question 37
\(a\) `@List.cons Nat 0 [1, 2, 3]`, `[0, 1, 2, 3]`\
\(b\) `@List.append Nat [0, 1] [2, 3]`, `[0, 1, 2, 3]`\
\(c\) `@List.cons String "Lean" ["4"]`, `["Lean", "4"]`\
\(d\) `@List.append String ["Lean"] ["4"]`, `["Lean", "4"]`

## Question 38
```
def Id.map {α β : Type} (f : α → β) (x : α) : β := f x
```
