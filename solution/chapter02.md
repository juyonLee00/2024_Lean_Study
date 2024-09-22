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
* 함수 타입으로, Bool 타입을 받아 Bool 타입을 반환하는 함수이다.

\(b\) `Bool × Bool`
* Cartesian product 타입으로, 2개의 Bool값을 갖는 튜플이다.

## Question 8
* 타입을 입력받아 타입을 반환하는 함수이므로 Type.id가 Nat을 받을 경우 Nat을 반환한다.

## Question 9

Define a constant of each type listed below.

\(a\) `(Nat, Type 0)` \
\(b\) `fun (f : Type 2) => (f -> f)`

## Question 10


## Question 11
* universe-polymorphic하지 않다. 8번의 함수는 타입을 입력받아 타입을 반환하는데, 입력받은 타입에 고정되어 있는 상태이기 때문이다.

## Question 12

\(a\) `(Nat, Type 0)` 
* universe-polymorphic하지 않다. Nat과 Type 0 둘 다 고정된 레벨을 갖기 때문이다.
  
\(b\) `fun (f : Type 2) => (f -> f)`
* universe-polymorphic하지 않다. f가 Type 2에 고정된 타입이어서 다른 유니버스 레벨에서 작동하지 않기 때문이다.

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

Define the following function, replacing the `sorry` identifier with an actual
expression *containing* the arguments `f`, `g`, and `s`.

```lean
def q17 (f : List Char → Nat) (g : (List Char → Nat) → (String → Nat)) (s : String) : Nat :=
  sorry
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

## Question 22

## Question 23

## Question 24

## Question 25

## Question 26

## Question 27

## Question 28

## Question 29

## Question 30

## Question 31

## Question 32

## Question 33

## Question 34

## Question 35

## Question 36

## Question 37

## Question 38

