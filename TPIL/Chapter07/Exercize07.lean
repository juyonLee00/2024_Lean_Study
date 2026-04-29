/-!
# Exercises

## Question 1
-/

namespace Hidden

-- 곱셈
def mul (m n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ n' => Nat.add (mul m n') m

-- Predecessor (pred 0 = 0)
def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ n' => n'

-- truncated subtraction (with n - m = 0 when m is greater than or equal to n)
def sub (m n : Nat) : Nat :=
  match n with
  | Nat.zero => m
  | Nat.succ n' => pred (sub m n')

-- 거듭제곱
def exp (m n : Nat) : Nat :=
  match n with
  | Nat.zero => 1
  | Nat.succ n' => mul (exp m n') m

-- n * 0 = 0
theorem mul_zero (n : Nat) : mul n 0 = 0 := rfl

-- pred (n + 1) = n
theorem pred_succ (n : Nat) : pred (Nat.succ n) = n := rfl

end Hidden


/-!
## Question 2
-/
namespace Hidden
open List

-- 리스트 연산 정의에 대한 기본 증명
def length {α : Type u} (xs : List α) : Nat :=
  match xs with
  | nil => 0
  | cons _ tail => Nat.succ (length tail)

def append {α : Type u} (xs ys : List α) : List α :=
  match xs with
  | nil => ys
  | cons head tail => cons head (append tail ys)

def reverse {α : Type u} (xs : List α) : List α :=
  match xs with
  | nil => nil
  | cons head tail => append (reverse tail) (cons head nil)

end Hidden
