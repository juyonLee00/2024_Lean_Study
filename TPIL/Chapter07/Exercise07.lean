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
  | List.nil => List.nil
  | List.cons head tail => append (reverse tail) (List.cons head List.nil)


theorem length_append {α : Type} (xs ys : List α) : length (append xs ys) = length xs + length ys := by
  induction xs with
  | nil =>
  simp [append, length]
  | cons x xs' ih =>
    calc length (append (x :: xs') ys)
      _ = length (x :: append xs' ys) := rfl
      _ = length (append xs' ys) + 1    := rfl
      _ = (length xs' + length ys) + 1 := by rw [ih]
      _ = (length xs' + 1) + length ys := by rw [Nat.add_right_comm]
      _ = length (x :: xs') + length ys := rfl

theorem length_reverse {α : Type} (xs : List α) : length (reverse xs) = length xs := by
  induction xs with
  | nil => rfl
  | cons x xs' ih =>
    calc length (reverse (x :: xs'))
      _ = length (append (reverse xs') [x]) := rfl
      _ = length (reverse xs') + length [x] := by rw [length_append]
      _ = length xs' + length [x]           := by rw [ih]
      _ = length (x :: xs')                 := rfl

-- append xs [] 처리
theorem append_nil {α : Type} (xs : List α) : append xs [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs' ih =>
    calc append (x :: xs') []
      _ = x :: append xs' [] := rfl
      _ = x :: xs'           := by rw [ih]

-- 리스트 결합법칙
theorem append_assoc {α : Type} (xs ys zs : List α) : append (append xs ys) zs = append xs (append ys zs) := by
  induction xs with
  | nil => rfl
  | cons x xs' ih =>
    calc append (append (x :: xs') ys) zs
    _ = append (x :: append xs' ys) zs := rfl
    _ = x :: append (append xs' ys) zs := rfl
    _ = x :: append xs' (append ys zs) := by rw [ih]
    _ = append (x :: xs') (append ys zs) := rfl

-- 합친 리스트 뒤집어도 동일
theorem reverse_append {α : Type} (xs ys : List α) : reverse (append xs ys) = append (reverse ys) (reverse xs) := by
  induction xs with
  | nil =>
    calc reverse (append [] ys)
      _ = reverse ys := rfl
      _ = append (reverse ys) [] := by rw [append_nil]
  | cons x xs' ih => -- xs'에 대해 정의가 맞다고 가정
    calc reverse (append (x :: xs') ys) -- reverse (x::xs')=append reverse(xs')[x]
    _ = reverse (x :: append xs' ys) := rfl -- append 정의 (x :: xs') 뒤 ys 붙임
    _ = append (reverse (append xs' ys)) [x] := rfl -- reverse 정의
    _ = append (append (reverse ys) (reverse xs')) [x] := by rw [ih]
    _ = append (reverse ys) (reverse (x :: xs')) := by rw [append_assoc];  rfl; --


theorem reverse_reverse {α : Type} (xs : List α) : reverse (reverse xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs' ih =>
  calc reverse (reverse (x :: xs'))
  _ = reverse (append (reverse xs') [x]) := rfl
  _ = append (reverse [x]) (reverse (reverse xs')) := by rw[reverse_append]
  _ = append [x] (reverse (reverse xs')) := rfl
  _ = append [x] xs' := by rw [ih]
  _ = x :: xs' := rfl


end Hidden
