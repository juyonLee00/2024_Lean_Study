# Chapter 3 Textbook Exercises

## Question 1

- `example : p ∧ q ↔ q ∧ p := sorry`
```
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
      And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
      And.intro (And.right h) (And.left h))
```

<br/>

- `example : p ∨ q ↔ q ∨ p := sorry`
```
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q =>
      h.elim (fun hp : p => Or.inr hp) (fun hq : q => Or.inl hq))
    (fun h : q ∨ p =>
      h.elim (fun hq : q => Or.inr hq) (fun hp : p => Or.inl hp))
```

<br/>

- `example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r)`
```
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r =>
      And.intro (And.left (And.left h)) (And.intro (And.right (And.left h)) (And.right h)))
    (fun h : p ∧ (q ∧ r) =>
      And.intro (And.intro (And.left h) (And.left (And.right h))) (And.right (And.right h)))
```

<br/>

- `example : p ∨ q) ∨ r ↔ p ∨ (q ∨ r)`
```
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r =>
      h.elim
        (fun hpq : p ∨ q => hpq.elim (fun hp : p => Or.inl hp) (fun hq : q => Or.inr (Or.inl hq)))
        (fun hr : r => Or.inr (Or.inr hr)))
    (fun h : p ∨ (q ∨ r) =>
      h.elim
        (fun hp : p => Or.inl (Or.inl hp))
        (fun hqr : q ∨ r => hqr.elim (fun hq : q => Or.inl (Or.inr hq)) (fun hr : r => Or.inr hr)))
```

<br/>

- `example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry`
```
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right) 
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)  
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩)) 
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q => 
          have hp : p := hpq.left 
          have hq : q := hpq.right 
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩) 
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))
```

<br/>

- `example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)`
```
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    -- 첫 번째 방향: p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r)
    (fun h : p ∨ (q ∧ r) =>
      And.intro
        (h.elim 
          (fun hp : p => show p ∨ q from Or.inl hp)
          (fun hqr : q ∧ r => show p ∨ q from Or.inr hqr.left))
        (h.elim
          (fun hp : p => show p ∨ r from Or.inl hp)
          (fun hqr : q ∧ r => show p ∨ r from Or.inr hqr.right)))
    -- 두 번째 방향: (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r)
    (fun h : (p ∨ q) ∧ (p ∨ r) =>
      h.left.elim
        (fun hp : p => show p ∨ (q ∧ r) from Or.inl hp) 
        (fun hq : q =>
          h.right.elim
            (fun hp : p => show p ∨ (q ∧ r) from Or.inl hp) 
            (fun hr : r => show p ∨ (q ∧ r) from Or.inr ⟨hq, hr⟩))) 
```

<br/>

- `example : (p → (q → r)) ↔ (p ∧ q → r)`
```
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun h : p → (q → r) =>
      fun h_and : p ∧ q =>
        let hp : p := h_and.left in 
        let hq : q := h_and.right in
        h hp hq)
    (fun h : p ∧ q → r =>
      fun hp : p =>
        fun hq : q =>
          h ⟨hp, hq⟩)
```

<br/>

- `example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry`
```
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
     (fun h : (p ∨ q) → r =>
      And.intro
        (fun hp : p => h (Or.inl hp)) 
        (fun hq : q => h (Or.inr hq))) 
    (fun h : (p → r) ∧ (q → r) =>
      fun hpq : p ∨ q =>
        hpq.elim 
          (fun hp : p => h.left hp) 
          (fun hq : q => h.right hq)) 
```

<br/>

- `example : ¬(p ∨ q) ↔ ¬p ∧ ¬q `
```
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h : ¬(p ∨ q) =>
      And.intro
        (fun hp : p => h (Or.inl hp))  
        (fun hq : q => h (Or.inr hq)))
    (fun h : ¬p ∧ ¬q =>
      fun hpq : p ∨ q => 
        hpq.elim
          (fun hp : p => h.left hp)  
          (fun hq : q => h.right hq)) 
```

<br/>

- `example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry`
```
example : ¬p ∨ ¬q → ¬(p ∧ q) := 
  Iff.intro?
   fun h : ¬p ∨ ¬q =>
    fun hpq : p ∧ q = --해당 경우 모순이라는 것 증명하면 될 것 같음
```

<br/>

- `example : ¬(p ∧ ¬p) := sorry`
```
example : ¬(p ∧ ¬p) :=
  fun h : p ∧ ¬p => 
    h.right h.left 
```

<br/>

- `example : p ∧ ¬q → ¬(p → q) := sorry`
```
example : p ∧ ¬q → ¬(p → q) :=
  fun h : p ∧ ¬q => 
    fun hpq : p → q => 
      h.right (hpq h.left) 
```

<br/>

- `example : ¬p → (p → q) := sorry`
```
example : ¬p → (p → q) :=
  fun hnp : ¬p =>   
    fun hp : p =>   --p가 참이라는 가정 임시로 추가
```

<br/>

- `example : (¬p ∨ q) → (p → q) := sorry`
```
example : (¬p ∨ q) → (p → q) :=
  fun h : ¬p ∨ q =>
    fun hp : p =>
      h.elim
        (fun hnp : ¬p ) -- np가 참일 경우
        (fun hq : q => hq) -- q가 참일 경우
```

<br/>

- `example : p ∨ False ↔ p := sorry`
```
example : p ∨ False ↔ p :=
  Iff.intro
    (fun h : p ∨ False =>
      h.elim
        (fun hp : p => hp) 
        (fun hf : False => ))
    (fun hp : p =>
      Or.inl hp) 
```

<br/>

- `example : p ∧ False ↔ False`
```
example : p ∧ False ↔ False :=
  Iff.intro
    (fun h : p ∧ False =>
      h.right) 
    (fun hf : False => ) 
```

<br/>

- `example : (p → q) → (¬q → ¬p)`
```
example : (p → q) → (¬q → ¬p) :=
  fun hpq : p → q =>
    fun hnq : ¬q =>
```

<br/>

## Question 2

- `example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry`
```
example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun h : p → q ∨ r =>
    byCases
      (fun hp : p => 
        (h hp).elim
          (fun hq : q => Or.inl (fun _ => hq)) 
          (fun hr : r => Or.inr (fun _ => hr))) 
      (fun hnp : ¬p => Or.inl (fun hp => )) -- p가 거짓이면 p → q는 항상 성립한다.
```

<br/>

- `example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry`
```
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun h : ¬(p ∧ q) =>
    byCases
      (fun hp : p =>
        byCases
          (fun hq : q => ) -- p ∧ q가 참일 경우
          (fun hnq : ¬q => Or.inr hnq)) 
      (fun hnp : ¬p => Or.inl hnp) 
```

<br/>

- `example : ¬(p → q) → p ∧ ¬q := sorry`
```
example : ¬(p → q) → p ∧ ¬q :=
  fun h : ¬(p → q) =>
    byCases
      (fun hp : p =>
        byCases
          (fun hq : q => ) -- p → q가 참이면 모순
          (fun hnq : ¬q => ⟨hp, hnq⟩)) 
      (fun hnp : ¬p => ) -- p가 거짓일 경우?
```

<br/>

- `example : (p → q) → (¬p ∨ q) := sorry`
```
example : (p → q) → (¬p ∨ q) :=
  fun h : p → q =>
    byCases
      (fun hp : p => Or.inr (h hp)) 
      (fun hnp : ¬p => Or.inl hnp)
```

<br/>

- `example : (¬q → ¬p) → (p → q) := sorry`
```
example : (¬q → ¬p) → (p → q) :=
  fun h : ¬q → ¬p =>
    fun hp : p =>
      byCases
        (fun hq : q => hq) -- q가 참이면 반환
        (fun hnq : ¬q => False.elim ()) -- ¬q가 참이면 모순?
```

<br/>

- `example : p ∨ ¬p := sorry`
```
example : p ∨ ¬p :=
  byCases
    (fun hp : p => Or.inl hp)
    (fun hnp : ¬p => Or.inr hnp)
```

- `example : (((p → q) → p) → p) := sorry`
```
```
