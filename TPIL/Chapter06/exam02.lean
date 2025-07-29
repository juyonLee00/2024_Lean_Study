/-
Copyright (c) 2025 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/
set_option linter.unusedVariables false

/-!
# Exam 2

This examination covers Chapter 6 of the text, focusing on implicit lambdas.

## Problem 1

Prove the following examples without using tactics:
-/

example : True ↔ ∀ {p : Prop}, p → p :=
  ⟨fun _ _ hp => hp, fun _ => True.intro⟩

example : False ↔ ∀ {p : Prop}, p :=
  Iff.intro
    (fun f => fun {p} => False.elim f)
    (fun f => f)

example {p q : Prop} : p ∧ q ↔ ∀ {r : Prop}, (p → q → r) → r :=
  Iff.intro
    (fun h => fun {r} f => f h.left h.right)
    (fun f => ⟨f (fun hp hq => hp), f (fun hp hq => hq)⟩)

example {p q : Prop} : p ∨ q ↔ ∀ {r : Prop}, (p → r) → (q → r) → r :=
  Iff.intro
    (fun h => fun {r} f g => h.elim f g)
    (fun f => f (fun hp => Or.inl hp) (fun hq => Or.inr hq))

example {α : Sort u} {p : α → Prop} :(∃ (x : α), p x) ↔ ∀ {r : Prop}, (∀ (w : α), p w → r) → r :=
  ⟨fun ⟨x, hx⟩ _ f => f x hx, fun h => h (fun x hx => ⟨x, hx⟩)⟩
