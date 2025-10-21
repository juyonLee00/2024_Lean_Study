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

/-!
## Problem 2: Drinker Paradox Revisited

Use either of the two lemmas in the `Drinker` namespace, `exists_or_left` or `exists_or_right`, to
complete the proof of the theorem `Paradox.spearShield`.
-/

/-- A class for formalizing the drinker paradox. -/


class Drinker (Pub : Type) where
  IsDrinking : Pub → Prop

namespace Drinker

theorem exists_or_left {α : Sort u} {p : α → Prop} {b : Prop} (a : α) :
    (∃ x, b ∨ p x) ↔ b ∨ (∃ x, p x) :=
  Iff.intro
    (fun ⟨w, h⟩ ↦ h.elim Or.inl (fun hp ↦ Or.inr ⟨w, hp⟩))
    (fun h ↦ h.elim
      (fun hb ↦ ⟨a, Or.inl hb⟩)
      (fun ⟨w, hp⟩ ↦ ⟨w, Or.inr hp⟩))

theorem exists_or_right {α : Sort u} {p : α → Prop} {b : Prop} (a : α) :
    (∃ x, p x ∨ b) ↔ (∃ x, p x) ∨ b :=
  Iff.intro
    (fun ⟨w, h⟩ ↦ h.elim (fun hp ↦ Or.inl ⟨w, hp⟩) Or.inr)
    (fun h ↦ h.elim
      (fun ⟨w, hp⟩ ↦ ⟨w, Or.inl hp⟩)
      (fun hb ↦ ⟨a, Or.inr hb⟩))

end Drinker

section

variable {Pub : Type} [Drinker Pub]

open Drinker Classical

theorem Paradox.drinker (someone : Pub) :
    ∃ (x : Pub), IsDrinking x → ∀ (y : Pub), IsDrinking y := by
  simp only [Decidable.imp_iff_not_or]
  have h : (∃ x : Pub, ¬ IsDrinking x) ∨ (∀ y : Pub, IsDrinking y) :=
    (Classical.em (∀ y : Pub, IsDrinking y)).elim
      (fun hall => Or.inr hall)
      (fun hnot => Or.inl ((not_forall).mp hnot))
  rw [exists_or_right someone]
  assumption

end
