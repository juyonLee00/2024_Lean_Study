variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
Iff.intro
  (fun h => ⟨fun x => (h x).left, fun x => (h x).right⟩)
  (fun ⟨hp, hq⟩ => fun x => ⟨hp x, hq x⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
fun h1 h2 x => h1 x (h2 x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
fun h x =>
  Or.elim h
    (fun hp => Or.inl (hp x))
    (fun hq => Or.inr (hq x))
/-
Copyright (c) 2025 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# Chapter 4 Quiz

## Question 1
-/

namespace Question01

universe u

variable {α : Sort u}

def p (x : α) : Prop := ∀ (q : α → Prop), ¬q x

theorem forall_not_p (x : α) : ¬p x :=
  fun (hp : p x) ↦ show False from hp p hp

-- alternative proof of theorem `forall_not_p`
example (x : α) : ¬p x :=
  fun (hp : p x) ↦ hp (fun _ ↦ True) True.intro

end Question01
