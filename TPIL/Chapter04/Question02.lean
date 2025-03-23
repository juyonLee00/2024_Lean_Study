open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
fun a =>
  Iff.intro
    (fun h => h a)
    (fun hr x => hr)


example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun h =>
      byCases
        (fun hr : r => Or.inr hr)
        (fun hnr : ¬r =>
          Or.inl (fun x =>
            match h x with
            | Or.inl hp => hp
            | Or.inr hr => False.elim (hnr hr))))
    (fun h =>
      Or.elim h
        (fun hp x => Or.inl (hp x))
        (fun hr x => Or.inr hr))


example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun h hr x => h x hr)
    (fun h x hr => h hr x)
