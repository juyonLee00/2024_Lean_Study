set_option warn.sorry false
set_option linter.unusedVariables false

/-!
# Chapter 7 Quiz

## Question 4
-/

namespace Question04

def PFun (α β : Type) := α → Option β

namespace PFun

def comp {α β γ : Type} (g : PFun β γ) (f : PFun α β) : PFun α γ :=
  fun x => Option.bind (f x) g

def pid (α : Type) : PFun α α :=
  fun x => some x

/-!
comp_id : 전략모드
theorem comp_id {α β} (f : PFun α β) : comp (pid β) f = f :=
  funext (fun x =>
    show (f x).bind (pid β) = f x from

    match f x with
    | none   => rfl
    | some b => rfl)
    -/

theorem comp_id {α β} (f : PFun α β) : comp (pid β) f = f := by
  funext x
  dsimp [comp, pid]

  cases f x with
  | none => rfl
  | some b => rfl


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

/-!
## Question 5
-/

namespace Question05

example : Inhabited Bool := Inhabited.mk true
example : Inhabited Nat := ⟨0⟩

instance instInhabitedProd {α β} [Inhabited α] [Inhabited β] : Inhabited (α × β) :=
  ⟨(default, default)⟩

instance instInhabitedArrow {α β} [Inhabited β] : Inhabited (α → β) :=
  ⟨fun _ => default⟩

def pickPair {α β} [Inhabited α] [Inhabited β] : α × β := default
def pickFun  {α β} [Inhabited β] : α → β := default

end Question05

/-!
## Question 6
-/

namespace Question06

def IsOdd (n : Nat) : Prop := ∃ k, n = 2 * k + 1

def OddNat : Type := { n : Nat // IsOdd n}

namespace OddNat

def val (x : OddNat) : Nat := x.1
def one : OddNat := ⟨1, ⟨0, rfl⟩⟩

end OddNat

end Question06
