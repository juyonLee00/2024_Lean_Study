inductive Term : Type where
  | const : Nat → Term -- 자연수 상수
  | var : Nat → Term -- 변수
  | plus : Term → Term → Term -- s+t 결과값
  | times : Term → Term → Term -- s*t 결과값

example : Term := Term.const 3
example : Term := Term.var 0
example : Term := Term.plus (Term.const 3) (Term.const 4)
example : Term := Term.times (Term.const 3) (Term.const 4)

def eval (assign : Nat → Nat) (t : Term) : Nat :=
  match t with
  | Term.const n => n
  | Term.var n => assign n
  | Term.plus s t => eval assign s + eval assign t
  | Term.times s t => eval assign s * eval assign t


#eval eval (fun _ => 0) (Term.const 5)

def example1 : Nat → Nat :=
  fun n =>
    match n with
    | 0 => 1
    | _ => 0
#eval eval example1 (Term.var 0)

def example2 : Term :=
  Term.plus (Term.var 1) (Term.const 2)
#eval eval (fun _ => 0) example2

def example3 : Term :=
  Term.times (Term.var 1) (Term.const 2)
#eval eval (fun _ => 0) example3

inductive Formula where
  | tru
  | fal
  | atom (n : Nat)
  | neg (p : Formula) --not
  | andF (p q : Formula) --and
  | orF (p q : Formula) --or
  | implF (p q : Formula) --implies
  | iffF (p q : Formula) --iff

def eval2 (assign : Nat → Bool) (p : Formula) : Bool :=
  match p with
  | Formula.tru => true
  | Formula.fal => false
  | Formula.atom n => assign n
  | Formula.neg p => !(eval2 assign p)
  | Formula.andF p q => (eval2 assign p) && (eval2 assign q)
  | Formula.orF p q => (eval2 assign p) || (eval2 assign q)
  | Formula.implF p q => !(eval2 assign p) || (eval2 assign q)
  | Formula.iffF p q => (eval2 assign p) == (eval2 assign q)
