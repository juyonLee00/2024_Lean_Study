example : p ∧ False ↔ False :=
  Iff.intro
    (fun h : p ∧ False => h.right) --p가 참, false가 참
    (fun hf : False => False.elim hf) --false는 거짓
