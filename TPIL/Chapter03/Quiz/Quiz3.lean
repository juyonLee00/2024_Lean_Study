/-
## Question 3
-/

def GetFifthValueInList {α : Type} (datas : List α) (h : datas.length > 4) : α :=
  datas.get ⟨4, h⟩
