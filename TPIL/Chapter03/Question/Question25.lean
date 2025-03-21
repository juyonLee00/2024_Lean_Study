example (p : Prop) : ¬(p ↔ ¬p) :=
  fun h ↦
    have hnp : ¬p := fun hp ↦ h.mp hp hp
    have hp : p := h.mpr hnp
    show False from hnp hp
