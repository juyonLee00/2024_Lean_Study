variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

/-- Bulhwi: this proof uses classical reasoning. -/
example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  let contradiction := h barber
  let forward := contradiction.mp
  let backward := contradiction.mpr
  by_cases s : shaves barber barber
  · exact forward s s
  · exact s (backward s)

/-- Bulhwi: a constructive proof of the barber paradox. -/
example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have contradiction := h barber
  have forward := contradiction.mp
  have backward := contradiction.mpr
  have ns : ¬shaves barber barber := fun s => forward s s
  have s : shaves barber barber := backward ns
  show False from ns s
