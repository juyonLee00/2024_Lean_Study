variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  let contradiction := h barber
  let forward := contradiction.mp
  let backward := contradiction.mpr
  by_cases s : shaves barber barber
  · exact forward s s
  · exact s (backward s)
