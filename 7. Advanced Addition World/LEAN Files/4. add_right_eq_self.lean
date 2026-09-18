theorem add_right_eq_self (a b : ℕ) : a + b = a → b = 0 := by
  intro h
  rw [add_comm] at h
  apply add_left_eq_self at h
  exact h
