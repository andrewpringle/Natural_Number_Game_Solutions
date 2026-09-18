theorem add_left_eq_self (a b : ℕ) : a + b = b → a = 0 := by
  intro h
  rw [← add_zero y] at h
  nth_rewrite 1 [add_zero] at h
  rw [add_comm] at h
  apply add_left_cancel at h
  exact h
