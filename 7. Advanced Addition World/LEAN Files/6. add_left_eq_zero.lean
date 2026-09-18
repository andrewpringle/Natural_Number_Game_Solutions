theorem add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by
  cases a with d
  intro h
  rw [zero_add] at h
  exact h
  intro h
  rw [succ_add] at h
  apply succ_ne_zero at h
  cases h
