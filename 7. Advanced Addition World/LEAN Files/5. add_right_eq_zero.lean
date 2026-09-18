theorem add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by
  cases b with d
  intro h
  rw [add_zero] at h
  exact h
  intro h
  rw [add_succ] at h
  apply succ_ne_zero at h
  cases h
