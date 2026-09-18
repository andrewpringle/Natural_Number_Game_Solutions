theorem is_zero (a : ℕ) (h : a = 0) : a = 0 := by
  intro h
  rw [← is_zero_succ a]
  rw [h]
  trivial
