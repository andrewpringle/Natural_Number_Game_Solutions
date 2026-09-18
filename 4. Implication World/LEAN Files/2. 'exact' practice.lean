theorem exact_practice (a b : ℕ) (h : 0 + a = 0 + b) : a = b := by
  rw [zero_add] at h
  rw [zero_add] at h
  exact h
