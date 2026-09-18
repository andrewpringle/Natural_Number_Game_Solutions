theorem mul_eq_zero (a b : ℕ) : a * b = 0 → a = 0 ∨ b = 0 := by
  cases b
  right
  rfl
  rw [mul_succ] at h
  cases a
  rw [zero_mul, add_zero] at h
  left
  rfl
  left
  rw [add_succ] at h
  cases h
