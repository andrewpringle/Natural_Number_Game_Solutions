theorem le_mul_right (a b : ℕ) : a ≤ a * b ∨ b = 0 := by
  cases b
  rw [mul_zero]
  rw [mul_zero] at h
  contrapose h
  decide
  rw [mul_succ]
  use a_1 * a
  rw [add_comm]
  rw [mul_comm]
  rfl
