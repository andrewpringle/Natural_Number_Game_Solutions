theorem mul_one (a : ℕ) : a * 1 = a := by
  rw [one_eq_succ_zero]
  rw [mul_succ]
  rw [mul_zero]
  rw [zero_add]
  rfl
