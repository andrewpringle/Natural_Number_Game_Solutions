theorem zero_mul (a : ℕ) : 0 * a = 0 := by
  induction m with d hd
  rw [mul_zero]
  rfl
  rw [mul_succ]
  rw [add_zero]
  rw [hd]
  rfl
