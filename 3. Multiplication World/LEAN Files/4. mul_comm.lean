theorem mul_comm (a b : ℕ) : a * b = b * a := by
  induction b with d hd
  rw [mul_zero]
  rw [zero_mul]
  rfl
  rw [succ_mul]
  rw [mul_succ]
  rw [hd]
  rfl
