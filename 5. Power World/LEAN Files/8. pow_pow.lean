theorem pow_pow (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  induction n with d hd
  rw [pow_zero, mul_zero]
  rw [pow_zero]
  rfl
  rw [pow_succ, mul_succ]
  rw [hd]
  rw [pow_add]
  rfl
