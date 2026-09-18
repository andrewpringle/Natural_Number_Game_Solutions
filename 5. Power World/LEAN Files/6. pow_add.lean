theorem pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with d hd
  rw [add_zero, pow_zero]
  rw [mul_one]
  rfl
  rw [add_succ, pow_succ]
  rw [pow_succ]
  rw [hd]
  rw [mul_assoc]
  rfl
