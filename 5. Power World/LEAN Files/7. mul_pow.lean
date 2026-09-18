theorem mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with d hd
  rw [pow_zero, pow_zero, pow_zero]
  rw [one_mul]
  rfl
  rw [pow_succ, pow_succ, pow_succ]
  rw [hd]
  rw [mul_assoc]
  rw [mul_comm (b^d)]
  rw [mul_assoc a]
  rw [← mul_assoc]
  rw [mul_comm b (b^d)]
  rfl
