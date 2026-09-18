theorem one_pow (m : ℕ) : 1 ^ m = 1 := by
  induction m with d hd
  rw [pow_zero]
  rfl
  rw [pow_succ]
  rw [mul_one]
  rw [hd]
  rfl
