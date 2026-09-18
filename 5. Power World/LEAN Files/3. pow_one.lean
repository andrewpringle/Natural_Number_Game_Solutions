theorem pow_one (a : ℕ) : a ^ 1 = a := by
  rw [one_eq_succ_zero]
  rw [pow_succ]
  rw [pow_zero]
  rw [one_mul]
  rfl
