theorem one_mul (a : ℕ) : 1 * a = a := by
  induction m with d hd
  rw [mul_zero]
  rfl
  rw [mul_succ]
  rw [succ_eq_add_one]
  rw [hd]
  rfl
