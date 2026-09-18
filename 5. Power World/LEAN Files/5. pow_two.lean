theorem pow_two (a : ℕ) : a ^ 2 = a * a := by
  rw [two_eq_succ_one]
  rw [pow_succ]
  rw [pow_one]
  rfl
