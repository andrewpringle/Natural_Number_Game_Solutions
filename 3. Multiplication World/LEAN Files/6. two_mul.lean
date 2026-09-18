theorem two_mul (a : ℕ) : 2 * a = a + a := by
  rw [two_eq_succ_one]
  rw [succ_mul]
  rw [one_mul]
  rfl
