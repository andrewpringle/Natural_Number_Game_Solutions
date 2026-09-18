theorem mul_ne_zero (a b : ℕ) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by
  cases a
  rw [zero_mul]
  exact ha
  rw [succ_mul]
  cases b
  rw [mul_zero, add_zero]
  exact hb
  rw [mul_succ]
  rw [add_succ]
  apply succ_ne_zero
