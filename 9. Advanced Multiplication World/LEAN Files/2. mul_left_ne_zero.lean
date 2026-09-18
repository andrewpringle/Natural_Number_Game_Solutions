theorem mul_left_ne_zero (a b : ℕ) : a * b ≠ 0 → a ≠ 0 := by
  induction b
  rw [mul_zero] at h
  exact h
  rw [mul_succ] at h
  cases a
  rw [zero_mul, add_zero] at h
  intro n_ih
  apply h
  rfl
  intro n_ih
  apply succ_ne_zero at n_ih
  exact n_ih
