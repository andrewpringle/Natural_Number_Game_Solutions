theorem mul_right_eq_self (a b : ℕ) : a * b = a → b = 1 := by
  nth_rewrite 2 [← mul_one a] at h
  apply mul_left_cancel at h
  exact h
  exact ha
