theorem mul_right_eq_one (x y : ℕ) : x * y = 1 → x = 1 := by
  have h2 : x * y ≠ 0
  rw [h]
  trivial
  apply le_mul_right at h2
  rw [h] at h2
  apply le_one at h2
  cases h2
  rw [h_1] at h
  rw [zero_mul] at h
  trivial
  exact h_1
