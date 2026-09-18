theorem le_zero (x : ℕ) : x ≤ 0 → x = 0 := by
  cases hx with d hd
  rw [add_comm] at hd
  symm at hd
  apply add_left_eq_zero at hd
  exact hd
