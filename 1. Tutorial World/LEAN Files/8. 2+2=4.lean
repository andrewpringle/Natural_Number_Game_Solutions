theorem tutorial_two_plus_two : 2 + 2 = 4 := by
  nth_rewrite 2 [two_eq_succ_one]
  rw [one_eq_succ_zero]
  rw [add_succ]
  rw [add_succ]
  rw [add_zero]
  rw [← three_eq_succ_two]
  rw [← four_eq_succ_three]
  rfl
