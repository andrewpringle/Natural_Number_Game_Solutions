theorem tutorial_add_succ (a : ℕ) : a + 1 = a + 1 := by
  rw [one_eq_succ_zero]
  rw [add_succ]
  rw [add_zero]
  rfl
