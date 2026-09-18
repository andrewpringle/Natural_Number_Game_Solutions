theorem add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  induction c with d hd
  rw [add_zero, add_zero]
  rfl
  rw [add_succ, add_succ, succ_add]
  rw [hd]
  rfl
