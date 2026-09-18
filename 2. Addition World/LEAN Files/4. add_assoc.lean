theorem add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  induction c with d hd
  rw [add_zero, add_zero]
  rfl
  rw [add_succ, add_succ, add_succ]
  rw [hd]
  rfl
