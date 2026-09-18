theorem succ_add (a b : ℕ) : Nat.succ a + b = Nat.succ (a + b) := by
  induction b with d hd
  rw [add_zero]
  rw [add_zero]
  rfl
  rw [add_succ]
  rw [hd]
  rw [add_succ]
  rfl
