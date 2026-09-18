theorem mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  induction c with d hd
  rw [add_zero, mul_zero, add_zero]
  rfl
  rw [add_succ, mul_succ]
  rw [hd]
  rw [add_assoc, add_comm, mul_succ, add_comm]
  rfl
