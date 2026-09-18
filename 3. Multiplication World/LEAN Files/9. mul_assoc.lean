theorem mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  induction c with d hd
  rw [mul_zero, mul_zero]
  rw [mul_zero]
  rfl
  rw [mul_succ]
  rw [mul_succ]
  rw [mul_add]
  rw [hd]
  rfl
