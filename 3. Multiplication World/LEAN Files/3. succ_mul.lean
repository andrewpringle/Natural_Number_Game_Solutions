theorem succ_mul (a b : ℕ) : Nat.succ a * b = a * b + b := by
  induction b with d hd
  rw [mul_zero]
  rw [mul_zero]
  rw [add_zero]
  rfl
  rw [mul_succ]
  rw [mul_succ]
  rw [hd]
  rw [succ_eq_add_one]
  rw [succ_eq_add_one]
  rw [← add_assoc]
  rw [← add_assoc]
  nth_rewrite 2 [add_right_comm]
  rfl
