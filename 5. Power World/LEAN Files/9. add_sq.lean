theorem add_sq (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  rw [pow_two]
  rw [add_mul]
  rw [mul_add, mul_add]
  rw [← pow_two, ← pow_two]
  rw [add_assoc]
  rw [← add_assoc (a*b)]
  rw [mul_comm b a]
  rw [← two_mul]
  rw [← mul_assoc]
  rw [add_comm (2 * a * b)]
  rw [← add_assoc]
  rfl
