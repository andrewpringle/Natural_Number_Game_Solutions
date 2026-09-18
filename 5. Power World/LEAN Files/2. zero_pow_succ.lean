theorem zero_pow_succ (m : ℕ) : 0 ^ Nat.succ m = 0 := by
  rw [pow_succ]
  rw [mul_zero]
  rfl
