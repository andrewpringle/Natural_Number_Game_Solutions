theorem mul_left_cancel (a b c : ℕ) : a * b = a * c → b = c := by
  induction b with d hd generalizing c
  cases c with e
  rfl
  rw [mul_zero, mul_succ] at h
  cases a with f
  tauto
  rw [succ_mul, add_succ] at h
  cases h
  cases c with e
  rw [mul_succ, mul_zero] at h
  cases a with f
  tauto
  rw [succ_mul, add_succ] at h
  cases h
  rw [mul_succ, mul_succ] at h
  have h2 := add_right_cancel _ _ _ h
  have h3 := hd e h2
  rw [h3]
  rfl
