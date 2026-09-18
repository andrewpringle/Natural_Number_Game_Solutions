theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  rw [add_comm b c]
  rw [add_comm]
  nth_rewrite 3 [add_comm]
  nth_rewrite 4 [add_comm]
  rw [add_right_comm]
  rfl
