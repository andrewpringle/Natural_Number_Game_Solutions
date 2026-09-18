theorem making_life_easier (a b c d : ℕ) : a + b + (c + d) = a + c + (b + d) := by
  repeat rw [add_assoc]
  rw [add_left_comm b c]
  rw [add_comm b d]
  rfl
