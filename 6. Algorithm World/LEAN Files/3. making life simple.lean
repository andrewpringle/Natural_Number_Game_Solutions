theorem making_life_simple (a b c : ℕ) : a + b + c = a + c + b := by
  simp only [add_left_comm, add_comm]
