theorem add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
  intro h
  rw [add_comm] at h
  rw [add_comm n b ] at h
  apply add_right_cancel at h
  exact h
