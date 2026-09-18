theorem tutorial_rw (a b : ℕ) (h : a = b) : a + 0 = b + 0 := by
  rw [h]
  rfl
