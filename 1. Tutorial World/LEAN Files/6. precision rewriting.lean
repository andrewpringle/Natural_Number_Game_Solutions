theorem tutorial_precision_rewriting (a b c : ℕ) : a + 0 + b + 0 + c = a + b + c := by
  rw [add_zero c]
  rw [add_zero]
  rfl
