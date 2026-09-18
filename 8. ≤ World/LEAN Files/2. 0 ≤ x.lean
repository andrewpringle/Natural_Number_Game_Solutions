theorem zero_le (x : ℕ) : 0 ≤ x := by
  use x
  rw [zero_add]
  rfl
