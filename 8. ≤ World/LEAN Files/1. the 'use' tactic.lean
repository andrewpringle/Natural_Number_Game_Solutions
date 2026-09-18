theorem use_tactic (a : ℕ) : 0 ≤ a := by
  use 0
  rw [add_zero]
  rfl
