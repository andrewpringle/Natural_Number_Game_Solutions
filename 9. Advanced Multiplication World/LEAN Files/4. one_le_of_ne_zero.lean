theorem one_le_of_ne_zero (a : ℕ) : a ≠ 0 → 1 ≤ a := by
  cases a
  contrapose ha
  decide
  use a_1
  rw [add_comm]
  rw [succ_eq_add_one]
  rfl
