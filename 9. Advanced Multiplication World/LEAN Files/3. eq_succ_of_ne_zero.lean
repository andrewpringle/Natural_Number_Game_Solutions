theorem eq_succ_of_ne_zero (a : ℕ) : a ≠ 0 → ∃ b, a = Nat.succ b := by
  cases a with d
  tauto
  use d
  rfl
