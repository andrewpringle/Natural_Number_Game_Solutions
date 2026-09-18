theorem le_succ_self (x : ℕ) : x ≤ Nat.succ x := by
  use 1
  rw [succ_eq_add_one]
  rfl
