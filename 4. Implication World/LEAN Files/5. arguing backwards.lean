theorem arguing_backwards (a b : ℕ) (h : Nat.succ a = Nat.succ b) : a = b := by
  apply succ_inj
  rw [succ_eq_add_one]
  rw [← four_eq_succ_three]
  exact h
