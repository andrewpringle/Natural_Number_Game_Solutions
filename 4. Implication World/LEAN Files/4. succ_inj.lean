theorem succ_inj (a b : ℕ) (h : Nat.succ a = Nat.succ b) : a = b := by
  rw [four_eq_succ_three] at h
  rw [← succ_eq_add_one] at h
  apply succ_inj at h
  exact h
