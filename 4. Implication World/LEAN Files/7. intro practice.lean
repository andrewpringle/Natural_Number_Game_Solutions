theorem intro_practice (a b : ℕ) (h : Nat.succ (Nat.succ a) = Nat.succ (Nat.succ b)) : a = b := by
  intro h
  rw [← succ_eq_add_one] at h
  rw [← succ_eq_add_one] at h
  apply succ_inj at h
  exact h
