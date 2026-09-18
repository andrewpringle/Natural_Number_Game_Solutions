theorem zero_ne_succ (n : ℕ) : 0 ≠ Nat.succ n := by
  intro h
  rw [one_eq_succ_zero] at h
  apply zero_ne_succ at h
  exact h
