theorem algorithm_for_equality (a b : ℕ) : a = b ∨ a ≠ b := by
  contrapose! h
  apply succ_inj at h
  exact h
