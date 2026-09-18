theorem one_ne_zero : 1 ≠ 0 := by
  intro h
  symm at h
  apply zero_ne_one at h
  exact h
