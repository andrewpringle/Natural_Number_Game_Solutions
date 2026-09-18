theorem apply_tactic (P Q : Prop) (h1 : P) (h2 : P → Q) : Q := by
  apply h2 at h1
  exact h1
