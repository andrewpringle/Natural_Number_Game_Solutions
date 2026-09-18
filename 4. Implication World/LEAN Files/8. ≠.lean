theorem not_equal (P : Prop) (h1 : P) (h2 : P → False) : False := by
  apply h2 at h1
  exact h1
