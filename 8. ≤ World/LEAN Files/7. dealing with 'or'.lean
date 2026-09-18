theorem dealing_with_or (P Q : Prop) : P ∨ Q → Q ∨ P := by
  cases h with hx hy
  right
  exact hx
  left
  exact hy
