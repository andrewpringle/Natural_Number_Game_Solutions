theorem le_trans (x y z : ℕ) : x ≤ y → y ≤ z → x ≤ z := by
  cases hxy with a ha
  cases hyz with b hb
  rw [ha] at hb
  use a+b
  rw [add_assoc] at hb
  rw [hb]
  rfl
