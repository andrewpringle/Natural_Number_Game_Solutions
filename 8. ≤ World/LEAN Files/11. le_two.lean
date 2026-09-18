theorem le_two (x : ℕ) : x ≤ 2 → x = 0 ∨ x = 1 ∨ x = 2 := by
  induction x
  left
  rfl
  cases n
  right
  left
  rw [one_eq_succ_zero]
  rfl
  cases a
  right
  right
  rw [← one_eq_succ_zero]
  rw [← two_eq_succ_one]
  rfl
  cases hx
  rw [succ_add, succ_add, succ_add] at h
  rw [two_eq_succ_one] at h
  apply succ_inj at h
  rw [one_eq_succ_zero] at h
  apply succ_inj at h
  cases h
