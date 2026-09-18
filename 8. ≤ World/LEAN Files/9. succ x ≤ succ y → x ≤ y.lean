theorem succ_le_succ (x y : ℕ) : Nat.succ x ≤ Nat.succ y → x ≤ y := by
  cases hx with d hd
  use d
  rw [succ_add] at hd
  apply succ_inj at hd
  exact hd
