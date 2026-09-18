theorem pred (a b : ℕ) (h : Nat.succ a = Nat.succ b) : a = b := by
  rw [← pred_succ a]
  rw [h]
  rw [pred_succ b]
  rfl
