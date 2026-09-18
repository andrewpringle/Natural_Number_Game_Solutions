theorem two_plus_two_ne_five : 2 + 2 ≠ 5 := by
  intro h
  rw [succ_add] at h
  rw [add_succ] at h
  rw [add_succ] at h
  rw [add_zero] at h
  apply succ_inj at h
  apply succ_inj at h
  apply succ_inj at h
  apply succ_inj at h
  apply zero_ne_succ at h
  exact h
