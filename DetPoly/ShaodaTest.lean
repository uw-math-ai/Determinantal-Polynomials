-- Test file by Shaoda

#eval 1 + 1

theorem my_first_theorem : 2 + 2 = 4 := by
  rfl

theorem add_zero_test (n : Nat) : n + 0 = n := by
  simp

#check my_first_theorem
