def solve_linear_equation_ax_plus_b_eq_c (a b c : ℝ) : ℝ :=
  (c - b) / a

-- Check the solution
example (a b c : ℝ) (h : a ≠ 0) : a * solve_linear_equation_ax_plus_b_eq_c a b c + b = c := by
  have : a * ((c - b) / a) + b = c := by
    calc
      a * ((c - b) / a) + b = (a * (c - b)) / a + b : by rw [mul_div_comm]
                           _ = (c - b) + b          : by rw [mul_div_cancel' _ h]
                           _ = c                    : by rw [sub_add_cancel]
  exact this
