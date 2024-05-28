-- Equation 3x + 5 = 11 + x
def solve_linear_equation_example_3_2 (x : ℝ) : x = 3 :=
begin
  have h1 : 3*x + 5 = 11 + x,
  have h2 : 3*x = 6 + x := add_right_cancel h1,
  have h3 : 2*x = 6 := add_left_cancel' h2,
  exact div_eq_of_mul_eq (by norm_num : 2 ≠ 0) h3,
  -- Check the solution
  have check : 3*3 + 5 = 14 := rfl,
  have check2 : 14 = 11 + 3 := rfl,
  exact check.trans check2.symm,
end


-- Equation ax + b = c
def solve_linear_equation_example_3_3 {a b c : ℝ} (ha : a ≠ 0) : ℝ :=
begin
  let x := (c - b) / a,
  have hx : a*x + b = c,
  calc
    a*x + b = a*((c - b) / a) + b : by rw mul_div_cancel' _ ha
        ... = (a*(c - b))/a + b : by rw mul_assoc
        ... = (c - b) + b : by rw mul_div_cancel _ ha
        ... = c : by rw sub_add_cancel,
  exact x,
end


-- Equation (1 + y) / y = 3
def solve_nonlinear_equation_example_3_4 : ℝ :=
begin
  let y : ℝ := 1/2,
  have hy : (1 + y) / y = 3,
  calc
    (1 + y) / y = (1 + 1/2) / (1/2) : by rw ← div_eq_mul_one_div
             ... = (3/2) * (2/1) : by rw one_div_div
             ... = 3/1 : by norm_num
             ... = 3 : by rw div_one,
  exact y,
end


-- Equation 3y + 2 = y - 3 + 4y
def solve_linear_equation_example_3_5 : ℝ :=
begin
  let y : ℝ,
  have h1 : 3*y + 2 = y - 3 + 4*y,
  have h2 : 3*y + 2 = 5*y - 3 := by rw add_assoc y (-3) (4*y),
  have h3 : 2 = 2*y - 3 := by linarith,
  have h4 : 2 + 3 = 2*y := by linarith,
  have h5 : 5 = 2*y := by linarith,
  have y_eq : y = 5 / 2 := by linarith,
  exact y_eq,
end
