-- Equation 3x + 5 = 11 + x
def solve_linear_equation_4 (x : R) : x = 3 :=
begin
  have h1 : 3 * x + 5 = 11 + x,
  have h2 : 3 * x = 6 + x := sorry,
  have h3 : 2 * x = 6 := sorry,
  exact (div_eq_of_eq_mul_left (by norm_num : (2 : R) ≠ 0) h3).symm,
end
-- Checking the solution by substituting x = 3 into the original equation
#reduce 3 * 3 + 5
#reduce 11 + 3



-- Equation ax + b = c
def solve_linear_equation_5 (a b c : R) (ha : a ≠ 0) : x = (c - b) / a :=
begin
  have h1 : a * x + b = c,
  have h2 : a * x = c - b := sorry,
  exact (div_eq_of_eq_mul_left ha h2).symm,
end


-- Equation (1 + y) / y = 3
def solve_nonlinear_equation_1 (y : R) (hy : y ≠ 0) : y = 1 / 2 :=
begin
  have h1 : (1 + y) / y = 3,
  have h2 : 1 + y = 3 * y := sorry,
  have h3 : 2 * y = 1 := sorry,
  exact (div_eq_of_eq_mul_left (by norm_num : (2 : R) ≠ 0) h3).symm,
end




-- Equation 3y + 2 = y - 3 + 4y
def solve_linear_equation_6 (y : R) : y = -5 :=
begin
  have h1 : 3 * y + 2 = y - 3 + 4 * y,
  have h2 : 3 * y + 2 = 5 * y - 3 := sorry,
  have h3 : 2 * y = -5 := sorry,
  exact (div_eq_of_eq_mul_left (by norm_num : (2 : R) ≠ 0) h3).symm,
end
