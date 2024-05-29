-- Equation 3x + 5 = 11 + x
def solve_linear_equation_3x_plus_5 (x : R) (h : 3 * x + 5 = 11 + x) : 2 * x = 6 :=
sorry

-- Now, divide both sides by 2
def solve_for_x (x : R) (h : 2 * x = 6) : x = 3 :=
sorry



-- Equation ax + b = c
def solve_linear_equation_ax_plus_b (a b c x : R) (h : a * x + b = c) : a * x = c - b :=
sorry

-- Now, divide both sides by a
def solve_for_x (a b c x : R) (h : a * x = c - b) (ha : a ≠ 0) : x = (c - b) / a :=
sorry



-- Equation (1 + y) / y = 3
def solve_rational_equation_1_plus_y_over_y (y : R) (h : (1 + y) / y = 3) (hy : y ≠ 0) : 1 + y = 3 * y :=
sorry

-- Now, collect y terms on one side
def solve_for_y_collect_terms (y : R) (h : 1 + y = 3 * y) : 2 * y = 1 :=
sorry

-- Finally, divide both sides by 2 to solve for y
def solve_for_y (y : R) (h : 2 * y = 1) : y = 1 / 2 :=
sorry




-- Equation 3y + 2 = y - 3 + 4y
def solve_linear_equation_3y_plus_2 (y : R) (h : 3 * y + 2 = y - 3 + 4 * y) : 2 * y = -5 :=
sorry

-- Now, divide both sides by 2 to solve for y
def solve_for_y (y : R) (h : 2 * y = -5) : y = -5 / 2 :=
sorry
