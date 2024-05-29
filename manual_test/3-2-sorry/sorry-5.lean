-- Equation 3x + 5 = 11 + x
def solve_linear_equation_3_2 (h : 3 * x + 5 = 11 + x) : x = 3 := sorry

-- Equation ax + b = c
def solve_linear_equation_3_3 {a b c : R} (h : a ≠ 0) : ∀ x, a * x + b = c → x = (c - b) / a := sorry

-- Equation (1 + y) / y = 3
def solve_linear_equation_3_4 : ∀ y, y ≠ 0 → (1 + y) / y = 3 → y = 1 / 2 := sorry

-- Using the library, solve for y: 3y + 2 = y - 3 + 4y
def solve_linear_equation_given (h : 3 * y + 2 = y - 3 + 4 * y) : y = -5 := sorry
