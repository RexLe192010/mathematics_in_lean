-- Define a function to solve the given equation for y
def solveForYExercise32 : Int :=
  let numerator := 2 -- the coefficient of y in the numerator
  let denominator := 3 -- the denominator from the original fraction
  let constant := -3 -- the constant on the left side of the equation
  let rightSideCoefficient := 1 -- the coefficient of y on the right side of the equation
  -- Clear the fraction by multiplying by the denominator and move y terms to one side
  let yCoefficient := denominator * rightSideCoefficient - numerator
  let constants := denominator * constant
  -- Solve for y by dividing the constants by the new coefficient of y
  constants / yCoefficient

-- Output the solution
#eval solveForYExercise32  -- Should output `-9`
