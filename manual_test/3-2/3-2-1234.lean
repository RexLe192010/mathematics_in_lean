import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Complex.Exponential
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Nat.Digits
import Mathlib.Analysis.SpecialFunctions.Pow.Real--for real power
import Mathlib.Data.Matrix.Basic--for matrix
import Mathlib.Data.Finset.Basic--for sup

open BigOperators
open Nat
open Finset --for range
open Function -- for Injective
open Real
open Topology

def solve_linear_equation (a b c : ℝ) : ℝ :=
  if h : a ≠ 0 then (c - b) / a
  else 0 -- Arbitrary value since the equation is not valid if a = 0

-- x + 4 = 5
#eval solve_linear_equation 1 4 5 -- Should yield x = 1

-- 3y + 4 = -5
#eval solve_linear_equation 3 4 (-5) -- Should yield y = -3


def solve_linear_equation_step_by_step (a1 a2 b c : ℝ) : ℝ :=
  if h1 : a1 - a2 ≠ 0 then (c - b) / (a1 - a2)
  else 0 -- The equation has no unique solution if a1 - a2 = 0

-- Given the equation 3x + 5 = 11 + x, we solve for x.
-- Subtract 5 from both sides: 3x = 6 + x
-- Subtract x from both sides: 2x = 6
-- Divide by the coefficient of x, which is 2: x = 3
#eval solve_linear_equation_step_by_step 3 1 5 11 -- Should yield x = 3



def solve_linear_equation_for_x (a b c : ℝ) : ℝ :=
  if h : a ≠ 0 then (c - b) / a
  else 0 -- Arbitrary value since the equation is not valid if a = 0

-- ax + b = c
#eval solve_linear_equation_for_x a b c -- Should yield x = (c - b) / a



def solve_for_y (a : ℝ) : ℝ :=
  if h : a ≠ 0 then 1 / (2 * a)
  else 0 -- Arbitrary value since the equation is not valid if a = 0

-- Given the equation (1 + y) / y = 3, we solve for y.
-- Multiply both sides by y: 1 + y = 3y
-- Collect y terms on one side: 1 = 2y
-- Divide by 2: y = 1/2
#eval solve_for_y 1 -- Should yield y = 1/2







def solve_linear_equation_simple (a1 a2 a3 b c : ℝ) : ℝ :=
  if h : a1 + a3 - a2 ≠ 0 then (b - c) / (a1 + a3 - a2)
  else 0 -- The equation has no unique solution if a1 + a3 - a2 = 0

-- Given the equation 3y + 2 = y - 3 + 4y, we solve for y.
-- Combine like terms: 3y - y - 4y = -3 - 2
-- This simplifies to: -2y = -5
-- Divide by -2: y = 5 / 2
#eval solve_linear_equation_simple 3 (-1) 4 2 (-3) -- Should yield y = 5 / 2
