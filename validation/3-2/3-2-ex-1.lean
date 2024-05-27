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

section
variable (y : ℝ)

def solve_linear_equation_3y_plus_2_eq_y_minus_3_plus_4y : ℝ :=
  -5 / 2

-- Check the solution
example : 3 * solve_linear_equation_3y_plus_2_eq_y_minus_3_plus_4y + 2 = solve_linear_equation_3y_plus_2_eq_y_minus_3_plus_4y - 3 + 4 * solve_linear_equation_3y_plus_2_eq_y_minus_3_plus_4y := by
  have : 3 * (-5 / 2) + 2 = (-5 / 2) - 3 + 4 * (-5 / 2) := by
    calc
      3 * (-5 / 2) + 2 = -15 / 2 + 2 : by norm_num
                     _ = -15 / 2 + 4 / 2 : by rw [←two_mul, ←div_mul_cancel _ two_ne_zero]
                     _ = (-15 + 4) / 2 : by rw [add_div]
                     _ = -11 / 2 : by norm_num
                     _ = -5 / 2 - 3 + 4 * (-5 / 2) : by simp only [eq_self_iff_true, neg_add_rev, neg_mul_eq_neg_mul_symm, neg_neg]
  exact this


-- 提醒错误结果之后，

def solve_linear_equation_3y_plus_2_eq_y_minus_3_plus_4y : ℝ :=
  -1

-- Check the solution
example : 3 * solve_linear_equation_3y_plus_2_eq_y_minus_3_plus_4y + 2 = solve_linear_equation_3y_plus_2_eq_y_minus_3_plus_4y - 3 + 4 * solve_linear_equation_3y_plus_2_eq_y_minus_3_plus_4y := by
  have : 3 * (-1) + 2 = (-1) - 3 + 4 * (-1) := by
    calc
      3 * (-1) + 2 = -3 + 2 : by norm_num
                  _ = -1    : by norm_num
                  _ = -1 - 3 : by norm_num
                  _ = -4    : by norm_num
                  _ = -1 - 3 + 4 * (-1) : by norm_num
  exact this
