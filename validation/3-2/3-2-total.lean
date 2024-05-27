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

def solve_linear_equation_1 (a b : ℝ) : ℝ :=
  (b - a) / 1

def solve_linear_equation_2 (a c : ℝ) : ℝ :=
  (-c - a) / 3



def solve_linear_equation_3x_plus_5_eq_11_plus_x : ℝ :=
  (11 - 5) / 2

-- Check the solution
example : 3 * solve_linear_equation_3x_plus_5_eq_11_plus_x + 5 = 11 + solve_linear_equation_3x_plus_5_eq_11_plus_x := by
  have : 3 * (11 - 5) / 2 + 5 = 11 + (11 - 5) / 2 := by
    calc
      3 * (11 - 5) / 2 + 5 = 3 * 6 / 2 + 5 : by rw [sub_self]
                         _ = 9 + 5         : by norm_num
                         _ = 14            : by norm_num
                         _ = 11 + 3        : by norm_num
                         _ = 11 + (11 - 5) / 2 : by rw [div_self]
  exact this



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



def solve_equation_one_plus_y_over_y_eq_3 : ℝ :=
  1 / 2

-- Check the solution
example : (1 + solve_equation_one_plus_y_over_y_eq_3) / solve_equation_one_plus_y_over_y_eq_3 = 3 := by
  have : (1 + 1 / 2) / (1 / 2) = 3 := by
    calc
      (1 + 1 / 2) / (1 / 2) = (2 / 2 + 1 / 2) / (1 / 2) : by rw [one_eq_div]
                            _ = (3 / 2) / (1 / 2)       : by rw [add_div]
                            _ = 3                       : by rw [div_self']
  exact this
