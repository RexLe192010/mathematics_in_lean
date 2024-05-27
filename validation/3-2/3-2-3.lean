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
