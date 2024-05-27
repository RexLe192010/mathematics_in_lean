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
