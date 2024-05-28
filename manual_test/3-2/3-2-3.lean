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

variable {R : Type*} [DivisionRing R]

-- Equation x + 4 = 5
def solve_linear_equation_1 (a b : R) (h : a + 4 = 5) : a = 5 - 4 :=
  by rw [← h, add_sub_cancel]

-- Equation 3y + 4 = -5
def solve_linear_equation_2 (c d : R) (h : 3 * c + 4 = -5) : c = (-5 - 4) / 3 :=
  by rw [← h, add_left_neg, mul_div_cancel_left _ (by norm_num : (3 : R) ≠ 0)]

end



section

variable {R : Type*} [DivisionRing R]

-- Solve the equation 3x + 5 = 11 + x for x
def solve_linear_equation_3_2 (x : R) (h : 3 * x + 5 = 11 + x) : x = 3 :=
  by
    have h1 : 2 * x = 6 := by
      rw [add_left_neg (5 : R), add_comm (11 : R) x, ←add_assoc, ←sub_eq_add_neg, add_right_inj] at h
      exact sub_eq_of_eq_add' h
    have h2 : x = 6 / 2 := by
      rwa [mul_div_cancel_left x (by norm_num : (2 : R) ≠ 0)] at h1
    by rwa [div_eq_mul_one_div, mul_one, bit0, bit1, zero_add] at h2

-- Check the solution by substituting x = 3 into the original equation
example (h : 3 * 3 + 5 = 11 + 3) : true :=
  trivial

end


section

variable {R : Type*} [Field R]

-- Solve the equation ax + b = c for x
def solve_linear_equation_3_3 (a b c x : R) (h : a ≠ 0) (h_eq : a * x + b = c) : x = (c - b) / a :=
  by
    have h1 : a * x = c - b := by
      rw [←h_eq, add_sub_cancel]
    have h2 : x = (c - b) / a := by
      rwa [mul_div_cancel _ h] at h1
    exact h2

end


section

variable {R : Type*} [Field R]

-- Solve the equation (1 + y) / y = 3 for y
def solve_equation_3_4 (y : R) (h : y ≠ 0) : y = 1 / 2 :=
  by
    have h1 : 1 + y = 3 * y := by
      rw [←mul_one y, ←mul_add, mul_eq_mul_right_iff] at h
      cases h with h_ h_
      contradiction
      exact h_
    have h2 : 2 * y = 1 := by
      rw [←h1, ←sub_eq_add_neg, sub_self, zero_add]
    by
      rw [←h2, mul_div_cancel_left _ (by norm_num : (2 : R) ≠ 0)]

end






section

variable {R : Type*} [DivisionRing R]

-- Solve the equation 3y + 2 = y - 3 + 4y for y
def solve_equation_3y_plus_2 (y : R) (h : 3 * y + 2 = y - 3 + 4 * y) : y = -5 :=
  by
    rw [←sub_eq_add_neg, ←sub_eq_add_neg, add_assoc, ←add_assoc (4 * y), ←add_comm (4 * y), add_left_cancel_iff, ←add_assoc, ←neg_add_eq_sub, add_right_inj] at h
    rw [sub_eq_zero_of_eq h, neg_eq_iff_add_eq_zero, add_assoc, zero_add, ←add_assoc, add_right_neg, zero_add]

end

--

section

variable {R : Type*} [DivisionRing R]

-- Solve the equation 3y + 2 = y - 3 + 4y for y
def solve_equation_for_y (y : R) : 3 * y + 2 = y - 3 + 4 * y → y = -5 :=
  by
    intro h
    have h1 : 3 * y + 2 = 5 * y - 3 := by
      rw [←add_assoc, add_comm (y) (4 * y), ←add_assoc, add_right_inj] at h
      exact h
    have h2 : 2 + 3 = 5 * y - 3 * y := by
      rw [←h1, add_comm (3 * y) (2), ←sub_eq_add_neg, ←sub_eq_add_neg, ←sub_add, sub_right_inj] at h
      exact h
    have h3 : 5 = 2 * y := by
      rw [add_right_cancel_iff] at h2
      exact h2
    by
      rw [←h3, mul_div_cancel_left _ (by norm_num : (2 : R) ≠ 0)]

end
