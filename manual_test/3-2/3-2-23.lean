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
variable {α : Type*} [Field α]

-- Solving x + 4 = 5
theorem solve_linear_equation_one (x : α) (h : x + 4 = 5) : x = 5 - 4 := by
  rw [← add_sub_assoc, add_comm 4, ← sub_add_eq_sub_sub, add_sub_cancel] at h
  exact h

-- Solving 3y + 4 = -5
theorem solve_linear_equation_two (y : α) (h : 3 * y + 4 = -5) : y = (-5 - 4) / 3 := by
  have h1 : 3 * y = -5 - 4, from sub_eq_of_eq_add' (eq_add_of_add_eq' h)
  exact div_eq_of_eq_mul_of_ne_zero (by rwa mul_comm) (by norm_num)

end



section
variable {α : Type*} [Field α] [Inhabited α]

-- Solving 3x + 5 = 11 + x
theorem solve_linear_equation_three (x : α) (h : 3 * x + 5 = 11 + x) : x = 3 := by
  have h1 : 2 * x = 6, from eq_of_sub_eq_zero (by linarith)
  exact eq_of_mul_eq_mul_left (by norm_num) h1

-- Checking the solution
example (h : 3 * 3 + 5 = 11 + 3) : true := by
  trivial

end


section
variables {α : Type*} [Field α]

-- Solving ax + b = c for x
theorem solve_linear_equation_with_constants (a b c x : α) (h : a ≠ 0) (h_eq : a * x + b = c) : x = (c - b) / a := by
  have h1 : a * x = c - b, from sub_eq_of_eq_add' (eq_add_of_add_eq' h_eq)
  exact div_eq_of_eq_mul_of_ne_zero h1 h

end




section
variables {α : Type*} [Field α]

-- Solving (1 + y) / y = 3 for y
theorem solve_nonlinear_equation (y : α) (h : y ≠ 0) : y = 1 / 2 := by
  have h1 : 1 + y = 3 * y, from (mul_eq_of_eq_div h).mp rfl
  have h2 : 2 * y = 1, by linarith
  exact eq_of_mul_eq_mul_left (by norm_num) h2

end








section
variables {α : Type*} [Field α]

-- Solving 3y + 2 = y - 3 + 4y for y
theorem solve_linear_equation_four (y : α) : y = -5 := by
  have h : 3 * y + 2 = 5 * y - 3, by linarith
  have h1 : 2 * y = -5, by linarith
  exact eq_of_mul_eq_mul_left (by norm_num) h1

end

--

section
variables {α : Type*} [Field α]

-- Solving 3y + 2 = y - 3 + 4y for y
theorem solve_linear_equation_four (y : α) (h : 3 * y + 2 = y - 3 + 4 * y) : y = -5 := by
  have h1 : 3 * y + 2 = 5 * y - 3, by linarith
  have h2 : 2 = 2 * y - 3, by linarith
  have h3 : 5 = 2 * y, by linarith
  exact eq_of_mul_eq_mul_left (by norm_num) h3

end
