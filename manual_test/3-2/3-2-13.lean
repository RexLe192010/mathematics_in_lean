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

-- Solve the equation x + 4 = 5 for x
theorem solve_linear_equation_1 (h : ∀ x : α, x + 4 = 5) : ∀ x : α, x = 1 := by
  intro x
  specialize h x
  have sub_h : x + 4 - 4 = 5 - 4 := by
    rw [← sub_eq_add_neg, ← sub_eq_add_neg]
    congr
    exact h
  simp at sub_h
  assumption

-- Solve the equation 3y + 4 = -5 for y
theorem solve_linear_equation_2 (h : ∀ y : α, 3 * y + 4 = -5) : ∀ y : α, y = -3 := by
  intro y
  specialize h y
  have sub_h : 3 * y + 4 - 4 = -5 - 4 := by
    rw [← sub_eq_add_neg, ← sub_eq_add_neg]
    congr
    exact h
  simp at sub_h
  have div_h : 3 * y / 3 = -9 / 3 := by
    rw [← mul_div_assoc]
    exact sub_h
  simp at div_h
  assumption

end



section
variable {α : Type*} [Field α]

-- Solve the equation 3x + 5 = 11 + x for x
theorem solve_linear_equation_3x_plus_5 (h : ∀ x : α, 3 * x + 5 = 11 + x) : ∀ x : α, x = 3 := by
  intro x
  specialize h x
  have sub_h1 : 3 * x + 5 - 5 = 11 + x - 5 := by
    rw [← sub_eq_add_neg, ← sub_eq_add_neg]
    congr
    exact h
  simp at sub_h1
  have sub_h2 : 3 * x - x = 6 := by
    rw [← sub_eq_add_neg]
    exact sub_h1
  have sub_h3 : 2 * x = 6 := by
    rw [← mul_sub, one_mul]
    exact sub_h2
  have div_h : x = 6 / 2 := by
    rw [← mul_div_cancel_left x (ne_of_gt (by norm_num : (0 : α) < 2))]
    exact sub_h3
  simp at div_h
  assumption

end


section
variables {α : Type*} [Field α]
variables (a b c : α) (h : a ≠ 0)

-- Solve the equation ax + b = c for x
theorem solve_linear_equation_ax_plus_b (eq : ∀ x : α, a * x + b = c) : ∀ x : α, x = (c - b) / a := by
  intro x
  specialize eq x
  have sub_h : a * x + b - b = c - b := by
    rw [← sub_eq_add_neg, ← sub_eq_add_neg]
    congr
    exact eq
  simp at sub_h
  have div_h : x = (c - b) / a := by
    rw [← mul_div_cancel_left x h]
    exact sub_h
  assumption

end


section
variables {α : Type*} [Field α]
variables (y : α) (h : y ≠ 0)

-- Solve the equation (1 + y) / y = 3 for y
theorem solve_equation_one_plus_y_over_y : (1 + y) / y = 3 → y = 1 / 2 := by
  intro eq
  have mul_h : 1 + y = 3 * y := by
    rw [eq, mul_comm y 3, ← mul_assoc, ← one_mul y, mul_inv_cancel h]
  have sub_h : 2 * y = 1 := by
    rw [← add_sub_assoc, add_comm 1 y, add_neg_self y]
    exact mul_h
  have div_h : y = 1 / 2 := by
    rw [← mul_div_cancel_left y (two_ne_zero : (2 : α) ≠ 0), sub_h]
  assumption

end









section
variable {α : Type*} [Field α]

-- Solve the equation 3y + 2 = y - 3 + 4y for y
theorem solve_linear_equation_3y_plus_2 (h : ∀ y : α, 3 * y + 2 = y - 3 + 4 * y) : ∀ y : α, y = -5 := by
  intro y
  specialize h y
  have eq_h : 3 * y + 2 = (1 * y + 4 * y) - 3 := by
    rw [← add_assoc, add_comm (4 * y) (-3), ← add_assoc, ← add_assoc, ← neg_add (-3) 2, add_comm (-3) 2, neg_add_cancel_right]
    exact h
  simp at eq_h
  have sub_h : 3 * y - y = -5 := by
    rw [add_right_inj, ← sub_add_eq_sub_sub_swap, sub_self, zero_sub]
    exact eq_h
  have sub_h2 : 2 * y = -5 := by
    rw [← mul_two, ← mul_sub, one_mul, two_mul]
    exact sub_h
  have div_h : y = -5 / 2 := by
    rw [← mul_div_cancel_left y (two_ne_zero : (2 : α) ≠ 0), sub_h2]
  simp at div_h
  assumption

end

--

section
variable {α : Type*} [Field α]

-- Solve the equation 3y + 2 = y - 3 + 4y for y
theorem solve_linear_equation_3y_plus_2 (h : ∀ y : α, 3 * y + 2 = y - 3 + 4 * y) : ∀ y : α, y = -5 := by
  intro y
  specialize h y
  have sub_h : 3 * y + 2 - (y + 4 * y) = -3 := by
    congr
    exact h
  simp at sub_h
  have combine_y : 3 * y - y - 4 * y = -5 := by
    rw [← sub_add, ← sub_sub, ← add_mul, sub_self, zero_mul, sub_zero, sub_self, zero_sub, neg_add, add_comm]
    exact sub_h
  assumption

end
