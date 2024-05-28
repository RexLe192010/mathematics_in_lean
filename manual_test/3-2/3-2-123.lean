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


variable {R : Type*} [division_ring R]

example (x : R) : x + 4 = 5 ↔ x = 1 := by
  constructor
  · intro h
    rw [←add_sub_assoc, add_comm 4 (-4), add_neg_self, zero_add] at h
    exact eq_of_add_eq_add_right h
  · intro h
    rw h
    refl

example (y : R) : 3 * y + 4 = -5 ↔ y = -3 := by
  constructor
  · intro h
    have h₁ : 3 * y = -5 - 4 := by
      rw ←add_eq_of_eq_sub' h
      simp only [add_left_inj]
    have h₂ : y = (-5 - 4) / 3 := by
      rw [h₁, mul_div_cancel_left (-5 - 4) (by norm_num : (3 : R) ≠ 0)]
    exact h₂
  · intro h
    rw h
    simp only [neg_mul_eq_neg_mul_symm, one_mul, neg_neg]
    norm_num


example : 3 * x + 5 = 11 + x ↔ x = 3 := by
  constructor
  · intro h
    have h₁ : 2 * x + 5 = 11 := by
      rw [←sub_eq_iff_eq_add, add_sub_cancel'] at h
    have h₂ : 2 * x = 6 := by
      rw [←sub_eq_iff_eq_add, add_sub_cancel'] at h₁
    have h₃ : x = 6 / 2 := by
      rw [←div_eq_mul_one_div, mul_comm, mul_one_div_cancel (two_ne_zero : (2 : R) ≠ 0), eq_comm] at h₂
    exact h₃
  · intro h
    rw h
    refl

-- Check the answer
example : 3 * 3 + 5 = 11 + 3 := by
  norm_num

-- The above example proves that the solution x = 3 is correct.



variables {a b c : R}

example (h : a ≠ 0) : a * x + b = c ↔ x = (c - b) / a := by
  constructor
  · intro habc
    have h₁ : a * x = c - b := by
      rw [←sub_eq_iff_eq_add, add_sub_cancel'] at habc
    have h₂ : x = (c - b) / a := by
      rw [←div_eq_mul_one_div, mul_comm, mul_one_div_cancel h, eq_comm] at h₁
    exact h₂
  · intro hcb
    rw hcb
    field_simp [h]
    ring

-- The above example proves the solution x = (c - b) / a when a ≠ 0.



example (hy : y ≠ 0) : (1 + y) / y = 3 ↔ y = 1/2 := by
  constructor
  · intro h
    have h₁ : 1 + y = 3 * y := by
      rw [eq_div_iff_mul_eq hy, mul_comm] at h
    have h₂ : 2 * y = 1 := by
      rw [←sub_eq_iff_eq_add, sub_self, zero_add] at h₁
    have h₃ : y = 1 / 2 := by
      rw [←div_eq_mul_one_div, mul_comm, mul_one_div_cancel (two_ne_zero : (2 : R) ≠ 0), eq_comm] at h₂
    exact h₃
  · intro hhalf
    rw hhalf
    field_simp [hy]
    ring

-- The above example proves the solution y = 1/2.







example : 3 * y + 2 = y - 3 + 4 * y ↔ y = -5 := by
  constructor
  · intro h
    have h₁ : 3 * y + 2 = 5 * y - 3 := by
      rw add_eq_of_eq_sub' h
    have h₂ : 2 * y = -5 := by
      linarith
    exact (eq_div_iff_mul_eq (two_ne_zero : (2 : R) ≠ 0)).mp h₂
  · intro h
    rw h
    ring

-- The above example proves the solution y = -5.

--

example : 3 * y + 2 = y - 3 + 4 * y ↔ y = -5 := by
  constructor
  · intro h
    have h₁ : 3 * y + 2 = 5 * y - 3 := by
      rw add_eq_of_eq_sub' h
    have h₂ : 2 * y = -5 := by
      linarith
    have h₃ : y = -5 / 2 := by
      rw [←div_eq_mul_one_div, mul_comm, mul_one_div_cancel (two_ne_zero : (2 : R) ≠ 0), eq_comm] at h₂
    exact h₃
  · intro h
    rw h
    ring

-- The above example proves the solution y = -5 / 2.
