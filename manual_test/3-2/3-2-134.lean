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


variable {x y : ℝ}

example : x + 4 = 5 → x = 1 := by
  intro h
  apply eq_of_add_eq_add_right h

example : 3 * y + 4 = -5 → y = -3 := by
  intro h
  have h1 : 3 * y = -9 := by linarith
  exact eq_of_mul_eq_mul_left (by norm_num) h1



example : 3 * x + 5 = 11 + x → x = 3 := by
  intro h
  have h1 : 2 * x = 6 := by linarith
  exact eq_of_mul_eq_mul_left (by norm_num) h1



variable {a b c : ℝ}

example (h : a ≠ 0) : a * x + b = c → x = (c - b) / a := by
  intro h_eq
  have h1 : a * x = c - b := by linarith
  exact div_eq_of_eq_mul_of_ne_zero h h1


example (hy : y ≠ 0) : (1 + y) / y = 3 → y = 1 / 2 := by
  intro h
  have h1 : 1 + y = 3 * y := by
    field_simp at h
    linarith
  have h2 : 2 * y = 1 := by linarith
  exact eq_of_mul_eq_mul_left (by norm_num) h2









example : 3 * y + 2 = y - 3 + 4 * y → y = -5 := by
  intro h
  have h1 : 3 * y + 2 = 5 * y - 3 := by rw [add_assoc y (-3) (4 * y), add_comm y (-3), ← add_assoc (4 * y) (-3) y]
  have h2 : 2 * y = -5 := by linarith
  exact eq_of_mul_eq_mul_left (by norm_num) h2


example : 3 * y + 2 = y - 3 + 4 * y → y = -5 := by
  intro h
  have h1 : 2 * y + 2 = -3 := by linarith
  have h2 : 2 * y = -5 := by linarith
  exact eq_of_mul_eq_mul_left (by norm_num) h2
