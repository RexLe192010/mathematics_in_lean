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


-- Solution for x + 4 = 5
def solve_linear_eq1 : ℝ :=
  let eq := x + 4 = 5 in
  let sub_eq := eq.sub_left (4:ℝ) in
  let div_eq := sub_eq.div_right (1:ℝ) in
  div_eq.result

-- Solution for 3y + 4 = -5
def solve_linear_eq2 : ℝ :=
  let eq := 3 * y + 4 = -5 in
  let sub_eq := eq.sub_left (4:ℝ) in
  let div_eq := sub_eq.div_right (3:ℝ) in
  div_eq.result


def solve_linear_eq3 : ℝ :=
  let eq := 3 * x + 5 = 11 + x in
  let sub_eq1 := eq.sub_left (5:ℝ) in
  let sub_eq2 := sub_eq1.sub_right x in
  let div_eq := sub_eq2.div_right (2:ℝ) in
  div_eq.result

-- Verification
def check_solution (x : ℝ) : Prop :=
  3 * x + 5 = 11 + x

theorem verify_solution : check_solution (solve_linear_eq3) := by
  have sol : solve_linear_eq3 = 3 := rfl
  rw [sol, check_solution, mul_comm (3:ℝ) _, add_assoc, add_comm (5:ℝ) (3 * 3)]
  exact rfl


variable {a b c : ℝ}

def solve_linear_eq4 (h : a ≠ 0) : ℝ :=
  let eq := a * x + b = c in
  let sub_eq := eq.sub_left b in
  let div_eq := sub_eq.div_left a h in
  div_eq.result

-- Verification
def check_solution4 (x : ℝ) (h : a ≠ 0) : Prop :=
  a * x + b = c

theorem verify_solution4 (h : a ≠ 0) : check_solution4 (solve_linear_eq4 h) h := by
  have sol : solve_linear_eq4 h = (c - b) / a := rfl
  rw [sol, check_solution4, mul_div_cancel' _ h]
  exact rfl


variable {y : ℝ}

def solve_nonlinear_eq1 (h : y ≠ 0) : ℝ :=
  let eq := (1 + y) / y = 3 in
  let mul_eq := eq.mul_right y h in
  let sub_eq := mul_eq.sub_right y in
  let div_eq := sub_eq.div_right (2:ℝ) in
  div_eq.result

-- Verification
def check_solution_nonlinear1 (y : ℝ) (h : y ≠ 0) : Prop :=
  (1 + y) / y = 3

theorem verify_solution_nonlinear1 (h : y ≠ 0) : check_solution_nonlinear1 (solve_nonlinear_eq1 h) h := by
  have sol : solve_nonlinear_eq1 h = 1 / 2 := rfl
  rw [sol, check_solution_nonlinear1, ←one_add, div_self h, mul_comm]
  exact rfl









def solve_linear_eq5 : ℝ :=
  let eq := 3 * y + 2 = y - 3 + 4 * y in
  let sub_eq1 := eq.sub_right y in
  let sub_eq2 := sub_eq1.sub_right (4 * y) in
  let add_eq := sub_eq2.add_left 3 in
  let div_eq := add_eq.div_right 2 in
  div_eq.result

-- Verification
def check_solution5 (y : ℝ) : Prop :=
  3 * y + 2 = y - 3 + 4 * y

theorem verify_solution5 : check_solution5 solve_linear_eq5 := by
  have sol : solve_linear_eq5 = -1/2 := rfl
  rw [sol, check_solution5]
  norm_num
  exact rfl

--


def solve_linear_eq5 : ℝ :=
  let eq := 3 * y + 2 = y - 3 + 4 * y in
  let sub_eq := eq.sub_right y in
  let sub_eq2 := sub_eq.sub_right (4 * y) in
  let add_eq := sub_eq2.add_right 3 in
  let div_eq := add_eq.div_right 2 in
  div_eq.result

-- Verification
def check_solution5 (y : ℝ) : Prop :=
  3 * y + 2 = y - 3 + 4 * y

theorem verify_solution5 : check_solution5 solve_linear_eq5 := by
  have sol : solve_linear_eq5 = 5/2 := rfl
  rw [sol, check_solution5]
  norm_num
  exact rfl
