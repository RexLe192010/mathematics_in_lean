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


-- Equation 3x + 5 = 11 + x
def solve_linear_equation_4 (x : R) : x = 3 :=
eq.trans (eq_of_sub_eq (eq.trans (add_right_eq_sub (eq.refl (3*x + 5)) 5)
(eq.trans (add_right_eq_sub (eq.symm (add_comm (11 : R) x)) 5) (add_comm (11 - 5 : R) x)))) (by norm_num)


-- Equation ax + b = c
def solve_linear_equation_5 (a b c : R) (ha : a ≠ 0) : c - b = a * ((c - b) / a) :=
begin
  field_simp [ha],
  ring,
end


-- Equation (1 + y) / y = 3
def solve_linear_equation_6 (y : R) (hy : y ≠ 0) : y = 1 / 2 :=
begin
  field_simp [hy],
  linarith,
end



-- Equation 3y + 2 = y - 3 + 4y
def solve_linear_equation_7 (y : R) : y = -1 :=
begin
  linarith,
end
