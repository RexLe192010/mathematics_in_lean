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

inductive TermType
| variable : TermType
| constant : TermType

structure Term :=
(coefficient : ℝ)
(variables : list ℝ)
(degree : ℕ)
(kind : TermType)

def is_linear (t : Term) : Prop :=
t.degree = 1 ∧ ∀ v ∈ t.variables, v = 1 ∧ ¬ ∃ n : ℝ, n ≠ 1 ∧ v = n^n

structure Equation :=
(lhs : list Term)
(rhs : Term)

def degree_of_equation (eq : Equation) : ℕ :=
max (eq.lhs.foldl (λ d t, max d t.degree) 0) eq.rhs.degree

def is_linear_equation (eq : Equation) : Prop :=
degree_of_equation eq = 1 ∧ ∀ t ∈ eq.lhs, is_linear t ∧ ¬ ∃ t', t'.degree ≠ 1 ∧ t' ∈ eq.lhs



def is_linear_term (t : Term) : Prop :=
t.degree = 1 ∧ t.kind = TermType.variable

def is_linear_equation (lhs_terms : list Term) (rhs_term : Term) : Prop :=
∀ t ∈ lhs_terms, is_linear_term t ∧ rhs_term.degree = 1 ∧ rhs_term.kind = TermType.constant

def equation_i : Equation := {
  lhs := [⟨1, [x], 2, TermType.variable⟩, ⟨1, [y], 1, TermType.variable⟩],
  rhs := ⟨4, [], 0, TermType.constant⟩
}
def equation_ii : Equation := {
  lhs := [⟨1, [x, y], 2, TermType.variable⟩],
  rhs := ⟨4, [], 0, TermType.constant⟩
}
def equation_iii : Equation := {
  lhs := [⟨1, [x], 1, TermType.variable⟩, ⟨1, [y], 1, TermType.variable⟩, ⟨1, [z], 1, TermType.variable⟩, ⟨1, [w], 1, TermType.variable⟩],
  rhs := ⟨0, [], 0, TermType.constant⟩
}
def equation_iv : Equation := {
  lhs := [⟨1, [3, x], 0, TermType.variable⟩, ⟨1, [y], 1, TermType.variable⟩], -- 3^x is not a valid term for a linear equation
  rhs := ⟨0, [], 0, TermType.constant⟩
}

#eval is_linear_equation equation_i.lhs equation_i.rhs   -- False, not linear due to x^2
#eval is_linear_equation equation_ii.lhs equation_ii.rhs -- False, not linear due to xy
#eval is_linear_equation equation_iii.lhs equation_iii.rhs -- True, this is linear
#eval is_linear_equation equation_iv.lhs equation_iv.rhs -- False, not linear due to 3^x
