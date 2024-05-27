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
