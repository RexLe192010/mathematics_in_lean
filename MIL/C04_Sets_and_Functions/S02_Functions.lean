import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by -- proved by github copilot
  constructor
  intro h
  intro x xs
  show x ∈ f ⁻¹' v
  show f x ∈ v
  · apply h
    use x, xs
  intro h
  intro y
  rintro ⟨x, xs, e⟩
  rw [← e]
  exact h xs


example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x
  rintro ⟨y, ys, e⟩
  exact mem_of_eq_of_mem (h (id e.symm)) ys

example : f '' (f ⁻¹' u) ⊆ u := by
  intro y
  rintro ⟨x, h, e⟩
  rw [← e]
  exact h

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro x
  intro h'
  rcases h x with ⟨y, e⟩
  rw [← e]
  use y
  constructor
  · show f y ∈ u
    rw [e]
    exact h'
  · rfl

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro y
  rintro ⟨x, xs, e⟩
  use x
  constructor
  · exact h xs
  · exact e

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x
  rintro h'
  show f x ∈ v
  exact h h'

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  · intro h
    have h' : f x ∈ u ∪ v := by
      exact h
    rcases h' with h' | h'
    · left
      exact h'
    · right
      exact h'
  · intro h
    rcases h with h | h
    · show f x ∈ u ∪ v
      left
      exact h
    · show f x ∈ u ∪ v
      right
      exact h

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro y
  rintro ⟨x, h, e⟩
  constructor
  · use x
    constructor
    · exact h.left
    · exact e
  · use x
    constructor
    · exact h.right
    · exact e

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro y
  rintro ⟨⟨x, xs, e₁⟩, ⟨x', xt, e₂⟩⟩
  have e : f x = f x' := by
    rw [e₁, e₂]
  use x
  constructor
  · constructor
    · exact xs
    · exact mem_of_eq_of_mem (h e) xt
  · exact e₁

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro y
  intro h
  have h' : y ∈ f '' s := by
    exact mem_of_mem_diff h
  have h'' : y ∉ f '' t := by
    exact not_mem_of_mem_diff h
  rcases h' with ⟨x, xs, e⟩
  use x
  constructor
  · use xs
    show x ∉ t
    intro h
    exact h'' ⟨x, h, e⟩
  · exact e


example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x
  intro h
  have h' : f x ∈ u := by
    exact mem_of_mem_diff h
  have h'' : f x ∉ v := by
    exact not_mem_of_mem_diff h
  show f x ∈ u \ v
  constructor
  · exact h'
  · exact h''

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  constructor
  · intro h
    have : y ∈ f '' s := by
      exact h.left
    rcases this with ⟨x, xs, e⟩
    use x
    constructor
    · use xs
      show f x ∈ v
      have : y ∈ v := by
        exact h.right
      exact e.symm ▸ this
    · exact e
  · intro h
    rcases h with ⟨x, ⟨xs, xv⟩, e⟩
    constructor
    · use x
    · have : f x ∈ v := by
        exact xv
      exact e ▸ this

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro y
  rintro ⟨x, ⟨xs, xu⟩, e⟩
  constructor
  · use x
  · exact e ▸ xu

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x
  rintro ⟨xs, xu⟩
  show f x ∈ f '' s ∩ u
  constructor
  · use x
  · exact xu

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  intro x
  rintro h
  show f x ∈ f '' s ∪ u
  rcases h with h | h
  · left
    use x
  · right
    exact h

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  simp
  constructor
  · rintro ⟨x, ⟨i, xAi⟩, fxeq⟩
    use i
    use x
  · rintro ⟨i, x, xAi, fxeq⟩
    use x
    constructor
    · use i
    · exact fxeq

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y
  simp
  intro h
  intro h'
  intro h''
  intro i
  use h
  constructor
  · exact h' i
  · exact h''


example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y
  simp
  intro h
  rcases h i with ⟨x, xAi, e⟩
  use x
  constructor
  · intro i'
    rcases h i' with ⟨x', xAi', e'⟩
    have : x = x' := by
      apply injf
      have : f x = f x' := by
        rw [e, e']
      exact this
    rw [this]
    exact xAi'
  · exact e

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  sorry

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  sorry

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  sorry

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  sorry

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f :=
  sorry

example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  sorry
  have h₃ : j ∉ S
  sorry
  contradiction

-- COMMENTS: TODO: improve this
end
