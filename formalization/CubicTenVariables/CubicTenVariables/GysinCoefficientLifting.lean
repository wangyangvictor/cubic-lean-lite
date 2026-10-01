import Mathlib.Algebra.FiveLemma
import Mathlib.Tactic

/-!
# Lifting a cohomological degree range through coefficient exact sequences

This is the additive-group argument of `SingularSupport.tex`, lines 429--460.
The integer degree is independent of the positive coefficient level. All
horizontal maps, exactness conditions, and commuting squares are explicit.
No sheaf, geometric, or Gysin theorem is assumed or encoded here.

The level-one map is bijective strictly above an integer cutoff and only
surjective at the cutoff. An induction proves the same two assertions at
every positive level. In particular, the first vertical map at degree
`a = t + 1` is only required to be surjective, not injective.
-/

set_option autoImplicit false

namespace CubicTenVariables.GysinCoefficientLifting

universe u v

variable (A : ℕ → ℤ → Type u) (B : ℕ → ℤ → Type v)
variable [∀ r a, AddGroup (A r a)] [∀ r a, AddGroup (B r a)]
variable (g : ∀ r a, A r a →+ B r a)

/-- The five consecutive objects in the coefficient long exact sequence
at the step from level `r` to level `r+1`, with their actual comparison maps:

`A 1 (a-1) → A r a → A (r+1) a → A 1 a → A r (a+1)`

and the identical row for `B`. Exactness is imposed at the three internal
objects in each row. This structure supplies no bijectivity or surjectivity
condition on any comparison map. -/
structure StepDiagram (r : ℕ) (a : ℤ) where
  upper₁ : A 1 (a-1) →+ A r a
  upper₂ : A r a →+ A (r+1) a
  upper₃ : A (r+1) a →+ A 1 a
  upper₄ : A 1 a →+ A r (a+1)
  lower₁ : B 1 (a-1) →+ B r a
  lower₂ : B r a →+ B (r+1) a
  lower₃ : B (r+1) a →+ B 1 a
  lower₄ : B 1 a →+ B r (a+1)
  comm₁ : lower₁.comp (g 1 (a-1)) = (g r a).comp upper₁
  comm₂ : lower₂.comp (g r a) = (g (r+1) a).comp upper₂
  comm₃ : lower₃.comp (g (r+1) a) = (g 1 a).comp upper₃
  comm₄ : lower₄.comp (g 1 a) = (g r (a+1)).comp upper₄
  upper_exact₁ : Function.Exact upper₁ upper₂
  upper_exact₂ : Function.Exact upper₂ upper₃
  upper_exact₃ : Function.Exact upper₃ upper₄
  lower_exact₁ : Function.Exact lower₁ lower₂
  lower_exact₂ : Function.Exact lower₂ lower₃
  lower_exact₃ : Function.Exact lower₃ lower₄

/-- The full positive-level induction, retaining both the strict-degree
isomorphism range and the boundary surjectivity needed by the next step.
The cutoff may be any integer, including a negative integer. -/
theorem finite_levels (t : ℤ)
    (diagrams : ∀ r : ℕ, 1 ≤ r → ∀ a : ℤ, StepDiagram A B g r a)
    (base_bijective : ∀ a : ℤ, t < a → Function.Bijective (g 1 a))
    (base_surjective : Function.Surjective (g 1 t)) :
    ∀ r : ℕ, 1 ≤ r →
      (∀ a : ℤ, t < a → Function.Bijective (g r a)) ∧
        Function.Surjective (g r t) := by
  intro r
  induction r with
  | zero => omega
  | succ r ih =>
    intro hr
    by_cases hr0 : r = 0
    · subst r
      exact ⟨base_bijective, base_surjective⟩
    have hr1 : 1 ≤ r := by omega
    obtain ⟨previous_bijective, previous_surjective⟩ := ih hr1
    constructor
    · intro a ha
      let d := diagrams r hr1 a
      have first_surjective : Function.Surjective (g 1 (a-1)) := by
        by_cases hboundary : a-1 = t
        · rw [hboundary]
          exact base_surjective
        · exact (base_bijective (a-1) (by omega)).2
      exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
        d.upper₁ d.upper₂ d.upper₃ d.upper₄
        d.lower₁ d.lower₂ d.lower₃ d.lower₄
        (g 1 (a-1)) (g r a) (g (r+1) a) (g 1 a) (g r (a+1))
        d.comm₁ d.comm₂ d.comm₃ d.comm₄
        d.upper_exact₁ d.upper_exact₂ d.upper_exact₃
        d.lower_exact₁ d.lower_exact₂ d.lower_exact₃
        first_surjective (previous_bijective a ha) (base_bijective a ha)
        (previous_bijective (a+1) (by omega)).1
    · let d := diagrams r hr1 t
      exact AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
        d.upper₂ d.upper₃ d.upper₄ d.lower₂ d.lower₃ d.lower₄
        (g r t) (g (r+1) t) (g 1 t) (g r (t+1))
        d.comm₂ d.comm₃ d.comm₄
        d.upper_exact₃ d.lower_exact₂ d.lower_exact₃
        previous_surjective base_surjective
        (previous_bijective (t+1) (by omega)).1

/-- Bijectivity above the cutoff, for any positive coefficient level. -/
theorem bijective_above (t : ℤ)
    (diagrams : ∀ r : ℕ, 1 ≤ r → ∀ a : ℤ, StepDiagram A B g r a)
    (base_bijective : ∀ a : ℤ, t < a → Function.Bijective (g 1 a))
    (base_surjective : Function.Surjective (g 1 t))
    (r : ℕ) (hr : 1 ≤ r) (a : ℤ) (ha : t < a) :
    Function.Bijective (g r a) :=
  (finite_levels A B g t diagrams base_bijective base_surjective r hr).1 a ha

/-- Surjectivity at the cutoff; injectivity at that degree is not claimed. -/
theorem surjective_at (t : ℤ)
    (diagrams : ∀ r : ℕ, 1 ≤ r → ∀ a : ℤ, StepDiagram A B g r a)
    (base_bijective : ∀ a : ℤ, t < a → Function.Bijective (g 1 a))
    (base_surjective : Function.Surjective (g 1 t))
    (r : ℕ) (hr : 1 ≤ r) : Function.Surjective (g r t) :=
  (finite_levels A B g t diagrams base_bijective base_surjective r hr).2

end CubicTenVariables.GysinCoefficientLifting
