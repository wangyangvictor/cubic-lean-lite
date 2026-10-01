import HessianTheorem11.GeometricInjectivity
import CubicTenVariables.SmoothZeroUpgrade
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
Local geometric consequences of rational anisotropy.

The actual Hessian pencil stays injective over every characteristic-zero
field, including every p-adic field. The proof reuses the proved rational
linear-functional descent argument in `GeometricInjectivity`; no local
solubility assertion or geometric input is assumed here.
-/

noncomputable section

namespace CubicTenVariables.LocalGeometry

open MvPolynomial HessianTheorem11

/-- Scalar extension preserves injectivity of the actual Hessian pencil of
an anisotropic rational cubic. -/
theorem hessian_injective_of_anisotropic
    {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}
    (F : MvPolynomial (Fin n) ℚ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic F) :
    Function.Injective (hessian (map (algebraMap ℚ K) F)) :=
  baseChange_hessian_injective ⟨F, hF, hA⟩

/-- Entrywise formulation using actual second partial derivatives and
coefficient-extension evaluation. -/
theorem eval₂_hessian_injective_of_anisotropic
    {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}
    (F : MvPolynomial (Fin n) ℚ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic F) :
    Function.Injective (fun x : Fin n → K =>
      fun i j => eval₂ (algebraMap ℚ K) x (pderiv j (pderiv i F))) := by
  intro x y hxy
  apply hessian_injective_of_anisotropic F hF hA
  ext i j
  simpa only [hessian, hessianPolynomial, pderiv_map, eval_map] using
    congrFun (congrFun hxy i) j

/-- The Hessian vanishes only at the zero vector, over any extension field. -/
theorem hessian_zero_iff_of_anisotropic
    {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}
    (F : MvPolynomial (Fin n) ℚ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic F) (x : Fin n → K) :
    hessian (map (algebraMap ℚ K) F) x = 0 ↔ x = 0 :=
  baseChange_hessian_zero_iff ⟨F, hF, hA⟩ x

/-- In particular, a nonzero vector has positive actual Hessian rank. -/
theorem hessian_rank_pos_of_anisotropic
    {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}
    (F : MvPolynomial (Fin n) ℚ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic F) (x : Fin n → K) (hx : x ≠ 0) :
    0 < (hessian (map (algebraMap ℚ K) F) x).rank := by
  apply Nat.pos_of_ne_zero
  intro hr
  exact hx ((hessian_zero_iff_of_anisotropic F hF hA x).mp
    (matrix_eq_zero_of_rank_eq_zero _ hr))

/-- The same pencil is injective over every p-adic field; there is no
restriction on the prime. -/
theorem padic_hessian_injective_of_anisotropic
    (p : ℕ) [Fact p.Prime] {n : ℕ}
    (F : MvPolynomial (Fin n) ℚ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic F) :
    Function.Injective (hessian (map (algebraMap ℚ ℚ_[p]) F)) :=
  hessian_injective_of_anisotropic F hF hA

/-- Literal p-adic second-partial formulation of Hessian injectivity. -/
theorem padic_eval₂_hessian_injective_of_anisotropic
    (p : ℕ) [Fact p.Prime] {n : ℕ}
    (F : MvPolynomial (Fin n) ℚ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic F) :
    Function.Injective (fun x : Fin n → ℚ_[p] =>
      fun i j => eval₂ (algebraMap ℚ ℚ_[p]) x (pderiv j (pderiv i F))) :=
  eval₂_hessian_injective_of_anisotropic F hF hA

/-- Any actual nonzero zero over an extension field can be replaced by an
actual nonzero zero with nonvanishing gradient. Local existence itself is
not asserted: it remains the explicit `hFz` hypothesis. -/
theorem nonsingular_zero_of_anisotropic
    {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}
    (F : MvPolynomial (Fin n) ℚ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic F) (z : Fin n → K) (hz : z ≠ 0)
    (hFz : eval z (map (algebraMap ℚ K) F) = 0) :
    ∃ x : Fin n → K, x ≠ 0 ∧
      eval x (map (algebraMap ℚ K) F) = 0 ∧
      gradient (map (algebraMap ℚ K) F) x ≠ 0 := by
  letI : CharZero K := charZero_of_injective_algebraMap
    (algebraMap ℚ K).injective
  exact nonsingular_zero_of_hessian_injective _ (hF.map _)
    (hessian_injective_of_anisotropic F hF hA) z hz hFz

/-- Literal evaluation formulation: a nontrivial local zero of a rational
anisotropic cubic yields a local zero at which some actual first partial
derivative is nonzero. -/
theorem eval₂_nonsingular_zero_of_anisotropic
    {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}
    (F : MvPolynomial (Fin n) ℚ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic F) (z : Fin n → K) (hz : z ≠ 0)
    (hFz : eval₂ (algebraMap ℚ K) z F = 0) :
    ∃ x : Fin n → K, x ≠ 0 ∧
      eval₂ (algebraMap ℚ K) x F = 0 ∧
      ∃ i, eval₂ (algebraMap ℚ K) x (pderiv i F) ≠ 0 := by
  classical
  obtain ⟨x, hx, hFx, hgrad⟩ := nonsingular_zero_of_anisotropic F hF hA z hz
    (by simpa only [eval_map] using hFz)
  refine ⟨x, hx, by simpa only [eval_map] using hFx, ?_⟩
  by_contra h
  push_neg at h
  apply hgrad
  ext i
  simpa only [gradient, pderiv_map, eval_map, Pi.zero_apply] using h i

/-- At every prime, a nonzero p-adic zero suffices; nonsingularity is a
proved consequence, not an extra premise for the local-solubility input. -/
theorem padic_eval₂_nonsingular_zero_of_anisotropic
    (p : ℕ) [Fact p.Prime] {n : ℕ}
    (F : MvPolynomial (Fin n) ℚ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic F) (z : Fin n → ℚ_[p]) (hz : z ≠ 0)
    (hFz : eval₂ (algebraMap ℚ ℚ_[p]) z F = 0) :
    ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧
      eval₂ (algebraMap ℚ ℚ_[p]) x F = 0 ∧
      ∃ i, eval₂ (algebraMap ℚ ℚ_[p]) x (pderiv i F) ≠ 0 :=
  eval₂_nonsingular_zero_of_anisotropic F hF hA z hz hFz

end CubicTenVariables.LocalGeometry
