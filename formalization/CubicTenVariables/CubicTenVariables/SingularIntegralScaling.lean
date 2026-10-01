import CubicTenVariables.SingularIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Exact normalization under multiplication of the polynomial by a real scalar.
The separate integrability equivalence prevents mistaking a totalized-integral
identity for a convergence assertion. -/

noncomputable section
namespace CubicTenVariables
open MvPolynomial MeasureTheory

theorem cubicOscillatoryIntegral_scale {n : ℕ}
    (F : MvPolynomial (Fin n) ℝ) (w : (Fin n → ℝ) → ℝ) (c β : ℝ) :
    cubicOscillatoryIntegral (C c * F) w β = cubicOscillatoryIntegral F w (c * β) := by
  unfold cubicOscillatoryIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  unfold cubicOscillatoryIntegrand
  simp only [eval_mul, eval_C, Complex.ofReal_mul]
  congr 2
  ring

theorem integrable_cubicOscillatoryIntegral_scale_iff {n : ℕ}
    (F : MvPolynomial (Fin n) ℝ) (w : (Fin n → ℝ) → ℝ) (c : ℝ) (hc : c ≠ 0) :
    Integrable (cubicOscillatoryIntegral (C c * F) w) ↔
      Integrable (cubicOscillatoryIntegral F w) := by
  change Integrable (fun β => cubicOscillatoryIntegral (C c * F) w β) ↔ _
  simp_rw [cubicOscillatoryIntegral_scale]
  exact integrable_comp_mul_left_iff _ hc

/-- Equality of actual integrals; convergence is supplied separately by the
preceding equivalence and the proved chart-weight integrability theorem. -/
theorem cubicSingularIntegral_scale {n : ℕ}
    (F : MvPolynomial (Fin n) ℝ) (w : (Fin n → ℝ) → ℝ) (c : ℝ) :
    cubicSingularIntegral (C c * F) w = |c⁻¹| • cubicSingularIntegral F w := by
  unfold cubicSingularIntegral
  simp_rw [cubicOscillatoryIntegral_scale]
  exact Measure.integral_comp_mul_left _ c

theorem cubicSingularIntegral_scale_six {n : ℕ}
    (F : MvPolynomial (Fin n) ℝ) (w : (Fin n → ℝ) → ℝ) :
    cubicSingularIntegral (C 6 * F) w = (1 / 6 : ℝ) • cubicSingularIntegral F w := by
  rw [cubicSingularIntegral_scale]
  norm_num

end CubicTenVariables
