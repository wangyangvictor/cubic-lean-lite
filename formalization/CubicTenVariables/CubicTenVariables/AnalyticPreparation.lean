import CubicTenVariables.TensorReduction
import CubicTenVariables.RealWeight
import CubicTenVariables.OrdinarySeriesOfHooleyKatz
import CubicTenVariables.IntegerAnisotropy
import CubicTenVariables.SingularIntegralPositivity

/-! A proved part of the circle-method preparation. The no-integer-zero
branch supplies rational anisotropy, a nonsingular real point, and an actual
smooth counting weight. The singular-series conclusion follows from Hooley--Katz and
Pleasants via internal prime-power estimates, local densities and the Euler
product. This is not a counting asymptotic or a
proof of MainTheorem. -/

noncomputable section
namespace CubicTenVariables
open MvPolynomial HessianTheorem11 MeasureTheory Filter
open scoped Topology

theorem map_int_rat_real {n : ℕ} (F : MvPolynomial (Fin n) ℤ) :
    map (algebraMap ℚ ℝ) (map (Int.castRingHom ℚ) F) =
      map (Int.castRingHom ℝ) F := by
  rw [MvPolynomial.map_map]
  congr 1

/-- The actual real-point and singular-series outputs needed for the later
main-term argument, with all conditions and the remaining literature inputs visible.
Neither positivity of the singular integral nor a localized series statement
nor an asymptotic for the weighted count is claimed by this theorem. -/
theorem prepare_real_place_and_series
    (hk : Literature.HooleyKatzPointCount)
    (pleasants : Literature.Pleasants1971Theorem2Qp)
    (T : SymmetricIntegerCubicTensor 10) (hzero : ¬ HasIntegerZero T.polynomial) :
    SingularSeriesAbsolutelyConvergent T.polynomial ∧
      Literature.PositiveRealSingularSeries T.polynomial ∧
      ∃ x : Fin 10 → ℝ, x ≠ 0 ∧
        eval₂ (Int.castRingHom ℝ) x T.polynomial = 0 ∧
        gradient (map (Int.castRingHom ℝ) T.polynomial) x ≠ 0 ∧
        Nonempty (SmoothCountingWeight x) := by
  have hs := OrdinarySeriesOfHooleyKatz.of_inputs hk pleasants T.polynomial
    T.polynomial_homogeneous hzero
  let F := anisotropicCubicOfNoIntegerZero T.polynomial T.polynomial_homogeneous hzero
  obtain ⟨x, hx, hFx, hgrad, hw⟩ := exists_nonsingular_real_zero_with_weight F (by omega)
  refine ⟨hs.1, hs.2, x, hx, ?_, ?_, hw⟩
  · change eval x (map (algebraMap ℚ ℝ) (map (Int.castRingHom ℚ) T.polynomial)) = 0 at hFx
    rw [map_int_rat_real, ← eval₂_eq_eval_map] at hFx
    exact hFx
  · change gradient (map (algebraMap ℚ ℝ) (map (Int.castRingHom ℚ) T.polynomial)) x ≠ 0 at hgrad
    rwa [map_int_rat_real] at hgrad

/-- The ordinary singular series and the actual singular integral are both
strictly positive. The archimedean assertion is proved internally; the
literature arguments are Hooley--Katz and Pleasants for the series. No localized series or
counting asymptotic is asserted. -/
theorem prepare_positive_real_place_and_series
    (hk : Literature.HooleyKatzPointCount)
    (pleasants : Literature.Pleasants1971Theorem2Qp)
    (T : SymmetricIntegerCubicTensor 10) (hzero : ¬ HasIntegerZero T.polynomial) :
    SingularSeriesAbsolutelyConvergent T.polynomial ∧
      Literature.PositiveRealSingularSeries T.polynomial ∧
      ∃ x : Fin 10 → ℝ, x ≠ 0 ∧
        eval₂ (Int.castRingHom ℝ) x T.polynomial = 0 ∧
        gradient (map (Int.castRingHom ℝ) T.polynomial) x ≠ 0 ∧
        ∃ w : SmoothCountingWeight x,
          Integrable (cubicOscillatoryIntegral (map (Int.castRingHom ℝ) T.polynomial) w.weight) ∧
            ∃ J : ℝ, 0 < J ∧
              cubicSingularIntegral (map (Int.castRingHom ℝ) T.polynomial) w.weight = (J : ℂ) ∧
              Tendsto (cubicSingularIntegralTruncated
                (map (Int.castRingHom ℝ) T.polynomial) w.weight) atTop (𝓝 (J : ℂ)) := by
  obtain ⟨hseries, hpos, x, hx, hFx, hgrad, _⟩ := prepare_real_place_and_series hk pleasants T hzero
  have hFx' : eval x (map (Int.castRingHom ℝ) T.polynomial) = 0 := by
    rwa [← eval₂_eq_eval_map]
  obtain ⟨w, hw⟩ := exists_smoothCountingWeight_positive_singularIntegral (m := 9)
    (map (Int.castRingHom ℝ) T.polynomial) x hx hFx' hgrad
  exact ⟨hseries, hpos, x, hx, hFx, hgrad, w, hw⟩

end CubicTenVariables
