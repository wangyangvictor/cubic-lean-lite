import CubicTenVariables.LocalizedSeriesPreparation
import CubicTenVariables.ConstructedDeltaSource
import CubicTenVariables.LocalizedCountingAsymptoticCriterion

/-! Positive actual zero-frequency main term, with the arithmetic series
hypotheses discharged by Hooley--Katz, Pleasants and the supplied local
geometric data through the proved ordinary-series argument.
The full count criterion still requires the actual shifted-average estimate.
This file does not assert that estimate or the main Diophantine theorem. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedPositiveMainTerm
open MvPolynomial MeasureTheory Filter PrimeLocalizationSeries
open RealRegularGradientChart LocalizedPoissonCount LocalizedShiftedWindow
open scoped Topology

/-- A single regular weight, chosen before the analytic scales and kernels,
has a strictly positive actual main constant and the normalized zero-term
limit for each canonical smaller-Q scale. -/
theorem exists_weight (hk : Literature.HooleyKatzPointCount)
    (pleasants : Literature.Pleasants1971Theorem2Qp)
    (T : SymmetricIntegerCubicTensor 10) (hzero : ¬ HasIntegerZero T.polynomial)
    (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s),
      @PrimeLocalizationData p ⟨hprimes p hp⟩ T.polynomial) :
    ∃ R : Data (map (Int.castRingHom ℝ) T.polynomial),
      Integrable (cubicOscillatoryIntegral (map (Int.castRingHom ℝ) T.polynomial)
        R.weight.weight) ∧
      ∃ c : ℝ, 0 < c ∧
        localizedSingularSeries T.polynomial (modulus s hprimes D)
          (restriction s hprimes D) *
          cubicSingularIntegral (map (Int.castRingHom ℝ) T.polynomial) R.weight.weight = (c:ℂ) ∧
        ∀ (p : ℕ → ℕ → ℝ → ℂ), DeltaMethod.KernelEstimates 1 p →
          ∀ η : ℝ, 0 < η → η ≤ 1/2 →
            Tendsto (fun k : ℕ => zeroTerm T.polynomial R.weight.weight k
              (CountingScaleSequence.scale η k) (modulus s hprimes D)
              (restriction s hprimes D) η p / (k:ℂ)^7) atTop (𝓝 (c:ℂ)) := by
  obtain ⟨ha,S,hS,hseries⟩ := LocalizedSeriesPreparation.series hk pleasants T hzero s hprimes D
  obtain ⟨R,hI,J,hJ,hint,_⟩ :=
    RegularChartPositiveWeight.exists_integer_data T.polynomial T.polynomial_homogeneous hzero
  have hc : localizedSingularSeries T.polynomial (modulus s hprimes D)
      (restriction s hprimes D) *
      cubicSingularIntegral (map (Int.castRingHom ℝ) T.polynomial) R.weight.weight =
      ((S*J:ℝ):ℂ) := by rw [hseries,hint,Complex.ofReal_mul]
  refine ⟨R,hI,S*J,mul_pos hS hJ,hc,?_⟩
  intro p hp η hη hηhalf
  simpa only [hc] using LocalizedZeroTermLimit.tendsto_normalized_scale
    T.polynomial T.polynomial_homogeneous R.weight.weight (modulus s hprimes D)
    (restriction s hprimes D) p hp η hη hηhalf ha hI

/-- Fully constructed local data, regular weight and delta kernel. The
only inputs are the two named literature propositions; the resulting
positive limit is the actual zero-frequency contribution, not the count. -/
theorem exists_positive_limit (hk : Literature.HooleyKatzPointCount)
    (pleasants : Literature.Pleasants1971Theorem2Qp)
    
    (T : SymmetricIntegerCubicTensor 10) (hzero : ¬ HasIntegerZero T.polynomial)
    (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime) :
    ∃ D : ∀ (p : ℕ) (hp : p ∈ s),
        @PrimeLocalizationData p ⟨hprimes p hp⟩ T.polynomial,
      ∃ R : Data (map (Int.castRingHom ℝ) T.polynomial),
        ∃ c : ℝ, 0 < c ∧ ∃ p : ℕ → ℕ → ℝ → ℂ,
          DeltaMethod.KernelEstimates 1 p ∧
          ∀ η : ℝ, 0 < η → η ≤ 1/2 →
            Tendsto (fun k : ℕ => zeroTerm T.polynomial R.weight.weight k
              (CountingScaleSequence.scale η k) (modulus s hprimes D)
              (restriction s hprimes D) η p / (k:ℂ)^7) atTop (𝓝 (c:ℂ)) := by
  let D := LocalizedSeriesPreparation.chosenData pleasants T hzero s hprimes
  obtain ⟨R,_,c,hc,_,hlimit⟩ := exists_weight hk pleasants T hzero s hprimes D
  obtain ⟨p,hp⟩ := ConstructedDeltaSource.exists_source_kernels
  exact ⟨D,R,c,hc,p,hp,hlimit p hp⟩

/-- For the exact chosen localization, the shifted-average estimate is the
only remaining arithmetic estimate in this integer-zero criterion.
Local data at the finite localization set are supplied; Pleasants also
supplies solubility at the other primes for ordinary-series positivity. -/
theorem hasIntegerZero (hk : Literature.HooleyKatzPointCount)
    (pleasants : Literature.Pleasants1971Theorem2Qp)
    
    (poisson : Literature.SteinShakarchi2011Poisson)
    
    (T : SymmetricIntegerCubicTensor 10)
    (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s),
      @PrimeLocalizationData p ⟨hprimes p hp⟩ T.polynomial)
    (b : ℝ) (hb : b < 20/3)
    (hshift : CleanShiftedAverage T.polynomial (modulus s hprimes D)
      (restriction s hprimes D) b) : HasIntegerZero T.polynomial := by
  by_contra hzero
  obtain ⟨ha,S,hS,hseries⟩ := LocalizedSeriesPreparation.series hk pleasants T hzero s hprimes D
  exact hzero (LocalizedCountingAsymptoticCriterion.hasIntegerZero poisson
    T.polynomial T.polynomial_homogeneous (modulus s hprimes D)
    (modulus_pos s hprimes D) (restriction s hprimes D) b hb hshift ha S hS hseries)

end CubicTenVariables.LocalizedPositiveMainTerm
