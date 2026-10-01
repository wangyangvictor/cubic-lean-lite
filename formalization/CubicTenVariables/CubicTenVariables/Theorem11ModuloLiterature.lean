import CubicTenVariables.PlanAlphaCleanShifted
import CubicTenVariables.LocalizedPositiveMainTermUnconditional
import CubicTenVariables.TensorReduction

/-! An intermediate form of the n ≥ 10 rational cubic theorem with
thirteen explicit inputs. The reduced wrapper supplies smooth-at-infinity
integrality, both required cubic spreading statements, prime-field family
counts, p-adic local existence and scalar-lattice Poisson summation by internal
proofs, leaving seven unproved literature premises. The ordinary and localized
series and positive main term are proved internally. Hooley--Katz is still
used for the sharper pointwise estimates in the shifted-average argument. The required cubic
oscillatory localization, rapid decay and delta kernels are proved internally. No shifted-average, application
majorant, local datum, anisotropy contradiction, or main theorem is assumed. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.Theorem11ModuloLiterature
open MvPolynomial HessianTheorem11 PrimeLocalizationSeries

/-- Theorem 1.1 for every rational homogeneous cubic in at least ten
variables, with the thirteen-argument intermediate interface retained. Six
inputs have internal proofs; the reduced wrapper requires seven literature
premises. The local-existence and Poisson arguments are retained for
compatibility and supplied internally in the count criterion. -/
theorem main
    (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (degreeSpan : TranslatedDepthSeven.StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCurveWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (salberger : TranslatedDepthSeven.Published.Salberger2023Theorem04)
    (integrality : CubicPrincipalOpenUniform.Uniform)
    (hk : Literature.HooleyKatzPointCount)
    (browning : Literature.BrowningCubicPointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    (pleasants : Literature.Pleasants1971Theorem2Qp)
    
    (poisson : Literature.SteinShakarchi2011Poisson)
     : MainTheorem := by
  classical
  apply main_iff_symmetricTen.mpr
  intro T
  by_contra hzero
  have hAn := (anisotropicCubicOfNoIntegerZero T.polynomial
    T.polynomial_homogeneous hzero).anisotropic
  obtain ⟨N,hN,p₀,hp₀,hshift⟩ := PlanAlphaCleanShifted.from_literature
    microlocal degreeSpan smooth spread weil dichotomy salberger
    integrality hk browning pointcount T.polynomial
    T.polynomial_homogeneous hAn ((1 : ℝ)/192) (by norm_num) (by norm_num)
  let s := N.primeFactors ∪ (Finset.range p₀).filter Nat.Prime
  have hprimes : ∀ p ∈ s, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Nat.prime_of_mem_primeFactors hp
    · exact (Finset.mem_filter.mp hp).2
  have hsN : N.primeFactors ⊆ s := Finset.subset_union_left
  have hsmall : ∀ p : ℕ, p.Prime → p < p₀ → p ∈ s := by
    intro p hp hlt
    exact Finset.mem_union.mpr (Or.inr
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt,hp⟩))
  let D := LocalizedSeriesUnconditional.chosenData T hzero s hprimes
  exact hzero (LocalizedPositiveMainTermUnconditional.hasIntegerZero
    T s hprimes D ((20 : ℝ)/3-1/192) (by norm_num)
    (hshift s hprimes D hsN hsmall))

end CubicTenVariables.Theorem11ModuloLiterature
