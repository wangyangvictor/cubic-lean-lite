import CubicTenVariables.PrimeLocalizationSeries
import CubicTenVariables.OrdinarySeriesOfHooleyKatz
import CubicTenVariables.IntegerAnisotropy

/-! Actual finite localizations of the tensor polynomial.
Hooley--Katz and Pleasants supply the ordinary series through the proved
prime-power, local-density and Euler-product arguments. Every restricted
local factor and the finite replacement argument are proved internally.
Pleasants supplies local solubility at all primes, including outside the
prescribed finite localization set.
There is no change of polynomial between the two singular series. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedSeriesPreparation
open MvPolynomial PrimeLocalizationSeries

/-- For any supplied finite collection of the actual local geometric data,
Hooley--Katz and Pleasants imply localized convergence and positivity.
The finite supplied data do not replace solubility at the other primes. -/
theorem series (hk : Literature.HooleyKatzPointCount)
    (pleasants : Literature.Pleasants1971Theorem2Qp)
    (T : SymmetricIntegerCubicTensor 10) (hzero : ¬ HasIntegerZero T.polynomial)
    (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s),
      @PrimeLocalizationData p ⟨hprimes p hp⟩ T.polynomial) :
    Summable (fun q => ‖localizedSingularSeriesTerm T.polynomial
      (modulus s hprimes D) (restriction s hprimes D) q‖) ∧
      ∃ S : ℝ, 0 < S ∧ localizedSingularSeries T.polynomial
        (modulus s hprimes D) (restriction s hprimes D) = (S:ℂ) := by
  obtain ⟨ha,S,hS,hvalue⟩ :=
    OrdinarySeriesOfHooleyKatz.of_inputs hk pleasants T.polynomial
      T.polynomial_homogeneous hzero
  exact assemble s hprimes D T.polynomial_homogeneous ha S hS hvalue

/-- Choose local data only at the prescribed finite set of primes.
The explicit Pleasants premise is initial p-adic solubility. -/
def chosenData (pleasants : Literature.Pleasants1971Theorem2Qp)
    (T : SymmetricIntegerCubicTensor 10) (hzero : ¬ HasIntegerZero T.polynomial)
    (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime) :
    ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ T.polynomial :=
  fun p hp => @Classical.choice _
    (@nonempty_primeLocalizationData pleasants T.polynomial T.polynomial_homogeneous
      (anisotropicCubicOfNoIntegerZero T.polynomial T.polynomial_homogeneous hzero).anisotropic
      p ⟨hprimes p hp⟩)

/-- No arithmetic convergence or positivity assumption remains: the
literal restricted series is positive and absolutely convergent modulo
exactly Hooley--Katz and Pleasants, for every prescribed finite prime set. -/
theorem exists_positive_series (hk : Literature.HooleyKatzPointCount)
    (pleasants : Literature.Pleasants1971Theorem2Qp)
    (T : SymmetricIntegerCubicTensor 10) (hzero : ¬ HasIntegerZero T.polynomial)
    (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime) :
    ∃ D : ∀ (p : ℕ) (hp : p ∈ s),
        @PrimeLocalizationData p ⟨hprimes p hp⟩ T.polynomial,
      0 < modulus s hprimes D ∧
      Summable (fun q => ‖localizedSingularSeriesTerm T.polynomial
        (modulus s hprimes D) (restriction s hprimes D) q‖) ∧
      ∃ S : ℝ, 0 < S ∧ localizedSingularSeries T.polynomial
        (modulus s hprimes D) (restriction s hprimes D) = (S:ℂ) := by
  let D := chosenData pleasants T hzero s hprimes
  exact ⟨D,modulus_pos s hprimes D,series hk pleasants T hzero s hprimes D⟩

end CubicTenVariables.LocalizedSeriesPreparation
