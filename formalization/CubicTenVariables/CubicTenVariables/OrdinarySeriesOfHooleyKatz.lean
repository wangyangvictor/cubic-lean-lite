import CubicTenVariables.OrdinarySeriesConvergence
import CubicTenVariables.OrdinarySeriesPositivity
import CubicTenVariables.OrdinaryLocalFactorPositivity

/-! The actual ten-variable ordinary singular series is absolutely
convergent and strictly positive from Hooley--Katz and Pleasants. The
prime-power estimates, multiplicativity, local-density limit, and Euler
product argument are proved internally; Bernert is not an input. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.OrdinarySeriesOfHooleyKatz
open MvPolynomial

/-- Given actual local data at every prime, Hooley--Katz suffices for
absolute convergence and strict positivity of the ordinary singular series.
The required local data are explicit here and supplied internally below. -/
theorem of_local_data
    (hk : Literature.HooleyKatzPointCount)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hzero : ¬ HasIntegerZero F)
    (data : ∀ (p : ℕ) [Fact p.Prime], Nonempty (PrimeLocalizationData p F)) :
    SingularSeriesAbsolutelyConvergent F ∧ Literature.PositiveRealSingularSeries F := by
  have hconv := OrdinarySeriesConvergence.summable_norm hk F hF hzero
  refine ⟨hconv, OrdinarySeriesPositivity.of_localFactors F (by decide) hconv
    (OrdinarySeriesConvergence.summable_prime_powers hk F hF hzero) ?_⟩
  intro p
  letI : Fact p.val.Prime := ⟨p.property⟩
  obtain ⟨D⟩ := data p.val
  exact OrdinaryLocalFactorPositivity.localFactor_re_pos D hconv

/-- For the actual anisotropic ten-variable cubic, both convergence and
positivity follow from the two named literature premises. No local data,
pointwise estimate, convergence theorem or positivity result is supplied. -/
theorem of_inputs
    (hk : Literature.HooleyKatzPointCount)
    (pleasants : Literature.Pleasants1971Theorem2Qp)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hzero : ¬ HasIntegerZero F) :
    SingularSeriesAbsolutelyConvergent F ∧ Literature.PositiveRealSingularSeries F := by
  apply of_local_data hk F hF hzero
  intro p _
  exact nonempty_primeLocalizationData pleasants F hF
    (anisotropicCubicOfNoIntegerZero F hF hzero).anisotropic p

end CubicTenVariables.OrdinarySeriesOfHooleyKatz
