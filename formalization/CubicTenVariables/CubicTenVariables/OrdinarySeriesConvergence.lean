import CubicTenVariables.PrimeSeriesConvergence
import CubicTenVariables.UnconditionalTenRootBound
import CubicTenVariables.PrimePowerMultiplicativeSummability
import CubicTenVariables.OrdinarySeriesMultiplicativity

/-! Absolute convergence of the actual ordinary ten-variable singular series.
The prime terms use Hooley--Katz; higher prime powers and multiplicativity
are proved internally. No Bernert input or positivity statement is used. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.OrdinarySeriesConvergence
open MvPolynomial

/-- The actual norms at every positive prime-power exponent are summable
jointly in the prime and exponent. -/
theorem summable_prime_powers
    (hk : Literature.HooleyKatzPointCount)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hzero : ¬ HasIntegerZero F) :
    Summable (fun pk : Nat.Primes × ℕ =>
      ‖singularSeriesTerm F (pk.1.val ^ (pk.2+1))‖) := by
  have hprime := PrimeSeriesConvergence.summable_norm hk F hF hzero
  have hhigh := (summable_prod_of_nonneg (fun pk : Nat.Primes × ℕ =>
    norm_nonneg (singularSeriesTerm F (pk.1.val ^ (pk.2+2))))).mp
      (UnconditionalTenRootBound.summable_higher_prime_powers F hF hzero)
  have hlocal (p : Nat.Primes) :
      Summable (fun k : ℕ => ‖singularSeriesTerm F (p.val ^ (k+1))‖) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hhigh.1 p
  apply (summable_prod_of_nonneg (fun pk : Nat.Primes × ℕ =>
    norm_nonneg (singularSeriesTerm F (pk.1.val ^ (pk.2+1))))).mpr
  refine ⟨hlocal, ?_⟩
  apply (hprime.add hhigh.2).congr
  intro p
  rw [(hlocal p).tsum_eq_zero_add]
  simp only [Nat.zero_add, pow_one, Nat.add_assoc, Nat.reduceAdd]

/-- Absolute convergence over all ordinary moduli, with the existing zero
modulus convention. The only literature premise is Hooley--Katz. -/
theorem summable_norm
    (hk : Literature.HooleyKatzPointCount)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hzero : ¬ HasIntegerZero F) :
    Summable (fun q : ℕ => ‖singularSeriesTerm F q‖) := by
  exact PrimePowerMultiplicativeSummability.summable_norm
    (singularSeriesTerm F) (singularSeriesTerm_zero F) (singularSeriesTerm_one F)
    (fun {a b} hab => OrdinarySeriesMultiplicativity.mul F a b hab)
    (summable_prime_powers hk F hF hzero)

/-- Convergence of the actual complex singular-series coefficients. -/
theorem summable
    (hk : Literature.HooleyKatzPointCount)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hzero : ¬ HasIntegerZero F) :
    Summable (singularSeriesTerm F) :=
  (summable_norm hk F hF hzero).of_norm

end CubicTenVariables.OrdinarySeriesConvergence
