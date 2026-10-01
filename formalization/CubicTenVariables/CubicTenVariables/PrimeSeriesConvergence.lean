import CubicTenVariables.ReducedAmbientPointCount
import CubicTenVariables.PrimePointCountTransfer
import CubicTenVariables.PrimePowerSeriesConvergence
import CubicTenVariables.IntegerAnisotropy
import CubicTenVariables.CubicPrincipalOpenUniform

/-! Absolute convergence of the prime terms of the actual ten-variable
singular series. Hooley--Katz supplies the ambient point count. Geometric
integrality is proved internally, and finitely many bad primes are absorbed
in a fixed constant. Neither Browning's hyperplane estimate nor Bernert's
singular-series convergence theorem is used. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PrimeSeriesConvergence
open MvPolynomial

/-- The actual normalized coefficient has a uniform three-halves decay
bound at every prime, including the finitely many bad reduction primes. -/
theorem exists_uniform_bound
    (hk : Literature.HooleyKatzPointCount)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hzero : ¬ HasIntegerZero F) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℕ, p.Prime →
      ‖singularSeriesTerm F p‖ ≤ C * (p : ℝ)^(-(3 : ℝ)/2) := by
  obtain ⟨D,hD,A,hA,hcount⟩ := ReducedAmbientPointCount.exists_prime_bound
    CubicPrincipalOpenUniform.proved hk F hF
    (anisotropicCubicOfNoIntegerZero F hF hzero).anisotropic
  let C : ℝ := A + (D : ℝ)^11
  have hDpow : 0 ≤ (D : ℝ)^11 := pow_nonneg (Nat.cast_nonneg _) _
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hDC : (D : ℝ)^11 ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg _
  have hbound : ‖completeCubicSum F p 0‖ ≤ C * (p : ℝ)^((17 : ℝ)/2) := by
    by_cases hbad : p ∣ D
    · have hpD : (p : ℝ) ≤ D := by
        exact_mod_cast Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hD) hbad
      have htriv : ‖completeCubicSum F p 0‖ ≤ C :=
        (PrimePointCountTransfer.trivial_bound F p 0).trans
          ((pow_le_pow_left₀ hp0 hpD 11).trans hDC)
      exact htriv.trans (le_mul_of_one_le_right (zero_le_one.trans hC)
        (Real.one_le_rpow hp1 (by norm_num)))
    · exact (PrimePointCountTransfer.zero_frequency_bound F p 0 (by ext i; simp)
        A (zero_le_one.trans hA) (hcount p hp hbad)).trans
          (mul_le_mul_of_nonneg_right hAC (Real.rpow_nonneg hp0 _))
  have h := PrimePowerSeriesConvergence.normalized_bound F hp.pos hbound
  norm_num at h ⊢
  exact h

/-- Hooley--Katz alone suffices for absolute convergence over the prime
moduli in the anisotropic ten-variable contradiction branch. -/
theorem summable_norm
    (hk : Literature.HooleyKatzPointCount)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hzero : ¬ HasIntegerZero F) :
    Summable (fun p : Nat.Primes => ‖singularSeriesTerm F p.val‖) := by
  obtain ⟨C,_,hC⟩ := exists_uniform_bound hk F hF hzero
  have hmajor : Summable (fun p : Nat.Primes => (p.val : ℝ)^(-(3 : ℝ)/2)) :=
    (Real.summable_nat_rpow.mpr (by norm_num)).comp_injective Subtype.val_injective
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => hC p.val p.property) (hmajor.mul_left C)

end CubicTenVariables.PrimeSeriesConvergence
