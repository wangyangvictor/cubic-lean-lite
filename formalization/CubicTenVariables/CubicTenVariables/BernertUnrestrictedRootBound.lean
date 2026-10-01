import CubicTenVariables.PrimePowerRootSeriesIdentity
import CubicTenVariables.SingularSeriesUniformBound
import CubicTenVariables.BernertRootPreparation
import CubicTenVariables.CubicGoodPrimeResidueBound

/-!
# Uniform prime-power roots from the already encoded Bernert input

The finite density identity is proved internally. Only absolute convergence
is used analytically. Bernert supplies it for 6F; root-set inclusion transfers
the bound to F without inverting six, including at primes two and three.
-/

noncomputable section
namespace CubicTenVariables.BernertUnrestrictedRootBound
open MvPolynomial

/-- Absolute convergence of the actual ordinary series bounds every
prime-power root density, with one natural constant before all primes. -/
theorem exists_uniform_root_bound_of_absolute_convergence {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hn : 1 ≤ n)
    (hconv : SingularSeriesAbsolutelyConvergent F) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ s : ℕ,
        (Finset.univ.filter fun z : Fin n → ZMod (p^s) =>
          eval₂ (Int.castRingHom (ZMod (p^s))) z F = 0).card ≤ C*p^(s*(n-1)) := by
  apply SingularSeriesUniformBound.exists_uniform_root_bound F hconv
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro s
  exact PrimePowerRootSeriesIdentity.root_density_eq_sum F hn p s

/-- The unrestricted count needed by the manuscript. Bernert is the only
unproved literature argument; all finite identities, Davenport goodness,
normalization, and the transfer from 6F back to F are proved internally. -/
theorem exists_uniform_root_bound
    (bernert : Literature.Bernert2025Theorem1) {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3) (hn : 10 ≤ n)
    (hA : HessianTheorem11.Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ s : ℕ,
        (Finset.univ.filter fun z : Fin n → ZMod (p^s) =>
          eval₂ (Int.castRingHom (ZMod (p^s))) z F = 0).card ≤ C*p^(s*(n-1)) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_root_bound_of_absolute_convergence
    (C 6 * F) (by omega)
    (BernertRootPreparation.singularSeriesAbsolutelyConvergent_six_mul bernert F hF hn hA)
  refine ⟨C,hC,?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro s
  exact (BernertRootPreparation.card_roots_le_C_mul F 6 p s).trans (hbound p hp s)

/-- The literal ten-variable estimate, uniform over every prime and level. -/
theorem exists_ten_uniform_root_bound
    (bernert : Literature.Bernert2025Theorem1)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : HessianTheorem11.Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ s : ℕ,
        (Finset.univ.filter fun z : Fin 10 → ZMod (p^s) =>
          eval₂ (Int.castRingHom (ZMod (p^s))) z F = 0).card ≤ C*p^(9*s) := by
  simpa only [Nat.reduceSub, Nat.mul_comm _ 9] using
    exists_uniform_root_bound bernert F hF (by omega) hA

/-- The previous good-prime case assembly now needs only Bernert, not a
separately supplied unrestricted-count hypothesis. -/
theorem exists_good_prime_residue_bound
    (bernert : Literature.Bernert2025Theorem1)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : HessianTheorem11.Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ C : ℕ, 1 ≤ C ∧
      ∀ (p : ℕ) (hp : p.Prime),
        letI : Fact p.Prime := ⟨hp⟩
        ¬ (p : ℤ) ∣ D → ∀ (k : Fin 10 → ℤ), (p : ℤ) ∣ eval k F →
          ∀ (r : ℕ) (hr : 2 ≤ r),
            (Finset.univ.filter fun z : Fin 10 → ZMod (p^r) =>
              (∀ i, SmoothResidueIteration.toPrime p r (by omega) (z i) = (k i : ZMod p)) ∧
              eval₂ (Int.castRingHom (ZMod (p^r))) z F = 0).card ≤
                C*(r-1)*p^(9*(r-1) +
                  if (∀ i, (p : ℤ) ∣ k i) then 2
                  else if (∀ i, (p : ℤ) ∣ eval k (pderiv i F)) then 1 else 0) := by
  obtain ⟨D,hD,hgood⟩ := CubicGoodPrimeResidueBound.exists_good_prime_residue_bound F hF hA
  obtain ⟨C,hC,hU⟩ := exists_ten_uniform_root_bound bernert F hF hA
  exact ⟨D,hD,C,hC,hgood C hC hU⟩

end CubicTenVariables.BernertUnrestrictedRootBound
