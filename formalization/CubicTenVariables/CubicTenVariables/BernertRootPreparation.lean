import CubicTenVariables.UnconditionalDavenport
import Mathlib.Data.ZMod.Basic

/-!
# Scalar root inclusion and the integral normalization for Bernert

Every root of an integral polynomial is a root of every integer scalar
multiple modulo every prime power, including modulus one. The converse is
not claimed: multiplication by six can add roots at the primes two and three.

For an integral homogeneous cubic with no nonzero rational zero in at least
ten variables, the already proved Davenport theorem supplies the geometric
hypothesis for Bernert's explicit literature proposition. Its conclusion
is absolute convergence for the actual normalized polynomial `C 6 * F`.
No equality of the singular series of `F` and `C 6 * F` is used.
-/

noncomputable section
namespace CubicTenVariables.BernertRootPreparation
open MvPolynomial

/-- Literal root-filter inclusion under arbitrary integer scalar
multiplication. No invertibility of the scalar is required. -/
theorem root_filter_subset_C_mul {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (c : ℤ) (p s : ℕ) [Fact p.Prime] :
    (Finset.univ.filter fun x : Fin n → ZMod (p^s) =>
      eval₂ (Int.castRingHom (ZMod (p^s))) x F = 0) ⊆
    (Finset.univ.filter fun x : Fin n → ZMod (p^s) =>
      eval₂ (Int.castRingHom (ZMod (p^s))) x (C c * F) = 0) := by
  classical
  intro x hx
  have hxF := (Finset.mem_filter.mp hx).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, by simp [hxF]⟩

/-- Scalar multiplication can only increase the actual number of roots.
This includes the primes two and three and the level-zero residue space. -/
theorem card_roots_le_C_mul {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (c : ℤ) (p s : ℕ) [Fact p.Prime] :
    (Finset.univ.filter fun x : Fin n → ZMod (p^s) =>
      eval₂ (Int.castRingHom (ZMod (p^s))) x F = 0).card ≤
    (Finset.univ.filter fun x : Fin n → ZMod (p^s) =>
      eval₂ (Int.castRingHom (ZMod (p^s))) x (C c * F) = 0).card :=
  Finset.card_le_card (root_filter_subset_C_mul F c p s)

/-- Bernert's normalization prepared from the original integral cubic and
its rational anisotropy. Bernert is the only explicit literature premise;
Davenport's geometric condition is supplied by its existing proof. -/
theorem singularSeriesAbsolutelyConvergent_six_mul
    (bernert : Literature.Bernert2025Theorem1) {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hn : 10 ≤ n)
    (hA : HessianTheorem11.Anisotropic (map (Int.castRingHom ℚ) F)) :
    SingularSeriesAbsolutelyConvergent (C 6 * F) := by
  have hzero : ¬ HasIntegerZero F := by
    intro hz
    obtain ⟨x, hx, hFx⟩ := hasRationalZero_of_hasIntegerZero hz
    exact hx (hA x hFx)
  exact (Literature.bernert_six_mul bernert F hF hn
    (proved_davenportGood_of_no_integer_zero F hF hzero)).1

end CubicTenVariables.BernertRootPreparation
