import CubicTenVariables.HessianResidueKernel
import CubicTenVariables.HessianSmithProfile
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
The initial cumulative Smith-profile entry is exactly the field rank of
the actual reduced integer Hessian. The integral diagonalization is fixed
before the prime and the positive truncation level. No homogeneity, rank
bound, geometric estimate, or finite-field counting premise is used.
-/

noncomputable section
namespace CubicTenVariables.HessianInitialRank

open MvPolynomial HessianTheorem11 PrimePowerKernelProfile SmithProfileMultiplicity
open MatrixSmithKernel
open scoped BigOperators Matrix

/-- At every positive truncation level, valuation zero means precisely a
nonzero residue. Zero integral entries are explicitly excluded on both sides. -/
theorem truncatedValuation_eq_zero_iff_intCast_ne_zero
    (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : 0 < a) (d : ℤ) :
    truncatedValuation p a d = 0 ↔ (d : ZMod p) ≠ 0 := by
  by_cases hd : d = 0
  · simp [hd, truncatedValuation, Nat.ne_of_gt ha]
  · have hc : (d : ZMod p) = 0 ↔ 1 ≤ d.natAbs.factorization p := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd,
        hp.dvd_iff_one_le_factorization (Int.natAbs_ne_zero.mpr hd)]
    rw [truncatedValuation, if_neg hd, ne_eq, hc]
    omega

/-- The actual field rank of an integer matrix reduction is the initial
cumulative profile of any displayed integral unimodular diagonalization. -/
theorem rank_intReduction_eq_initialProfile {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℤ)
    (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (d : Fin n → ℤ)
    (hD : (U : Matrix (Fin n) (Fin n) ℤ) * B * V = Matrix.diagonal d)
    (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : 0 < a) :
    (B.map (Int.castRingHom (ZMod p))).rank =
      profile (fun ν => truncatedValuation p a (d ν)) 0 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hmod : (reduceUnit p U : Matrix (Fin n) (Fin n) (ZMod p)) *
      B.map (Int.castRingHom (ZMod p)) * reduceUnit p V =
      Matrix.diagonal (fun i => (d i : ZMod p)) := by
    simpa only [reduceUnit_val, Matrix.map_mul,
      Matrix.diagonal_map (map_zero (Int.castRingHom (ZMod p)))] using
      congrArg (fun M : Matrix (Fin n) (Fin n) ℤ =>
        M.map (Int.castRingHom (ZMod p))) hD
  have h := congrArg Matrix.rank hmod
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units (reduceUnit p V)),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnits_det_units (reduceUnit p U)),
    Matrix.rank_diagonal] at h
  simpa only [profile, Nat.le_zero, truncatedValuation_eq_zero_iff_intCast_ne_zero p hp a ha,
    Fintype.card_subtype] using h

/-- In particular the profile is the rank of the Hessian formed after
actual coefficient reduction and evaluation at the reduced integer point. -/
theorem rank_hessianReduction_eq_initialProfile {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (y : Fin n → ℤ)
    (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (d : Fin n → ℤ)
    (hD : (U : Matrix (Fin n) (Fin n) ℤ) * hessian F y * V = Matrix.diagonal d)
    (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : 0 < a) :
    (hessian (F.map (Int.castRingHom (ZMod p))) (fun i => (y i : ZMod p))).rank =
      profile (fun ν => truncatedValuation p a (d ν)) 0 := by
  rw [← HessianResidueKernel.hessian_intCast F p y]
  exact rank_intReduction_eq_initialProfile (hessian F y) U V d hD p hp a ha

/-- One actual integral diagonalization supplies the rank identity for
every prime and positive truncation level; no normal-form input remains. -/
theorem exists_diagonalization_and_initialRank {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (y : Fin n → ℤ) :
    ∃ (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (d : Fin n → ℤ),
      (U : Matrix (Fin n) (Fin n) ℤ) * hessian F y * V = Matrix.diagonal d ∧
      ∀ (p : ℕ), p.Prime → ∀ (a : ℕ), 0 < a →
        (hessian (F.map (Int.castRingHom (ZMod p)))
          (fun i => (y i : ZMod p))).rank =
            profile (fun ν => truncatedValuation p a (d ν)) 0 := by
  obtain ⟨U,V,d,hD⟩ := MatrixSmithExistence.exists_integer_diagonalization (hessian F y)
  exact ⟨U,V,d,hD,rank_hessianReduction_eq_initialProfile F y U V d hD⟩

/-- The actual first entry of the finite ten-variable profile is precisely
the reduced Hessian rank used by the finite-field base strata. -/
theorem ten_entry_zero_eq_hessian_rank
    (F : MvPolynomial (Fin 10) ℤ) (y : Fin 10 → ℤ)
    (U V : (Matrix (Fin 10) (Fin 10) ℤ)ˣ) (d : Fin 10 → ℤ)
    (hD : (U : Matrix (Fin 10) (Fin 10) ℤ) * hessian F y * V = Matrix.diagonal d)
    (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : 0 < a) :
    SmithProfileNumerics.entry (HessianSmithProfile.ofDiagonal p a d) 0 =
      (hessian (F.map (Int.castRingHom (ZMod p))) (fun i => (y i : ZMod p))).rank := by
  rw [HessianSmithProfile.entry_ofDiagonal p a d 0 ha]
  exact (rank_hessianReduction_eq_initialProfile F y U V d hD p hp a ha).symm

end CubicTenVariables.HessianInitialRank
