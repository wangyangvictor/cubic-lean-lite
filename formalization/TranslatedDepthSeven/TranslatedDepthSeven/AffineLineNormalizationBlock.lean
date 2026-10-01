import TranslatedDepthSeven.ColumnwiseDeterminantBound
import TranslatedDepthSeven.LinearNormalizationMonomialIndependence
import TranslatedDepthSeven.WeightedDeterminantDivisibility
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The complete affine-curve normalization block

For a projective curve the normalization base has two homogeneous
coordinates.  The degree-`k` monomials are `X₀^(k-j) X₁^j`, and their
affine weights sum to `k(k+1)/2`.  This file proves the exact homogeneous,
independence, archimedean determinant, and local divisibility statements for
that block.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial
open scoped BigOperators

universe u v w x

/-- Exponent vector of `X₀^(k-j) X₁^j`. -/
def affineLineMonomialExponent (k : ℕ) (j : Fin (k + 1)) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![k - j.1, j.1]

/-- The two exponents add to `k`. -/
theorem affineLineMonomialExponent_degree (k : ℕ) (j : Fin (k + 1)) :
    Finsupp.degree (affineLineMonomialExponent k j) = k := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  have hzero : (affineLineMonomialExponent k j) 0 = k - j.1 := by
    simp [affineLineMonomialExponent]
  have hone : (affineLineMonomialExponent k j) 1 = j.1 := by
    simp [affineLineMonomialExponent]
  rw [hzero, hone]
  omega

/-- The degree-`k` homogeneous monomial indexed by its affine weight `j`. -/
def affineLineHomogeneousMonomial
    (R : Type u) [CommSemiring R] (k : ℕ) (j : Fin (k + 1)) :
  MvPolynomial (Fin 2) R :=
  MvPolynomial.monomial (affineLineMonomialExponent k j) 1

/-- The displayed line monomial has degree `k`. -/
theorem affineLineHomogeneousMonomial_isHomogeneous
    (R : Type u) [CommSemiring R] (k : ℕ) (j : Fin (k + 1)) :
    (affineLineHomogeneousMonomial R k j).IsHomogeneous k := by
  intro d hd
  rw [affineLineHomogeneousMonomial, MvPolynomial.coeff_monomial] at hd
  split_ifs at hd with h
  · subst d
    simpa only [Finsupp.degree_eq_weight_one] using
      affineLineMonomialExponent_degree k j
  · simp at hd

/-- Twice the total affine weight in the degree-`k` line block. -/
theorem two_mul_sum_affineLineWeight (k : ℕ) :
    2 * ∑ j : Fin (k + 1), j.1 = k * (k + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ j) (k + 1)]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      ring

/-- Distinct indices give distinct exponent vectors. -/
theorem affineLineMonomialExponent_injective (k : ℕ) :
    Function.Injective (affineLineMonomialExponent k) := by
  intro i j h
  apply Fin.ext
  have := DFunLike.congr_fun h (1 : Fin 2)
  simpa using this

/-- The complete degree-`k` line monomial family is independent. -/
theorem linearIndependent_affineLineHomogeneousMonomial
    (K : Type u) [Field K] (k : ℕ) :
    LinearIndependent K (affineLineHomogeneousMonomial K k) := by
  let e : Fin (k + 1) → (Fin 2 →₀ ℕ) := fun j ↦
    affineLineMonomialExponent k j
  have he : Function.Injective e := affineLineMonomialExponent_injective k
  have hmon : LinearIndependent K
      (fun d : Fin 2 →₀ ℕ ↦ MvPolynomial.monomial d (1 : K)) := by
    simpa only [MvPolynomial.coe_basisMonomials] using
      (MvPolynomial.basisMonomials (Fin 2) K).linearIndependent
  simpa only [affineLineHomogeneousMonomial, e] using hmon.comp e he

/-- A rank-`e` normalization basis times the complete line monomial block is
independent over the ground field. -/
theorem linearIndependent_normalizationCurveBlock
    (K : Type u) (A : Type w)
    [Field K] [CommRing A]
    [Algebra K A] [Algebra (MvPolynomial (Fin 2) K) A]
    [IsScalarTower K (MvPolynomial (Fin 2) K) A]
    (I : Type x) [Fintype I]
    (g : I → A)
    (hg : LinearIndependent (MvPolynomial (Fin 2) K) g)
    (k : ℕ) :
    LinearIndependent K
      (fun p : I × Fin (k + 1) ↦
        algebraMap (MvPolynomial (Fin 2) K) A
          (affineLineHomogeneousMonomial K k p.2) * g p.1) := by
  exact linearIndependent_algebraMap_mul
    K (MvPolynomial (Fin 2) K) A I (Fin (k + 1))
      (affineLineHomogeneousMonomial K k) g
      (linearIndependent_affineLineHomogeneousMonomial K k) hg

/-- Exact evaluation after substituting two arbitrary linear forms. -/
theorem eval_aeval_affineLineHomogeneousMonomial
    {σ : Type*} (L : Fin 2 → MvPolynomial σ ℤ)
    (y : σ → ℤ) (k : ℕ) (j : Fin (k + 1)) :
    MvPolynomial.eval y
        (MvPolynomial.aeval L (affineLineHomogeneousMonomial ℤ k j)) =
      MvPolynomial.eval y (L 0) ^ (k - j.1) *
        MvPolynomial.eval y (L 1) ^ j.1 := by
  rw [affineLineHomogeneousMonomial, MvPolynomial.aeval_monomial]
  simp only [map_one, one_mul]
  rw [Finsupp.prod_fintype]
  · rw [Fin.prod_univ_two]
    have hzero : (affineLineMonomialExponent k j) 0 = k - j.1 := by
      simp [affineLineMonomialExponent]
    have hone : (affineLineMonomialExponent k j) 1 = j.1 := by
      simp [affineLineMonomialExponent]
    rw [hzero, hone]
    simp
  · intro i
    simp

/-- Exact pointwise height bound on the affine chart. -/
theorem eval_aeval_affineLineHomogeneousMonomial_natAbs_le
    {σ : Type*} (L : Fin 2 → MvPolynomial σ ℤ)
    (y : σ → ℤ) (R k : ℕ) (j : Fin (k + 1))
    (hzero : MvPolynomial.eval y (L 0) = 1)
    (hone : (MvPolynomial.eval y (L 1)).natAbs ≤ R) :
    (MvPolynomial.eval y
      (MvPolynomial.aeval L
        (affineLineHomogeneousMonomial ℤ k j))).natAbs ≤ R ^ j.1 := by
  rw [eval_aeval_affineLineHomogeneousMonomial, hzero, one_pow, one_mul,
    Int.natAbs_pow]
  exact Nat.pow_le_pow_left hone j.1

/-- Exact determinant-height bound for the complete curve monomial block. -/
theorem det_affineLineMonomialEvaluation_natAbs_le
    {σ : Type*} (L : Fin 2 → MvPolynomial σ ℤ)
    (R k : ℕ) (y : Fin (k + 1) → σ → ℤ)
    (hzero : ∀ v, MvPolynomial.eval (y v) (L 0) = 1)
    (hone : ∀ v, (MvPolynomial.eval (y v) (L 1)).natAbs ≤ R) :
    let A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
      Matrix.of (fun v j ↦ MvPolynomial.eval (y v)
        (MvPolynomial.aeval L
          (affineLineHomogeneousMonomial ℤ k j)))
    A.det.natAbs ≤ (k + 1).factorial * R ^ (∑ j : Fin (k + 1), j.1) := by
  dsimp only
  have hdet := det_natAbs_le_factorial_mul_prod_column_bounds
    (Matrix.of (fun v j ↦ MvPolynomial.eval (y v)
      (MvPolynomial.aeval L
        (affineLineHomogeneousMonomial ℤ k j))))
    (fun j ↦ R ^ j.1)
    (fun v j ↦ eval_aeval_affineLineHomogeneousMonomial_natAbs_le
      L (y v) R k j (hzero v) (hone v))
  rw [Finset.prod_pow_eq_pow_sum] at hdet
  simpa using hdet

/-- Exact pointwise local divisibility by the affine weight. -/
theorem pow_dvd_eval_aeval_affineLineHomogeneousMonomial
    {σ : Type*} (L : Fin 2 → MvPolynomial σ ℤ)
    (y : σ → ℤ) (p : ℤ) (k : ℕ) (j : Fin (k + 1))
    (hone : p ∣ MvPolynomial.eval y (L 1)) :
    p ^ j.1 ∣ MvPolynomial.eval y
      (MvPolynomial.aeval L (affineLineHomogeneousMonomial ℤ k j)) := by
  rw [eval_aeval_affineLineHomogeneousMonomial]
  exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hone j.1) _

/-- Exact local determinant factor for the complete curve monomial block. -/
theorem pow_sum_affineLineWeight_dvd_det
    {σ : Type*} (L : Fin 2 → MvPolynomial σ ℤ)
    (k : ℕ) (y : Fin (k + 1) → σ → ℤ) (p : ℤ)
    (hone : ∀ v, p ∣ MvPolynomial.eval (y v) (L 1)) :
    p ^ (∑ j : Fin (k + 1), j.1) ∣
      (Matrix.of (fun v j ↦ MvPolynomial.eval (y v)
        (MvPolynomial.aeval L
          (affineLineHomogeneousMonomial ℤ k j)))).det := by
  exact pow_sum_dvd_det_of_columns_pow_dvd
    (Matrix.of (fun v j ↦ MvPolynomial.eval (y v)
      (MvPolynomial.aeval L
        (affineLineHomogeneousMonomial ℤ k j))))
    p (fun j ↦ j.1)
    (fun v j ↦ pow_dvd_eval_aeval_affineLineHomogeneousMonomial
      L (y v) p k j (hone v))

end

end TranslatedDepthSeven
