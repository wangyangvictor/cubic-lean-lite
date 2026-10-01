import CubicTenVariables.Literature.Bernert

/-! The Hessian normalization for an arbitrary integral symmetric cubic
tensor, including repeated indices. The Hessian is six times the tensor's
matrix, so their ranks over the rationals agree. -/

noncomputable section
namespace CubicTenVariables
open MvPolynomial HessianTheorem11

namespace SymmetricIntegerCubicTensor
variable {n : ℕ}

theorem polynomial_pderiv (T : SymmetricIntegerCubicTensor n) (a : Fin n) :
    pderiv a T.polynomial =
      3 * ∑ j, ∑ k, C (T.coeff a j k) * X j * X k := by
  classical
  have h₁ (i j : Fin n) : (T.coeff i j a : MvPolynomial (Fin n) ℤ) * X i * X j =
      (T.coeff a i j : MvPolynomial (Fin n) ℤ) * X i * X j := by rw [T.cyclic a i j]
  have h₂ (i j : Fin n) : X j * ((T.coeff i a j : MvPolynomial (Fin n) ℤ) * X i) =
      (T.coeff a i j : MvPolynomial (Fin n) ℤ) * X i * X j := by
    rw [T.swap_first i a j]; ring
  have h₃ (i j : Fin n) : X j * (X i * (T.coeff a i j : MvPolynomial (Fin n) ℤ)) =
      (T.coeff a i j : MvPolynomial (Fin n) ℤ) * X i * X j := by ring
  simp [polynomial, Finset.sum_add_distrib, Pi.single_apply,
    mul_add, mul_ite]
  simp_rw [h₁, h₂, h₃]
  ring

theorem polynomial_pderiv_pderiv (T : SymmetricIntegerCubicTensor n) (a b : Fin n) :
    pderiv b (pderiv a T.polynomial) =
      6 * ∑ k, C (T.coeff a b k) * X k := by
  classical
  have hb3 : pderiv b (3 : MvPolynomial (Fin n) ℤ) = 0 :=
    (pderiv b).map_natCast 3
  have hc (i : Fin n) : T.coeff a i b = T.coeff a b i := T.swap_last a i b
  have hm (i : Fin n) : X i * (T.coeff a b i : MvPolynomial (Fin n) ℤ) =
      (T.coeff a b i : MvPolynomial (Fin n) ℤ) * X i := mul_comm _ _
  rw [polynomial_pderiv]
  simp [Pi.single_apply, mul_ite, Finset.sum_add_distrib, mul_add, hb3]
  simp_rw [hc, hm]
  ring

/-- In the ordered symmetric tensor convention, every Hessian entry is
exactly six times the corresponding entry of the tensor matrix. -/
theorem polynomial_hessian (T : SymmetricIntegerCubicTensor n) (x : Fin n → ℤ) :
    hessian T.polynomial x = (6 : ℤ) • T.matrix x := by
  ext a b
  change eval x (pderiv b (pderiv a T.polynomial)) =
    6 * ∑ i, T.coeff i a b * x i
  rw [polynomial_pderiv_pderiv]
  simp only [map_mul, map_ofNat, map_sum, eval_C, eval_X]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [T.cyclic i a b]

/-- The same identity after the literal coefficient extension to rationals. -/
theorem polynomial_hessian_rat (T : SymmetricIntegerCubicTensor n) (x : Fin n → ℤ) :
    hessian (map (Int.castRingHom ℚ) T.polynomial) (fun i => (x i : ℚ)) =
      (6 : ℚ) • (fun a b => (T.matrix x a b : ℚ)) := by
  ext a b
  change eval (fun i => (x i : ℚ))
      (pderiv b (pderiv a (map (Int.castRingHom ℚ) T.polynomial))) =
    6 * (T.matrix x a b : ℚ)
  rw [pderiv_map, pderiv_map]
  have hmap : ((eval x (pderiv b (pderiv a T.polynomial)) : ℤ) : ℚ) =
      eval (fun i => (x i : ℚ))
        (map (Int.castRingHom ℚ) (pderiv b (pderiv a T.polynomial))) :=
    MvPolynomial.map_eval (Int.castRingHom ℚ) x _
  rw [← hmap]
  change ((hessian T.polynomial x a b : ℤ) : ℚ) = _
  rw [polynomial_hessian]
  simp

end SymmetricIntegerCubicTensor

/-- The actual rational rank in Bernert's tensor convention is the actual
full Hessian rank of its cubic, for every integer vector. -/
theorem tensorMatrixRank_eq_integerHessianRank {n : ℕ}
    (T : SymmetricIntegerCubicTensor n) (x : Fin n → ℤ) :
    Literature.tensorMatrixRank T x = integerHessianRank T.polynomial x := by
  classical
  unfold Literature.tensorMatrixRank integerHessianRank
  rw [T.polynomial_hessian_rat]
  symm
  rw [Matrix.smul_eq_diagonal_mul]
  apply Matrix.rank_mul_eq_right_of_isUnit_det
  rw [Matrix.det_diagonal]
  exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun _ _ => by norm_num)

end CubicTenVariables
