import CubicTenVariables.SquarefullWeightedLifting
import CubicTenVariables.SquarefullRootMassLifting
import CubicTenVariables.GcdWeightedHessianCRT
import CubicTenVariables.SquarefullExponentAssembly

/-! The selected ten-variable j=1 cube-sum estimate. -/

noncomputable section
namespace CubicTenVariables.SquarefullCubeSumOne
open MvPolynomial HessianTheorem11 SquarefullWeightedSums
open scoped BigOperators

/-- One constant precedes both moduli, the finite frequency set and its weights.
The c/d root count is proved without an unproved literature input. -/
theorem exists_weightedL1_bound 
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (c d : ℕ) [NeZero c] [NeZero d],
      Squarefree d → (hdc : d ∣ c) →
      ∀ (V : Finset (Fin 10 → ℤ)) (w : (Fin 10 → ℤ) → ℝ),
      (∀ v ∈ V, 0 ≤ w v) →
      weightedL1 F c d V w ≤
        C*(c : ℝ)^(21+ε)*(d : ℝ)^((15:ℝ)/2)*WeightedResidueMaximum.maximum c V w := by
  obtain ⟨C,hC,hroot⟩ := SquarefullRootMassLifting.exists_uniform_bound  F hF hA ε hε
  obtain ⟨D,hD,hgcd⟩ := GcdWeightedHessianCRT.exists_uniform_squarefree_bound F hF hA ε hε
  refine ⟨C*D, by nlinarith [mul_le_mul_of_nonneg_left hD (zero_le_one.trans hC)], ?_⟩
  intro c d _ _ hd hdc V w hw
  have hE := WeightedResidueMaximum.maximum_nonneg c V w hw
  have hmass : rootMass F c d hdc ≤
      C*((c/d : ℕ) : ℝ)^(9+ε)*(D*(d : ℝ)^((21:ℝ)/2+ε)) :=
    (hroot c d hd hdc).trans (mul_le_mul_of_nonneg_left (hgcd d hd)
      (mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
  calc
    _ ≤ (c : ℝ)^12*(d : ℝ)^6*WeightedResidueMaximum.maximum c V w*
        rootMass F c d hdc :=
      SquarefullWeightedLifting.weightedL1_le_residue_maximum F c d hdc V w hw
    _ ≤ (c : ℝ)^12*(d : ℝ)^6*WeightedResidueMaximum.maximum c V w*
        (C*((c/d : ℕ) : ℝ)^(9+ε)*(D*(d : ℝ)^((21:ℝ)/2+ε))) :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg (by positivity) hE)
    _ = _ := SquarefullExponentAssembly.exact_weighted_exponents c d
      (NeZero.pos c) (NeZero.pos d) hdc ε C D (WeightedResidueMaximum.maximum c V w)

/-- The corresponding actual weighted complete-sum estimate. All squarefree d
and positive c divisible by d are included, even at primes two and three. -/
theorem exists_complete_sum_bound 
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (c d : ℕ) [NeZero c] [NeZero d],
      Squarefree d → d ∣ c →
      ∀ (V : Finset (Fin 10 → ℤ)) (w : (Fin 10 → ℤ) → ℝ),
      (∀ v ∈ V, 0 ≤ w v) →
      (∑ v ∈ V, w v * ‖completeCubicSum F (c^2*d) v‖) ≤
        C*(c : ℝ)^(21+ε)*(d : ℝ)^((15:ℝ)/2)*WeightedResidueMaximum.maximum c V w := by
  obtain ⟨C,hC,hbound⟩ := exists_weightedL1_bound  F hF hA ε hε
  refine ⟨C,hC,?_⟩
  intro c d _ _ hd hdc V w hw
  exact (SquarefullWeightedLifting.weighted_norm_sum_le_weightedL1 F hF c d hdc V w hw).trans
    (hbound c d hd hdc V w hw)

end CubicTenVariables.SquarefullCubeSumOne
