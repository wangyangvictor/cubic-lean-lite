import CubicTenVariables.SquarefullCubeSumOne
import CubicTenVariables.ResidueBoxCount

/-! The elementary large-box branch of the selected squarefull L1 bound.
The small-box Poisson step is not asserted here. -/

noncomputable section
namespace CubicTenVariables.SquarefullLargeBox
open MvPolynomial HessianTheorem11 SquarefullWeightedSums
open scoped BigOperators

/-- Numerical large-box comparison, retaining the real exponents. -/
theorem large_box_factor_le (c d R ε : ℝ)
    (hc : 1 ≤ c) (hd : 1 ≤ d) (hdc : d ≤ c) (hε : 0 ≤ ε) :
    c^(21+ε)*d^((15:ℝ)/2)*(7*R/c)^10 ≤
      (7:ℝ)^10*(c^2*d)^(6+ε)*d^((1:ℝ)/2)*R^10 := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hcd0 : 0 < c^2*d := by positivity
  have hbase : c ≤ c^2*d := by
    calc
      _ ≤ c*c := le_mul_of_one_le_right hc0.le hc
      _ ≤ c*c*d := le_mul_of_one_le_right (by positivity) hd
      _ = _ := by ring
  have hpow : c^ε ≤ (c^2*d)^ε := Real.rpow_le_rpow hc0.le hbase hε
  have hpoly : c^11*d^7 ≤ c^12*d^6 := by
    convert mul_le_mul_of_nonneg_left hdc (show 0 ≤ c^11*d^6 by positivity) using 1 <;> ring
  have hprod : c^11*d^7*c^ε ≤ c^12*d^6*(c^2*d)^ε :=
    mul_le_mul hpoly hpow (Real.rpow_nonneg hc0.le _) (by positivity)
  have hleft : c^(21+ε)*d^((15:ℝ)/2)*(7*R/c)^10 =
      ((7:ℝ)^10*d^((1:ℝ)/2)*R^10)*(c^11*d^7*c^ε) := by
    rw [show (15:ℝ)/2 = 7 + 1/2 by norm_num,
      Real.rpow_add hc0, Real.rpow_add hd0]
    norm_num
    rw [div_pow, mul_pow]
    field_simp
    ring
  have hright : (7:ℝ)^10*(c^2*d)^(6+ε)*d^((1:ℝ)/2)*R^10 =
      ((7:ℝ)^10*d^((1:ℝ)/2)*R^10)*(c^12*d^6*(c^2*d)^ε) := by
    rw [Real.rpow_add hcd0]
    norm_num
    ring
  rw [hleft, hright]
  exact mul_le_mul_of_nonneg_left hprod (by positivity)

/-- Uniform translated real boxes of radius at least c. This is only the
large-box branch, with no unproved literature argument. -/
theorem exists_weightedL1_bound 
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (c d : ℕ) [NeZero c] [NeZero d],
      Squarefree d → d ∣ c →
      ∀ (V : Finset (Fin 10 → ℤ)) (u : Fin 10 → ℝ) (R : ℝ),
      (c : ℝ) ≤ R → (∀ v ∈ V, ∀ i, |(v i : ℝ)-u i| ≤ R) →
      weightedL1 F c d V (fun _ => 1) ≤
        K*((c^2*d : ℕ) : ℝ)^(6+ε)*(d : ℝ)^((1:ℝ)/2)*R^10 := by
  obtain ⟨C,hC,hbound⟩ := SquarefullCubeSumOne.exists_weightedL1_bound  F hF hA ε hε
  refine ⟨(7:ℝ)^10*C, ?_, ?_⟩
  · nlinarith
  intro c d _ _ hd hdc V u R hcR hbox
  have hc1 : (1:ℝ) ≤ c := by exact_mod_cast NeZero.pos c
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast NeZero.pos d
  have hdcle : (d:ℝ) ≤ c := by exact_mod_cast Nat.le_of_dvd (NeZero.pos c) hdc
  have hE := ResidueBoxCount.maximum_one_le_of_modulus_le_radius c V u R hcR hbox
  have hnum := large_box_factor_le (c:ℝ) d R ε hc1 hd1 hdcle hε.le
  have hraw := hbound c d hd hdc V (fun _ => 1) (by intros; norm_num)
  calc
    _ ≤ C*(c:ℝ)^(21+ε)*(d:ℝ)^((15:ℝ)/2)*
        WeightedResidueMaximum.maximum c V (fun _ => 1) := hraw
    _ ≤ C*(c:ℝ)^(21+ε)*(d:ℝ)^((15:ℝ)/2)*(7*R/(c:ℝ))^10 :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ = C*((c:ℝ)^(21+ε)*(d:ℝ)^((15:ℝ)/2)*(7*R/(c:ℝ))^10) := by ring
    _ ≤ C*((7:ℝ)^10*((c:ℝ)^2*d)^(6+ε)*(d:ℝ)^((1:ℝ)/2)*R^10) :=
      mul_le_mul_of_nonneg_left hnum (zero_le_one.trans hC)
    _ = _ := by push_cast; ring

end CubicTenVariables.SquarefullLargeBox
