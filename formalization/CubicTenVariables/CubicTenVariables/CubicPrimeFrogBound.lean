import CubicTenVariables.CubicPrimeFrogOneBound

/-!
# The complete source-shaped ten-variable prime frog bound

One constant covers j=0,1,2, all primes and all four choices of the literal
gcd weights. The three cases are proved dependencies, not input hypotheses.
-/

noncomputable section
namespace CubicTenVariables.CubicPrimeFrogBound
open MvPolynomial HessianTheorem11 PrimeFrogZeroMass PrimeFrogOneMass
  SquarefreeResidueFactors HessianKernelCRT
open scoped BigOperators

/-- The entire n=10 specialization of the source's weighted prime Smith
mass lemma, with real exponents and all omission variants. -/
theorem exists_uniform_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩
      ∀ (j : ℕ), j ∈ ({0,1,2} : Finset ℕ) →
      ∀ (includeGradient includeCoordinates : Bool),
        (∑ x ∈ Finset.univ.filter (fun x : Fin 10 → ZMod p =>
          eval₂ (Int.castRingHom (ZMod p)) x F = 0),
          (hessianKernelCard F p x : ℝ)^((j : ℝ)/2) *
          (((if includeGradient then
            vectorGcd p (fun i => eval (integerLift p x) (pderiv i F)) else 1) *
          (if includeCoordinates then vectorGcd p (integerLift p x) else 1) : ℕ) : ℝ)) ≤
            A*(p : ℝ)^((9 : ℝ)+3*(j : ℝ)/2) := by
  classical
  obtain ⟨C₀,_hC₀,hzero⟩ := CubicPrimeFrogZeroBound.exists_uniform_bound_with_optional_gcds F hF hA
  obtain ⟨A₁,hA₁,hone⟩ := CubicPrimeFrogOneBound.exists_uniform_bound F hF hA
  obtain ⟨C₂,_hC₂,htwo⟩ := CubicPrimeFrogTwoBound.exists_uniform_bound_with_optional_gcds F hF hA
  have hC₀' : (0 : ℝ) ≤ C₀ := Nat.cast_nonneg _
  have hC₂' : (0 : ℝ) ≤ C₂ := Nat.cast_nonneg _
  let A : ℝ := C₀+A₁+C₂
  have hA₀ : (C₀ : ℝ) ≤ A := by dsimp [A]; linarith
  have hA₁' : A₁ ≤ A := by dsimp [A]; linarith
  have hA₂ : (C₂ : ℝ) ≤ A := by dsimp [A]; linarith
  refine ⟨A, by dsimp [A]; linarith, ?_⟩
  intro p hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro j hj includeGradient includeCoordinates
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by simpa using hj
  rcases hj' with rfl | rfl | rfl
  · have hbound :
        (∑ x ∈ Finset.univ.filter (fun x : Fin 10 → ZMod p =>
          eval₂ (Int.castRingHom (ZMod p)) x F = 0),
          (optionalRootWeight F p x includeGradient includeCoordinates : ℝ)) ≤
          (C₀ : ℝ)*(p : ℝ)^9 := by
      exact_mod_cast hzero p hp includeGradient includeCoordinates
    have hh := hbound.trans (mul_le_mul_of_nonneg_right hA₀ (by positivity : (0 : ℝ) ≤ (p : ℝ)^9))
    simpa only [Nat.cast_zero, zero_div, Real.rpow_zero, one_mul, mul_zero,
      add_zero, Real.rpow_natCast, Real.rpow_ofNat, optionalRootWeight] using hh
  · have hbound := hone p hp includeGradient includeCoordinates
    have hh := hbound.trans (mul_le_mul_of_nonneg_right hA₁'
      (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    norm_num only [Nat.cast_one] at ⊢
    convert hh using 1
  · have hbound :
        (∑ x ∈ Finset.univ.filter (fun x : Fin 10 → ZMod p =>
          eval₂ (Int.castRingHom (ZMod p)) x F = 0),
          (optionalRootWeight F p x includeGradient includeCoordinates : ℝ) *
            (hessianKernelCard F p x : ℝ)) ≤ (C₂ : ℝ)*(p : ℝ)^12 := by
      exact_mod_cast htwo p hp includeGradient includeCoordinates
    have hh := hbound.trans (mul_le_mul_of_nonneg_right hA₂ (by positivity : (0 : ℝ) ≤ (p : ℝ)^12))
    norm_num only [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      div_self, Real.rpow_one] at ⊢
    norm_num [optionalRootWeight, mul_comm] at hh ⊢
    exact hh

end CubicTenVariables.CubicPrimeFrogBound
