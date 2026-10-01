import CubicTenVariables.ClippedPhaseRange

/-! The exact integral scales Q=P^(3/2) are cofinal, so the hypotheses of
the count-saving theorem hold at arbitrarily large integer physical scales.
The explicit subsequence is P=t², Q=t³. No literature premise is used. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CountingExactScales

/-- Explicit cofinality of the square/cube subsequence. -/
theorem exists_square_cube_above (P₀ : ℝ) :
    ∃ t : ℕ, 0 < t ∧ 4 ≤ t^2 ∧ P₀ ≤ ((t^2 : ℕ):ℝ) ∧
      1 ≤ t^3 ∧ ((t^3 : ℕ):ℝ)=((t^2 : ℕ):ℝ)^((3:ℝ)/2) := by
  obtain ⟨t,ht⟩ := exists_nat_gt (max 4 P₀)
  have ht4 : (4:ℝ) < t := (le_max_left _ _).trans_lt ht
  have htP : P₀ < (t:ℝ) := (le_max_right _ _).trans_lt ht
  have ht0 : 0 < t := by exact_mod_cast (by linarith : (0:ℝ)<t)
  have ht2 : (4:ℝ) ≤ (t:ℝ)^2 := by nlinarith only [ht4]
  have htP2 : P₀ ≤ (t:ℝ)^2 := by nlinarith only [ht4,htP]
  obtain ⟨_,hQ,hQP⟩ := ClippedPhaseRange.exact_scales t ht0
  refine ⟨t,ht0,by exact_mod_cast ht2,by exact_mod_cast htP2,hQ,hQP⟩

/-- Every real threshold is exceeded by positive integral counting scales
with P≥4 and the exact relation Q=P^(3/2). -/
theorem exists_exact_scales (P₀ : ℝ) :
    ∃ P Q : ℕ, 4 ≤ P ∧ P₀ ≤ (P:ℝ) ∧ 1 ≤ Q ∧
      (Q:ℝ)=(P:ℝ)^((3:ℝ)/2) := by
  obtain ⟨t,_,ht4,htP,htQ,hQP⟩ := exists_square_cube_above P₀
  exact ⟨t^2,t^3,ht4,htP,htQ,hQP⟩

end CubicTenVariables.CountingExactScales
