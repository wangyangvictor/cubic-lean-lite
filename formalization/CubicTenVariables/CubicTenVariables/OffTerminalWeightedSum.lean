import CubicTenVariables.OffTerminalGcdSum
import CubicTenVariables.PrimeConstantEpsilonBound
import CubicTenVariables.PolynomialHeightDivisorBound

/-! Uniform epsilon absorption for the off-terminal gcd modulus kernel,
with an actual polynomial-height bound on its positive exceptional integer. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.OffTerminalWeightedSum
open scoped BigOperators

/-- The fixed coefficient and height degree precede epsilon; the resulting
constant precedes both scales, the exceptional integer and every finite
family of positive modulus pairs. -/
theorem exists_bound (C : ℝ) (hC : 1 ≤ C) (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ D H : ℝ, 1 ≤ D → 1 ≤ H →
      ∀ Δ : ℕ, 1 ≤ Δ → (Δ : ℝ) ≤ C*H^d → ∀ Q : Finset (ℕ × ℕ),
        (∀ x ∈ Q, 1 ≤ x.1 ∧ 1 ≤ x.2 ∧
          (x.1 : ℝ)*(x.2 : ℝ)^2 ≤ 2*D) →
        (∑ x ∈ Q, C^(x.1.primeFactors.card+x.2.primeFactors.card)*
          (x.1 : ℝ)^((15 : ℝ)/2)*(x.2 : ℝ)^15*
          (Nat.gcd x.1 Δ : ℝ)*(Nat.gcd x.2 Δ : ℝ)^2) ≤
          M*(D*H)^ε*D^((17 : ℝ)/2) := by
  obtain ⟨A,hA,hprime⟩ := PrimeConstantEpsilonBound.exists_two_factor_bound C hC ε hε
  obtain ⟨R,hR,hsum⟩ := OffTerminalGcdSum.exists_bound
  obtain ⟨B,hB,hdiv⟩ := PolynomialHeightDivisorBound.exists_product_bound C hC d ε hε
  let M : ℝ := A*(2 : ℝ)^ε*R*B
  refine ⟨max 1 M,le_max_left _ _,?_⟩
  intro D H hD hH Δ hΔ hΔH Q hQ
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  let g : ℕ × ℕ → ℝ := fun x =>
    (x.1 : ℝ)^((15 : ℝ)/2)*(x.2 : ℝ)^15*
      (Nat.gcd x.1 Δ : ℝ)*(Nat.gcd x.2 Δ : ℝ)^2
  have hg (x : ℕ × ℕ) : 0 ≤ g x := by dsimp [g]; positivity
  have hweight (x : ℕ × ℕ) (hx : x ∈ Q) :
      C^(x.1.primeFactors.card+x.2.primeFactors.card) ≤ A*(2*D)^ε := by
    have hb1 : (1 : ℝ) ≤ x.2 := by exact_mod_cast (hQ x hx).2.1
    have hab : ((x.1*x.2 : ℕ) : ℝ) ≤ 2*D := by
      rw [Nat.cast_mul]
      have hbb : (x.2 : ℝ) ≤ (x.2 : ℝ)^2 := by nlinarith
      exact (mul_le_mul_of_nonneg_left hbb (Nat.cast_nonneg x.1)).trans (hQ x hx).2.2
    exact (hprime x.1 x.2 (hQ x hx).1 (hQ x hx).2.1).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hab hε.le) (by linarith))
  have hdivΔ : (Δ.divisors.card : ℝ)^2 ≤ B*H^ε := by
    simpa only [pow_two] using hdiv H hH Δ Δ hΔ hΔ hΔH hΔH
  have he : (A*(2*D)^ε)*(R*D^((17 : ℝ)/2)*(B*H^ε)) =
      M*(D*H)^ε*D^((17 : ℝ)/2) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hD0.le,
      Real.mul_rpow hD0.le hH0.le]
    dsimp [M]
    ring
  calc
    _ = ∑ x ∈ Q, C^(x.1.primeFactors.card+x.2.primeFactors.card)*g x := by
      apply Finset.sum_congr rfl
      intro x _
      dsimp [g]
      ring
    _ ≤ ∑ x ∈ Q, (A*(2*D)^ε)*g x :=
      Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_right (hweight x hx) (hg x))
    _ = (A*(2*D)^ε)*∑ x ∈ Q, g x := (Finset.mul_sum ..).symm
    _ ≤ (A*(2*D)^ε)*(R*D^((17 : ℝ)/2)*(Δ.divisors.card : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (hsum D hD Δ hΔ Q hQ) (by positivity)
    _ ≤ (A*(2*D)^ε)*(R*D^((17 : ℝ)/2)*(B*H^ε)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdivΔ (by positivity)) (by positivity)
    _ = M*(D*H)^ε*D^((17 : ℝ)/2) := he
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 M) (by positivity)) (by positivity)

end CubicTenVariables.OffTerminalWeightedSum
