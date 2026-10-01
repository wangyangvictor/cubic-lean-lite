import CubicTenVariables.GcdProductWindowSum

/-! The off-terminal modulus kernel is the proved gcd-product kernel
multiplied by `(a*b²)²`. The actual modulus cutoff pays for this factor. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.OffTerminalGcdSum
open scoped BigOperators

/-- One constant precedes the cutoff, the positive exceptional integer,
and the arbitrary finite family of positive modulus pairs. -/
theorem exists_bound :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ D : ℝ, 1 ≤ D → ∀ Δ : ℕ, 1 ≤ Δ →
      ∀ Q : Finset (ℕ × ℕ),
        (∀ x ∈ Q, 1 ≤ x.1 ∧ 1 ≤ x.2 ∧
          (x.1 : ℝ)*(x.2 : ℝ)^2 ≤ 2*D) →
        (∑ x ∈ Q, (x.1 : ℝ)^((15 : ℝ)/2)*(x.2 : ℝ)^15*
          (Nat.gcd x.1 Δ : ℝ)*(Nat.gcd x.2 Δ : ℝ)^2) ≤
          M*D^((17 : ℝ)/2)*(Δ.divisors.card : ℝ)^2 := by
  obtain ⟨C,hC,hbound⟩ := GcdProductWindowSum.exists_bound
  refine ⟨4*C,by linarith,?_⟩
  intro D hD Δ hΔ Q hQ
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  let k : ℕ × ℕ → ℝ := fun x =>
    ((x.1 : ℝ)^((11 : ℝ)/2)*(Nat.gcd x.1 Δ : ℝ))*
      ((x.2 : ℝ)^11*(Nat.gcd x.2 Δ : ℝ)^2)
  have hk (x : ℕ × ℕ) : 0 ≤ k x := by dsimp [k]; positivity
  have hterm (x : ℕ × ℕ) (hx : x ∈ Q) :
      (x.1 : ℝ)^((15 : ℝ)/2)*(x.2 : ℝ)^15*
        (Nat.gcd x.1 Δ : ℝ)*(Nat.gcd x.2 Δ : ℝ)^2 ≤ (4*D^2)*k x := by
    have ha : 0 < (x.1 : ℝ) := by
      have h := (hQ x hx).1
      exact_mod_cast (show 0 < x.1 by omega)
    have hp : ((x.1 : ℝ)*(x.2 : ℝ)^2)^2 ≤ 4*D^2 := by
      have h := (hQ x hx).2.2
      have hnonneg : 0 ≤ (x.1 : ℝ)*(x.2 : ℝ)^2 := by positivity
      nlinarith
    calc
      _ = ((x.1 : ℝ)*(x.2 : ℝ)^2)^2*k x := by
        have he : (15 : ℝ)/2 = 2+11/2 := by norm_num
        rw [he,Real.rpow_add ha,Real.rpow_ofNat]
        dsimp [k]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (hk x)
  calc
    _ ≤ ∑ x ∈ Q, (4*D^2)*k x := Finset.sum_le_sum hterm
    _ = (4*D^2)*∑ x ∈ Q, k x := (Finset.mul_sum ..).symm
    _ ≤ (4*D^2)*(C*D^((13 : ℝ)/2)*(Δ.divisors.card : ℝ)*
        (Δ.divisors.card : ℝ)) :=
      mul_le_mul_of_nonneg_left (hbound D hD Δ Δ hΔ hΔ Q hQ) (by positivity)
    _ = (4*C)*D^((17 : ℝ)/2)*(Δ.divisors.card : ℝ)^2 := by
      have he : D^2*D^((13 : ℝ)/2) = D^((17 : ℝ)/2) := by
        rw [← Real.rpow_ofNat,← Real.rpow_add hD0]
        norm_num
      calc
        _ = (4*C)*(D^2*D^((13 : ℝ)/2))*(Δ.divisors.card : ℝ)^2 := by ring
        _ = _ := by rw [he]

end CubicTenVariables.OffTerminalGcdSum
