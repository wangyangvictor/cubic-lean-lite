import CubicTenVariables.Interpolation

/-! Explicit loss budgets and removal of harmless real-power factors in
`eq:n10-complement-closed` and `eq:n10-generic-closed`.
These are inequalities of actual real powers, with no analytic input.
The fixed Smith loss is chosen from gamma and its fixed loss coefficient;
no subsequent epsilon parameter enters that choice. -/

namespace CubicTenVariables

/-- A fixed positive loss with enough room for the desired saving gamma. -/
noncomputable def smithLossBudget (γ K : ℝ) : ℝ := ((1 : ℝ) / 96 - γ) / (K + 1)

theorem smithLossBudget_pos {γ K : ℝ} (hγ : γ < (1 : ℝ) / 96) (hK : 0 ≤ K) :
    0 < smithLossBudget γ K := by
  unfold smithLossBudget
  exact div_pos (sub_pos.mpr hγ) (by linarith)

theorem smithLossBudget_saves {γ K : ℝ} (hγ : γ < (1 : ℝ) / 96) (hK : 0 ≤ K) :
    γ + K * smithLossBudget γ K < (1 : ℝ) / 96 := by
  have hp := smithLossBudget_pos hγ hK
  have he : smithLossBudget γ K * (K + 1) = (1 : ℝ) / 96 - γ := by
    unfold smithLossBudget
    exact div_mul_cancel₀ _ (by linarith)
  nlinarith

/-- In particular, for every requested 0<gamma<1/96, one can fix a positive
Smith loss before choosing any later small-error parameters. Positivity of
gamma is unnecessary for this elementary budget lemma. -/
theorem exists_smith_loss_budget {γ K : ℝ} (hγ : γ < (1 : ℝ) / 96) (hK : 0 ≤ K) :
    ∃ η : ℝ, 0 < η ∧ γ + K * η < (1 : ℝ) / 96 :=
  ⟨smithLossBudget γ K, smithLossBudget_pos hγ hK, smithLossBudget_saves hγ hK⟩

/-- A separate arbitrary subpower budget may be chosen without changing
an already fixed Smith loss. -/
theorem exists_secondary_loss_budget {ε J : ℝ} (hε : 0 < ε) (hJ : 0 ≤ J) :
    ∃ δ : ℝ, 0 < δ ∧ J * δ < ε := by
  let δ := ε / (J + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have he : δ * (J + 1) = ε := div_mul_cancel₀ _ (by linarith)
  exact ⟨δ, hδ, by nlinarith⟩

/-- Nonpositive powers of a base at least one contribute at most one. -/
theorem nonpositive_rpow_le_one {G b : ℝ} (hG : 1 ≤ G) (hb : b ≤ 0) : G ^ b ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hG hb

theorem discard_nonpositive_rpow {Q G a b : ℝ} (hQ : 0 ≤ Q)
    (hG : 1 ≤ G) (hb : b ≤ 0) : Q ^ a * G ^ b ≤ Q ^ a := by
  calc
    Q ^ a * G ^ b ≤ Q ^ a * 1 :=
      mul_le_mul_of_nonneg_left (nonpositive_rpow_le_one hG hb) (Real.rpow_nonneg hQ a)
    _ = Q ^ a := mul_one _

theorem complementary_bound_to_common {Q G : ℝ} (hQ : 1 ≤ Q) (hG : 1 ≤ G) :
    Q ^ ((10 : ℝ) - 1 / 96) * G ^ (-(19 : ℝ) / 32) ≤
      Q ^ ((10 : ℝ) - 1 / 96) :=
  discard_nonpositive_rpow (by linarith) hG (by norm_num)

/-- The generic saving 1/78 is stronger than the common saving 1/96. -/
theorem generic_bound_to_common {Q G : ℝ} (hQ : 1 ≤ Q) (hG : 1 ≤ G) :
    Q ^ ((10 : ℝ) - 1 / 78) * G ^ (-(7 : ℝ) / 26) ≤
      Q ^ ((10 : ℝ) - 1 / 96) := by
  calc
    Q ^ ((10 : ℝ) - 1 / 78) * G ^ (-(7 : ℝ) / 26) ≤
        Q ^ ((10 : ℝ) - 1 / 78) :=
      discard_nonpositive_rpow (by linarith) hG (by norm_num)
    _ ≤ Q ^ ((10 : ℝ) - 1 / 96) :=
      Real.rpow_le_rpow_of_exponent_le hQ (by norm_num)

/-- Sum the two normalized monomial bounds at the common saving. -/
theorem combined_benchmark_bound {Q G : ℝ} (hQ : 1 ≤ Q) (hG : 1 ≤ G) :
    Q ^ ((10 : ℝ) - 1 / 96) * G ^ (-(19 : ℝ) / 32) +
      Q ^ ((10 : ℝ) - 1 / 78) * G ^ (-(7 : ℝ) / 26) ≤
      2 * Q ^ ((10 : ℝ) - 1 / 96) := by
  have hc := complementary_bound_to_common hQ hG
  have hg := generic_bound_to_common hQ hG
  linarith

/-- Absorb an actual power loss Q^(K eta) into the requested saving. -/
theorem benchmark_loss_absorption {Q γ K η : ℝ} (hQ : 1 ≤ Q)
    (hbudget : γ + K * η ≤ (1 : ℝ) / 96) :
    Q ^ ((10 : ℝ) - 1 / 96 + K * η) ≤ Q ^ ((10 : ℝ) - γ) :=
  Real.rpow_le_rpow_of_exponent_le hQ (by linarith)

/-- The two manuscript monomials, multiplied by the fixed Smith loss, are
bounded by the desired benchmark power. The factor two records their sum. -/
theorem combined_benchmark_with_smith_loss {Q G γ K : ℝ}
    (hQ : 1 ≤ Q) (hG : 1 ≤ G) (hγ : γ < (1 : ℝ) / 96) (hK : 0 ≤ K) :
    Q ^ (K * smithLossBudget γ K) *
      (Q ^ ((10 : ℝ) - 1 / 96) * G ^ (-(19 : ℝ) / 32) +
        Q ^ ((10 : ℝ) - 1 / 78) * G ^ (-(7 : ℝ) / 26)) ≤
      2 * Q ^ ((10 : ℝ) - γ) := by
  have hQpos : 0 < Q := by linarith
  calc
    _ ≤ Q ^ (K * smithLossBudget γ K) *
        (2 * Q ^ ((10 : ℝ) - 1 / 96)) :=
      mul_le_mul_of_nonneg_left (combined_benchmark_bound hQ hG)
        (Real.rpow_nonneg hQpos.le _)
    _ = 2 * Q ^ ((10 : ℝ) - 1 / 96 + K * smithLossBudget γ K) := by
      rw [Real.rpow_add hQpos]
      ring
    _ ≤ 2 * Q ^ ((10 : ℝ) - γ) :=
      mul_le_mul_of_nonneg_left
        (benchmark_loss_absorption hQ (smithLossBudget_saves hγ hK).le) (by norm_num)

end CubicTenVariables
