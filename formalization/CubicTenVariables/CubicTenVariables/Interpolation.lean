import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The two real-power interpolations in the proof of the manuscript's clean
shifted estimate. These prove the actual inequalities, including elimination
of the conductor parameter. They do not assume or prove that the displayed
initial bounds hold for the exponential sums. -/

namespace CubicTenVariables

theorem le_geometric_interpolation {E A B θ : ℝ}
    (hE : 0 ≤ E) (hA : E ≤ A) (hB : E ≤ B)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) :
    E ≤ A ^ θ * B ^ (1 - θ) := by
  calc
    E = E ^ (θ + (1 - θ)) := by norm_num
    _ = E ^ θ * E ^ (1 - θ) :=
      Real.rpow_add_of_nonneg hE hθ (sub_nonneg.mpr hθ')
    _ ≤ A ^ θ * B ^ (1 - θ) :=
      mul_le_mul (Real.rpow_le_rpow hE hA hθ)
        (Real.rpow_le_rpow hE hB (sub_nonneg.mpr hθ'))
        (Real.rpow_nonneg hE _) (Real.rpow_nonneg (hE.trans hA) _)

theorem three_power_interpolation
    {E Q G D θ : ℝ} (hE : 0 ≤ E)
    (hQ : 0 < Q) (hG : 0 < G) (hD : 0 < D)
    (a₁ b₁ c₁ a₂ b₂ c₂ : ℝ) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (h₁ : E ≤ Q ^ a₁ * G ^ b₁ * D ^ c₁)
    (h₂ : E ≤ Q ^ a₂ * G ^ b₂ * D ^ c₂) :
    E ≤ Q ^ (a₁ * θ + a₂ * (1 - θ)) *
      G ^ (b₁ * θ + b₂ * (1 - θ)) *
      D ^ (c₁ * θ + c₂ * (1 - θ)) := by
  have hp (a b c t : ℝ) : (Q ^ a * G ^ b * D ^ c) ^ t =
      Q ^ (a * t) * G ^ (b * t) * D ^ (c * t) := by
    rw [Real.mul_rpow
      (mul_nonneg (Real.rpow_nonneg hQ.le _) (Real.rpow_nonneg hG.le _))
      (Real.rpow_nonneg hD.le _),
      Real.mul_rpow (Real.rpow_nonneg hQ.le _) (Real.rpow_nonneg hG.le _),
      ← Real.rpow_mul hQ.le, ← Real.rpow_mul hG.le, ← Real.rpow_mul hD.le]
  calc
    E ≤ (Q ^ a₁ * G ^ b₁ * D ^ c₁) ^ θ *
        (Q ^ a₂ * G ^ b₂ * D ^ c₂) ^ (1 - θ) :=
      le_geometric_interpolation hE h₁ h₂ hθ hθ'
    _ = (Q ^ (a₁ * θ) * Q ^ (a₂ * (1 - θ))) *
        (G ^ (b₁ * θ) * G ^ (b₂ * (1 - θ))) *
        (D ^ (c₁ * θ) * D ^ (c₂ * (1 - θ))) := by
      rw [hp, hp]
      ring
    _ = _ := by rw [← Real.rpow_add hQ, ← Real.rpow_add hG, ← Real.rpow_add hD]

/-- The complementary conductor bounds interpolate with weights 15/16 and
1/16. The D exponent cancels, and the Q saving is exactly 1/96. -/
theorem complementary_interpolation {E Q G D : ℝ}
    (hE : 0 ≤ E) (hQ : 0 < Q) (hG : 0 < G) (hD : 0 < D)
    (h₁ : E ≤ Q ^ (10 : ℝ) * G ^ (-(2 : ℝ) / 3) * D ^ (-(1 : ℝ) / 6))
    (h₂ : E ≤ Q ^ ((10 : ℝ) - 1 / 6) * G ^ ((1 : ℝ) / 2) * D ^ ((5 : ℝ) / 2)) :
    E ≤ Q ^ ((10 : ℝ) - 1 / 96) * G ^ (-(19 : ℝ) / 32) := by
  have h := three_power_interpolation (θ := (15 : ℝ) / 16)
    hE hQ hG hD 10 (-(2 : ℝ) / 3) (-(1 : ℝ) / 6)
    (10 - (1 : ℝ) / 6) ((1 : ℝ) / 2) ((5 : ℝ) / 2)
    (by norm_num) (by norm_num) h₁ h₂
  norm_num at h ⊢
  exact h

/-- The generic conductor bounds interpolate with weights 8/13 and 5/13.
The K exponent cancels, and the Q saving is exactly 1/78. -/
theorem generic_interpolation {E Q G K : ℝ}
    (hE : 0 ≤ E) (hQ : 0 < Q) (hG : 0 < G) (hK : 0 < K)
    (h₁ : E ≤ Q ^ ((10 : ℝ) + 1 / 12) * G ^ (-(3 : ℝ) / 4) * K ^ (-(5 : ℝ) / 8))
    (h₂ : E ≤ Q ^ ((10 : ℝ) - 1 / 6) * G ^ ((1 : ℝ) / 2) * K) :
    E ≤ Q ^ ((10 : ℝ) - 1 / 78) * G ^ (-(7 : ℝ) / 26) := by
  have h := three_power_interpolation (θ := (8 : ℝ) / 13)
    hE hQ hG hK (10 + (1 : ℝ) / 12) (-(3 : ℝ) / 4) (-(5 : ℝ) / 8)
    (10 - (1 : ℝ) / 6) ((1 : ℝ) / 2) 1
    (by norm_num) (by norm_num) h₁ (by simpa using h₂)
  norm_num at h ⊢
  exact h

end CubicTenVariables
