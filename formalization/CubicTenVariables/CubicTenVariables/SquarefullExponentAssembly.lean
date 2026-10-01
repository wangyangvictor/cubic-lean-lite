import CubicTenVariables.SmithGlobalExponents

/-! Exact epsilon and exponent accounting for the j=1 squarefull bound. -/

namespace CubicTenVariables.SquarefullExponentAssembly

private theorem real_identity (u v ε : ℝ) (hu : 0 < u) (hv : 0 < v) :
    (u*v)^12*v^6*u^(9+ε)*v^((21:ℝ)/2+ε) =
      (u*v)^(21+ε)*v^((15:ℝ)/2) := by
  have hsplit : v^((21:ℝ)/2+ε) = v^(3:ℝ)*v^((15:ℝ)/2)*v^ε := by
    rw [← Real.rpow_add hv, ← Real.rpow_add hv]
    congr 1
    ring
  rw [hsplit, Real.mul_rpow hu.le hv.le, Real.rpow_add hu, Real.rpow_add hu,
    Real.rpow_add hv]
  norm_num
  ring

/-- Identical epsilon choices in the quotient and squarefree bounds produce
exactly c^epsilon. No additional d^epsilon loss remains. -/
theorem exact_exponents (c d : ℕ) (hc : 0 < c) (hd : 0 < d) (hdc : d ∣ c)
    (ε : ℝ) :
    (c : ℝ)^12*(d : ℝ)^6*((c/d : ℕ) : ℝ)^(9+ε)*(d : ℝ)^((21:ℝ)/2+ε) =
      (c : ℝ)^(21+ε)*(d : ℝ)^((15:ℝ)/2) := by
  have hq : 0 < c/d := Nat.div_pos (Nat.le_of_dvd hc hdc) hd
  have he : ((c/d : ℕ) : ℝ)*(d : ℝ) = (c : ℝ) := by
    exact_mod_cast Nat.div_mul_cancel hdc
  rw [← he]
  exact real_identity _ _ ε (by exact_mod_cast hq) (by exact_mod_cast hd)

/-- Constant factors and the residue maximum are retained exactly. -/
theorem exact_weighted_exponents (c d : ℕ) (hc : 0 < c) (hd : 0 < d) (hdc : d ∣ c)
    (ε C D E : ℝ) :
    (c : ℝ)^12*(d : ℝ)^6*E*
      (C*((c/d : ℕ) : ℝ)^(9+ε)*(D*(d : ℝ)^((21:ℝ)/2+ε))) =
      (C*D)*(c : ℝ)^(21+ε)*(d : ℝ)^((15:ℝ)/2)*E := by
  calc
    _ = (C*D)*((c : ℝ)^12*(d : ℝ)^6*((c/d : ℕ) : ℝ)^(9+ε)*
        (d : ℝ)^((21:ℝ)/2+ε))*E := by ring
    _ = _ := by rw [exact_exponents c d hc hd hdc ε]; ring

end CubicTenVariables.SquarefullExponentAssembly
