import TranslatedDepthSeven.TangentPacketSpan
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Explicit height bounds for integral resultants

The point-local triangular description uses resultants, and separability can
be certified by the resultant with the derivative.  Since a resultant is a
Sylvester determinant, the needed coefficient growth is an immediate
factorial determinant bound.
-/

namespace TranslatedDepthSeven

noncomputable section

open Polynomial

/-- Every entry of a Sylvester matrix is either zero or a coefficient of one
of its two input polynomials. -/
theorem sylvester_entry_natAbs_le
    (f g : ℤ[X]) (m n C : ℕ)
    (hf : ∀ i, (f.coeff i).natAbs ≤ C)
    (hg : ∀ i, (g.coeff i).natAbs ≤ C) :
    ∀ i j, (f.sylvester g m n i j).natAbs ≤ C := by
  intro i j
  induction j using Fin.addCases with
  | left j =>
      simp only [Polynomial.sylvester, Matrix.of_apply,
        Fin.addCases_left]
      split_ifs
      · exact hg _
      · simp
  | right j =>
      simp only [Polynomial.sylvester, Matrix.of_apply,
        Fin.addCases_right]
      split_ifs
      · exact hf _
      · simp

/-- Literal determinant bound for an integral resultant with user-supplied
degree parameters. -/
theorem resultant_natAbs_le_factorial_mul_pow
    (f g : ℤ[X]) (m n C : ℕ)
    (hf : ∀ i, (f.coeff i).natAbs ≤ C)
    (hg : ∀ i, (g.coeff i).natAbs ≤ C) :
    (f.resultant g m n).natAbs ≤
      (m + n).factorial * C ^ (m + n) := by
  rw [Polynomial.resultant]
  exact TangentPacketSpan.det_natAbs_le_factorial_mul_pow
    (f.sylvester g m n) (sylvester_entry_natAbs_le f g m n C hf hg)

/-- If an integral polynomial has degree at most `D` and coefficients at
most `C`, the coefficients of its derivative are at most `D*C`. -/
theorem derivative_coeff_natAbs_le_degree_mul
    (f : ℤ[X]) (D C : ℕ)
    (hdegree : f.natDegree ≤ D)
    (hcoeff : ∀ i, (f.coeff i).natAbs ≤ C) :
    ∀ i, (f.derivative.coeff i).natAbs ≤ D * C := by
  intro i
  rw [Polynomial.coeff_derivative, Int.natAbs_mul]
  have hInt : (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) := by omega
  have hcast : ((i : ℤ) + 1).natAbs = i + 1 := by
    rw [hInt, Int.natAbs_natCast]
  rw [hcast]
  by_cases hi : i + 1 ≤ D
  · calc
      (f.coeff (i + 1)).natAbs * (i + 1) ≤ C * D :=
        Nat.mul_le_mul (hcoeff (i + 1)) hi
      _ = D * C := Nat.mul_comm C D
  · have hzero : f.coeff (i + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (hdegree.trans_lt (Nat.lt_of_not_ge hi))
    simp [hzero]

/-- A polynomial bound for the resultant with the derivative.  This
resultant is the explicit separability certificate used by a triangular
finite system; no abstract discriminant height is invoked. -/
theorem resultant_derivative_natAbs_le
    (f : ℤ[X]) (D C : ℕ) (hD : 1 ≤ D)
    (hdegree : f.natDegree ≤ D)
    (hcoeff : ∀ i, (f.coeff i).natAbs ≤ C) :
    (f.resultant f.derivative D (D - 1)).natAbs ≤
      (2 * D - 1).factorial * (D * C) ^ (2 * D - 1) := by
  have hfDC : ∀ i, (f.coeff i).natAbs ≤ D * C := by
    intro i
    calc
      (f.coeff i).natAbs ≤ C := hcoeff i
      _ ≤ D * C := by
        simpa only [one_mul] using Nat.mul_le_mul_right C hD
  have hres := resultant_natAbs_le_factorial_mul_pow
    f f.derivative D (D - 1) (D * C) hfDC
      (derivative_coeff_natAbs_le_degree_mul f D C hdegree hcoeff)
  have hsum : D + (D - 1) = 2 * D - 1 := by omega
  rw [hsum] at hres
  exact hres

end

end TranslatedDepthSeven
