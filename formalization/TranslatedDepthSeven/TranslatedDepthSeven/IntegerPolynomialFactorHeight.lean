import Mathlib.NumberTheory.MahlerMeasure
import Mathlib.Data.Nat.Choose.Bounds

/-!
# An explicit coefficient bound for integral polynomial factors

The fixed-complexity elimination route produces univariate integral
polynomials and then passes to their factors.  This file isolates the small
height estimate needed at that step.  It is a direct consequence of the
multiplicativity of Mahler measure, the fact that a nonzero integral
polynomial has Mahler measure at least one, and the standard coefficient
bound in terms of Mahler measure.
-/

namespace TranslatedDepthSeven

noncomputable section

open Polynomial

/-- If `q` is an integral polynomial factor of `p`, every coefficient of
`q` is bounded by the corresponding binomial coefficient times the `ℓ¹`
coefficient norm of `p` after embedding in `ℂ`. -/
theorem norm_coeff_map_intCast_factor_le
    (p q r : ℤ[X]) (hp : p = q * r) (hr : r ≠ 0) (i : ℕ) :
    ‖(q.map (Int.castRingHom ℂ)).coeff i‖ ≤
      q.natDegree.choose i *
        (p.map (Int.castRingHom ℂ)).sum (fun _ a => ‖a‖) := by
  let pℂ := p.map (Int.castRingHom ℂ)
  let qℂ := q.map (Int.castRingHom ℂ)
  let rℂ := r.map (Int.castRingHom ℂ)
  have hrℂ : rℂ ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff
      (Int.castRingHom ℂ).injective_int).mpr hr
  have hfactor : pℂ = qℂ * rℂ := by
    simp only [pℂ, qℂ, rℂ, hp, Polynomial.map_mul]
  have hone : 1 ≤ rℂ.mahlerMeasure := by
    simpa [rℂ] using Polynomial.one_le_mahlerMeasure_of_ne_zero hr
  have hq_nonneg : 0 ≤ qℂ.mahlerMeasure := Polynomial.mahlerMeasure_nonneg qℂ
  have hmeasure : qℂ.mahlerMeasure ≤ pℂ.mahlerMeasure := by
    rw [hfactor, Polynomial.mahlerMeasure_mul]
    nlinarith
  calc
    ‖qℂ.coeff i‖ ≤ qℂ.natDegree.choose i * qℂ.mahlerMeasure :=
      Polynomial.norm_coeff_le_choose_mul_mahlerMeasure i qℂ
    _ ≤ qℂ.natDegree.choose i * pℂ.mahlerMeasure := by
      gcongr
    _ ≤ qℂ.natDegree.choose i * pℂ.sum (fun _ a => ‖a‖) := by
      gcongr
      exact Polynomial.mahlerMeasure_le_sum_norm_coeff pℂ
    _ = q.natDegree.choose i *
        (p.map (Int.castRingHom ℂ)).sum (fun _ a => ‖a‖) := by
      simp only [qℂ, pℂ]
      rw [Polynomial.natDegree_map_eq_of_injective
        (Int.castRingHom ℂ).injective_int]

/-- A degree-only version: when `deg q ≤ D`, the binomial factor can be
replaced by `2^D`. -/
theorem norm_coeff_map_intCast_factor_le_two_pow
    (p q r : ℤ[X]) (hp : p = q * r) (hr : r ≠ 0)
    (D i : ℕ) (hqD : q.natDegree ≤ D) :
    ‖(q.map (Int.castRingHom ℂ)).coeff i‖ ≤
      2 ^ D * (p.map (Int.castRingHom ℂ)).sum (fun _ a => ‖a‖) := by
  calc
    ‖(q.map (Int.castRingHom ℂ)).coeff i‖ ≤
        q.natDegree.choose i *
          (p.map (Int.castRingHom ℂ)).sum (fun _ a => ‖a‖) :=
      norm_coeff_map_intCast_factor_le p q r hp hr i
    _ ≤ 2 ^ q.natDegree *
          (p.map (Int.castRingHom ℂ)).sum (fun _ a => ‖a‖) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.choose_le_two_pow q.natDegree i
      · exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    _ ≤ 2 ^ D *
          (p.map (Int.castRingHom ℂ)).sum (fun _ a => ‖a‖) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.pow_le_pow_right (by omega) hqD
      · exact Finset.sum_nonneg fun _ _ => norm_nonneg _

end

end TranslatedDepthSeven
