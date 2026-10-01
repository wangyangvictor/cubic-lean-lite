import HessianTheorem11.PolarizationExpansion
import HessianTheorem11.KernelGradientSpan

/-! Elementary nonsingular-zero upgrade for a nondegenerate cubic.

Over any characteristic-zero field, injectivity of the full Hessian pencil
and existence of a nonzero zero imply existence of a nonzero zero with
nonzero gradient. This proves the smoothness upgrade used in Pleasants'
Lemma 2, directly with the polynomial's actual derivatives. It assumes
neither anisotropy over the field nor any local-solubility theorem.
-/

noncomputable section
namespace CubicTenVariables
open MvPolynomial HessianTheorem11

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- A nonzero symmetric Hessian has a nonzero value on some diagonal
pair of vectors. Polarization handles the possible off-diagonal entries. -/
theorem exists_polarization_diagonal_ne_zero
    (F : MvPolynomial (Fin n) K) (z : Fin n → K) (hH : hessian F z ≠ 0) :
    ∃ u : Fin n → K, polarization F u u z ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  have hb (u v : Fin n → K) : polarization F u v z = 0 := by
    have he := h (u + v)
    rw [polarization_add_first, polarization_add_second, polarization_add_second,
      h u, h v, polarization_swap_first F v u z] at he
    linear_combination (1 / 2 : K) * he
  apply hH
  ext i j
  have he := hb (Pi.single i 1) (Pi.single j 1)
  simpa [polarization, Matrix.mulVec, dotProduct, Pi.single_apply] using he

/-- Starting at a singular point where the Hessian is nonzero, a line in
that direction meets the cubic at a point with nonzero directional derivative. -/
theorem exists_nonsingular_zero_of_singular_point_hessian_ne_zero
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (z : Fin n → K) (hz : gradient F z = 0) (hH : hessian F z ≠ 0) :
    ∃ x : Fin n → K, x ≠ 0 ∧ eval x F = 0 ∧ gradient F x ≠ 0 := by
  obtain ⟨u, hu⟩ := exists_polarization_diagonal_ne_zero F z hH
  have hzz (v : Fin n → K) : polarization F v z z = 0 := by
    rw [polarization_diagonal_eq_gradient F hF, hz]
    simp
  have hzz' (v : Fin n → K) : polarization F z z v = 0 := by
    rw [polarization_rotate hF, hzz]
  have hzz'' (v : Fin n → K) : polarization F z v z = 0 := by
    rw [polarization_swap_first, hzz]
  let c : K := (1 / 2 : K) * polarization F u u z
  have hc : c ≠ 0 := mul_ne_zero (by norm_num) hu
  let t : K := -eval u F / c
  let x : Fin n → K := u + t • z
  have htz : eval (t • z) F = 0 := by
    rw [eval_cubic_eq_polarization hF, polarization_smul_first,
      polarization_smul_second, polarization_smul_third hF, hzz]
    ring
  have hxzero : eval x F = 0 := by
    dsimp [x]
    rw [eval_cubic_add hF, htz, polarization_smul_third hF,
      polarization_smul_second, polarization_smul_third hF, hzz]
    have htc : t * c = -eval u F := div_mul_cancel₀ _ hc
    dsimp [c] at htc
    linear_combination htc
  have hxq : polarization F z x x = polarization F u u z := by
    dsimp [x]
    rw [polarization_add_second, polarization_add_third hF,
      polarization_add_third hF, polarization_smul_second,
      polarization_smul_second, polarization_smul_third hF,
      polarization_smul_third hF, hzz, hzz', hzz'']
    rw [← polarization_rotate hF u u z]
    ring
  have hx : x ≠ 0 := by
    intro he
    have h := hxq
    rw [he, polarization_zero_second] at h
    exact hu h.symm
  refine ⟨x, hx, hxzero, ?_⟩
  intro hsing
  have he : polarization F z x x = 0 := by
    rw [polarization_diagonal_eq_gradient F hF, hsing]
    simp
  exact hu (hxq.symm.trans he)

/-- The smoothness upgrade for an actual nonzero zero of a homogeneous cubic.
The only nondegeneracy hypothesis is injectivity of its full Hessian pencil. -/
theorem nonsingular_zero_of_hessian_injective
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (hH : Function.Injective (hessian F))
    (z : Fin n → K) (hz : z ≠ 0) (hFz : eval z F = 0) :
    ∃ x : Fin n → K, x ≠ 0 ∧ eval x F = 0 ∧ gradient F x ≠ 0 := by
  by_cases hsing : gradient F z = 0
  · have hHz : hessian F z ≠ 0 := by
      intro he
      exact hz (hH (he.trans (hessian_zero hF).symm))
    exact exists_nonsingular_zero_of_singular_point_hessian_ne_zero F hF z hsing hHz
  · exact ⟨z, hz, hFz, hsing⟩

/-- For a homogeneous cubic with injective Hessian pencil, a local theorem
need supply only a nontrivial zero; nonsingularity follows from the proof above. -/
theorem exists_nonsingular_zero_iff_exists_zero
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (hH : Function.Injective (hessian F)) :
    (∃ x : Fin n → K, x ≠ 0 ∧ eval x F = 0 ∧ gradient F x ≠ 0) ↔
      ∃ x : Fin n → K, x ≠ 0 ∧ eval x F = 0 := by
  constructor
  · rintro ⟨x, hx, hFx, _⟩
    exact ⟨x, hx, hFx⟩
  · rintro ⟨x, hx, hFx⟩
    exact nonsingular_zero_of_hessian_injective F hF hH x hx hFx

end CubicTenVariables
