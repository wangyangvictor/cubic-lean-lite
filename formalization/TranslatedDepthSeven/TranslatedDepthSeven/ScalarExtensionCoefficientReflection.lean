import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import TranslatedDepthSeven.EquationFamilyTangentBaseChange

/-!
# Reflection of coefficients through a scalar extension
-/

namespace TranslatedDepthSeven

noncomputable section

universe u v w

variable {K : Type u} {E : Type v} {n : Type w}
  [Field K] [Field E] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Matrix-vector multiplication commutes with a coefficient homomorphism. -/
theorem map_matrix_mulVec (f : K →+* E) (M : Matrix n n K) (v : n → K) :
    (M.map f).mulVec (fun i ↦ f (v i)) = fun i ↦ f (M.mulVec v i) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

/-- If an invertible square system over `K` has a solution after extending
coefficients to `E`, that solution is the extension of its unique solution
over `K`. -/
theorem exists_preimage_of_mapMatrix_mulVec_eq
    (f : K →+* E) (hf : Function.Injective f)
    (M : Matrix n n K) (hdet : M.det ≠ 0)
    (v : n → K) (a : n → E)
    (ha : (M.map f).mulVec a = fun i ↦ f (v i)) :
    ∃ a₀ : n → K, (fun i ↦ f (a₀ i)) = a := by
  let a₀ : n → K := M⁻¹.mulVec v
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hMa₀ : M.mulVec a₀ = v := by
    change M.mulVec (M⁻¹.mulVec v) = v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hunit,
      Matrix.one_mulVec]
  have hmapdet : (M.map f).det ≠ 0 := by
    change (f.mapMatrix M).det ≠ 0
    rw [← f.map_det]
    exact fun h ↦ hdet (hf (by simpa using h))
  have hinj : Function.Injective (M.map f).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((M.map f).isUnit_iff_isUnit_det.mpr
        (isUnit_iff_ne_zero.mpr hmapdet))
  refine ⟨a₀, hinj ?_⟩
  rw [map_matrix_mulVec, hMa₀, ha]

/-- Coordinate form of scalar-reflection: an invertible selected coordinate
minor forces all coefficients of an extended-scalar relation to descend. -/
theorem exists_preimage_coefficients_of_selectedMinor
    {N r : ℕ} (f : K →+* E) (hf : Function.Injective f)
    (b : Fin r → Fin N → K) (cols : Fin r → Fin N)
    (hdet : Matrix.det (Matrix.of (fun i j ↦ b j (cols i))) ≠ 0)
    (v : Fin N → K) (a : Fin r → E)
    (ha : ∀ x, ∑ j, a j * f (b j x) = f (v x)) :
    ∃ a₀ : Fin r → K, (fun i ↦ f (a₀ i)) = a := by
  let M : Matrix (Fin r) (Fin r) K :=
    Matrix.of (fun i j ↦ b j (cols i))
  have hsystem :
      (M.map f).mulVec a = fun i ↦ f (v (cols i)) := by
    funext i
    simpa [M, Matrix.mulVec, dotProduct, mul_comm] using ha (cols i)
  exact exists_preimage_of_mapMatrix_mulVec_eq
    f hf M hdet (fun i ↦ v (cols i)) a hsystem

/-- Scalar-reflection for a finite linearly independent family: any
extended-scalar linear combination which lands back in the base-coordinate
space already has all coefficients in the base field. -/
theorem exists_preimage_coefficients_of_linearIndependent_family
    {N r : ℕ} (f : K →+* E) (hf : Function.Injective f)
    (b : Fin r → Fin N → K) (hb : LinearIndependent K b)
    (v : Fin N → K) (a : Fin r → E)
    (ha : ∀ x, ∑ j, a j * f (b j x) = f (v x)) :
    ∃ a₀ : Fin r → K, (fun i ↦ f (a₀ i)) = a := by
  let A : Matrix (Fin r) (Fin N) K := Matrix.of (fun i j ↦ b i j)
  have hrow : A.row = b := by rfl
  obtain ⟨cols, -, hdet⟩ :=
    TangentBaseChange.exists_selectedMinor_ne_zero_of_linearIndependent_rows
      A (hrow ▸ hb)
  apply exists_preimage_coefficients_of_selectedMinor f hf b cols
      (v := v) (a := a)
  · have ht : Matrix.of (fun i j ↦ b j (cols i)) =
        (A.submatrix id cols).transpose := by rfl
    rw [ht, Matrix.det_transpose]
    exact hdet
  · exact ha

end

end TranslatedDepthSeven
