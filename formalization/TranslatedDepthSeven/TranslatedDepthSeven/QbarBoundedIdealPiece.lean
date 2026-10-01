import TranslatedDepthSeven.QbarFiniteCoefficientField
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Finite bases of bounded-degree pieces of ideals over `Qbar`
-/

namespace TranslatedDepthSeven

noncomputable section

universe u

variable {σ : Type u} [Fintype σ]

/-- The finite-dimensional vector space of elements of `P` of total degree
at most `D`. -/
def boundedIdealPiece
    (P : Ideal (MvPolynomial σ (AlgebraicClosure ℚ))) (D : ℕ) :
    Submodule (AlgebraicClosure ℚ)
      (MvPolynomial σ (AlgebraicClosure ℚ)) where
  carrier := (P : Set _) ∩
    MvPolynomial.restrictTotalDegree σ (AlgebraicClosure ℚ) D
  zero_mem' := ⟨P.zero_mem,
    (MvPolynomial.restrictTotalDegree σ (AlgebraicClosure ℚ) D).zero_mem⟩
  add_mem' := fun hf hg ↦ ⟨P.add_mem hf.1 hg.1,
    (MvPolynomial.restrictTotalDegree σ (AlgebraicClosure ℚ) D).add_mem hf.2 hg.2⟩
  smul_mem' := fun c f hf ↦ ⟨by
      rw [Algebra.smul_def]
      exact P.mul_mem_left _ hf.1,
    (MvPolynomial.restrictTotalDegree σ (AlgebraicClosure ℚ) D).smul_mem c hf.2⟩

instance boundedIdealPiece_moduleFinite
    (P : Ideal (MvPolynomial σ (AlgebraicClosure ℚ))) (D : ℕ) :
    Module.Finite (AlgebraicClosure ℚ) (boundedIdealPiece P D) := by
  apply Module.Finite.of_injective
    (Submodule.inclusion (show boundedIdealPiece P D ≤
      MvPolynomial.restrictTotalDegree σ (AlgebraicClosure ℚ) D from
        fun _ h ↦ h.2))
  exact Submodule.inclusion_injective _

/-- A literal finite polynomial family underlying a basis of the bounded
piece. -/
def boundedIdealPieceBasisFamily
    (P : Ideal (MvPolynomial σ (AlgebraicClosure ℚ))) (D : ℕ) :
    Finset (MvPolynomial σ (AlgebraicClosure ℚ)) := by
  classical
  exact Finset.univ.image (fun i ↦
    ((Module.finBasis (AlgebraicClosure ℚ) (boundedIdealPiece P D)) i).1)

theorem boundedIdealPieceBasisFamily_subset
    (P : Ideal (MvPolynomial σ (AlgebraicClosure ℚ))) (D : ℕ) :
    (↑(boundedIdealPieceBasisFamily P D) :
      Set (MvPolynomial σ (AlgebraicClosure ℚ))) ⊆
        (boundedIdealPiece P D :
          Set (MvPolynomial σ (AlgebraicClosure ℚ))) := by
  classical
  intro f hf
  simp only [boundedIdealPieceBasisFamily, Finset.mem_coe,
    Finset.mem_image, Finset.mem_univ, true_and] at hf
  obtain ⟨i, rfl⟩ := hf
  exact (Module.finBasis (AlgebraicClosure ℚ) (boundedIdealPiece P D) i).2

/-- The explicit finite Galois coefficient field attached to the bounded
ideal-piece basis. -/
def boundedIdealPieceGaloisField
    (P : Ideal (MvPolynomial σ (AlgebraicClosure ℚ))) (D : ℕ) :
    FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
  polynomialFamilyGaloisField (boundedIdealPieceBasisFamily P D)

theorem boundedIdealPieceBasis_coefficient_mem_galoisField
    (P : Ideal (MvPolynomial σ (AlgebraicClosure ℚ))) (D : ℕ)
    {f : MvPolynomial σ (AlgebraicClosure ℚ)}
    (hf : f ∈ boundedIdealPieceBasisFamily P D)
    {c : AlgebraicClosure ℚ} (hc : c ∈ f.coeffs) :
    c ∈ (boundedIdealPieceGaloisField P D :
      IntermediateField ℚ (AlgebraicClosure ℚ)) :=
  coefficient_mem_polynomialFamilyGaloisField
    (boundedIdealPieceBasisFamily P D) hf hc

end

end TranslatedDepthSeven
