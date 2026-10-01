import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Total rank of the reduced components of a finite algebra

The generic fibre of a finite normalization is a finite-dimensional
commutative algebra over a field.  Its distinct irreducible components are
represented by distinct maximal ideals.  The Chinese remainder map onto the
product of their residue fields is surjective, so the sum of the residue-field
degrees is at most the vector-space dimension of the original algebra.

This is the algebraic degree-mass inequality needed in the vertical argument;
it uses neither Hilbert polynomials nor Chow varieties.
-/

namespace TranslatedDepthSeven

noncomputable section

open Function

universe u v w

/-- For any finite pairwise-coprime family of ideals in a finite-dimensional
algebra, the sum of the dimensions of the quotients is at most the dimension
of the algebra. -/
theorem sum_finrank_quotients_le_of_pairwise_isCoprime
    {K : Type u} {A : Type v} {ι : Type w}
    [Field K] [CommRing A] [Algebra K A] [Fintype ι]
    [Module.Finite K A]
    (I : ι → Ideal A) (hI : Pairwise (IsCoprime on I)) :
    (∑ i, Module.finrank K (A ⧸ I i)) ≤ Module.finrank K A := by
  let f : A →ₗ[K] ∀ i, A ⧸ I i :=
    LinearMap.pi fun i ↦ (Ideal.Quotient.mkₐ K (I i)).toLinearMap
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective hI x
    refine ⟨a, ?_⟩
    funext i
    exact ha i
  calc
    (∑ i, Module.finrank K (A ⧸ I i)) =
        Module.finrank K (∀ i, A ⧸ I i) :=
      (Module.finrank_pi_fintype K).symm
    _ = Module.finrank K (LinearMap.range f) := by
      rw [LinearMap.range_eq_top.mpr hf,
        finrank_top K (∀ i, A ⧸ I i)]
    _ ≤ Module.finrank K A := f.finrank_range_le

/-- Applied to every maximal ideal of a finite-dimensional commutative
algebra, the preceding inequality bounds the total degree of all reduced
Artinian components by the rank of the finite algebra. -/
theorem sum_finrank_maximal_quotients_le
    (K : Type u) (A : Type v)
    [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] :
    letI : IsArtinianRing A := IsArtinianRing.of_finite K A
    letI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
    (∑ P : MaximalSpectrum A,
      Module.finrank K (A ⧸ P.asIdeal)) ≤ Module.finrank K A := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  letI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  apply sum_finrank_quotients_le_of_pairwise_isCoprime
  intro P Q hPQ
  exact Ideal.isCoprime_iff_sup_eq.mpr <|
    P.isMaximal.coprime_of_ne Q.isMaximal fun h ↦
      hPQ (MaximalSpectrum.ext h)

end

end TranslatedDepthSeven
