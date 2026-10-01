import TranslatedDepthSeven.FiniteAlgebraComponentRankMass
import TranslatedDepthSeven.FiniteFreeFibrePointCount
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Component mass in the generic fibre of a finite projection

Let `B → A` be a finite map with `B` a domain.  After passing to the
fraction field of `B`, the generic fibre is a finite-dimensional commutative
algebra.  The Chinese-remainder rank inequality therefore bounds the sum of
the residue-field ranks of all its reduced components by the rank of the
whole generic fibre.

If `D` displayed elements span `A` over `B`, scalar extension shows that the
same component mass is at most `D`.  This is the exact algebraic replacement
for the only component-degree mass estimate needed from a parameter space.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct

universe u v

/-- The total residue-field rank of the reduced components of a generic
finite fibre is at most the rank of that fibre. -/
theorem sum_finrank_genericFibre_maximal_quotients_le
    {B : Type u} {A : Type v}
    [CommRing B] [IsDomain B]
    [CommRing A] [Algebra B A] [Module.Finite B A] :
    let K := FractionRing B
    let G := K ⊗[B] A
    letI : IsArtinianRing G := IsArtinianRing.of_finite K G
    letI : Fintype (MaximalSpectrum G) := Fintype.ofFinite _
    (∑ P : MaximalSpectrum G,
      Module.finrank K (G ⧸ P.asIdeal)) ≤ Module.finrank K G := by
  dsimp only
  exact sum_finrank_maximal_quotients_le (FractionRing B)
    (FractionRing B ⊗[B] A)

/-- If `D` elements span the finite algebra before passing to the generic
fibre, then `D` also bounds the total residue-field rank of every reduced
generic component. -/
theorem sum_finrank_genericFibre_maximal_quotients_le_of_span_fin
    {B : Type u} {A : Type v}
    [CommRing B] [IsDomain B]
    [CommRing A] [Algebra B A] [Module.Finite B A]
    {D : ℕ} (s : Fin D → A)
    (hs : Submodule.span B (Set.range s) = ⊤) :
    let K := FractionRing B
    let G := K ⊗[B] A
    letI : IsArtinianRing G := IsArtinianRing.of_finite K G
    letI : Fintype (MaximalSpectrum G) := Fintype.ofFinite _
    (∑ P : MaximalSpectrum G,
      Module.finrank K (G ⧸ P.asIdeal)) ≤ D := by
  dsimp only
  letI : IsArtinianRing (FractionRing B ⊗[B] A) :=
    IsArtinianRing.of_finite (FractionRing B) (FractionRing B ⊗[B] A)
  letI : Fintype (MaximalSpectrum (FractionRing B ⊗[B] A)) :=
    Fintype.ofFinite _
  calc
    (∑ P : MaximalSpectrum (FractionRing B ⊗[B] A),
      Module.finrank (FractionRing B)
        ((FractionRing B ⊗[B] A) ⧸ P.asIdeal)) ≤
        Module.finrank (FractionRing B) (FractionRing B ⊗[B] A) :=
      sum_finrank_genericFibre_maximal_quotients_le
    _ ≤ D := finrank_scalarFibre_le_of_span_fin B (FractionRing B) A D s hs

end

end TranslatedDepthSeven
