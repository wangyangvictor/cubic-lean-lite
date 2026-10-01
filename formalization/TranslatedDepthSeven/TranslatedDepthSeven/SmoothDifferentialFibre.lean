import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.LocalRing.Module

/-!
# Differential fibres of standard-smooth algebras

This file records the part of the smooth-local dimension calculation that is
already available in Mathlib: standard smoothness of a specified relative
dimension determines the dimension of every residue differential fibre.

It deliberately makes no comparison with Krull dimension.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct
open KaehlerDifferential

universe u v

/-- A standard-smooth algebra of relative dimension `n` has residual
Kaehler differential fibre of dimension `n` at a local target. -/
theorem finrank_residueTensor_kaehler_eq_of_isStandardSmoothOfRelativeDimension
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Nontrivial S]
    [Algebra R S] [IsLocalRing S] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    Module.finrank (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField S ⊗[S] Ω[S⁄R]) = n := by
  haveI : Algebra.IsStandardSmooth R S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  haveI : Module.Free S Ω[S⁄R] := inferInstance
  haveI : Module.Finite S Ω[S⁄R] := inferInstance
  rw [Module.finrank_baseChange]
  apply Nat.cast_injective (R := Cardinal)
  rw [Module.finrank_eq_rank]
  exact Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n

/-- For an essentially finite type formally smooth algebra over a local ring,
the module of Kaehler differentials is finite free.  This does not identify
its rank with the Krull dimension. -/
theorem free_kaehlerDifferential_of_formallySmooth_essFiniteType_local
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [IsLocalRing S] [Algebra.EssFiniteType R S]
    [Algebra.FormallySmooth R S] :
    Module.Free S Ω[S⁄R] := by
  haveI : Module.Finite S Ω[S⁄R] := inferInstance
  exact Module.free_of_flat_of_isLocalRing

end

end TranslatedDepthSeven
