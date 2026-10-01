import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraTower
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Finite-dimensional size of one monic triangular step

A monic triangular equation adjoins one new coordinate.  Its residue classes
`1, z, ..., z^(e-1)` form a basis over the preceding coordinate algebra.
Combining that power basis with a basis over the ground field gives the exact
multiplicative dimension formula below.  Iterating this lemma is the literal
algebra behind the product-of-degrees bound for a monic triangular system.
-/

namespace TranslatedDepthSeven

noncomputable section

open Polynomial

/-- Adjoining a root of a monic polynomial multiplies the dimension over the
ground field by the degree of that polynomial.  The intermediate algebra need
not be a field or a domain. -/
theorem finrank_adjoinRoot_eq_finrank_mul_natDegree
    {K B : Type*} [Field K] [CommRing B] [Algebra K B]
    [Module.Finite K B] (g : B[X]) (hg : g.Monic) :
    Module.finrank K (AdjoinRoot g) =
      Module.finrank K B * g.natDegree := by
  let b : Module.Basis (Fin (Module.finrank K B)) K B := Module.finBasis K B
  let c : Module.Basis (Fin g.natDegree) B (AdjoinRoot g) :=
    (AdjoinRoot.powerBasis' hg).basis
  let bc : Module.Basis
      (Fin (Module.finrank K B) × Fin g.natDegree) K (AdjoinRoot g) :=
    b.smulTower c
  calc
    Module.finrank K (AdjoinRoot g) =
        Fintype.card
          (Fin (Module.finrank K B) × Fin g.natDegree) :=
      Module.finrank_eq_card_basis bc
    _ = Module.finrank K B * g.natDegree := by simp

/-- In particular, one monic triangular step supplies a finite-dimensional
ground-field algebra. -/
theorem finiteDimensional_adjoinRoot_of_monic
    {K B : Type*} [Field K] [CommRing B] [Algebra K B]
    [Module.Finite K B] (g : B[X]) (hg : g.Monic) :
    Module.Finite K (AdjoinRoot g) := by
  let b : Module.Basis (Fin (Module.finrank K B)) K B := Module.finBasis K B
  let c : Module.Basis (Fin g.natDegree) B (AdjoinRoot g) :=
    (AdjoinRoot.powerBasis' hg).basis
  exact Module.Finite.of_basis (b.smulTower c)

/-- The first genuinely triangular case: two successive monic equations give
the product of their degrees.  Further triangular steps are obtained by the
same literal induction. -/
theorem finrank_two_monic_steps
    {K B : Type*} [Field K] [CommRing B] [Algebra K B]
    [Module.Finite K B] (g : B[X]) (hg : g.Monic)
    (h : (AdjoinRoot g)[X]) (hh : h.Monic) :
    Module.finrank K (AdjoinRoot h) =
      Module.finrank K B * g.natDegree * h.natDegree := by
  letI : Module.Finite K (AdjoinRoot g) :=
    finiteDimensional_adjoinRoot_of_monic g hg
  rw [finrank_adjoinRoot_eq_finrank_mul_natDegree h hh,
    finrank_adjoinRoot_eq_finrank_mul_natDegree g hg]

end

end TranslatedDepthSeven
