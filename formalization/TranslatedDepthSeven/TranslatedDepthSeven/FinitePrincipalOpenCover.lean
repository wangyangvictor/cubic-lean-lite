import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Finite principal-open covers from explicit denominators

The relative elimination argument must eventually produce explicit chart
denominators.  This file records the elementary algebraic part of that
passage.  If a (possibly infinite) set of denominators generates the unit
ideal, finitely many already do so.  Under every specialization into a
nontrivial ring, at least one member of that finite list remains nonzero.

This is only the finite-cover mechanism.  It does not assert that any
particular Noether projection is finite or birational on one of the charts,
nor does it bound the coefficients of the selected denominators.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u v w

/-- Algebraic quasi-compactness for a cover by principal opens: if a set of
elements generates the unit ideal, a finite subset already generates it. -/
theorem exists_finset_span_eq_top_of_span_eq_top
    {R : Type u} [CommSemiring R] {S : Set R}
    (hS : Ideal.span S = ⊤) :
    ∃ T : Finset R, (T : Set R) ⊆ S ∧ Ideal.span (T : Set R) = ⊤ := by
  classical
  have hOne : (1 : R) ∈ Ideal.span S := by
    rw [hS]
    simp
  obtain ⟨T, hTS, hOneT⟩ := Submodule.mem_span_finite_of_mem_span hOne
  exact ⟨T, hTS, (Ideal.eq_top_iff_one _).mpr hOneT⟩

/-- If finitely many elements generate the unit ideal, then after every ring
specialization to a nontrivial ring at least one of them is nonzero. -/
theorem exists_mem_map_ne_zero_of_finset_span_eq_top
    {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Nontrivial A]
    (T : Finset R) (hT : Ideal.span (T : Set R) = ⊤)
    (φ : R →+* A) :
    ∃ f ∈ T, φ f ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  have hle : Ideal.span (T : Set R) ≤ RingHom.ker φ := by
    apply Ideal.span_le.mpr
    intro f hf
    exact RingHom.mem_ker.mpr (h f hf)
  have htop : (⊤ : Ideal R) ≤ RingHom.ker φ := by
    simpa [hT] using hle
  have hOne : φ 1 = 0 := RingHom.mem_ker.mp (htop (by simp))
  exact one_ne_zero (by simpa only [map_one] using hOne)

/-- A finite polynomial family whose principal opens cover affine space has
a member nonvanishing at every displayed point. -/
theorem exists_polynomial_chart_nonzero_at_point
    {K : Type u} {A : Type v} {σ : Type w}
    [CommSemiring K] [CommSemiring A] [Nontrivial A]
    (T : Finset (MvPolynomial σ K))
    (hT : Ideal.span (T : Set (MvPolynomial σ K)) = ⊤)
    (z : σ → A) (φ : K →+* A) :
    ∃ f ∈ T, MvPolynomial.eval₂Hom φ z f ≠ 0 :=
  exists_mem_map_ne_zero_of_finset_span_eq_top T hT
    (MvPolynomial.eval₂Hom φ z)

/-- Combined finite extraction and specialization statement for a possibly
infinite collection of polynomial chart denominators. -/
theorem exists_finite_polynomial_principalOpen_subcover
    {K : Type u} {σ : Type v} [CommSemiring K]
    {S : Set (MvPolynomial σ K)}
    (hS : Ideal.span S = ⊤) :
    ∃ T : Finset (MvPolynomial σ K),
      (T : Set (MvPolynomial σ K)) ⊆ S ∧
      Ideal.span (T : Set (MvPolynomial σ K)) = ⊤ ∧
      ∀ {A : Type w} [CommSemiring A] [Nontrivial A]
        (z : σ → A) (φ : K →+* A),
        ∃ f ∈ T, MvPolynomial.eval₂Hom φ z f ≠ 0 := by
  obtain ⟨T, hTS, hT⟩ := exists_finset_span_eq_top_of_span_eq_top hS
  refine ⟨T, hTS, hT, ?_⟩
  intro A _ _ z φ
  exact exists_polynomial_chart_nonzero_at_point T hT z φ

end

end TranslatedDepthSeven
