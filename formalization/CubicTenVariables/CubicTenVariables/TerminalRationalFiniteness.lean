import CubicTenVariables.TerminalTenBound
import CubicTenVariables.TerminalProjectiveDimension
import HessianTheorem11.ReducedStrictDimension

/-!
Actual rational bad normals, not just their closure, form finitely many
punctured rational lines in ten variables. The proof uses the dimension-one
rational closure, its actual cone components, and density of the original
rational generators. Parameter closedness and equality of rational points
with a geometric closure are neither assumed nor needed.
-/

noncomputable section
namespace CubicTenVariables.TerminalRationalFiniteness
open MvPolynomial HessianTheorem11 Module
open RationalConeClosure RationalConeComponents RationalClosureIdempotent
open TerminalSectionIncidence TerminalProjectiveDimension BibleProjectiveGeometry

/-- A nonzero line in a closed irreducible cone of dimension at most one
is the whole component, by strict dimension decrease for proper inclusions. -/
theorem irreducible_cone_eq_line {n : ℕ} (Z : Set (GeometricPoint n))
    (hZ : AlgebraicallyClosedSet Z) (hiZ : GeometricallyIrreducible Z)
    (hcZ : IsAffineCone Z) (hdZ : affineDimension Z ≤ 1)
    (z : GeometricPoint n) (hz : z ∈ Z) (hz0 : z ≠ 0) :
    Z = (Submodule.span GeometricField {z} : Set (GeometricPoint n)) := by
  have hsub : (Submodule.span GeometricField {z} : Set (GeometricPoint n)) ⊆ Z := by
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact hcZ a z hz
  apply (Set.Subset.antisymm_iff).mpr
  refine ⟨?_, hsub⟩
  by_contra hnot
  have hne : (Submodule.span GeometricField {z} : Set (GeometricPoint n)) ≠ Z := by
    intro h
    exact hnot (h ▸ Set.Subset.refl _)
  have hlt := ReducedStrictDimension.proper_closed _ Z
    (algebraicallyClosedSet_submodule _) hZ hiZ
    (Set.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  rw [affineDimension_submodule_from_generic_rank Unconditional.genericRankOpen,
    finrank_span_singleton hz0] at hlt
  exact (not_lt_of_ge hdZ) hlt

/-- Proportional rational vectors are already proportional over Q, even
if their given proportionality scalar lives in the geometric field. -/
theorem rational_proportionality {n : ℕ} (q v : Fin n → ℚ) (hq : q ≠ 0)
    (a : GeometricField) (ha : a • rationalEmbedding q = rationalEmbedding v) :
    ∃ b : ℚ, b • q = v := by
  obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hq (funext h)
  have hi' : algebraMap ℚ GeometricField (q i) ≠ 0 :=
    (map_ne_zero (algebraMap ℚ GeometricField)).mpr hi
  have hai := congrFun ha i
  change a * algebraMap ℚ GeometricField (q i) = algebraMap ℚ GeometricField (v i) at hai
  have he : a = algebraMap ℚ GeometricField (v i / q i) := by
    rw [map_div₀]
    exact (eq_div_iff hi').mpr hai
  refine ⟨v i / q i, rationalEmbedding_injective ?_⟩
  rw [rationalEmbedding_smul, ← he]
  exact ha

/-- Each nonzero component contains an original nonzero rational generator,
not just a rational point acquired on taking closure. -/
theorem component_rational_generator {n : ℕ} (C Z : Set (GeometricPoint n))
    (hZ : IsIrreducibleComponent (rationalConeClosure C) Z)
    (hn : ¬ Z ⊆ {0}) :
    ∃ q : Fin n → ℚ, q ≠ 0 ∧ rationalEmbedding q ∈ C ∧ rationalEmbedding q ∈ Z := by
  obtain ⟨z, hz, hz0⟩ := Set.not_subset.mp hn
  change z ≠ 0 at hz0
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hz0 (funext h)
  let A := rationalEmbedding '' (rationalPoints C ∪ {0})
  have hd : geometricClosure (A ∩ Z) = Z :=
    closure_inter_component_of_dense _ A Z (rationalConeClosure_closed C)
      (closure_rational_generators C) hZ
  obtain ⟨x, hx, hxne⟩ := exists_on_dense_set_eval_ne_zero hd (X i) ⟨z, hz, by simpa using hi⟩
  obtain ⟨⟨q, hq, rfl⟩, hqZ⟩ := hx
  have hq0 : q ≠ 0 := by
    intro he
    subst q
    simp at hxne
  refine ⟨q, hq0, ?_, hqZ⟩
  exact hq.resolve_right hq0

/-- Any geometric cone whose rational closure has dimension at most one
has precisely a finite union of punctured rational lines as its nonzero
rational points. This does not require the original cone to be closed. -/
theorem exists_finite_rational_line_generators {n : ℕ}
    (C : Set (GeometricPoint n)) (hcone : IsAffineCone C)
    (hd : affineDimension (rationalConeClosure C) ≤ 1) :
    ∃ D : Finset (Fin n → ℚ),
      (∀ q ∈ D, rationalEmbedding q ∈ C ∧ q ≠ 0) ∧
      ∀ v : Fin n → ℚ,
        (rationalEmbedding v ∈ C ∧ v ≠ 0) ↔
          ∃ q ∈ D, ∃ a : ℚ, a ≠ 0 ∧ v = a • q := by
  classical
  obtain ⟨c, Z, hcover, hZ⟩ := ReducedMaximalComponent.finite_components
    (rationalConeClosure C) (rationalConeClosure_closed C)
  have hgen : ∀ i : Fin c, ∃ q : Fin n → ℚ,
      (q = 0 ∨ rationalEmbedding q ∈ C) ∧
      ∀ x ∈ Z i, ∃ a : GeometricField, a • rationalEmbedding q = x := by
    intro i
    by_cases hz : Z i ⊆ {0}
    · refine ⟨0, Or.inl rfl, ?_⟩
      intro x hx
      have hx0 : x = 0 := hz hx
      exact ⟨0, by simp [hx0]⟩
    · obtain ⟨q, hq0, hqC, hqZ⟩ := component_rational_generator C (Z i) (hZ i) hz
      have hline := irreducible_cone_eq_line (Z i) (hZ i).closed (hZ i).irreducible
        ((hZ i).isAffineCone Unconditional.concentrationGeometry.toAffineComponentsInput
          (rationalConeClosure_closed C) (rationalConeClosure_isAffineCone C hcone))
        ((affineDimension_mono (hZ i).subset).trans hd)
        (rationalEmbedding q) hqZ ((rationalEmbedding_eq_zero_iff q).not.mpr hq0)
      refine ⟨q, Or.inr hqC, ?_⟩
      intro x hx
      apply Submodule.mem_span_singleton.mp
      change x ∈ (Submodule.span GeometricField {rationalEmbedding q} : Set (GeometricPoint n))
      rw [← hline]
      exact hx
  choose q hqC hqspan using hgen
  let D := (Finset.univ.image q).filter (fun v => v ≠ 0)
  have hD : ∀ v ∈ D, rationalEmbedding v ∈ C ∧ v ≠ 0 := by
    intro v hv
    obtain ⟨hv, hv0⟩ := Finset.mem_filter.mp hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨(hqC i).resolve_left hv0, hv0⟩
  refine ⟨D, hD, ?_⟩
  intro v
  constructor
  · rintro ⟨hv, hv0⟩
    have hvR : rationalEmbedding v ∈ rationalConeClosure C :=
      rational_generators_subset C ⟨v, Or.inl hv, rfl⟩
    rw [hcover] at hvR
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hvR
    obtain ⟨a, ha⟩ := hqspan i _ hi
    have hqi : q i ≠ 0 := by
      intro h0
      rw [h0, rationalEmbedding_zero, smul_zero] at ha
      exact hv0 ((rationalEmbedding_eq_zero_iff v).mp ha.symm)
    obtain ⟨b, hb⟩ := rational_proportionality (q i) v hqi a ha
    refine ⟨q i, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩,
      hqi⟩, b, ?_, hb.symm⟩
    intro h0
    exact hv0 (by simpa [h0] using hb.symm)
  · rintro ⟨q, hq, a, ha, rfl⟩
    refine ⟨?_, smul_ne_zero ha (hD q hq).2⟩
    rw [rationalEmbedding_smul]
    exact hcone _ _ (hD q hq).1

/-- The source's actual fourth bad-normal set is exactly a finite union
of punctured rational lines, with generators themselves in that set. -/
theorem ten_fourth_bad_normals_finite_lines (F : AnisotropicCubic 10) :
    ∃ D : Finset (Fin 10 → ℚ),
      (∀ q ∈ D, q ≠ 0 ∧ (4 : Dimension) ≤ projectiveDimension
        (sectionSingularFiber (geometricPolynomial F.polynomial) (rationalEmbedding q))) ∧
      ∀ v : Fin 10 → ℚ,
        ((4 : Dimension) ≤ projectiveDimension
          (sectionSingularFiber (geometricPolynomial F.polynomial) (rationalEmbedding v)) ∧
          v ≠ 0) ↔ ∃ q ∈ D, ∃ a : ℚ, a ≠ 0 ∧ v = a • q := by
  obtain ⟨D, hD, hcover⟩ := exists_finite_rational_line_generators
    (TerminalBadNormals.badNormals (geometricPolynomial F.polynomial) 4)
    (TerminalBadNormals.badNormals_isAffineCone _ _)
    (TerminalTenBound.rational_fourth_stratum_dimension_le_one F)
  have he (v : Fin 10 → ℚ) : rationalEmbedding v ∈
      TerminalBadNormals.badNormals (geometricPolynomial F.polynomial) 4 ↔
      (4 : Dimension) ≤ projectiveDimension
        (sectionSingularFiber (geometricPolynomial F.polynomial) (rationalEmbedding v)) :=
    (sectionSingularFiber_projective_threshold _ (geometric_homogeneous F.homogeneous)
      (rationalEmbedding v) 4).symm
  refine ⟨D, ?_, ?_⟩
  · intro q hq
    exact ⟨(hD q hq).2, (he q).mp (hD q hq).1⟩
  · intro v
    rw [← he]
    exact hcover v

/-- Finiteness of the actual rational projective bad locus, without
identifying it with the rational points of a larger closed parameter set. -/
theorem ten_fourth_projective_bad_normals_finite (F : AnisotropicCubic 10) :
    {p : Projectivization ℚ (Fin 10 → ℚ) |
      ∃ (v : Fin 10 → ℚ) (hv : v ≠ 0),
        Projectivization.mk ℚ v hv = p ∧
          (4 : Dimension) ≤ projectiveDimension
            (sectionSingularFiber (geometricPolynomial F.polynomial) (rationalEmbedding v))}.Finite := by
  classical
  obtain ⟨D, hD, hcover⟩ := ten_fourth_bad_normals_finite_lines F
  let f : {q // q ∈ D} → Projectivization ℚ (Fin 10 → ℚ) :=
    fun q => Projectivization.mk ℚ q.val (hD q.val q.property).1
  apply (Set.finite_range f).subset
  rintro p ⟨v, hv, rfl, hbad⟩
  obtain ⟨q, hq, a, _, ha⟩ := (hcover v).mp ⟨hbad, hv⟩
  refine Set.mem_range.mpr ⟨⟨q, hq⟩, ?_⟩
  exact ((Projectivization.mk_eq_mk_iff' ℚ v q hv (hD q hq).1).mpr ⟨a, ha.symm⟩).symm

end CubicTenVariables.TerminalRationalFiniteness
