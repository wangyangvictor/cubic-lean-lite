import CubicTenVariables.GaussGraphProjection

/-! The affine Gauss graph is unchanged when its generators are restricted
to smooth, nonzero points of the cubic and nonzero normal scalars. -/

noncomputable section
namespace CubicTenVariables.GaussGraph
open MvPolynomial HessianTheorem11
open ReducedKernelTangent TerminalFiberCoordinates AffineProductGeometry

def smoothSource {n : ℕ} (F : GeometricPolynomial n) : Set (GeometricPoint (n+1)) :=
  {p | p ∈ source F ∧ gradient F (baseProjection n 1 p) ≠ 0 ∧
    fiberProjection n 1 p 0 ≠ 0}

theorem smoothSource_open {n : ℕ} (F : GeometricPolynomial n) :
    RelativelyOpenSet (source F) (smoothSource F) := by
  have hs : RelativelyOpenSet (source F)
      {p | p ∈ source F ∧ fiberProjection n 1 p 0 ≠ 0} := by
    refine ⟨polynomialHypersurface (linearCoordinatePolynomials (fiberProjection n 1) 0),
      polynomialHypersurface_closed _, ?_⟩
    have he : ∀ p, eval p (linearCoordinatePolynomials (fiberProjection n 1) 0) =
        fiberProjection n 1 p 0 := fun p =>
      congrFun (polynomialMap_linearCoordinatePolynomials (fiberProjection n 1) p) 0
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_diff, polynomialHypersurface, he]
  have ho := (source_nonsingular_open F).inter hs
  convert ho using 1
  ext p
  simp only [smoothSource, Set.mem_setOf_eq, Set.mem_inter_iff]
  tauto

theorem smoothSource_nonempty {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (hi : Irreducible F) : (smoothSource F).Nonempty := by
  obtain ⟨x, hx, hg, _, _, _⟩ := exists_smooth_cubic_point_avoiding_polynomial
    ReducedGenericRank.genericMatrixRankInput F hF hi 1
      (fun h => hi.not_isUnit (isUnit_of_dvd_one h))
  refine ⟨sourcePair x 1, ?_⟩
  simp only [smoothSource, Set.mem_setOf_eq, sourcePair_mem,
    base_sourcePair, scalar_sourcePair]
  exact ⟨hx, hg, one_ne_zero⟩

theorem smoothSource_dense {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (hi : Irreducible F) :
    geometricClosure (smoothSource F) = source F :=
  (smoothSource_open F).dense_of_nonempty (source_closed F) (source_irreducible F hi)
    (smoothSource_nonempty F hF hi)

theorem graph_eq_closure_smooth_image {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (hi : Irreducible F) :
    graph F = geometricClosure (polynomialMap (parametrization F) '' smoothSource F) := by
  apply Set.Subset.antisymm
  · apply geometricClosure_subset_closed _ (algebraicallyClosedSet_geometricClosure _)
    have hh := polynomialMap_image_closure_subset (parametrization F) (smoothSource F)
    rw [smoothSource_dense F hF hi] at hh
    exact hh
  · exact geometricClosure_mono (Set.image_mono (fun _ h => h.1))

theorem smooth_image_eq_literal {n : ℕ} (F : GeometricPolynomial n) :
    polynomialMap (parametrization F) '' smoothSource F =
      {p | ∃ x : GeometricPoint n, eval x F = 0 ∧ gradient F x ≠ 0 ∧
        ∃ a : GeometricField, a ≠ 0 ∧ p = join x (a • gradient F x)} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨baseProjection n 1 q, hq.1, hq.2.1, fiberProjection n 1 q 0,
      hq.2.2, parametrization_apply F q⟩
  · rintro ⟨x, hx, hg, a, ha, rfl⟩
    refine ⟨sourcePair x a, ?_, parametrization_sourcePair F x a⟩
    simp only [smoothSource, Set.mem_setOf_eq, sourcePair_mem,
      base_sourcePair, scalar_sourcePair]
    exact ⟨hx, hg, ha⟩

theorem gradient_ne_zero_point_ne_zero {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) {x : GeometricPoint n} (hx : gradient F x ≠ 0) : x ≠ 0 := by
  intro h
  subst x
  have hz := gradient_smul F hF 0 (0 : GeometricPoint n)
  norm_num at hz
  exact hx hz

/-- Literal generators use nonzero smooth points and nonzero normal scalars,
matching the affine bicone over the projective Gauss graph. -/
theorem graph_eq_closure_smooth_literal {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (hi : Irreducible F) :
    graph F = geometricClosure
      {p | ∃ x : GeometricPoint n, x ≠ 0 ∧ eval x F = 0 ∧ gradient F x ≠ 0 ∧
        ∃ a : GeometricField, a ≠ 0 ∧ p = join x (a • gradient F x)} := by
  rw [graph_eq_closure_smooth_image F hF hi, smooth_image_eq_literal]
  congr 1
  ext p
  constructor
  · rintro ⟨x, hx, hg, a, ha, hp⟩
    exact ⟨x, gradient_ne_zero_point_ne_zero F hF hg, hx, hg, a, ha, hp⟩
  · rintro ⟨x, _, hx, hg, a, ha, hp⟩
    exact ⟨x, hx, hg, a, ha, hp⟩

end CubicTenVariables.GaussGraph
