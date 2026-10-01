import CubicTenVariables.Literature.ProjectiveMicrolocalCertificate
import CubicTenVariables.GaussGraphSmooth
import CubicTenVariables.GaussTerminalBound

/-! The two actual closed Gauss graphs have the same fibers at every
nonzero normal. Multiplication by a nonzero normal coordinate removes the
extra zero-normal generators of the older graph. No irreducibility,
anisotropy or literature premise is used. -/

noncomputable section
namespace CubicTenVariables.MicrolocalGaussBridge
open MvPolynomial HessianTheorem11 TerminalFiberCoordinates
open ReducedKernelTangent AffineProductGeometry

private def oldIndex (n : ℕ) : Fin n ⊕ Fin n → Fin (n+n) :=
  Sum.elim (Fin.natAdd n) (Fin.castAdd n)

private def newIndex (n : ℕ) : Fin (n+n) → Fin n ⊕ Fin n :=
  Fin.addCases Sum.inr Sum.inl

private theorem eval_oldIndex {n : ℕ} (P : MvPolynomial (Fin n ⊕ Fin n) GeometricField)
    (x v : GeometricPoint n) :
    eval (join x v) (rename (oldIndex n) P) = eval (Sum.elim v x) P := by
  rw [eval_rename]
  apply congrArg (fun z => eval z P)
  funext i
  cases i <;> simp only [Function.comp_apply, oldIndex, Sum.elim_inl,
    Sum.elim_inr, join, Fin.addCases_left, Fin.addCases_right]

private theorem eval_newIndex {n : ℕ} (P : GeometricPolynomial (n+n))
    (x v : GeometricPoint n) :
    eval (Sum.elim v x) (rename (newIndex n) P) = eval (join x v) P := by
  rw [eval_rename]
  apply congrArg (fun z => eval z P)
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp only [Function.comp_apply, newIndex, join, Fin.addCases_left,
      Fin.addCases_right, Sum.elim_inl, Sum.elim_inr]

theorem gradient_map {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (x : GeometricPoint n) :
    gradient (map (Int.castRingHom GeometricField) F) x =
      ProjectiveMicrolocalData.gradient F GeometricField x := by
  ext i
  simp only [HessianTheorem11.gradient, ProjectiveMicrolocalData.gradient, pderiv_map, eval_map]

/-- The new closed graph is contained in the old graph on every fiber,
including the zero-normal fiber. This direction needs no homogeneity. -/
theorem new_fiber_subset_old {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (v : GeometricPoint n) :
    ProjectiveMicrolocalData.gaussFiberClosure F GeometricField v ⊆
      GaussTerminalBound.fiber (map (Int.castRingHom GeometricField) F) v := by
  intro x hx
  rw [GaussTerminalBound.fiber, Set.mem_setOf_eq, GaussGraph.graph_eq_closure_literal]
  apply mem_zeroLocus_iff.mpr
  intro P hP
  have hrename : rename (newIndex n) P ∈ vanishingIdeal GeometricField
      (ProjectiveMicrolocalData.gaussGraph F GeometricField) := by
    apply mem_vanishingIdeal_iff.mpr
    intro z hz
    rcases hz with ⟨hx0, hF, hg, a, ha, hv⟩
    have hz : z = Sum.elim (fun i => z (.inl i)) (fun i => z (.inr i)) := by
      ext i
      cases i <;> rfl
    change eval z (rename (newIndex n) P) = 0
    rw [hz, eval_newIndex]
    apply (mem_vanishingIdeal_iff.mp hP)
    refine ⟨fun i => z (.inr i), ?_, a, ?_⟩
    · simpa only [eval_map] using hF
    · rw [gradient_map, ← hv]
  have hh := mem_zeroLocus_iff.mp hx _ hrename
  change eval (Sum.elim v x) (rename (newIndex n) P) = 0 at hh
  rw [eval_newIndex] at hh
  exact hh

/-- At a nonzero normal, the old generators excluded from the new graph
cannot contribute an additional point after taking closure. -/
theorem old_fiber_subset_new {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (v : GeometricPoint n) (hv : v ≠ 0) :
    GaussTerminalBound.fiber (map (Int.castRingHom GeometricField) F) v ⊆
      ProjectiveMicrolocalData.gaussFiberClosure F GeometricField v := by
  intro x hx
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  apply mem_zeroLocus_iff.mpr
  intro P hP
  change eval (Sum.elim v x) P = 0
  let Q : GeometricPolynomial (n+n) :=
    normalProjection n i * rename (oldIndex n) P
  have hQ : Q ∈ vanishingIdeal GeometricField
      {p | ∃ y : GeometricPoint n,
        eval y (map (Int.castRingHom GeometricField) F) = 0 ∧
        ∃ a : GeometricField,
          p = join y (a • gradient (map (Int.castRingHom GeometricField) F) y)} := by
    apply mem_vanishingIdeal_iff.mpr
    rintro p ⟨y, hy, a, rfl⟩
    change eval _ (normalProjection n i * rename (oldIndex n) P) = 0
    rw [map_mul, eval_oldIndex]
    by_cases hn : a • gradient (map (Int.castRingHom GeometricField) F) y = 0
    · have hz : eval (join y (a • gradient (map (Int.castRingHom GeometricField) F) y))
          (normalProjection n i) = 0 := by
        change (polynomialMap (normalProjection n) _) i = 0
        rw [normal_join, hn]
        rfl
      rw [hz, zero_mul]
    · have ha : a ≠ 0 := by
        intro h
        apply hn
        simp [h]
      have hg : gradient (map (Int.castRingHom GeometricField) F) y ≠ 0 := by
        intro h
        apply hn
        simp [h]
      have hnew : Sum.elim
          (a • gradient (map (Int.castRingHom GeometricField) F) y) y ∈
          ProjectiveMicrolocalData.gaussGraph F GeometricField := by
        refine ⟨GaussGraph.gradient_ne_zero_point_ne_zero _ (hF.map _) hg,
          ?_, ?_, a, ha, ?_⟩
        · simpa only [eval_map] using hy
        · simpa only [gradient_map] using hg
        · simpa only [Sum.elim_inl, Sum.elim_inr] using
            congrArg (fun g => a • g) (gradient_map F y)
      have hpzero := mem_vanishingIdeal_iff.mp hP _ hnew
      change eval _ P = 0 at hpzero
      rw [hpzero, mul_zero]
  have hx' : join x v ∈ geometricClosure
      {p | ∃ y : GeometricPoint n,
        eval y (map (Int.castRingHom GeometricField) F) = 0 ∧
        ∃ a : GeometricField,
          p = join y (a • gradient (map (Int.castRingHom GeometricField) F) y)} := by
    change join x v ∈ GaussGraph.graph _ at hx
    rwa [GaussGraph.graph_eq_closure_literal] at hx
  have hh := mem_zeroLocus_iff.mp hx' _ hQ
  change eval (join x v) (normalProjection n i * rename (oldIndex n) P) = 0 at hh
  rw [map_mul, eval_oldIndex] at hh
  have he : eval (join x v) (normalProjection n i) = v i :=
    congrFun (normal_join x v) i
  rw [he] at hh
  exact (mul_eq_zero.mp hh).resolve_left hi

/-- Equality of the literal point fibers of the two closed Gauss graphs.
The cubic may be reducible, nonreduced or zero. -/
theorem fiber_eq {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (v : GeometricPoint n) (hv : v ≠ 0) :
    GaussTerminalBound.fiber (map (Int.castRingHom GeometricField) F) v =
      ProjectiveMicrolocalData.gaussFiberClosure F GeometricField v :=
  Set.Subset.antisymm (old_fiber_subset_new F hF v hv) (new_fiber_subset_old F v)

end CubicTenVariables.MicrolocalGaussBridge
