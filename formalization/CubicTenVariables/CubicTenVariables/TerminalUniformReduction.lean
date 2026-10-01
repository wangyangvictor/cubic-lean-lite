import CubicTenVariables.TerminalChartSpreading
import CubicTenVariables.TerminalModelIdentification

/-! Fixed integral models of the actual ten-variable terminal cones, with
one exceptional integer before every prime, extension field and normal.
Only the generic spreading corollary is a literature premise. Model
construction, characteristic-zero identifications, dimensions and counts
are supplied by the previously proved results. -/

noncomputable section
namespace CubicTenVariables.TerminalUniformReduction
open MvPolynomial HessianTheorem11 TerminalSectionIncidence
open TerminalIntegralClosureModels TerminalBadParameterClosed

/-- The rational and geometric coefficient maps agree with direct reduction
of the original integral cubic. -/
theorem geometric_integral_map {n : ℕ} (F : MvPolynomial (Fin n) ℤ) :
    geometricPolynomial (map (Int.castRingHom ℚ) F) =
      map (Int.castRingHom GeometricField) F := by
  unfold geometricPolynomial
  rw [map_map, RingHom.ext_int ((algebraMap ℚ GeometricField).comp
    (Int.castRingHom ℚ)) (Int.castRingHom GeometricField)]

/-- The fixed models and one exceptional integer work simultaneously for
B4 and W5. The actual reduced Gauss graph is the closure of the literal
scalar-gradient image; no independently supplied bad-locus model is used.
The displayed model dimensions are affine, hence at most four and three. -/
theorem exists_terminal_models
    (spread : Literature.FiberDimensionContainmentSpreading)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ mB mW : ℕ,
    ∃ B : Fin mB → MvPolynomial (Fin 10) ℤ,
    ∃ W : Fin mW → MvPolynomial (Fin 10) ℤ,
    ∃ D CB CW : ℕ, 1 ≤ D ∧ 1 ≤ CB ∧ 1 ≤ CW ∧
      (∀ v : GeometricPoint 10,
        (∀ i, eval₂ (Int.castRingHom GeometricField) v (B i)=0) ↔
          v=0 ∨ (4 : Dimension) ≤ BibleProjectiveGeometry.projectiveDimension
            (sectionSingularFiber (map (Int.castRingHom GeometricField) F) v)) ∧
      (∀ v : GeometricPoint 10,
        (∀ i, eval₂ (Int.castRingHom GeometricField) v (W i)=0) ↔
          v=0 ∨ (5 : Dimension) ≤ BibleProjectiveGeometry.projectiveDimension
            (GaussTerminalBound.fiber (map (Int.castRingHom GeometricField) F) v)) ∧
      (∀ p : ℕ, p.Prime →
        Nat.card {v : Fin 10 → ZMod p //
          ∀ i, eval₂ (Int.castRingHom (ZMod p)) v (B i)=0} ≤ CB*p^4 ∧
        Nat.card {v : Fin 10 → ZMod p //
          ∀ i, eval₂ (Int.castRingHom (ZMod p)) v (W i)=0} ≤ CW*p^3) ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ D → ∀ (K : Type) [Field K] [CharP K p],
        ringKrullDim (MvPolynomial (Fin 10) K ⧸
          FixedEquationNormalization.equationIdeal B K) ≤ (4 : Dimension) ∧
        ringKrullDim (MvPolynomial (Fin 10) K ⧸
          FixedEquationNormalization.equationIdeal W K) ≤ (3 : Dimension) ∧
        ringKrullDim (MvPolynomial (Fin 10) K ⧸ vanishingIdeal K
          {v | ∀ i, eval₂ (Int.castRingHom K) v (B i)=0}) ≤ (4 : Dimension) ∧
        ringKrullDim (MvPolynomial (Fin 10) K ⧸ vanishingIdeal K
          {v | ∀ i, eval₂ (Int.castRingHom K) v (W i)=0}) ≤ (3 : Dimension) ∧
        (∀ v : Fin 10 → K,
          (4 : Dimension) ≤ ReducedGaussSection.projectiveDimension
            (sectionSingularFiber (map (Int.castRingHom K) F) v) →
          ∀ i, eval₂ (Int.castRingHom K) v (B i)=0) ∧
        (∀ v : Fin 10 → K,
          (5 : Dimension) ≤ ReducedGaussSection.projectiveDimension
            (ReducedGaussSection.fiber (map (Int.castRingHom K) F) v) →
          ∀ i, eval₂ (Int.castRingHom K) v (W i)=0) := by
  let A : AnisotropicCubic 10 := ⟨map (Int.castRingHom ℚ) F,hF.map _,hA⟩
  have hgeom : geometricPolynomial A.polynomial =
      map (Int.castRingHom GeometricField) F := geometric_integral_map F
  obtain ⟨mB,B,_hBI,hB,hBb⟩ := TerminalFixedModelBounds.exists_section_model A
  obtain ⟨mW,W,_hWI,hW,hWb⟩ := TerminalFixedModelBounds.exists_gauss_model A
  have hBraw (v : GeometricPoint 10) :
      (∀ i, eval₂ (Int.castRingHom GeometricField) v (B i)=0) ↔
        v=0 ∨ (4 : Dimension) ≤ BibleProjectiveGeometry.projectiveDimension
          (sectionSingularFiber (map (Int.castRingHom GeometricField) F) v) := by
    rw [← hB v, mem_sectionClosure_iff A.polynomial A.homogeneous 4 v, hgeom]
    norm_num only [Nat.cast_ofNat]
  have hWraw (v : GeometricPoint 10) :
      (∀ i, eval₂ (Int.castRingHom GeometricField) v (W i)=0) ↔
        v=0 ∨ (5 : Dimension) ≤ BibleProjectiveGeometry.projectiveDimension
          (GaussTerminalBound.fiber (map (Int.castRingHom GeometricField) F) v) := by
    rw [← hW v, mem_ten_gaussClosure_iff A v, hgeom]
  obtain ⟨DBs,hDBs,hBs⟩ := TerminalChartSpreading.exists_section_bound spread F B 4
    (fun v hv => (hBraw v).mpr (Or.inr hv))
  have hWgeneric (v : GeometricPoint 10)
      (hv : (5 : Dimension) ≤ BibleProjectiveGeometry.projectiveDimension
        (sectionSingularFiber (map (Int.castRingHom GeometricField) F) v)) :
      ∀ i, eval₂ (Int.castRingHom GeometricField) v (W i)=0 := by
    apply (hW v).mp
    rw [← TerminalFifthComparison.ten_fifth_closures_eq A]
    apply (mem_sectionClosure_iff A.polynomial A.homogeneous 5 v).mpr
    right
    simpa only [hgeom,Nat.cast_ofNat] using hv
  obtain ⟨DWs,hDWs,hWs⟩ :=
    TerminalChartSpreading.exists_section_bound spread F W 5 hWgeneric
  obtain ⟨DB,CB,hDB,hCB,hBc,hBd⟩ := hBb
  obtain ⟨DW,CW,hDW,hCW,hWc,hWd⟩ := hWb
  refine ⟨mB,mW,B,W,(DB*DW)*(DBs*DWs),CB,CW,
    Nat.mul_pos (Nat.mul_pos hDB hDW) (Nat.mul_pos hDBs hDWs),
    hCB,hCW,hBraw,hWraw,fun p hp => ⟨hBc p hp,hWc p hp⟩,?_⟩
  intro p hp hgood K _ _
  have hDBgood : ¬ p ∣ DB := fun hd => hgood (dvd_trans hd
    (dvd_trans (dvd_mul_right DB DW) (dvd_mul_right (DB*DW) (DBs*DWs))))
  have hDWgood : ¬ p ∣ DW := fun hd => hgood (dvd_trans hd
    (dvd_trans (dvd_mul_left DW DB) (dvd_mul_right (DB*DW) (DBs*DWs))))
  have hDBsgood : ¬ p ∣ DBs := fun hd => hgood (dvd_trans hd
    (dvd_trans (dvd_mul_right DBs DWs) (dvd_mul_left (DBs*DWs) (DB*DW))))
  have hDWsgood : ¬ p ∣ DWs := fun hd => hgood (dvd_trans hd
    (dvd_trans (dvd_mul_left DWs DBs) (dvd_mul_left (DBs*DWs) (DB*DW))))
  have hb := hBd p hp hDBgood K
  have hw := hWd p hp hDWgood K
  refine ⟨hb.1,hw.1,hb.2,hw.2,hBs p hp hDBsgood K,?_⟩
  intro v hv
  apply hWs p hp hDWsgood K v
  exact ReducedGaussSection.projective_threshold_section _ (hF.map _) v 5 hv

end CubicTenVariables.TerminalUniformReduction
