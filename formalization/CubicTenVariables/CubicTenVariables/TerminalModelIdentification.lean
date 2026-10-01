import CubicTenVariables.TerminalBadParameterClosed
import CubicTenVariables.TerminalFixedModelBounds

/-! Fixed integral equations for the actual terminal cones, and nonzero
equation values at rational or integral points outside them. -/

noncomputable section
namespace CubicTenVariables.TerminalModelIdentification
open MvPolynomial HessianTheorem11 BibleProjectiveGeometry
open TerminalSectionIncidence TerminalBadParameterClosed

theorem exists_section_model (F : AnisotropicCubic 10) :
    ∃ m : ℕ, ∃ G : Fin m → MvPolynomial (Fin 10) ℤ,
      (∀ v : GeometricPoint 10,
        (∀ i, eval₂ (Int.castRingHom GeometricField) v (G i) = 0) ↔
          v = 0 ∨ (4 : Dimension) ≤ projectiveDimension
            (sectionSingularFiber (geometricPolynomial F.polynomial) v)) ∧
      TerminalFixedModelBounds.Bounds G 4 := by
  obtain ⟨m,G,_hideal,hzero,hbound⟩ := TerminalFixedModelBounds.exists_section_model F
  refine ⟨m,G,?_,hbound⟩
  intro v
  exact (hzero v).symm.trans (by
    simpa only [Nat.cast_ofNat] using
      mem_sectionClosure_iff F.polynomial F.homogeneous 4 v)

theorem exists_gauss_model (F : AnisotropicCubic 10) :
    ∃ m : ℕ, ∃ G : Fin m → MvPolynomial (Fin 10) ℤ,
      (∀ v : GeometricPoint 10,
        (∀ i, eval₂ (Int.castRingHom GeometricField) v (G i) = 0) ↔
          v = 0 ∨ (5 : Dimension) ≤ projectiveDimension
            (GaussTerminalBound.fiber (geometricPolynomial F.polynomial) v)) ∧
      TerminalFixedModelBounds.Bounds G 3 := by
  obtain ⟨m,G,_hideal,hzero,hbound⟩ := TerminalFixedModelBounds.exists_gauss_model F
  exact ⟨m,G,fun v => (hzero v).symm.trans (mem_ten_gaussClosure_iff F v),hbound⟩

/-- Integer values, not merely nonzero geometric evaluations. -/
theorem integer_avoidance {n m : ℕ} (G : Fin m → MvPolynomial (Fin n) ℤ)
    (Z : Set (GeometricPoint n))
    (hmodel : ∀ x, (∀ i, eval₂ (Int.castRingHom GeometricField) x (G i)=0) ↔ x∈Z)
    (v : Fin n → ℤ) (hv : (fun i => (v i : GeometricField)) ∉ Z) :
    ∃ i, eval v (G i) ≠ 0 := by
  by_contra! h
  apply hv
  apply (hmodel _).mp
  intro i
  have he := eval₂_comp (Int.castRingHom GeometricField) v (G i)
  simpa only [h i, map_zero, Function.comp_def, Int.coe_castRingHom] using he.symm

/-- The same fixed integer equation list separates every rational point
outside its actual geometric zero set. -/
theorem rational_avoidance {n m : ℕ} (G : Fin m → MvPolynomial (Fin n) ℤ)
    (Z : Set (GeometricPoint n))
    (hmodel : ∀ x, (∀ i, eval₂ (Int.castRingHom GeometricField) x (G i)=0) ↔ x∈Z)
    (v : Fin n → ℚ) (hv : RationalConeClosure.rationalEmbedding v ∉ Z) :
    ∃ i, eval₂ (Int.castRingHom ℚ) v (G i) ≠ 0 := by
  by_contra! h
  apply hv
  apply (hmodel _).mp
  have hc : (algebraMap ℚ GeometricField).comp (Int.castRingHom ℚ) =
      Int.castRingHom GeometricField := by ext a; simp
  intro i
  have he := eval₂_comp_left (algebraMap ℚ GeometricField) (Int.castRingHom ℚ) v (G i)
  simpa only [hc,h i,map_zero,Function.comp_def,RationalConeClosure.rationalEmbedding] using he.symm

end CubicTenVariables.TerminalModelIdentification
