import CubicTenVariables.Literature.FiberDimensionSpreading
import CubicTenVariables.SectionIntegralCharts
import CubicTenVariables.ReducedGaussSection
import HessianTheorem11.BibleProjectiveGeometry
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! The explicit constructibility-spreading literature input, applied to each
actual normalized section chart. One product exceptional integer works for
all charts, primes, extension fields, and parameter vectors. No homogeneity
is needed for section charts; the Gauss corollary uses cubic homogeneity. -/

noncomputable section
namespace CubicTenVariables.TerminalChartSpreading
open MvPolynomial HessianTheorem11 TerminalSectionIncidence SectionIntegralCharts
open scoped BigOperators

/-- A finite normalized cover attains every natural dimension threshold.
The zero-variable case is vacuous because its projective dimension is bottom. -/
theorem exists_chart_of_nat_le {K : Type*} [Field K] {n : ℕ}
    (Z : Set (Fin n → K)) (t : ℕ)
    (h : (t : Dimension) ≤ ReducedGaussSection.projectiveDimension Z) :
    ∃ i : Fin n, (t : Dimension) ≤ ReducedGaussSection.coordinateDimension
      (ReducedGaussSection.normalizedChart Z i) := by
  by_cases hn : n=0
  · subst n
    simp [ReducedGaussSection.projectiveDimension] at h
  · letI : NeZero n := ⟨hn⟩
    obtain ⟨i,hi⟩ := exists_eq_ciSup_of_finite
      (f := fun i : Fin n => ReducedGaussSection.coordinateDimension
        (ReducedGaussSection.normalizedChart Z i))
    exact ⟨i,by simpa only [ReducedGaussSection.projectiveDimension,← hi] using h⟩

/-- The section-family containment over Qbar spreads to all fields outside
one fixed finite set of characteristics. The only external premise is spread. -/
theorem exists_section_bound
    (spread : Literature.FiberDimensionContainmentSpreading)
    {n : ℕ} {κ : Type} [Fintype κ]
    (F : MvPolynomial (Fin n) ℤ) (G : κ → MvPolynomial (Fin n) ℤ) (t : ℕ)
    (hgeneric : ∀ v : GeometricPoint n,
      (t : Dimension) ≤ BibleProjectiveGeometry.projectiveDimension
        (sectionSingularFiber (map (Int.castRingHom GeometricField) F) v) →
      ∀ i, eval₂ (Int.castRingHom GeometricField) v (G i)=0) :
    ∃ D : ℕ, 1≤D ∧ ∀ p : ℕ, p.Prime → ¬p∣D →
      ∀ (K : Type) [Field K] [CharP K p] (v : Fin n → K),
        (t : Dimension) ≤ ReducedGaussSection.projectiveDimension
          (sectionSingularFiber (map (Int.castRingHom K) F) v) →
        ∀ i, eval₂ (Int.castRingHom K) v (G i)=0 := by
  classical
  have hchart (k : Fin n) := spread n n t
    (Option (SectionHomogeneousFamily.Index n)) κ (chartEquation F k) G
    (by
      intro v hv
      change (t : Dimension) ≤ ringKrullDim
        (GeometricPolynomial n ⧸ chartIdeal F k v) at hv
      rw [geometric_quotient_dimension F k v] at hv
      apply hgeneric v (hv.trans ?_)
      exact le_iSup (fun i : Fin n => affineDimension
        (BibleProjectiveGeometry.affineChart
          (sectionSingularFiber (map (Int.castRingHom GeometricField) F) v) i)) k)
  choose D hD hgood using hchart
  refine ⟨∏ k, D k,?_,?_⟩
  · have hpos : 0 < ∏ k, D k := Finset.prod_pos (fun k _ =>
      lt_of_lt_of_le Nat.zero_lt_one (hD k))
    exact hpos
  · intro p hp hbad K _ _ v hv
    obtain ⟨k,hk⟩ := exists_chart_of_nat_le _ t hv
    apply hgood k p hp (fun hpk => hbad (hpk.trans
      (Finset.dvd_prod_of_mem D (Finset.mem_univ k)))) K v
    exact hk.trans (chart_dimension_le_quotient F k v)

/-- Cubic homogeneity also gives the literal reduced Gauss-fiber containment,
with the very same exceptional integer as the section family. -/
theorem exists_section_and_gauss_bound
    (spread : Literature.FiberDimensionContainmentSpreading)
    {n : ℕ} {κ : Type} [Fintype κ]
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (G : κ → MvPolynomial (Fin n) ℤ) (t : ℕ)
    (hgeneric : ∀ v : GeometricPoint n,
      (t : Dimension) ≤ BibleProjectiveGeometry.projectiveDimension
        (sectionSingularFiber (map (Int.castRingHom GeometricField) F) v) →
      ∀ i, eval₂ (Int.castRingHom GeometricField) v (G i)=0) :
    ∃ D : ℕ, 1≤D ∧ ∀ p : ℕ, p.Prime → ¬p∣D →
      ∀ (K : Type) [Field K] [CharP K p] (v : Fin n → K),
        ((t : Dimension) ≤ ReducedGaussSection.projectiveDimension
          (sectionSingularFiber (map (Int.castRingHom K) F) v) →
          ∀ i, eval₂ (Int.castRingHom K) v (G i)=0) ∧
        ((t : Dimension) ≤ ReducedGaussSection.projectiveDimension
          (ReducedGaussSection.fiber (map (Int.castRingHom K) F) v) →
          ∀ i, eval₂ (Int.castRingHom K) v (G i)=0) := by
  obtain ⟨D,hD,hgood⟩ := exists_section_bound spread F G t hgeneric
  refine ⟨D,hD,?_⟩
  intro p hp hbad K _ _ v
  refine ⟨hgood p hp hbad K v,?_⟩
  intro hv
  apply hgood p hp hbad K v
  exact ReducedGaussSection.projective_threshold_section _
    (hF.map (Int.castRingHom K)) v t hv

end CubicTenVariables.TerminalChartSpreading
