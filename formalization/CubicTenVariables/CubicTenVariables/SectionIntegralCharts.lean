import CubicTenVariables.SectionHomogeneousFamily
import HessianTheorem11.UnconditionalCutDimension

/-! Fixed integer equations for the normalized affine charts of the actual
section-singularity family. Their specializations are exact in every field;
only the dimension comparison with the actual zero set discards nilpotents. -/

noncomputable section
namespace CubicTenVariables.SectionIntegralCharts
open MvPolynomial HessianTheorem11 TerminalSectionIncidence SectionHomogeneousFamily

variable {n : ℕ}

/-- One additional equation normalizes the selected point coordinate. -/
def chartEquation (F : MvPolynomial (Fin n) ℤ) (k : Fin n) :
    Option (SectionHomogeneousFamily.Index n) →
      MvPolynomial (Fin n) (MvPolynomial (Fin n) ℤ)
  | none => X k - 1
  | some i => SectionHomogeneousFamily.equation F i

/-- Literal coefficient specialization at the normal parameter. -/
def chartIdeal (F : MvPolynomial (Fin n) ℤ) (k : Fin n)
    {K : Type*} [CommRing K] (v : Fin n → K) : Ideal (MvPolynomial (Fin n) K) :=
  Ideal.span (Set.range (fun i =>
    map (eval₂Hom (Int.castRingHom K) v) (chartEquation F k i)))

theorem specialize_integral_form (F : MvPolynomial (Fin n) ℤ)
    {K : Type*} [CommRing K] (v : Fin n → K) :
    map (eval₂Hom (Int.castRingHom K) v) (formEquation F) =
      map (Int.castRingHom K) F := by
  have he : (eval₂Hom (Int.castRingHom K) v).comp
      (C : ℤ →+* MvPolynomial (Fin n) ℤ) = Int.castRingHom K :=
    RingHom.ext_int _ _
  rw [formEquation,map_map,he]

/-- Integer coefficient reduction commutes with all three section equations,
including the actual formal first derivatives. -/
theorem specialize_integral_equation (F : MvPolynomial (Fin n) ℤ)
    {K : Type*} [CommRing K] (v : Fin n → K) (i : SectionHomogeneousFamily.Index n) :
    map (eval₂Hom (Int.castRingHom K) v) (SectionHomogeneousFamily.equation F i) =
      map (eval v) (SectionHomogeneousFamily.equation (map (Int.castRingHom K) F) i) := by
  rcases i with k | ⟨i,j⟩
  · fin_cases k
    · change map _ (formEquation F) = map _ (formEquation _)
      rw [specialize_formEquation,specialize_integral_form]
    · change map _ (dotEquation n ℤ) = map _ (dotEquation n K)
      simp only [dotEquation,map_sum,map_mul,map_C,eval₂Hom_X',map_X,eval_X]
  · change map _ (minorEquation F i j) = map _ (minorEquation _ i j)
    rw [specialize_minorEquation]
    change map _ (C (X i)*formEquation (pderiv j F)-
      C (X j)*formEquation (pderiv i F)) = _
    rw [map_sub,map_mul,map_mul,map_C,map_C,eval₂Hom_X',eval₂Hom_X',
      specialize_integral_form,specialize_integral_form]
    simp only [pderiv_map]

/-- Exact literal equations of the normalized section fiber. No homogeneity,
anisotropy or nonzero-normal assumption is needed. -/
theorem chart_zero_iff (F : MvPolynomial (Fin n) ℤ) (k : Fin n)
    {K : Type*} [CommRing K] (v x : Fin n → K) :
    (∀ i, eval x (map (eval₂Hom (Int.castRingHom K) v) (chartEquation F k i)) = 0) ↔
      x ∈ sectionSingularFiber (map (Int.castRingHom K) F) v ∧ x k = 1 := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · apply (SectionHomogeneousFamily.eval_equation _ v x).mp
      intro i
      simpa only [chartEquation,specialize_integral_equation] using h (some i)
    · simpa [chartEquation,sub_eq_zero] using h none
  · rintro ⟨hx,hk⟩ i
    cases i with
    | none => simp [chartEquation,hk]
    | some i =>
      simpa only [chartEquation,specialize_integral_equation] using
        (SectionHomogeneousFamily.eval_equation _ v x).mpr hx i

theorem chart_zeroSet (F : MvPolynomial (Fin n) ℤ) (k : Fin n)
    {K : Type*} [CommRing K] (v : Fin n → K) :
    {x | ∀ i, eval x (map (eval₂Hom (Int.castRingHom K) v) (chartEquation F k i)) = 0} =
      {x | x ∈ sectionSingularFiber (map (Int.castRingHom K) F) v ∧ x k = 1} := by
  ext x
  exact chart_zero_iff F k v x

/-- The full original specialized equation ideal defines exactly this chart. -/
theorem zeroLocus_chartIdeal (F : MvPolynomial (Fin n) ℤ) (k : Fin n)
    {K : Type*} [Field K] (v : Fin n → K) :
    zeroLocus K (chartIdeal F k v) =
      {x | x ∈ sectionSingularFiber (map (Int.castRingHom K) F) v ∧ x k = 1} := by
  ext x
  rw [chartIdeal,zeroLocus_span]
  change (∀ g ∈ Set.range (fun i =>
    map (eval₂Hom (Int.castRingHom K) v) (chartEquation F k i)), eval x g = 0) ↔ _
  simpa only [Set.forall_mem_range] using chart_zero_iff F k v x

/-- Every actual chart has dimension at most its displayed equation quotient
in an arbitrary field, without algebraic closedness or radicality. -/
theorem chart_dimension_le_quotient (F : MvPolynomial (Fin n) ℤ) (k : Fin n)
    {K : Type*} [Field K] (v : Fin n → K) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ vanishingIdeal K
      {x | x ∈ sectionSingularFiber (map (Int.castRingHom K) F) v ∧ x k = 1}) ≤
      ringKrullDim (MvPolynomial (Fin n) K ⧸ chartIdeal F k v) := by
  rw [← zeroLocus_chartIdeal F k v]
  exact ringKrullDim_le_of_surjective
    (Ideal.Quotient.factor (le_vanishingIdeal_zeroLocus _))
    (Ideal.Quotient.factor_surjective _)

/-- Over Qbar the exact quotient and actual normalized chart have identical
dimension; the equation ideal need not itself be radical. -/
theorem geometric_quotient_dimension (F : MvPolynomial (Fin n) ℤ) (k : Fin n)
    (v : GeometricPoint n) :
    ringKrullDim (GeometricPolynomial n ⧸ chartIdeal F k v) =
      affineDimension {x | x ∈ sectionSingularFiber (map (Int.castRingHom GeometricField) F) v ∧
        x k = 1} := by
  rw [← zeroLocus_chartIdeal F k v,affineDimension,
    vanishingIdeal_zeroLocus_eq_radical,
    UnconditionalCutDimension.quotient_radical_dimension]

end CubicTenVariables.SectionIntegralCharts
