import TranslatedDepthSeven.StrictRankAtMostSixQbarFrontier
import TranslatedDepthSeven.RationalQbarPrimePila

/-!
# Pila on the Qbar-prime high-degree strict low-rank components

This file applies the rational, geometrically integral form of Pila's
Theorem A to the actual finite component list left by the Galois-frontier
argument.  Every occurrence of geometric integrality is the literal prime
assertion for coefficient extension to `Qbar` already present in the
definition of the component list.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

local instance strictRankAtMostSixQbarPrimePilaClassicalDecidablePred
    {A : Type*} (q : A → Prop) : DecidablePred q := Classical.decPred q

/-- The complete Qbar-prime, degree-at-least-eight component sum satisfies
Pila's `33/8 + ε` estimate, uniformly in the translated packet. -/
theorem exists_qbarPrimeHighDegree_componentSum_le_pila
    (hPila : Pila1995TheoremARationalQbarPrime)
    (integralEquations : Finset (MvPolynomial (Fin 13) ℤ))
    (componentEquations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ componentEquations, ∃ d : ℕ, f.IsHomogeneous d)
    (hqualification :
      ∀ (Q : JacobianExceptionalComponent componentEquations),
        Q ∈ topProjectiveJacobianExceptionalComponents
          componentEquations hhomogeneous →
        (jacobianExceptionalComponentNormalization
              componentEquations hhomogeneous Q).parameterCount = 5 ∧
          Q.1.IsHomogeneous
            (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) ∧
          IsSaturatedByProjectiveIrrelevantIdeal Q.1 ∧
          Q.1.IsPrime ∧
          ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ Q.1) < 6 ∧
          ∀ r d : ℕ, HasProjectiveDimensionDegree Q.1 r d → r = 4)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : Parameters) (x₀ : IntVector 13) (CF : ℕ),
        (∑ Q ∈ qbarPrimeHighDegreeJacobianExceptionalComponents
            componentEquations hhomogeneous,
          (((depthSevenNormalizedDisplacementFinset
              p x₀ integralEquations CF).filter fun z ↦
            (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
              affineIdealZeroLocus Q.1).card : ℝ)) ≤
          ((qbarPrimeHighDegreeJacobianExceptionalComponents
              componentEquations hhomogeneous).card : ℝ) * C *
            ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
              ((33 / 8 : ℝ) + ε) := by
  classical
  let components := qbarPrimeHighDegreeJacobianExceptionalComponents
    componentEquations hhomogeneous
  have hdegree : ∀ Q : {Q // Q ∈ components},
      ∃ d : ℕ, HasProjectiveDimensionDegree Q.1.1 4 d := by
    intro Q
    have hQhigh := (Finset.mem_filter.mp Q.2).1
    exact (Finset.mem_filter.mp hQhigh).2.2
  choose d hd using hdegree
  have hdEight : ∀ Q : {Q // Q ∈ components}, 8 ≤ d Q := by
    intro Q
    exact
      degree_ge_eight_of_mem_highDegreeTopProjectiveJacobianExceptionalComponents
        (Finset.mem_filter.mp Q.2).1 (hd Q)
  have hsource : ∀ Q : {Q // Q ∈ components},
      ∃ c : ℝ, 0 < c ∧
        ∀ (p : Parameters) (x₀ : IntVector 13) (CF : ℕ),
          ((((depthSevenNormalizedDisplacementFinset
              p x₀ integralEquations CF).filter fun z ↦
            (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
              affineIdealZeroLocus Q.1.1).card : ℝ) ≤
            c * ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
              ((33 / 8 : ℝ) + ε)) := by
    intro Q
    obtain ⟨c, hc, hbound⟩ :=
      pila1995_finiteSet_rationalQbarPrime_projectiveFourfold_packet_degreeAtLeastEight
        hPila 12 (d Q) ε hε
    refine ⟨c, hc, ?_⟩
    intro p x₀ CF
    have hQhigh := (Finset.mem_filter.mp Q.2).1
    have hQtop := (Finset.mem_filter.mp hQhigh).1
    have hQbar := (Finset.mem_filter.mp Q.2).2
    apply hbound (d Q) p.m (hdEight Q) le_rfl p.hm Q.1.1
      (hqualification Q.1 hQtop).2.1 hQbar (hd Q) x₀
      ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ)
    · exact_mod_cast (by
        have := one_le_surfaceTangentNaturalSide p
        omega : 1 < 2 * surfaceTangentNaturalSide p + 1)
    · intro z hz i
      have hzbase := (Finset.mem_filter.mp hz).1
      have hcoord :=
        depthSevenNormalized_coordinate_le_two_surfaceTangentNaturalSide
          p x₀ integralEquations CF hzbase i
      have hcast : |(z i : ℝ)| ≤
          (2 * surfaceTangentNaturalSide p : ℕ) := by
        simpa only [Int.cast_abs, Nat.cast_ofNat, Nat.cast_mul,
          Nat.cast_natAbs] using (by exact_mod_cast hcoord :
            ((z i).natAbs : ℝ) ≤
              (2 * surfaceTangentNaturalSide p : ℕ))
      have hsucc : ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) <
          ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega :
          2 * surfaceTangentNaturalSide p <
            2 * surfaceTangentNaturalSide p + 1)
      exact hcast.trans_lt hsucc
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
  choose c hc hcbound using hsource
  let C : ℝ := 1 + ∑ Q : {Q // Q ∈ components}, c Q
  have hC : 0 < C := by
    have hsum : 0 ≤ ∑ Q : {Q // Q ∈ components}, c Q :=
      Finset.sum_nonneg fun Q _ ↦ (hc Q).le
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro p x₀ CF
  have hterm (Q : {Q // Q ∈ components}) : c Q ≤ C := by
    have hle : c Q ≤ ∑ R : {R // R ∈ components}, c R := by
      exact Finset.single_le_sum
        (fun R _ ↦ (hc R).le) (Finset.mem_univ Q)
    dsimp only [C]
    linarith
  calc
    (∑ Q ∈ qbarPrimeHighDegreeJacobianExceptionalComponents
        componentEquations hhomogeneous,
      (((depthSevenNormalizedDisplacementFinset
          p x₀ integralEquations CF).filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
          affineIdealZeroLocus Q.1).card : ℝ)) ≤
        ∑ Q : {Q // Q ∈ components},
          C * ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
            ((33 / 8 : ℝ) + ε) := by
      rw [← Finset.sum_attach]
      apply Finset.sum_le_sum
      intro Q _hQ
      exact (hcbound Q p x₀ CF).trans
        (mul_le_mul_of_nonneg_right (hterm Q) (by positivity))
    _ = ((components.card : ℝ) * C) *
        ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
          ((33 / 8 : ℝ) + ε) := by
      simp [mul_assoc]
    _ = ((qbarPrimeHighDegreeJacobianExceptionalComponents
          componentEquations hhomogeneous).card : ℝ) * C *
        ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
          ((33 / 8 : ℝ) + ε) := rfl

/-- The Qbar-prime top components whose displayed five-parameter
normalization has generic rank at least three. -/
noncomputable def qbarPrimeGenericRankAtLeastThreeTopComponents
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) :
    Finset (JacobianExceptionalComponent equations) :=
  (qbarPrimeTopProjectiveJacobianExceptionalComponents
    equations hhomogeneous).filter fun Q ↦
      3 ≤ (jacobianExceptionalComponentNormalization
        equations hhomogeneous Q).genericRank

/-- The complementary Qbar-prime top components.  Their displayed
normalization has generic rank one or two (positivity follows from
primality). -/
noncomputable def qbarPrimeGenericRankBelowThreeTopComponents
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) :
    Finset (JacobianExceptionalComponent equations) :=
  (qbarPrimeTopProjectiveJacobianExceptionalComponents
    equations hhomogeneous).filter fun Q ↦
      ¬ 3 ≤ (jacobianExceptionalComponentNormalization
        equations hhomogeneous Q).genericRank

/-- Exact normalization-rank partition of the Qbar-prime top-component
sum. -/
theorem sum_qbarPrimeTop_eq_genericRankAtLeastThree_add_belowThree
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (weight : JacobianExceptionalComponent equations → ℕ) :
    (∑ Q ∈ qbarPrimeTopProjectiveJacobianExceptionalComponents
        equations hhomogeneous, weight Q) =
      (∑ Q ∈ qbarPrimeGenericRankAtLeastThreeTopComponents
          equations hhomogeneous, weight Q) +
      ∑ Q ∈ qbarPrimeGenericRankBelowThreeTopComponents
          equations hhomogeneous, weight Q := by
  classical
  simpa only [qbarPrimeGenericRankAtLeastThreeTopComponents,
    qbarPrimeGenericRankBelowThreeTopComponents] using
    (Finset.sum_filter_add_sum_filter_not
      (qbarPrimeTopProjectiveJacobianExceptionalComponents
        equations hhomogeneous)
      (fun Q ↦ 3 ≤ (jacobianExceptionalComponentNormalization
        equations hhomogeneous Q).genericRank)
      weight).symm

/-- Membership in the complementary normalization-rank piece gives the
literal upper bound two. -/
theorem genericRank_le_two_of_mem_qbarPrimeGenericRankBelowThree
    {equations : Finset (MvPolynomial (Fin 13) ℚ)}
    {hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d}
    {Q : JacobianExceptionalComponent equations}
    (hQ : Q ∈ qbarPrimeGenericRankBelowThreeTopComponents
      equations hhomogeneous) :
    (jacobianExceptionalComponentNormalization
      equations hhomogeneous Q).genericRank ≤ 2 := by
  have hnot := (Finset.mem_filter.mp hQ).2
  omega

/-- The complete Qbar-prime generic-rank-at-least-three component sum
satisfies Pila's `13/3 + ε` estimate, uniformly in the translated packet.
No Hilbert-polynomial certificate or separate degree cutoff occurs: the
ordinary degree is the literal generic rank of the displayed homogeneous
linear normalization. -/
theorem exists_qbarPrimeGenericRankAtLeastThree_componentSum_le_pila
    (hPila : Pila1995TheoremARationalQbarPrimeNormalization)
    (integralEquations : Finset (MvPolynomial (Fin 13) ℤ))
    (componentEquations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ componentEquations, ∃ d : ℕ, f.IsHomogeneous d)
    (hqualification :
      ∀ (Q : JacobianExceptionalComponent componentEquations),
        Q ∈ topProjectiveJacobianExceptionalComponents
          componentEquations hhomogeneous →
        (jacobianExceptionalComponentNormalization
              componentEquations hhomogeneous Q).parameterCount = 5 ∧
          Q.1.IsHomogeneous
            (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) ∧
          IsSaturatedByProjectiveIrrelevantIdeal Q.1 ∧
          Q.1.IsPrime ∧
          ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ Q.1) < 6 ∧
          ∀ r d : ℕ, HasProjectiveDimensionDegree Q.1 r d → r = 4)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : Parameters) (x₀ : IntVector 13) (CF : ℕ),
        (∑ Q ∈ qbarPrimeGenericRankAtLeastThreeTopComponents
            componentEquations hhomogeneous,
          (((depthSevenNormalizedDisplacementFinset
              p x₀ integralEquations CF).filter fun z ↦
            (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
              affineIdealZeroLocus Q.1).card : ℝ)) ≤
          ((qbarPrimeGenericRankAtLeastThreeTopComponents
              componentEquations hhomogeneous).card : ℝ) * C *
            ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
              ((13 / 3 : ℝ) + ε) := by
  classical
  let components := qbarPrimeGenericRankAtLeastThreeTopComponents
    componentEquations hhomogeneous
  have hsource : ∀ Q : {Q // Q ∈ components},
      ∃ c : ℝ, 0 < c ∧
        ∀ (p : Parameters) (x₀ : IntVector 13) (CF : ℕ),
          ((((depthSevenNormalizedDisplacementFinset
              p x₀ integralEquations CF).filter fun z ↦
            (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
              affineIdealZeroLocus Q.1.1).card : ℝ) ≤
            c * ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
              ((13 / 3 : ℝ) + ε)) := by
    intro Q
    let D₀ := jacobianExceptionalComponentNormalization
      componentEquations hhomogeneous Q.1
    obtain ⟨c, hc, hbound⟩ :=
      pila1995_finiteSet_rationalQbarPrimeNormalization_packet_degreeAtLeastThree
        hPila 13 D₀.genericRank ε hε
    refine ⟨c, hc, ?_⟩
    intro p x₀ CF
    have hQrank := (Finset.mem_filter.mp Q.2).2
    have hQqbarTop := (Finset.mem_filter.mp Q.2).1
    have hQtop := (Finset.mem_filter.mp hQqbarTop).1
    have hQbar := (Finset.mem_filter.mp hQqbarTop).2
    apply hbound D₀.genericRank p.m hQrank le_rfl p.hm Q.1.1
      (hqualification Q.1 hQtop).2.1 hQbar D₀
      (hqualification Q.1 hQtop).1 rfl x₀
      ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ)
    · exact_mod_cast (by
        have := one_le_surfaceTangentNaturalSide p
        omega : 1 < 2 * surfaceTangentNaturalSide p + 1)
    · intro z hz i
      have hzbase := (Finset.mem_filter.mp hz).1
      have hcoord :=
        depthSevenNormalized_coordinate_le_two_surfaceTangentNaturalSide
          p x₀ integralEquations CF hzbase i
      have hcast : |(z i : ℝ)| ≤
          (2 * surfaceTangentNaturalSide p : ℕ) := by
        simpa only [Int.cast_abs, Nat.cast_ofNat, Nat.cast_mul,
          Nat.cast_natAbs] using (by exact_mod_cast hcoord :
            ((z i).natAbs : ℝ) ≤
              (2 * surfaceTangentNaturalSide p : ℕ))
      have hsucc : ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) <
          ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega :
          2 * surfaceTangentNaturalSide p <
            2 * surfaceTangentNaturalSide p + 1)
      exact hcast.trans_lt hsucc
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
  choose c hc hcbound using hsource
  let C : ℝ := 1 + ∑ Q : {Q // Q ∈ components}, c Q
  have hC : 0 < C := by
    have hsum : 0 ≤ ∑ Q : {Q // Q ∈ components}, c Q :=
      Finset.sum_nonneg fun Q _ ↦ (hc Q).le
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro p x₀ CF
  have hterm (Q : {Q // Q ∈ components}) : c Q ≤ C := by
    have hle : c Q ≤ ∑ R : {R // R ∈ components}, c R := by
      exact Finset.single_le_sum
        (fun R _ ↦ (hc R).le) (Finset.mem_univ Q)
    dsimp only [C]
    linarith
  calc
    (∑ Q ∈ qbarPrimeGenericRankAtLeastThreeTopComponents
        componentEquations hhomogeneous,
      (((depthSevenNormalizedDisplacementFinset
          p x₀ integralEquations CF).filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
          affineIdealZeroLocus Q.1).card : ℝ)) ≤
        ∑ Q : {Q // Q ∈ components},
          C * ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
            ((13 / 3 : ℝ) + ε) := by
      rw [← Finset.sum_attach]
      apply Finset.sum_le_sum
      intro Q _hQ
      exact (hcbound Q p x₀ CF).trans
        (mul_le_mul_of_nonneg_right (hterm Q) (by positivity))
    _ = ((components.card : ℝ) * C) *
        ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
          ((13 / 3 : ℝ) + ε) := by
      simp [mul_assoc]
    _ = ((qbarPrimeGenericRankAtLeastThreeTopComponents
          componentEquations hhomogeneous).card : ℝ) * C *
        ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
          ((13 / 3 : ℝ) + ε) := rfl

end

end TranslatedDepthSeven
