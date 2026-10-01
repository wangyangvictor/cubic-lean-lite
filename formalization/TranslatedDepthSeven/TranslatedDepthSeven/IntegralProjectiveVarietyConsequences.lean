import TranslatedDepthSeven.HilbertAffineChange

/-!
# Literal consequences of the projective dimension--degree certificate

This file only eliminates conjunctions in
`Published.IsIntegralProjectiveVariety`.  In particular, the Krull dimension
of the affine cone is not imported through a geometric interface: it is the
first component of the displayed projective Hilbert certificate.  The final
theorem combines those literal components with the internally proved
projective-to-affine Hilbert-polynomial comparison.
-/

namespace TranslatedDepthSeven
namespace Published

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The homogeneous ideal occurring in an integral projective variety. -/
theorem homogeneous_of_isIntegralProjectiveVariety
    {N r d : ℕ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (hI : IsIntegralProjectiveVariety I r d) :
    I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) :=
  hI.1

/-- Projective saturation is also a literal component of the definition. -/
theorem saturated_of_isIntegralProjectiveVariety
    {N r d : ℕ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (hI : IsIntegralProjectiveVariety I r d) :
    IsSaturatedByProjectiveIrrelevantIdeal I :=
  hI.2.1

/-- The prime ideal occurring in an integral projective variety. -/
theorem prime_of_isIntegralProjectiveVariety
    {N r d : ℕ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (hI : IsIntegralProjectiveVariety I r d) : I.IsPrime :=
  hI.2.2.1

/-- The exact projective Hilbert certificate contained in the definition. -/
theorem hasProjectiveDimensionDegree_of_isIntegralProjectiveVariety
    {N r d : ℕ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (hI : IsIntegralProjectiveVariety I r d) :
    HasProjectiveDimensionDegree I r d :=
  hI.2.2.2

/-- The affine cone over an integral projective `r`-fold has coordinate-ring
Krull dimension exactly `r + 1`.  This is a literal projection from the
projective dimension--degree certificate. -/
theorem cone_ringKrullDim_eq_succ_of_isIntegralProjectiveVariety
    {N r d : ℕ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (hI : IsIntegralProjectiveVariety I r d) :
    ringKrullDim (MvPolynomial (Fin (N + 1)) ℚ ⧸ I) = r + 1 :=
  hI.2.2.2.1

/-- The specialization used by the depth-seven fivefold branch. -/
theorem cone_ringKrullDim_eq_six_of_isIntegralProjectiveFivefold
    {d : ℕ} {I : Ideal (MvPolynomial (Fin 13) ℚ)}
    (hI : IsIntegralProjectiveVariety (N := 12) I 5 d) :
    ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ I) = 6 := by
  simpa using
    cone_ringKrullDim_eq_succ_of_isIntegralProjectiveVariety hI

/-- Positivity of the displayed projective degree. -/
theorem degree_pos_of_isIntegralProjectiveVariety
    {N r d : ℕ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (hI : IsIntegralProjectiveVariety I r d) : 0 < d :=
  hI.2.2.2.2.1

/-- The affine cone has the cumulative Hilbert polynomial of dimension
`r + 1` and the same degree `d`.  This uses only the literal homogeneous,
prime, and projective Hilbert data in `IsIntegralProjectiveVariety`. -/
theorem cone_hasAffineDimensionDegree_of_isIntegralProjectiveVariety
    {N r d : ℕ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (hI : IsIntegralProjectiveVariety I r d) :
    HasAffineDimensionDegree I (r + 1) d :=
  hasAffineDimensionDegree_of_homogeneous_hasProjectiveDimensionDegree
    I
    (homogeneous_of_isIntegralProjectiveVariety hI)
    (prime_of_isIntegralProjectiveVariety hI)
    r d
    (hasProjectiveDimensionDegree_of_isIntegralProjectiveVariety hI)

/-- The fivefold specialization gives exactly the six-dimensional affine
cone certificate required by Pila's affine theorem. -/
theorem cone_hasAffineDimensionDegree_of_isIntegralProjectiveFivefold
    {d : ℕ} {I : Ideal (MvPolynomial (Fin 13) ℚ)}
    (hI : IsIntegralProjectiveVariety (N := 12) I 5 d) :
    HasAffineDimensionDegree I 6 d := by
  simpa using
    cone_hasAffineDimensionDegree_of_isIntegralProjectiveVariety hI

end

end Published
end TranslatedDepthSeven
