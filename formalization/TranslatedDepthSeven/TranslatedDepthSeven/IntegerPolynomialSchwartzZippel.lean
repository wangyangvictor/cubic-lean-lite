import TranslatedDepthSeven.PolynomialCRTResidueCount
import TranslatedDepthSeven.SchwartzZippelResidueCount

/-!
# Schwartz--Zippel for literal integral polynomial models

This file connects the common zero sets of the displayed integral equations
to the finite-field Schwartz--Zippel bound.  At each prime one explicitly
chooses one equation whose reduction is nonzero.  No irreducibility,
dimension, or geometric interface is assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- Coefficientwise reduction of an integral multivariate polynomial. -/
def integerPolynomialReduction {N p : ℕ}
    (f : MvPolynomial (Fin N) ℤ) : MvPolynomial (Fin N) (ZMod p) :=
  f.map (Int.castRingHom (ZMod p))

@[simp]
theorem eval_integerPolynomialReduction {N p : ℕ}
    (f : MvPolynomial (Fin N) ℤ) (x : Fin N → ZMod p) :
    MvPolynomial.eval x (integerPolynomialReduction f) =
      integerPolynomialValue f x := by
  exact MvPolynomial.eval_map _ _ _

/-- The common zero set of the integral equations is contained in the zero
set of the reduction of every one of its members. -/
theorem integerPolynomialZeroSet_subset_reducedZeroSet_of_mem
    {p N : ℕ} (hp : p.Prime)
    (polynomials : Finset (MvPolynomial (Fin N) ℤ))
    {f : MvPolynomial (Fin N) ℤ} (hfmem : f ∈ polynomials) :
    integerPolynomialZeroSet p N hp.ne_zero polynomials ⊆
      mvPolynomialZeroSet p N hp (integerPolynomialReduction f) := by
  intro x hx
  rw [mem_mvPolynomialZeroSet_iff, eval_integerPolynomialReduction]
  exact (mem_integerPolynomialZeroSet_iff.mp hx) f hfmem

/-- One explicitly nonzero reduced equation of degree at most e bounds the
literal common zero set by e times p to the power N-1. -/
theorem card_integerPolynomialZeroSet_le_degree_mul_of_reduction_ne_zero
    {p N e : ℕ} (hp : p.Prime)
    (polynomials : Finset (MvPolynomial (Fin N) ℤ))
    {f : MvPolynomial (Fin N) ℤ} (hfmem : f ∈ polynomials)
    (hf : integerPolynomialReduction (p := p) f ≠ 0)
    (hdegree : (integerPolynomialReduction (p := p) f).totalDegree ≤ e) :
    (integerPolynomialZeroSet p N hp.ne_zero polynomials).card ≤
      e * p ^ (N - 1) := by
  exact (Finset.card_le_card
    (integerPolynomialZeroSet_subset_reducedZeroSet_of_mem
      hp polynomials hfmem)).trans
    (card_mvPolynomialZeroSet_le_degree_mul hp
      (integerPolynomialReduction f) hf hdegree)

/-- Prime-dependent choices of one nonzero reduced equation give a literal
square-free common-zero-set estimate. -/
theorem card_integerPolynomialZeroSet_squarefreeProduct_le_schwartzZippel
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (N e : ℕ) (polynomials : Finset (MvPolynomial (Fin N) ℤ))
    (chosen : P → MvPolynomial (Fin N) ℤ)
    (hmem : ∀ p : P, chosen p ∈ polynomials)
    (hnonzero : ∀ p : P,
      integerPolynomialReduction (p := (p : ℕ)) (chosen p) ≠ 0)
    (hdegree : ∀ p : P,
      (integerPolynomialReduction (p := (p : ℕ))
        (chosen p)).totalDegree ≤ e) :
    (integerPolynomialZeroSet (∏ p : P, (p : ℕ)) N
      (Finset.prod_ne_zero_iff.mpr fun p _ ↦
        primeSubtype_ne_zero hprime p) polynomials).card ≤
      e ^ P.card * (primeProduct P) ^ (N - 1) := by
  let hcop := primeSubtype_pairwise_coprime hprime
  let hzero := primeSubtype_ne_zero hprime
  letI (p : P) : NeZero (p : ℕ) := ⟨hzero p⟩
  letI : NeZero (∏ p : P, (p : ℕ)) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun p _ ↦ hzero p⟩
  rw [integerPolynomialZeroSet_product_eq_crtGlobalResidues
    (fun p : P ↦ (p : ℕ)) hcop hzero]
  apply card_squarefreePrime_crtGlobalResidues_le
    P hprime N (N - 1) e
  intro p
  exact card_integerPolynomialZeroSet_le_degree_mul_of_reduction_ne_zero
    (hprime p p.property) polynomials (hmem p) (hnonzero p) (hdegree p)

/-- The same exact Schwartz--Zippel consequence, with the zero set written
directly modulo the reservoir integer `primeProduct P`. -/
theorem card_integerPolynomialZeroSet_primeProduct_le_schwartzZippel
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (N e : ℕ) (polynomials : Finset (MvPolynomial (Fin N) ℤ))
    (chosen : P → MvPolynomial (Fin N) ℤ)
    (hmem : ∀ p : P, chosen p ∈ polynomials)
    (hnonzero : ∀ p : P,
      integerPolynomialReduction (p := (p : ℕ)) (chosen p) ≠ 0)
    (hdegree : ∀ p : P,
      (integerPolynomialReduction (p := (p : ℕ))
        (chosen p)).totalDegree ≤ e) :
    (integerPolynomialZeroSet (primeProduct P) N
      (primeProduct_ne_zero fun p hp ↦ hprime p hp) polynomials).card ≤
      e ^ P.card * (primeProduct P) ^ (N - 1) := by
  let hsubzero : (∏ p : P, (p : ℕ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ ↦ primeSubtype_ne_zero hprime p
  calc
    (integerPolynomialZeroSet (primeProduct P) N
      (primeProduct_ne_zero fun p hp ↦ hprime p hp) polynomials).card =
        (integerPolynomialZeroSet (∏ p : P, (p : ℕ)) N
          hsubzero polynomials).card :=
      card_integerPolynomialZeroSet_congr_modulus
        (primeSubtype_prod_eq_primeProduct P).symm _ _ polynomials
    _ ≤ e ^ P.card * (primeProduct P) ^ (N - 1) :=
      card_integerPolynomialZeroSet_squarefreeProduct_le_schwartzZippel
        P hprime N e polynomials chosen hmem hnonzero hdegree

/-- The same square-free estimate with the fixed degree factor absorbed
into H^epsilon at logarithmic reservoir depth. -/
theorem card_integerPolynomialZeroSet_squarefreeProduct_cast_le_rpow_mul_schwartzZippel
    {M0 ε H : ℝ} (hM0 : 0 ≤ M0) (hε : 0 < ε)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (N e : ℕ) (he : 1 ≤ e)
    (hPcard : P.card ≤ reservoirDepth M0 H)
    (hH : reservoirSubpowerThreshold M0 (e : ℝ) ε ≤ H)
    (polynomials : Finset (MvPolynomial (Fin N) ℤ))
    (chosen : P → MvPolynomial (Fin N) ℤ)
    (hmem : ∀ p : P, chosen p ∈ polynomials)
    (hnonzero : ∀ p : P,
      integerPolynomialReduction (p := (p : ℕ)) (chosen p) ≠ 0)
    (hdegree : ∀ p : P,
      (integerPolynomialReduction (p := (p : ℕ))
        (chosen p)).totalDegree ≤ e) :
    ((integerPolynomialZeroSet (∏ p : P, (p : ℕ)) N
      (Finset.prod_ne_zero_iff.mpr fun p _ ↦
        primeSubtype_ne_zero hprime p) polynomials).card : ℝ) ≤
      H ^ ε * (primeProduct P : ℝ) ^ (N - 1) := by
  let hcop := primeSubtype_pairwise_coprime hprime
  let hzero := primeSubtype_ne_zero hprime
  letI (p : P) : NeZero (p : ℕ) := ⟨hzero p⟩
  letI : NeZero (∏ p : P, (p : ℕ)) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun p _ ↦ hzero p⟩
  rw [integerPolynomialZeroSet_product_eq_crtGlobalResidues
    (fun p : P ↦ (p : ℕ)) hcop hzero]
  apply card_squarefreePrime_crtGlobalResidues_cast_le_rpow_mul
    hM0 hε P hprime N (N - 1) e he hPcard hH
  intro p
  exact card_integerPolynomialZeroSet_le_degree_mul_of_reduction_ne_zero
    (hprime p p.property) polynomials (hmem p) (hnonzero p) (hdegree p)

/-- The subpower Schwartz--Zippel estimate stated directly modulo the
reservoir integer `primeProduct P`. -/
theorem card_integerPolynomialZeroSet_primeProduct_cast_le_rpow_mul_schwartzZippel
    {M0 ε H : ℝ} (hM0 : 0 ≤ M0) (hε : 0 < ε)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (N e : ℕ) (he : 1 ≤ e)
    (hPcard : P.card ≤ reservoirDepth M0 H)
    (hH : reservoirSubpowerThreshold M0 (e : ℝ) ε ≤ H)
    (polynomials : Finset (MvPolynomial (Fin N) ℤ))
    (chosen : P → MvPolynomial (Fin N) ℤ)
    (hmem : ∀ p : P, chosen p ∈ polynomials)
    (hnonzero : ∀ p : P,
      integerPolynomialReduction (p := (p : ℕ)) (chosen p) ≠ 0)
    (hdegree : ∀ p : P,
      (integerPolynomialReduction (p := (p : ℕ))
        (chosen p)).totalDegree ≤ e) :
    ((integerPolynomialZeroSet (primeProduct P) N
      (primeProduct_ne_zero fun p hp ↦ hprime p hp) polynomials).card : ℝ) ≤
      H ^ ε * (primeProduct P : ℝ) ^ (N - 1) := by
  let hsubzero : (∏ p : P, (p : ℕ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ ↦ primeSubtype_ne_zero hprime p
  calc
    ((integerPolynomialZeroSet (primeProduct P) N
      (primeProduct_ne_zero fun p hp ↦ hprime p hp) polynomials).card : ℝ) =
        ((integerPolynomialZeroSet (∏ p : P, (p : ℕ)) N
          hsubzero polynomials).card : ℝ) := by
      exact_mod_cast card_integerPolynomialZeroSet_congr_modulus
        (primeSubtype_prod_eq_primeProduct P).symm
        (primeProduct_ne_zero fun p hp ↦ hprime p hp) hsubzero polynomials
    _ ≤ H ^ ε * (primeProduct P : ℝ) ^ (N - 1) :=
      card_integerPolynomialZeroSet_squarefreeProduct_cast_le_rpow_mul_schwartzZippel
        hM0 hε P hprime N e he hPcard hH polynomials chosen hmem hnonzero
          hdegree

end

end TranslatedDepthSeven
