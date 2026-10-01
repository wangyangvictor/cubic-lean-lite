import TranslatedDepthSeven.StrictRootTheorem

/-!
# Removing the sufficiently-large-height restriction

The prime reservoir is an eventual statement in the height `H`.  The strict
theorem is uniform for every parameter tuple.  This file closes that harmless
but logically necessary endpoint: below one fixed threshold, the literal
counted set is bounded by its ambient thirteen-dimensional integer box.
-/

namespace TranslatedDepthSeven

noncomputable section

open Filter

local instance strictSmallHeightClassicalDecidablePred
    {A : Type*} (q : A → Prop) : DecidablePred q := Classical.decPred q

/-- The literal translated point set has the elementary ambient-box bound
with radius `ceil H`. -/
theorem card_depthSevenTranslatedPointFinset_le_heightBox
    (p : Parameters)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ) :
    (depthSevenTranslatedPointFinset p equations CF).card ≤
      (2 * ⌈p.H⌉₊ + 1) ^ 13 := by
  have hsubset : depthSevenTranslatedPointFinset p equations CF ⊆
      integerSupNormBox 13 ⌈p.B + p.L⌉₊ := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hBL : p.B + p.L ≤ p.H := by
    unfold Parameters.H
    have hm : (0 : ℝ) ≤ p.m := p.natCast_m_pos.le
    linarith
  have hceil : ⌈p.B + p.L⌉₊ ≤ ⌈p.H⌉₊ := Nat.ceil_mono hBL
  calc
    (depthSevenTranslatedPointFinset p equations CF).card ≤
        (integerSupNormBox 13 ⌈p.B + p.L⌉₊).card :=
      Finset.card_le_card hsubset
    _ = (2 * ⌈p.B + p.L⌉₊ + 1) ^ 13 :=
      card_integerSupNormBox 13 ⌈p.B + p.L⌉₊
    _ ≤ (2 * ⌈p.H⌉₊ + 1) ^ 13 := by
      gcongr

/-- A bound proved above one fixed real height threshold extends to every
parameter tuple after enlarging its constant by one explicit ambient-box
constant. -/
theorem strictTranslatedBound_of_largeHeight
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (a ε : ℝ) (hε : 0 < ε) (ha : 0 ≤ a)
    (H₀ : ℝ) (Clarge : NNReal)
    (hlarge : ∀ p : Parameters, H₀ ≤ p.H →
      ((depthSevenTranslatedPointFinset p equations CF).card : NNReal) ≤
        powerEnvelope Clarge p.strictHeight p.strictNormalizedSide a ε) :
    ∃ C : NNReal, ∀ p : Parameters,
      ((depthSevenTranslatedPointFinset p equations CF).card : NNReal) ≤
        powerEnvelope C p.strictHeight p.strictNormalizedSide a ε := by
  let Csmall : NNReal := ((2 * ⌈H₀⌉₊ + 1) ^ 13 : ℕ)
  let C : NNReal := Clarge + Csmall
  refine ⟨C, ?_⟩
  intro p
  by_cases hp : H₀ ≤ p.H
  · refine (hlarge p hp).trans ?_
    unfold powerEnvelope
    gcongr
    exact le_add_right (le_refl Clarge)
  · have hpH : p.H ≤ H₀ := le_of_not_ge hp
    have hceil : ⌈p.H⌉₊ ≤ ⌈H₀⌉₊ := Nat.ceil_mono hpH
    have hcardNat :
        (depthSevenTranslatedPointFinset p equations CF).card ≤
          (2 * ⌈H₀⌉₊ + 1) ^ 13 :=
      (card_depthSevenTranslatedPointFinset_le_heightBox
        p equations CF).trans (by gcongr)
    have hcard :
        ((depthSevenTranslatedPointFinset p equations CF).card : NNReal) ≤
          Csmall := by
      change ((depthSevenTranslatedPointFinset p equations CF).card : NNReal) ≤
        (((2 * ⌈H₀⌉₊ + 1) ^ 13 : ℕ) : NNReal)
      exact_mod_cast hcardNat
    have hHpow : 1 ≤ p.strictHeight ^ ε :=
      NNReal.one_le_rpow p.one_le_strictHeight hε.le
    have hTpow : 1 ≤ p.strictNormalizedSide ^ (a + ε) :=
      NNReal.one_le_rpow p.one_le_strictNormalizedSide (by linarith)
    calc
      ((depthSevenTranslatedPointFinset p equations CF).card : NNReal) ≤
          Csmall := hcard
      _ ≤ C := le_add_left (le_refl Csmall)
      _ = C * 1 * 1 := by simp
      _ ≤ C * p.strictHeight ^ ε *
          p.strictNormalizedSide ^ (a + ε) := by
        gcongr
      _ = powerEnvelope C p.strictHeight p.strictNormalizedSide a ε := rfl

/-- Eventual form of `strictTranslatedBound_of_largeHeight`.  This is the
form consumed by the canonical prime reservoir: the eventual quantifier is
opened once, at a single threshold independent of the translated parameter
tuple, and the elementary ambient-box estimate handles everything below that
threshold. -/
theorem strictTranslatedBound_of_eventually_largeHeight
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (a ε : ℝ) (hε : 0 < ε) (ha : 0 ≤ a)
    (Clarge : NNReal)
    (hlarge : ∀ᶠ H : ℝ in atTop,
      ∀ p : Parameters, p.H = H →
        ((depthSevenTranslatedPointFinset p equations CF).card : NNReal) ≤
          powerEnvelope Clarge p.strictHeight p.strictNormalizedSide a ε) :
    ∃ C : NNReal, ∀ p : Parameters,
      ((depthSevenTranslatedPointFinset p equations CF).card : NNReal) ≤
        powerEnvelope C p.strictHeight p.strictNormalizedSide a ε := by
  obtain ⟨H₀, hH₀⟩ := (eventually_atTop.1 hlarge)
  apply strictTranslatedBound_of_largeHeight equations CF a ε hε ha H₀ Clarge
  intro p hp
  exact hH₀ p.H hp p rfl

end

end TranslatedDepthSeven
