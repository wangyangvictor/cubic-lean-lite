import Mathlib
import TranslatedDepthSeven.AffinePlaneMonomialDivisibility

/-!
# The local-algebra determinant step of Salberger's Lemma 2.4

This file expresses the elementary local determinant argument using actual
ideal powers and actual evaluation homomorphisms.  It also records the lifted
meaning of a generator bound for a residue graded piece and formalises the
single Nakayama/elementary-operation step used to raise a filtration order.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option linter.unusedSectionVars false

open scoped BigOperators

variable {R : Type*} [CommRing R] [Algebra ℤ R]

/-- Evaluation of a finite family under a finite family of ring maps to `ℤ`. -/
def localEvaluationMatrix {ι : Type*}
    (f : ι → R) (ev : ι → R →+* ℤ) : Matrix ι ι ℤ :=
  fun i j ↦ ev j (f i)

/-- If an evaluation maps `M` into `(p)`, it maps `M^e` into `(p^e)`. -/
theorem localEvaluation_dvd_pow
    (M : Ideal R) (p : ℤ) (ev : R →+* ℤ)
    (hev : Ideal.map ev M ≤ Ideal.span {p})
    (e : ℕ) (x : R) (hx : x ∈ M ^ e) :
    p ^ e ∣ ev x := by
  have hxmap : ev x ∈ Ideal.map ev (M ^ e) := Ideal.mem_map_of_mem ev hx
  rw [Ideal.map_pow] at hxmap
  have hpow := pow_le_pow_left' hev e
  have hmem : ev x ∈ Ideal.span {p} ^ e := hpow hxmap
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  exact hmem

/-- A convenient way to verify the mapping hypothesis: every member of `M`
has zero reduction modulo `p` after evaluation. -/
theorem map_le_span_of_eval_eq_zero_mod_prime
    {p : ℕ} (M : Ideal R) (ev : R →+* ℤ)
    (hmod : ∀ x ∈ M, ((ev x : ℤ) : ZMod p) = 0) :
    Ideal.map ev M ≤ Ideal.span {(p : ℤ)} := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change ev x ∈ Ideal.span {(p : ℤ)}
  rw [Ideal.mem_span_singleton]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (ev x) p).mp (hmod x hx)

/-- The determinant-divisibility conclusion after the functions have been
put in increasing powers of the actual local ideal. -/
theorem localFilteredEvaluation_det_dvd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Ideal R) (p : ℤ) (ev : ι → R →+* ℤ)
    (f : ι → R) (weight : ι → ℕ)
    (hev : ∀ j, Ideal.map (ev j) M ≤ Ideal.span {p})
    (hf : ∀ i, f i ∈ M ^ weight i) :
    p ^ (∑ i, weight i) ∣ (localEvaluationMatrix f ev).det := by
  have hdiv := prod_dvd_det_of_rows_dvd
    (localEvaluationMatrix f ev)
    (fun i ↦ p ^ weight i)
    (fun i j ↦ localEvaluation_dvd_pow M p (ev j) (hev j)
      (weight i) (f i) (hf i))
  simpa only [Finset.prod_pow_eq_pow_sum Finset.univ weight p] using hdiv

/-- The same theorem with the natural congruence hypothesis stated directly
modulo the prime. -/
theorem localFilteredEvaluation_det_dvd_of_eq_zero_mod_prime
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (M : Ideal R) (ev : ι → R →+* ℤ)
    (f : ι → R) (weight : ι → ℕ)
    (hev : ∀ j x, x ∈ M → (((ev j) x : ℤ) : ZMod p) = 0)
    (hf : ∀ i, f i ∈ M ^ weight i) :
    (p : ℤ) ^ (∑ i, weight i) ∣ (localEvaluationMatrix f ev).det := by
  apply localFilteredEvaluation_det_dvd M (p : ℤ) ev f weight
  · exact fun j ↦ map_le_span_of_eval_eq_zero_mod_prime M (ev j) (hev j)
  · exact hf

/-- The maximal-ideal specialisation in an actual Noetherian local ring. -/
theorem maximalIdealFilteredEvaluation_det_dvd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [IsNoetherianRing R] [IsLocalRing R]
    (p : ℤ) (ev : ι → R →+* ℤ)
    (f : ι → R) (weight : ι → ℕ)
    (hev : ∀ j, Ideal.map (ev j) (IsLocalRing.maximalIdeal R) ≤ Ideal.span {p})
    (hf : ∀ i, f i ∈ (IsLocalRing.maximalIdeal R) ^ weight i) :
    p ^ (∑ i, weight i) ∣ (localEvaluationMatrix f ev).det :=
  localFilteredEvaluation_det_dvd (IsLocalRing.maximalIdeal R) p ev f weight hev hf

/-! ## The concrete graded-piece input -/

/-- A displayed family generates the actual residue graded piece
`M^t/M^(t+1)`, written in its lifted integral form. -/
def GeneratesGradedPiece (M : Ideal R) (t h : ℕ) (g : Fin h → R) : Prop :=
  (∀ a, g a ∈ M ^ t) ∧
    ∀ x ∈ M ^ t, ∃ c : Fin h → ℤ,
      x - ∑ a, algebraMap ℤ R (c a) * g a ∈ M ^ (t + 1)

theorem GeneratesGradedPiece.generator_mem
    {M : Ideal R} {t h : ℕ} {g : Fin h → R}
    (hg : GeneratesGradedPiece M t h g) (a : Fin h) :
    g a ∈ M ^ t :=
  hg.1 a

theorem GeneratesGradedPiece.exists_coefficients
    {M : Ideal R} {t h : ℕ} {g : Fin h → R}
    (hg : GeneratesGradedPiece M t h g) {x : R} (hx : x ∈ M ^ t) :
    ∃ c : Fin h → ℤ,
      x - ∑ a, algebraMap ℤ R (c a) * g a ∈ M ^ (t + 1) :=
  hg.2 x hx

/-! ## Finite-field dependence in a residue graded piece -/

/-- `h+1` coefficient vectors of length `h` admit an integral relation with
a pivot which is a unit modulo `p`.  The coordinate sums are all divisible by
`p`.  This is the finite-field linear algebra used in Nakayama elimination. -/
theorem exists_unitPivot_integral_relation
    {p h : ℕ} (hp : p.Prime) (b : Fin (h + 1) → Fin h → ℤ) :
    ∃ (c : Fin (h + 1) → ℤ) (k : Fin (h + 1)),
      ¬ (p : ℤ) ∣ c k ∧
        ∀ a : Fin h, (p : ℤ) ∣ ∑ j, c j * b j a := by
  letI : Fact p.Prime := ⟨hp⟩
  let B : Matrix (Fin h) (Fin (h + 1)) (ZMod p) :=
    fun a j ↦ (b j a : ZMod p)
  have hdim : Module.finrank (ZMod p) (Fin h → ZMod p) <
      Module.finrank (ZMod p) (Fin (h + 1) → ZMod p) := by
    simp
  have hker : LinearMap.ker B.mulVecLin ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  letI : Nontrivial (LinearMap.ker B.mulVecLin) :=
    Submodule.nontrivial_iff_ne_bot.mpr hker
  obtain ⟨z, hz⟩ := exists_ne (0 : LinearMap.ker B.mulVecLin)
  have hzfun : (z : Fin (h + 1) → ZMod p) ≠ 0 := by
    intro h
    apply hz
    apply Subtype.ext
    exact h
  have hex : ∃ k, (z : Fin (h + 1) → ZMod p) k ≠ 0 := by
    by_contra hn
    apply hzfun
    funext k
    exact not_ne_iff.mp (not_exists.mp hn k)
  obtain ⟨k, hk⟩ := hex
  let c : Fin (h + 1) → ℤ := fun j ↦ ((z : Fin (h + 1) → ZMod p) j).val
  refine ⟨c, k, ?_, ?_⟩
  · intro hdvd
    apply hk
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hdvd
    simpa [c, Int.cast_natCast, ZMod.natCast_zmod_val] using hdvd
  · intro a
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hzker : B.mulVecLin (z : Fin (h + 1) → ZMod p) = 0 :=
      LinearMap.mem_ker.mp z.property
    have ha : ∑ j, (b j a : ZMod p) * (z : Fin (h + 1) → ZMod p) j = 0 := by
      exact congr_fun hzker a
    simpa [B, c, Matrix.mulVec, dotProduct, Int.cast_sum,
      Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val, mul_comm] using ha

/-- A coefficient divisible by `p` raises the `M`-adic order by one when
`p ∈ M`. -/
theorem integerCoefficient_mul_mem_ideal_succ
    {p : ℕ} (M : Ideal R) (hpM : algebraMap ℤ R (p : ℤ) ∈ M)
    {t : ℕ} {x : R} (hx : x ∈ M ^ t) {d : ℤ} (hd : (p : ℤ) ∣ d) :
    algebraMap ℤ R d * x ∈ M ^ (t + 1) := by
  obtain ⟨q, rfl⟩ := hd
  have hprod : x * algebraMap ℤ R (p : ℤ) ∈ M ^ t * M :=
    Ideal.mul_mem_mul hx hpM
  have hbase : x * algebraMap ℤ R (p : ℤ) ∈ M ^ (t + 1) := by
    simpa [pow_succ] using hprod
  have hmul := (M ^ (t + 1)).mul_mem_left (algebraMap ℤ R q) hbase
  convert hmul using 1
  rw [map_mul]
  ring

/-- The generator bound on `M^t/M^(t+1)` produces the unit-pivot relation
used in one Nakayama elimination step. -/
theorem exists_unitPivot_relation_of_generatesGradedPiece
    {p t h : ℕ} (hp : p.Prime) (M : Ideal R)
    (hpM : algebraMap ℤ R (p : ℤ) ∈ M)
    (g : Fin h → R) (hg : GeneratesGradedPiece M t h g)
    (f : Fin (h + 1) → R) (hf : ∀ j, f j ∈ M ^ t) :
    ∃ (c : Fin (h + 1) → ℤ) (k : Fin (h + 1)),
      ¬ (p : ℤ) ∣ c k ∧
        ∑ j, algebraMap ℤ R (c j) * f j ∈ M ^ (t + 1) := by
  choose b hb using fun j ↦ hg.exists_coefficients (hf j)
  obtain ⟨c, k, hck, hc⟩ := exists_unitPivot_integral_relation hp b
  refine ⟨c, k, hck, ?_⟩
  have hrem : ∀ j, f j - ∑ a, algebraMap ℤ R (b j a) * g a ∈ M ^ (t + 1) := hb
  have hfirst :
      ∑ j, algebraMap ℤ R (c j) *
        (f j - ∑ a, algebraMap ℤ R (b j a) * g a) ∈ M ^ (t + 1) := by
    exact Submodule.sum_mem _ fun j _ ↦
      (M ^ (t + 1)).mul_mem_left _ (hrem j)
  have hsecond :
      ∑ a, algebraMap ℤ R (∑ j, c j * b j a) * g a ∈ M ^ (t + 1) := by
    exact Submodule.sum_mem _ fun a _ ↦
      integerCoefficient_mul_mem_ideal_succ M hpM (hg.generator_mem a) (hc a)
  have hsum := (M ^ (t + 1)).add_mem hfirst hsecond
  have hswitch :
      ∑ j, algebraMap ℤ R (c j) *
          (∑ a, algebraMap ℤ R (b j a) * g a) =
        ∑ a, algebraMap ℤ R (∑ j, c j * b j a) * g a := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_mul]
    ring
  rw [← hswitch] at hsum
  convert hsum using 1
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-! ## The elementary operation in Salberger's proof -/

/-- Replace the `k`-th member by an integral linear combination. -/
def replaceByIntegralCombination {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → R) (k : ι) (c : ι → ℤ) : ι → R :=
  Function.update f k (∑ j, algebraMap ℤ R (c j) * f j)

/-- Evaluation commutes with the literal replacement. -/
theorem localEvaluationMatrix_replaceByIntegralCombination
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → R) (ev : ι → R →+* ℤ) (k : ι) (c : ι → ℤ) :
    localEvaluationMatrix (replaceByIntegralCombination f k c) ev =
      (localEvaluationMatrix f ev).updateRow k
        (∑ j, (c j) • (localEvaluationMatrix f ev) j) := by
  ext i j
  by_cases hik : i = k
  · subst i
    simp [localEvaluationMatrix, replaceByIntegralCombination]
  · simp [localEvaluationMatrix, replaceByIntegralCombination, hik]

/-- The replacement multiplies the determinant by the pivot coefficient. -/
theorem det_localEvaluationMatrix_replaceByIntegralCombination
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → R) (ev : ι → R →+* ℤ) (k : ι) (c : ι → ℤ) :
    (localEvaluationMatrix (replaceByIntegralCombination f k c) ev).det =
      c k * (localEvaluationMatrix f ev).det := by
  rw [localEvaluationMatrix_replaceByIntegralCombination]
  simpa [smul_eq_mul] using
    Matrix.det_updateRow_sum (localEvaluationMatrix f ev) k c

/-- A pivot which is a unit modulo `p` can be cancelled after a
filtration-improving replacement. -/
theorem prime_pow_dvd_det_of_replace_mem_powers
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (hp : p.Prime)
    (M : Ideal R) (ev : ι → R →+* ℤ)
    (f : ι → R) (weight : ι → ℕ)
    (k : ι) (c : ι → ℤ)
    (hpivot : ¬ (p : ℤ) ∣ c k)
    (hev : ∀ j, Ideal.map (ev j) M ≤ Ideal.span {(p : ℤ)})
    (hf : ∀ i, replaceByIntegralCombination f k c i ∈ M ^ weight i) :
    (p : ℤ) ^ (∑ i, weight i) ∣ (localEvaluationMatrix f ev).det := by
  have hdiv := localFilteredEvaluation_det_dvd M (p : ℤ) ev
    (replaceByIntegralCombination f k c) weight hev hf
  rw [det_localEvaluationMatrix_replaceByIntegralCombination] at hdiv
  exact (Nat.prime_iff_prime_int.mp hp).pow_dvd_of_dvd_mul_left
    (∑ i, weight i) hpivot hdiv

/-- The pivot acquires one more filtration step from a graded relation. -/
theorem replaceByIntegralCombination_pivot_mem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Ideal R) (f : ι → R) (k : ι) (c : ι → ℤ) (t : ℕ)
    (hrelation : ∑ j, algebraMap ℤ R (c j) * f j ∈ M ^ (t + 1)) :
    replaceByIntegralCombination f k c k ∈ M ^ (t + 1) := by
  simpa [replaceByIntegralCombination] using hrelation

/-- Every non-pivot row is unchanged. -/
theorem replaceByIntegralCombination_ne
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → R) (k i : ι) (c : ι → ℤ) (hik : i ≠ k) :
    replaceByIntegralCombination f k c i = f i := by
  simp [replaceByIntegralCombination, hik]

/-! ## One complete residue-layer step -/

/-- Literal one-layer form of Salberger's filtration argument.  If the
`t`-th residue graded piece has at most `h` displayed generators, then among
`h+1` functions of order at least `t` one integral elementary operation has a
unit pivot modulo `p` and raises one row to order `t+1`.  Consequently the
determinant gains the valuation `(h+1)t+1` contributed by this block. -/
theorem salberger_one_residue_layer
    {p t h : ℕ} (hp : p.Prime) (M : Ideal R)
    (hpM : algebraMap ℤ R (p : ℤ) ∈ M)
    (g : Fin h → R) (hg : GeneratesGradedPiece M t h g)
    (f : Fin (h + 1) → R) (hf : ∀ j, f j ∈ M ^ t)
    (ev : Fin (h + 1) → R →+* ℤ)
    (hev : ∀ j, Ideal.map (ev j) M ≤ Ideal.span {(p : ℤ)}) :
    (p : ℤ) ^ ((h + 1) * t + 1) ∣ (localEvaluationMatrix f ev).det := by
  obtain ⟨c, k, hck, hrelation⟩ :=
    exists_unitPivot_relation_of_generatesGradedPiece hp M hpM g hg f hf
  let weight : Fin (h + 1) → ℕ := fun i ↦ if i = k then t + 1 else t
  have hfiltered : ∀ i,
      replaceByIntegralCombination f k c i ∈ M ^ weight i := by
    intro i
    by_cases hik : i = k
    · subst i
      simpa [weight] using
        replaceByIntegralCombination_pivot_mem M f k c t hrelation
    · simpa [weight, hik, replaceByIntegralCombination_ne f k i c hik] using hf i
  have hdiv := prime_pow_dvd_det_of_replace_mem_powers hp M ev f weight k c
    hck hev hfiltered
  convert hdiv using 1
  congr 1
  have hw : ∀ i : Fin (h + 1), weight i = t + if i = k then 1 else 0 := by
    intro i
    simp only [weight]
    split <;> omega
  simp_rw [hw, Finset.sum_add_distrib]
  simp

/-! ## Finite accumulation of the elementary operations -/

/-- The literal data of one integral elementary replacement. -/
structure IntegralReplacement (ι : Type*) where
  pivot : ι
  coefficient : ι → ℤ

/-- Apply a finite list of literal replacements, in the displayed order. -/
def applyIntegralReplacements {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → R) : List (IntegralReplacement ι) → ι → R
  | [] => f
  | u :: us => applyIntegralReplacements
      (replaceByIntegralCombination f u.pivot u.coefficient) us

/-- Product of the displayed pivot coefficients. -/
def replacementPivotProduct {ι : Type*} : List (IntegralReplacement ι) → ℤ
  | [] => 1
  | u :: us => u.coefficient u.pivot * replacementPivotProduct us

/-- Iterating the replacement formula multiplies the determinant by the
product of the literal pivots. -/
theorem det_localEvaluationMatrix_applyIntegralReplacements
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → R) (ev : ι → R →+* ℤ)
    (ops : List (IntegralReplacement ι)) :
    (localEvaluationMatrix (applyIntegralReplacements f ops) ev).det =
      replacementPivotProduct ops * (localEvaluationMatrix f ev).det := by
  induction ops generalizing f with
  | nil => simp [applyIntegralReplacements, replacementPivotProduct]
  | cons u us ih =>
      rw [applyIntegralReplacements, ih,
        det_localEvaluationMatrix_replaceByIntegralCombination]
      simp [replacementPivotProduct]
      ring

/-- A product of pivots which are units modulo `p` is again a unit modulo
`p`. -/
theorem prime_not_dvd_replacementPivotProduct
    {ι : Type*} {p : ℕ} (hp : p.Prime)
    (ops : List (IntegralReplacement ι))
    (hunit : ∀ u ∈ ops, ¬ (p : ℤ) ∣ u.coefficient u.pivot) :
    ¬ (p : ℤ) ∣ replacementPivotProduct ops := by
  have hpint : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  induction ops with
  | nil => simpa [replacementPivotProduct] using hpint.not_dvd_one
  | cons u us ih =>
      rw [replacementPivotProduct]
      exact hpint.not_dvd_mul (hunit u (by simp))
        (ih (fun v hv ↦ hunit v (by simp [hv])))

/-- A finite, explicitly displayed Nakayama reduction ending in an adapted
family gives the sum-of-weights divisibility.  Together with
`exists_unitPivot_relation_of_generatesGradedPiece`, this isolates the finite
combinatorial scheduling from both the local algebra and determinant algebra. -/
theorem prime_pow_dvd_det_of_finite_integral_reduction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (hp : p.Prime) (M : Ideal R) (ev : ι → R →+* ℤ)
    (f : ι → R) (weight : ι → ℕ)
    (ops : List (IntegralReplacement ι))
    (hunit : ∀ u ∈ ops, ¬ (p : ℤ) ∣ u.coefficient u.pivot)
    (hev : ∀ j, Ideal.map (ev j) M ≤ Ideal.span {(p : ℤ)})
    (hadapted : ∀ i, applyIntegralReplacements f ops i ∈ M ^ weight i) :
    (p : ℤ) ^ (∑ i, weight i) ∣ (localEvaluationMatrix f ev).det := by
  have hdiv := localFilteredEvaluation_det_dvd M (p : ℤ) ev
    (applyIntegralReplacements f ops) weight hev hadapted
  rw [det_localEvaluationMatrix_applyIntegralReplacements] at hdiv
  exact (Nat.prime_iff_prime_int.mp hp).pow_dvd_of_dvd_mul_left
    (∑ i, weight i) (prime_not_dvd_replacementPivotProduct hp ops hunit) hdiv

end

end TranslatedDepthSeven
