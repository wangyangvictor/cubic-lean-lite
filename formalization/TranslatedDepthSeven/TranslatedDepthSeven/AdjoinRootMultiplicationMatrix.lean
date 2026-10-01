import TranslatedDepthSeven.CharacteristicPolynomialHeight
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.PowerBasis

/-!
# Multiplication matrices for one monic triangular step

For a monic polynomial `f`, multiplication by the distinguished root in
`AdjoinRoot f` is the literal companion matrix of `f` in the power basis.
Mathlib proves the companion formula for an arbitrary power basis in terms of
its `minpolyGen`; the first part of this file identifies that polynomial with
the original defining polynomial `f`.

The final results give direct support, coefficient, total-degree, and
evaluation bounds when the coefficient ring is an integral multivariate
polynomial ring.  No height predicate or external effective-algebra input is
introduced.
-/

namespace TranslatedDepthSeven

noncomputable section

open Finset Polynomial

universe u v w

variable {R : Type u} [CommRing R] {f : R[X]}

/-- The first reduction in the power basis: for a monic `f`, the remainder of
`X ^ deg f` is exactly its lower-degree part `X ^ deg f - f`. -/
theorem monic_X_pow_natDegree_modByMonic (hf : f.Monic) :
    X ^ f.natDegree %ₘ f = X ^ f.natDegree - f := by
  cases subsingleton_or_nontrivial R
  · subsingleton
  have hdeg : (X ^ f.natDegree - f).degree < f.degree := by
    have h := Polynomial.degree_sub_lt
      (p := X ^ f.natDegree) (q := f)
      (by rw [Polynomial.degree_X_pow,
        Polynomial.degree_eq_natDegree hf.ne_zero])
      (Polynomial.monic_X_pow f.natDegree).ne_zero
      (by rw [Polynomial.leadingCoeff_X_pow, hf])
    simpa [Polynomial.degree_eq_natDegree hf.ne_zero] using h
  have hdecomp : X ^ f.natDegree - f + f * 1 = X ^ f.natDegree := by
    ring
  exact (Polynomial.div_modByMonic_unique
    1 (X ^ f.natDegree - f) hf ⟨hdecomp, hdeg⟩).2

/-- The coordinate vector of the first reducible root power consists of the
negatives of the lower coefficients of `f`. -/
theorem adjoinRoot_powerBasis_repr_root_pow_natDegree
    (hf : f.Monic) (i : Fin f.natDegree) :
    (AdjoinRoot.powerBasis' hf).basis.repr
      (AdjoinRoot.root f ^ f.natDegree) i = -f.coeff i := by
  change (AdjoinRoot.modByMonicHom hf
      (AdjoinRoot.root f ^ f.natDegree)).coeff i = _
  rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.modByMonicHom_mk,
    monic_X_pow_natDegree_modByMonic hf, coeff_sub]
  have hi : (i : ℕ) ≠ f.natDegree := Nat.ne_of_lt i.isLt
  simp [coeff_X_pow, hi]

/-- The canonical power basis of `AdjoinRoot f` recovers `f` itself as its
power-basis defining polynomial.  This is the missing identification needed
to specialize Mathlib's general companion-matrix theorem. -/
theorem adjoinRoot_powerBasis_minpolyGen (hf : f.Monic) :
    (AdjoinRoot.powerBasis' hf).minpolyGen = f := by
  rw [PowerBasis.minpolyGen]
  change X ^ f.natDegree -
      ∑ i : Fin f.natDegree,
        C ((AdjoinRoot.powerBasis' hf).basis.repr
          (AdjoinRoot.root f ^ f.natDegree) i) * X ^ (i : ℕ) = f
  simp_rw [adjoinRoot_powerBasis_repr_root_pow_natDegree hf]
  have hsum :
      (∑ i : Fin f.natDegree, C (-f.coeff (i : ℕ)) * X ^ (i : ℕ)) =
        ∑ i ∈ Finset.range f.natDegree, C (-f.coeff i) * X ^ i :=
    Fin.sum_univ_eq_sum_range
      (fun i : ℕ ↦ C (-f.coeff i) * X ^ i) f.natDegree
  rw [hsum]
  have hneg :
      (∑ i ∈ Finset.range f.natDegree, C (-f.coeff i) * X ^ i) =
        -(∑ i ∈ Finset.range f.natDegree, C (f.coeff i) * X ^ i) := by
    calc
      _ = ∑ i ∈ Finset.range f.natDegree,
          -(C (f.coeff i) * X ^ i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            simp
      _ = _ := by
        simpa only using
          (Finset.sum_neg_distrib
            (s := Finset.range f.natDegree)
            (fun i ↦ C (f.coeff i) * X ^ i))
  rw [hneg, sub_neg_eq_add]
  have hexpand := f.as_sum_range_C_mul_X_pow
  rw [Finset.sum_range_succ, hf.coeff_natDegree, map_one, one_mul] at hexpand
  exact (add_comm _ _).trans hexpand.symm

/-- Multiplication by the distinguished root is the companion matrix of the
original monic polynomial, with columns indexed by the images of the power
basis vectors. -/
theorem adjoinRoot_powerBasis_leftMulMatrix_root (hf : f.Monic) :
    Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hf).basis
        (AdjoinRoot.root f) =
      @Matrix.of (Fin f.natDegree) (Fin f.natDegree) _ fun i j ↦
        if (j : ℕ) + 1 = f.natDegree then -f.coeff i
        else if (i : ℕ) = j + 1 then 1 else 0 := by
  change Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hf).basis
      (AdjoinRoot.powerBasis' hf).gen = _
  rw [(AdjoinRoot.powerBasis' hf).leftMulMatrix,
    adjoinRoot_powerBasis_minpolyGen hf]
  simp [AdjoinRoot.powerBasis'_dim]

/-- Entrywise form of the companion matrix. -/
theorem adjoinRoot_powerBasis_leftMulMatrix_root_apply
    (hf : f.Monic) (i j : Fin f.natDegree) :
    Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hf).basis
        (AdjoinRoot.root f) i j =
      if (j : ℕ) + 1 = f.natDegree then -f.coeff i
      else if (i : ℕ) = j + 1 then 1 else 0 := by
  rw [adjoinRoot_powerBasis_leftMulMatrix_root hf]
  rfl

section Tower

variable {S : Type v} [CommRing S] [Algebra R S]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- The same formula after placing the monic step over a lower explicit
basis.  The only nontrivial new blocks are the lower-stage multiplication
matrices of the coefficients of `f`; all remaining blocks are identity or
zero.  This is the exact recursion used when iterating triangular steps. -/
theorem smulTower_adjoinRoot_leftMulMatrix_root
    (b : Module.Basis ι R S) {g : S[X]} (hg : g.Monic)
    (i j : ι) (k l : Fin g.natDegree) :
    Algebra.leftMulMatrix
        (b.smulTower (AdjoinRoot.powerBasis' hg).basis)
        (AdjoinRoot.root g) (i, k) (j, l) =
      if (l : ℕ) + 1 = g.natDegree then
        -Algebra.leftMulMatrix b (g.coeff k) i j
      else if (k : ℕ) = l + 1 then
        if i = j then 1 else 0
      else 0 := by
  rw [Algebra.smulTower_leftMulMatrix,
    adjoinRoot_powerBasis_leftMulMatrix_root_apply hg]
  split_ifs <;> simp_all

end Tower

section IntegralPolynomialCoefficients

variable {σ : Type*}
variable {g : (MvPolynomial σ ℤ)[X]}

/-- The constant polynomial `1` has exactly one monomial in its support over
the integral coefficient ring. -/
theorem mvPolynomial_one_support_card :
    (1 : MvPolynomial σ ℤ).support.card = 1 := by
  classical
  rw [show (1 : MvPolynomial σ ℤ) = MvPolynomial.C 1 by simp]
  change (MvPolynomial.monomial 0 (1 : ℤ)).support.card = 1
  rw [MvPolynomial.support_monomial]
  simp

/-- The unique supported coefficient of the constant polynomial `1` has
natural absolute value one. -/
theorem mvPolynomial_one_coeff_natAbs
    (m : σ →₀ ℕ) (hm : m ∈ (1 : MvPolynomial σ ℤ).support) :
    ((1 : MvPolynomial σ ℤ).coeff m).natAbs = 1 := by
  classical
  have h0 : m = 0 := by
    by_contra hm0
    have hz : (1 : MvPolynomial σ ℤ).coeff m = 0 := by
      simp [MvPolynomial.coeff_one, Ne.symm hm0]
    exact (MvPolynomial.mem_support_iff.mp hm) hz
  subst m
  simp [MvPolynomial.coeff_one]

/-- A total-degree bound for the coefficients of `g` is inherited literally
by every entry of the root multiplication matrix. -/
theorem adjoinRoot_rootMatrix_entry_totalDegree_le
    (hg : g.Monic) {e : ℕ}
    (hdegree : ∀ i < g.natDegree, (g.coeff i).totalDegree ≤ e)
    (i j : Fin g.natDegree) :
    (Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hg).basis
      (AdjoinRoot.root g) i j).totalDegree ≤ e := by
  rw [adjoinRoot_powerBasis_leftMulMatrix_root_apply hg]
  split_ifs
  · simpa using hdegree i i.isLt
  · simp
  · simp

/-- A literal support-cardinality bound for the coefficients of `g` gives an
entrywise support bound for the companion matrix.  The `max 1` accounts for
the shift entries equal to `1`. -/
theorem adjoinRoot_rootMatrix_entry_support_card_le
    (hg : g.Monic) {S : ℕ}
    (hsupport : ∀ i < g.natDegree, (g.coeff i).support.card ≤ S)
    (i j : Fin g.natDegree) :
    (Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hg).basis
      (AdjoinRoot.root g) i j).support.card ≤ max 1 S := by
  rw [adjoinRoot_powerBasis_leftMulMatrix_root_apply hg]
  split_ifs
  · simpa using (hsupport i i.isLt).trans (Nat.le_max_right 1 S)
  · rw [mvPolynomial_one_support_card]
    exact Nat.le_max_left 1 S
  · simp

/-- Literal coefficient-size inheritance for the companion matrix. -/
theorem adjoinRoot_rootMatrix_entry_coeff_natAbs_le
    (hg : g.Monic) {C : ℕ}
    (hcoeff : ∀ i < g.natDegree, ∀ m ∈ (g.coeff i).support,
      ((g.coeff i).coeff m).natAbs ≤ C)
    (i j : Fin g.natDegree)
    (m : σ →₀ ℕ)
    (hm : m ∈ (Algebra.leftMulMatrix
      (AdjoinRoot.powerBasis' hg).basis (AdjoinRoot.root g) i j).support) :
    ((Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hg).basis
      (AdjoinRoot.root g) i j).coeff m).natAbs ≤ max 1 C := by
  rw [adjoinRoot_powerBasis_leftMulMatrix_root_apply hg] at hm ⊢
  split_ifs at hm ⊢
  · have hm' : m ∈ (g.coeff i).support := by simpa using hm
    simpa using (hcoeff i i.isLt m hm').trans (Nat.le_max_right 1 C)
  · rw [mvPolynomial_one_coeff_natAbs m hm]
    exact Nat.le_max_left 1 C
  · simp at hm

/-- After evaluating the projection variables at integral values bounded by
`Y`, every entry of the companion matrix has the explicit polynomial bound
coming from the literal support, coefficient, and total-degree hypotheses. -/
theorem eval_adjoinRoot_rootMatrix_entry_natAbs_le
    (hg : g.Monic) {e C S Y : ℕ} (y : σ → ℤ)
    (hdegree : ∀ i < g.natDegree, (g.coeff i).totalDegree ≤ e)
    (hsupport : ∀ i < g.natDegree, (g.coeff i).support.card ≤ S)
    (hcoeff : ∀ i < g.natDegree, ∀ m ∈ (g.coeff i).support,
      ((g.coeff i).coeff m).natAbs ≤ C)
    (hy : ∀ a, (y a).natAbs ≤ Y)
    (i j : Fin g.natDegree) :
    (MvPolynomial.eval y
      (Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hg).basis
        (AdjoinRoot.root g) i j)).natAbs ≤
      max 1 (S * C * max 1 Y ^ e) := by
  rw [adjoinRoot_powerBasis_leftMulMatrix_root_apply hg]
  split_ifs
  · rw [map_neg, Int.natAbs_neg]
    calc
      (MvPolynomial.eval y (g.coeff i)).natAbs ≤
          (g.coeff i).support.card * C * max 1 Y ^ e :=
        eval_natAbs_le_support_mul_coeff_mul_pow_generic
          (g.coeff i) y (hcoeff i i.isLt) (hdegree i i.isLt) hy
      _ ≤ S * C * max 1 Y ^ e :=
        Nat.mul_le_mul_right _
          (Nat.mul_le_mul_right C (hsupport i i.isLt))
      _ ≤ max 1 (S * C * max 1 Y ^ e) := Nat.le_max_right _ _
  · simp
  · simp

/-- Feeding the preceding entry bound into the universal characteristic
polynomial estimate gives an entirely explicit one-step coefficient bound.
This is the form that can be iterated after the corresponding concrete bounds
for the lower-stage multiplication matrices have been established. -/
theorem evaluated_adjoinRoot_rootMatrix_charpoly_coeff_natAbs_le
    (hg : g.Monic) {e C S Y : ℕ} (y : σ → ℤ)
    (hdegree : ∀ i < g.natDegree, (g.coeff i).totalDegree ≤ e)
    (hsupport : ∀ i < g.natDegree, (g.coeff i).support.card ≤ S)
    (hcoeff : ∀ i < g.natDegree, ∀ m ∈ (g.coeff i).support,
      ((g.coeff i).coeff m).natAbs ≤ C)
    (hy : ∀ a, (y a).natAbs ≤ Y)
    (r : ℕ) :
    (((Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hg).basis
        (AdjoinRoot.root g)).map (MvPolynomial.eval y)).charpoly.coeff r).natAbs ≤
      universalCharpolyCoefficientSupportCard g.natDegree r *
        universalCharpolyCoefficientNatAbsMax g.natDegree r *
          max 1 (max 1 (S * C * max 1 Y ^ e)) ^ g.natDegree := by
  apply charpoly_coeff_natAbs_le_universal
  intro i j
  simpa only [Matrix.map_apply] using
    eval_adjoinRoot_rootMatrix_entry_natAbs_le
      hg y hdegree hsupport hcoeff hy i j

end IntegralPolynomialCoefficients

section IntegralPolynomialTower

variable {σ : Type*}
variable {B : Type v} [CommRing B] [Algebra (MvPolynomial σ ℤ) B]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]
variable (b : Module.Basis ι (MvPolynomial σ ℤ) B)
variable {g : B[X]}

/-- Recursive total-degree inheritance in a triangular tower.  The
hypothesis concerns the literal lower-stage multiplication matrices of the
coefficients of the new equation, not an abstract height function. -/
theorem smulTower_adjoinRoot_rootMatrix_entry_totalDegree_le
    (hg : g.Monic) {e : ℕ}
    (hdegree : ∀ k : Fin g.natDegree, ∀ i j,
      (Algebra.leftMulMatrix b (g.coeff k) i j).totalDegree ≤ e)
    (i j : ι) (k l : Fin g.natDegree) :
    (Algebra.leftMulMatrix
      (b.smulTower (AdjoinRoot.powerBasis' hg).basis)
      (AdjoinRoot.root g) (i, k) (j, l)).totalDegree ≤ e := by
  rw [smulTower_adjoinRoot_leftMulMatrix_root b hg]
  split_ifs
  · simpa using hdegree k i j
  · simp
  · simp [MvPolynomial.totalDegree_zero]
  · simp [MvPolynomial.totalDegree_zero]

/-- Recursive support-cardinality inheritance.  Identity blocks account for
the single extra monomial represented by `max 1 S`. -/
theorem smulTower_adjoinRoot_rootMatrix_entry_support_card_le
    (hg : g.Monic) {S : ℕ}
    (hsupport : ∀ k : Fin g.natDegree, ∀ i j,
      (Algebra.leftMulMatrix b (g.coeff k) i j).support.card ≤ S)
    (i j : ι) (k l : Fin g.natDegree) :
    (Algebra.leftMulMatrix
      (b.smulTower (AdjoinRoot.powerBasis' hg).basis)
      (AdjoinRoot.root g) (i, k) (j, l)).support.card ≤ max 1 S := by
  rw [smulTower_adjoinRoot_leftMulMatrix_root b hg]
  split_ifs
  · simpa using (hsupport k i j).trans (Nat.le_max_right 1 S)
  · rw [mvPolynomial_one_support_card]
    exact Nat.le_max_left 1 S
  · rw [MvPolynomial.support_zero]
    simp
  · rw [MvPolynomial.support_zero]
    simp

/-- Recursive literal coefficient-size inheritance. -/
theorem smulTower_adjoinRoot_rootMatrix_entry_coeff_natAbs_le
    (hg : g.Monic) {C : ℕ}
    (hcoeff : ∀ k : Fin g.natDegree, ∀ i j,
      ∀ m ∈ (Algebra.leftMulMatrix b (g.coeff k) i j).support,
        ((Algebra.leftMulMatrix b (g.coeff k) i j).coeff m).natAbs ≤ C)
    (i j : ι) (k l : Fin g.natDegree)
    (m : σ →₀ ℕ)
    (hm : m ∈ (Algebra.leftMulMatrix
      (b.smulTower (AdjoinRoot.powerBasis' hg).basis)
      (AdjoinRoot.root g) (i, k) (j, l)).support) :
    ((Algebra.leftMulMatrix
      (b.smulTower (AdjoinRoot.powerBasis' hg).basis)
      (AdjoinRoot.root g) (i, k) (j, l)).coeff m).natAbs ≤ max 1 C := by
  rw [smulTower_adjoinRoot_leftMulMatrix_root b hg] at hm ⊢
  split_ifs at hm ⊢
  · have hm' : m ∈
        (Algebra.leftMulMatrix b (g.coeff k) i j).support := by
      simpa using hm
    simpa using (hcoeff k i j m hm').trans (Nat.le_max_right 1 C)
  · rw [mvPolynomial_one_coeff_natAbs m hm]
    exact Nat.le_max_left 1 C
  · rw [MvPolynomial.support_zero] at hm
    simp at hm
  · rw [MvPolynomial.support_zero] at hm
    simp at hm

/-- Evaluated-entry form of the recursive tower bounds.  In particular, if
`S,C ≥ 1`, a monic triangular step introduces no new support or coefficient
factor at all; only the fixed matrix dimension grows. -/
theorem eval_smulTower_adjoinRoot_rootMatrix_entry_natAbs_le
    (hg : g.Monic) {e C S Y : ℕ} (y : σ → ℤ)
    (hdegree : ∀ k : Fin g.natDegree, ∀ i j,
      (Algebra.leftMulMatrix b (g.coeff k) i j).totalDegree ≤ e)
    (hsupport : ∀ k : Fin g.natDegree, ∀ i j,
      (Algebra.leftMulMatrix b (g.coeff k) i j).support.card ≤ S)
    (hcoeff : ∀ k : Fin g.natDegree, ∀ i j,
      ∀ m ∈ (Algebra.leftMulMatrix b (g.coeff k) i j).support,
        ((Algebra.leftMulMatrix b (g.coeff k) i j).coeff m).natAbs ≤ C)
    (hy : ∀ a, (y a).natAbs ≤ Y)
    (i j : ι) (k l : Fin g.natDegree) :
    (MvPolynomial.eval y
      (Algebra.leftMulMatrix
        (b.smulTower (AdjoinRoot.powerBasis' hg).basis)
        (AdjoinRoot.root g) (i, k) (j, l))).natAbs ≤
      max 1 S * max 1 C * max 1 Y ^ e := by
  let p : MvPolynomial σ ℤ :=
    Algebra.leftMulMatrix
      (b.smulTower (AdjoinRoot.powerBasis' hg).basis)
      (AdjoinRoot.root g) (i, k) (j, l)
  calc
    (MvPolynomial.eval y p).natAbs ≤
        p.support.card * max 1 C * max 1 Y ^ e :=
      eval_natAbs_le_support_mul_coeff_mul_pow_generic p y
        (smulTower_adjoinRoot_rootMatrix_entry_coeff_natAbs_le
          b hg hcoeff i j k l)
        (smulTower_adjoinRoot_rootMatrix_entry_totalDegree_le
          b hg hdegree i j k l) hy
    _ ≤ max 1 S * max 1 C * max 1 Y ^ e :=
      Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right _
          (smulTower_adjoinRoot_rootMatrix_entry_support_card_le
            b hg hsupport i j k l))

end IntegralPolynomialTower

end

end TranslatedDepthSeven
