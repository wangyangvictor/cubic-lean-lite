import TranslatedDepthSeven.AffineTransformBounds
import TranslatedDepthSeven.HomogeneousProjectiveTransport
import TranslatedDepthSeven.JacobianCertificatePolynomialHeight

/-!
# Coefficient bounds for a homogeneous affine substitution

For integral homogeneous coordinates `(s,z)`, this file treats the literal
substitution

`(s,z) ↦ (s, s y₀ + r z)`.

All estimates are stated directly in terms of support cardinalities and the
natural absolute values of integer coefficients.  No geometric component,
Chow-form, or elimination-theoretic assertion is used.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators

open Finset MvPolynomial

/-- The integral polynomial-ring endomorphism induced by
`(s,z) ↦ (s,s y₀+r z)`. -/
def integralHomogeneousAffineTransform {n : ℕ}
    (y₀ : Fin n → ℤ) (r : ℤ) :
    MvPolynomial (Option (Fin n)) ℤ →+*
      MvPolynomial (Option (Fin n)) ℤ :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun j ↦
    match j with
    | none => MvPolynomial.X none
    | some i =>
        MvPolynomial.C (y₀ i) * MvPolynomial.X none +
          MvPolynomial.C r * MvPolynomial.X (some i)

@[simp]
theorem integralHomogeneousAffineTransform_C {n : ℕ}
    (y₀ : Fin n → ℤ) (r a : ℤ) :
    integralHomogeneousAffineTransform y₀ r (MvPolynomial.C a) =
      MvPolynomial.C a := by
  simp [integralHomogeneousAffineTransform]

@[simp]
theorem integralHomogeneousAffineTransform_X_none {n : ℕ}
    (y₀ : Fin n → ℤ) (r : ℤ) :
    integralHomogeneousAffineTransform y₀ r
        (MvPolynomial.X (none : Option (Fin n))) =
      MvPolynomial.X none := by
  simp [integralHomogeneousAffineTransform]

@[simp]
theorem integralHomogeneousAffineTransform_X_some {n : ℕ}
    (y₀ : Fin n → ℤ) (r : ℤ) (i : Fin n) :
    integralHomogeneousAffineTransform y₀ r
        (MvPolynomial.X (some i)) =
      MvPolynomial.C (y₀ i) * MvPolynomial.X none +
        MvPolynomial.C r * MvPolynomial.X (some i) := by
  simp [integralHomogeneousAffineTransform]

/-- After extension of coefficients to `ℚ`, the integral endomorphism is
exactly the polynomial pullback used by the projective affine automorphism. -/
theorem map_integralHomogeneousAffineTransform_eq_projectivePullback
    {n : ℕ} (y₀ : Fin n → ℤ) (r : ℤ) (hr : r ≠ 0)
    (f : MvPolynomial (Option (Fin n)) ℤ) :
    MvPolynomial.map (Int.castRingHom ℚ)
        (integralHomogeneousAffineTransform y₀ r f) =
      homogeneousAffinePolynomialChangeAlgEquiv
        (fun i ↦ (y₀ i : ℚ)) (r : ℚ) (by exact_mod_cast hr)
        (MvPolynomial.map (Int.castRingHom ℚ) f) := by
  let lhs : MvPolynomial (Option (Fin n)) ℤ →+*
      MvPolynomial (Option (Fin n)) ℚ :=
    (MvPolynomial.map (Int.castRingHom ℚ)).comp
      (integralHomogeneousAffineTransform y₀ r)
  let rhs : MvPolynomial (Option (Fin n)) ℤ →+*
      MvPolynomial (Option (Fin n)) ℚ :=
    (homogeneousAffinePolynomialChangeAlgEquiv
      (fun i ↦ (y₀ i : ℚ)) (r : ℚ) (by exact_mod_cast hr)).toRingHom.comp
        (MvPolynomial.map (Int.castRingHom ℚ))
  change lhs f = rhs f
  apply DFunLike.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [lhs, rhs]
  · intro j
    cases j with
    | none => simp [lhs, rhs]
    | some i => simp [lhs, rhs]

/-- Homogeneous degree is preserved by the integral homogeneous affine
substitution, without requiring `r` to be nonzero. -/
theorem integralHomogeneousAffineTransform_isHomogeneous
    {n d : ℕ} (y₀ : Fin n → ℤ) (r : ℤ)
    {f : MvPolynomial (Option (Fin n)) ℤ}
    (hf : f.IsHomogeneous d) :
    (integralHomogeneousAffineTransform y₀ r f).IsHomogeneous d := by
  let g : Option (Fin n) → MvPolynomial (Option (Fin n)) ℤ := fun j ↦
    match j with
    | none => MvPolynomial.X none
    | some i =>
          MvPolynomial.C (y₀ i) * MvPolynomial.X none +
          MvPolynomial.C r * MvPolynomial.X (some i)
  change (MvPolynomial.aeval g f).IsHomogeneous d
  have hg : ∀ j, (g j).IsHomogeneous 1 := by
    intro j
    cases j with
    | none => exact MvPolynomial.isHomogeneous_X ℤ none
    | some i =>
        exact
          (MvPolynomial.isHomogeneous_C_mul_X (y₀ i) none).add
            (MvPolynomial.isHomogeneous_C_mul_X r (some i))
  simpa using hf.aeval g hg

/-- One transformed source monomial has at most `2^degree` terms, and every
integer coefficient obeys the displayed literal bound. -/
theorem integralHomogeneousAffineTransform_monomial_bounds
    {n H R : ℕ} (y₀ : Fin n → ℤ) (r : ℤ)
    (hy₀ : ∀ i, (y₀ i).natAbs ≤ H) (hr : r.natAbs ≤ R)
    (m : Option (Fin n) →₀ ℕ) (a : ℤ) :
    (integralHomogeneousAffineTransform y₀ r
        (MvPolynomial.monomial m a)).support.card ≤
        2 ^ Finsupp.degree m ∧
      ∀ v,
        ((integralHomogeneousAffineTransform y₀ r
          (MvPolynomial.monomial m a)).coeff v).natAbs ≤
          a.natAbs *
            (2 * max 1 (max H R)) ^ Finsupp.degree m := by
  classical
  induction hdeg : Finsupp.degree m using Nat.strong_induction_on generalizing m with
  | _ D ih =>
      by_cases hD : D = 0
      · have hm : m = 0 :=
          (Finsupp.degree_eq_zero_iff m).mp (hdeg.trans hD)
        subst m
        subst D
        constructor
        · rw [← MvPolynomial.C_apply,
            integralHomogeneousAffineTransform_C, pow_zero]
          exact
            (Finset.card_le_card MvPolynomial.support_monomial_subset).trans_eq
              (Finset.card_singleton 0)
        · intro v
          rw [← MvPolynomial.C_apply,
            integralHomogeneousAffineTransform_C,
            MvPolynomial.coeff_C, pow_zero, mul_one]
          split_ifs <;> simp
      · have hm0 : m ≠ 0 := by
          intro hm
          subst m
          exact hD (by simpa using hdeg.symm)
        obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hm0
        let m' : Option (Fin n) →₀ ℕ := m - Finsupp.single j 1
        have hdegree : Finsupp.degree m' + 1 = D := by
          calc
            Finsupp.degree m' + 1 = Finsupp.degree m := by
              simpa only [Finsupp.degree_eq_weight_one, m'] using
                (Finsupp.weight_sub_single_add
                  (w := fun _ : Option (Fin n) ↦ 1) hj)
            _ = D := hdeg
        have hlt : Finsupp.degree m' < D := by omega
        have hm_add : m' + Finsupp.single j 1 = m :=
          Finsupp.sub_add_single_one_cancel hj
        have hmonomial :
            MvPolynomial.monomial m a =
              MvPolynomial.monomial m' a * MvPolynomial.X j := by
          rw [← hm_add, MvPolynomial.monomial_add_single, pow_one]
        let P : MvPolynomial (Option (Fin n)) ℤ :=
          integralHomogeneousAffineTransform y₀ r
            (MvPolynomial.monomial m' a)
        let L : MvPolynomial (Option (Fin n)) ℤ :=
          integralHomogeneousAffineTransform y₀ r (MvPolynomial.X j)
        have hrewrite :
            integralHomogeneousAffineTransform y₀ r
                (MvPolynomial.monomial m a) = P * L := by
          rw [hmonomial, map_mul]
        have hIH := ih (Finsupp.degree m') hlt m' rfl
        have hLsupport : L.support.card ≤ 2 := by
          cases j with
          | none =>
              rw [show L = MvPolynomial.X (none : Option (Fin n)) by simp [L]]
              rw [MvPolynomial.X]
              calc
                _ ≤ ({Finsupp.single (none : Option (Fin n)) 1} :
                    Finset (Option (Fin n) →₀ ℕ)).card :=
                  Finset.card_le_card MvPolynomial.support_monomial_subset
                _ = 1 := Finset.card_singleton _
                _ ≤ 2 := by omega
          | some i =>
              rw [show L =
                  MvPolynomial.C (y₀ i) * MvPolynomial.X none +
                    MvPolynomial.C r * MvPolynomial.X (some i) by
                simp [L]]
              calc
                _ ≤
                    (MvPolynomial.C (y₀ i) * MvPolynomial.X none :
                      MvPolynomial (Option (Fin n)) ℤ).support.card +
                    (MvPolynomial.C r * MvPolynomial.X (some i) :
                      MvPolynomial (Option (Fin n)) ℤ).support.card := by
                  exact (Finset.card_le_card MvPolynomial.support_add).trans
                    (Finset.card_union_le _ _)
                _ ≤ 1 + 1 := by
                  apply Nat.add_le_add
                  · rw [MvPolynomial.C_mul_X_eq_monomial]
                    exact
                      (Finset.card_le_card
                        MvPolynomial.support_monomial_subset).trans_eq
                        (Finset.card_singleton _)
                  · rw [MvPolynomial.C_mul_X_eq_monomial]
                    exact
                      (Finset.card_le_card
                        MvPolynomial.support_monomial_subset).trans_eq
                        (Finset.card_singleton _)
                _ = 2 := rfl
        constructor
        · rw [hrewrite, ← hdegree, pow_succ]
          calc
            (P * L).support.card ≤ P.support.card * L.support.card := by
              exact (Finset.card_le_card (MvPolynomial.support_mul P L)).trans
                Finset.card_add_le
            _ ≤ 2 ^ Finsupp.degree m' * 2 :=
              Nat.mul_le_mul hIH.1 hLsupport
        · intro v
          rw [hrewrite, ← hdegree]
          let M : ℕ := max 1 (max H R)
          have hM : 1 ≤ M := Nat.le_max_left 1 (max H R)
          have hyM : ∀ i, (y₀ i).natAbs ≤ M := by
            intro i
            exact (hy₀ i).trans
              ((Nat.le_max_left H R).trans (Nat.le_max_right 1 (max H R)))
          have hrM : r.natAbs ≤ M :=
            hr.trans
              ((Nat.le_max_right H R).trans (Nat.le_max_right 1 (max H R)))
          cases j with
          | none =>
              rw [show L = MvPolynomial.X (none : Option (Fin n)) by simp [L],
                MvPolynomial.coeff_mul_X']
              split_ifs
              · calc
                  _ ≤ a.natAbs * (2 * M) ^ Finsupp.degree m' := hIH.2 _
                  _ ≤ a.natAbs * (2 * M) ^ (Finsupp.degree m' + 1) := by
                    apply Nat.mul_le_mul_left
                    exact pow_le_pow_right₀ (by omega) (Nat.le_succ _)
              · simp
          | some i =>
              let e₀ : Option (Fin n) →₀ ℕ := Finsupp.single none 1
              let eᵢ : Option (Fin n) →₀ ℕ := Finsupp.single (some i) 1
              have hL : L =
                  MvPolynomial.monomial e₀ (y₀ i) +
                    MvPolynomial.monomial eᵢ r := by
                rw [← MvPolynomial.C_mul_X_eq_monomial,
                  ← MvPolynomial.C_mul_X_eq_monomial]
                simp [L]
              have hfirst :
                  ((P * MvPolynomial.monomial e₀ (y₀ i)).coeff v).natAbs ≤
                    (a.natAbs * (2 * M) ^ Finsupp.degree m') * M := by
                rw [MvPolynomial.coeff_mul_monomial']
                split_ifs
                · rw [Int.natAbs_mul]
                  exact Nat.mul_le_mul (hIH.2 _) (hyM i)
                · simp
              have hsecond :
                  ((P * MvPolynomial.monomial eᵢ r).coeff v).natAbs ≤
                    (a.natAbs * (2 * M) ^ Finsupp.degree m') * M := by
                rw [MvPolynomial.coeff_mul_monomial']
                split_ifs
                · rw [Int.natAbs_mul]
                  exact Nat.mul_le_mul (hIH.2 _) hrM
                · simp
              rw [hL, mul_add, MvPolynomial.coeff_add]
              calc
                _ ≤
                    ((P * MvPolynomial.monomial e₀ (y₀ i)).coeff v).natAbs +
                      ((P * MvPolynomial.monomial eᵢ r).coeff v).natAbs :=
                  Int.natAbs_add_le _ _
                _ ≤
                    (a.natAbs * (2 * M) ^ Finsupp.degree m') * M +
                      (a.natAbs * (2 * M) ^ Finsupp.degree m') * M :=
                  Nat.add_le_add hfirst hsecond
                _ = a.natAbs * (2 * M) ^ (Finsupp.degree m' + 1) := by
                  rw [pow_succ]
                  ring

/-- The transformed polynomial is the sum of the transformed source
monomials indexed by the literal source support. -/
theorem integralHomogeneousAffineTransform_as_sum
    {n : ℕ} (y₀ : Fin n → ℤ) (r : ℤ)
    (f : MvPolynomial (Option (Fin n)) ℤ) :
    integralHomogeneousAffineTransform y₀ r f =
      ∑ m ∈ f.support,
        integralHomogeneousAffineTransform y₀ r
          (MvPolynomial.monomial m (f.coeff m)) := by
  conv_lhs => rw [f.as_sum]
  simp only [map_sum]

/-- Literal support growth under homogeneous affine substitution. -/
theorem integralHomogeneousAffineTransform_support_card_le
    {n d H R : ℕ} (y₀ : Fin n → ℤ) (r : ℤ)
    (f : MvPolynomial (Option (Fin n)) ℤ)
    (hdegree : f.totalDegree ≤ d)
    (hy₀ : ∀ i, (y₀ i).natAbs ≤ H) (hr : r.natAbs ≤ R) :
    (integralHomogeneousAffineTransform y₀ r f).support.card ≤
      f.support.card * 2 ^ d := by
  classical
  rw [integralHomogeneousAffineTransform_as_sum]
  calc
    _ ≤ (f.support.biUnion fun m ↦
        (integralHomogeneousAffineTransform y₀ r
          (MvPolynomial.monomial m (f.coeff m))).support).card :=
      Finset.card_le_card MvPolynomial.support_sum
    _ ≤ ∑ m ∈ f.support,
        (integralHomogeneousAffineTransform y₀ r
          (MvPolynomial.monomial m (f.coeff m))).support.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _m ∈ f.support, 2 ^ d := by
      apply Finset.sum_le_sum
      intro m hm
      have hmdegree : Finsupp.degree m ≤ d :=
        (MvPolynomial.le_totalDegree hm).trans hdegree
      exact
        (integralHomogeneousAffineTransform_monomial_bounds
          y₀ r hy₀ hr m (f.coeff m)).1.trans
          (pow_le_pow_right₀ (by omega) hmdegree)
    _ = f.support.card * 2 ^ d := by simp

/-- Every coefficient of the transformed polynomial obeys a literal bound
in source support, source coefficients, degree, translation coordinates,
and scale. -/
theorem integralHomogeneousAffineTransform_coeff_natAbs_le
    {n d C H R : ℕ} (y₀ : Fin n → ℤ) (r : ℤ)
    (f : MvPolynomial (Option (Fin n)) ℤ)
    (hcoeff : ∀ m ∈ f.support, (f.coeff m).natAbs ≤ C)
    (hdegree : f.totalDegree ≤ d)
    (hy₀ : ∀ i, (y₀ i).natAbs ≤ H) (hr : r.natAbs ≤ R)
    (v : Option (Fin n) →₀ ℕ) :
    ((integralHomogeneousAffineTransform y₀ r f).coeff v).natAbs ≤
      f.support.card * C * (2 * max 1 (max H R)) ^ d := by
  classical
  rw [integralHomogeneousAffineTransform_as_sum,
    MvPolynomial.coeff_sum]
  calc
    _ ≤ ∑ m ∈ f.support,
        ((integralHomogeneousAffineTransform y₀ r
          (MvPolynomial.monomial m (f.coeff m))).coeff v).natAbs :=
      int_natAbs_sum_le_sum_natAbs _ _
    _ ≤ ∑ _m ∈ f.support,
        C * (2 * max 1 (max H R)) ^ d := by
      apply Finset.sum_le_sum
      intro m hm
      have hmdegree : Finsupp.degree m ≤ d :=
        (MvPolynomial.le_totalDegree hm).trans hdegree
      calc
        _ ≤ (f.coeff m).natAbs *
            (2 * max 1 (max H R)) ^ Finsupp.degree m :=
          (integralHomogeneousAffineTransform_monomial_bounds
            y₀ r hy₀ hr m (f.coeff m)).2 v
        _ ≤ C * (2 * max 1 (max H R)) ^ d :=
          Nat.mul_le_mul (hcoeff m hm)
            (pow_le_pow_right₀ (by omega) hmdegree)
    _ = f.support.card * C * (2 * max 1 (max H R)) ^ d := by
      simp [mul_assoc]

/-- Rename the homogeneous coordinates from `Option (Fin n)` to the standard
finite type `Fin (n+1)`. -/
def finRenameHomogeneousCoordinates {n : ℕ}
    (g : MvPolynomial (Option (Fin n)) ℤ) :
    MvPolynomial (Fin (n + 1)) ℤ :=
  MvPolynomial.rename (finSuccEquiv n).symm g

/-- The corresponding point after the same coordinate relabelling. -/
def finRenameHomogeneousPoint {n : ℕ}
    (x : Option (Fin n) → ℤ) : Fin (n + 1) → ℤ :=
  fun j ↦ x (finSuccEquiv n j)

/-- Relabelling the homogeneous coordinates commutes with partial
differentiation and evaluation. -/
theorem eval_pderiv_finRenameHomogeneousCoordinates
    {n : ℕ} (g : MvPolynomial (Option (Fin n)) ℤ)
    (x : Option (Fin n) → ℤ) (j : Fin (n + 1)) :
    MvPolynomial.eval (finRenameHomogeneousPoint x)
        (MvPolynomial.pderiv j (finRenameHomogeneousCoordinates g)) =
      MvPolynomial.eval x
        (MvPolynomial.pderiv (finSuccEquiv n j) g) := by
  let e : Option (Fin n) ≃ Fin (n + 1) := (finSuccEquiv n).symm
  have hj : j = e (finSuccEquiv n j) := by simp [e]
  rw [finRenameHomogeneousCoordinates, hj,
    MvPolynomial.pderiv_rename e.injective]
  rw [MvPolynomial.eval_rename]
  have hxcomp : finRenameHomogeneousPoint x ∘ e = x := by
    funext i
    simp [finRenameHomogeneousPoint, e]
  rw [hxcomp]
  simp [e]

/-- Combining the literal transformed support and coefficient bounds with
termwise differentiation gives a direct bound for every evaluated partial
derivative.  The input is assumed homogeneous because these are the
projective equations for which the substitution is used. -/
theorem eval_pderiv_integralHomogeneousAffineTransform_natAbs_le
    {n d e C H R Y : ℕ} (y₀ : Fin n → ℤ) (r : ℤ)
    (f : MvPolynomial (Option (Fin n)) ℤ)
    (hf : f.IsHomogeneous e) (hed : e ≤ d)
    (hcoeff : ∀ m ∈ f.support, (f.coeff m).natAbs ≤ C)
    (hy₀ : ∀ i, (y₀ i).natAbs ≤ H) (hr : r.natAbs ≤ R)
    (x : Option (Fin n) → ℤ)
    (hx : ∀ j, (x j).natAbs ≤ Y)
    (j : Option (Fin n)) :
    (MvPolynomial.eval x
      (MvPolynomial.pderiv j
        (integralHomogeneousAffineTransform y₀ r f))).natAbs ≤
      (f.support.card * 2 ^ d) * d *
        (f.support.card * C * (2 * max 1 (max H R)) ^ d) *
          max 1 Y ^ d := by
  let g := integralHomogeneousAffineTransform y₀ r f
  let e : Option (Fin n) ≃ Fin (n + 1) := (finSuccEquiv n).symm
  let gFin : MvPolynomial (Fin (n + 1)) ℤ := MvPolynomial.rename e g
  let xFin : Fin (n + 1) → ℤ := fun k ↦ x (e.symm k)
  let B := f.support.card * C * (2 * max 1 (max H R)) ^ d
  have hfdegree : f.totalDegree ≤ d :=
    hf.totalDegree_le.trans hed
  have hgdegree : g.totalDegree ≤ d :=
    (integralHomogeneousAffineTransform_isHomogeneous y₀ r hf).totalDegree_le.trans hed
  have hgsupport : g.support.card ≤ f.support.card * 2 ^ d :=
    integralHomogeneousAffineTransform_support_card_le
      y₀ r f hfdegree hy₀ hr
  have hgcoeff : ∀ m ∈ g.support, (g.coeff m).natAbs ≤ B := by
    intro m _hm
    exact integralHomogeneousAffineTransform_coeff_natAbs_le
      y₀ r f hcoeff hfdegree hy₀ hr m
  have hgFinDegree : gFin.totalDegree ≤ d :=
    (MvPolynomial.totalDegree_rename_le e g).trans hgdegree
  have hgFinSupport : gFin.support.card ≤ f.support.card * 2 ^ d := by
    calc
      gFin.support.card = g.support.card := by
        rw [show gFin = MvPolynomial.rename e g by rfl,
          MvPolynomial.support_rename_of_injective e.injective,
          Finset.card_image_of_injective _
            (Finsupp.mapDomain_injective e.injective)]
      _ ≤ f.support.card * 2 ^ d := hgsupport
  have hgFinCoeff : ∀ m ∈ gFin.support, (gFin.coeff m).natAbs ≤ B := by
    intro m hm
    rw [show gFin = MvPolynomial.rename e g by rfl,
      MvPolynomial.support_rename_of_injective e.injective] at hm
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hm
    rw [show gFin = MvPolynomial.rename e g by rfl,
      MvPolynomial.coeff_rename_mapDomain e e.injective]
    exact hgcoeff u hu
  have hxFin : ∀ k, (xFin k).natAbs ≤ Y := by
    intro k
    exact hx (e.symm k)
  have hFin :=
    eval_pderiv_natAbs_le_support_mul_degree_mul_coeff_mul_pow
      gFin xFin (e j) hgFinCoeff hgFinDegree hxFin
  have htransfer :
      MvPolynomial.eval xFin (MvPolynomial.pderiv (e j) gFin) =
        MvPolynomial.eval x (MvPolynomial.pderiv j g) := by
    rw [show gFin = MvPolynomial.rename e g by rfl,
      MvPolynomial.pderiv_rename e.injective]
    rw [MvPolynomial.eval_rename]
    have hxcomp : xFin ∘ e = x := by
      funext k
      simp [xFin, e]
    rw [hxcomp]
  calc
    (MvPolynomial.eval x (MvPolynomial.pderiv j g)).natAbs =
        (MvPolynomial.eval xFin
          (MvPolynomial.pderiv (e j) gFin)).natAbs := by rw [htransfer]
    _ ≤ gFin.support.card * d * B * max 1 Y ^ d := hFin
    _ ≤ (f.support.card * 2 ^ d) * d * B * max 1 Y ^ d := by
      exact Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right B
          (Nat.mul_le_mul_right d hgFinSupport))

/-- Uniform source bounds and a rational rank hypothesis therefore give an
honest nonzero integral Jacobian minor for the transformed family, together
with a completely explicit natural-absolute-value bound. -/
theorem exists_bounded_nonzero_integralJacobianMinor_of_homogeneousAffineTransform
    {c n q d S C H R Y : ℕ}
    (y₀ : Fin n → ℤ) (r : ℤ)
    (F : Fin c → MvPolynomial (Option (Fin n)) ℤ)
    (degree : Fin c → ℕ)
    (x : Option (Fin n) → ℤ)
    (hrank : q ≤
      ((integralJacobianMatrix
        (fun i ↦ finRenameHomogeneousCoordinates
          (integralHomogeneousAffineTransform y₀ r (F i)))
        (finRenameHomogeneousPoint x)).map
          (Int.castRingHom ℚ)).rank)
    (hhom : ∀ i, (F i).IsHomogeneous (degree i))
    (hdegree : ∀ i, degree i ≤ d)
    (hsupport : ∀ i, (F i).support.card ≤ S)
    (hcoeff : ∀ i m, m ∈ (F i).support → ((F i).coeff m).natAbs ≤ C)
    (hy₀ : ∀ i, (y₀ i).natAbs ≤ H) (hr : r.natAbs ≤ R)
    (hx : ∀ j, (x j).natAbs ≤ Y) :
    ∃ rows : Fin q → Fin c, ∃ cols : Fin q → Fin (n + 1),
      Function.Injective rows ∧ Function.Injective cols ∧
        integralJacobianMinor
            (fun i ↦ finRenameHomogeneousCoordinates
              (integralHomogeneousAffineTransform y₀ r (F i)))
            (finRenameHomogeneousPoint x) rows cols ≠ 0 ∧
        (integralJacobianMinor
          (fun i ↦ finRenameHomogeneousCoordinates
            (integralHomogeneousAffineTransform y₀ r (F i)))
          (finRenameHomogeneousPoint x) rows cols).natAbs ≤
          q.factorial *
            (((S * 2 ^ d) * d *
              (S * C * (2 * max 1 (max H R)) ^ d) *
                max 1 Y ^ d) ^ q) := by
  apply exists_bounded_nonzero_integralJacobianMinor
    (fun i ↦ finRenameHomogeneousCoordinates
      (integralHomogeneousAffineTransform y₀ r (F i)))
    (finRenameHomogeneousPoint x) hrank
  intro i j
  change
    (MvPolynomial.eval (finRenameHomogeneousPoint x)
      (MvPolynomial.pderiv j
        (finRenameHomogeneousCoordinates
          (integralHomogeneousAffineTransform y₀ r (F i))))).natAbs ≤ _
  rw [eval_pderiv_finRenameHomogeneousCoordinates]
  have hi := eval_pderiv_integralHomogeneousAffineTransform_natAbs_le
    y₀ r (F i) (hhom i) (hdegree i) (hcoeff i) hy₀ hr x hx
      (finSuccEquiv n j)
  calc
    _ ≤ ((F i).support.card * 2 ^ d) * d *
        ((F i).support.card * C * (2 * max 1 (max H R)) ^ d) *
          max 1 Y ^ d := hi
    _ ≤ (S * 2 ^ d) * d *
        (S * C * (2 * max 1 (max H R)) ^ d) *
          max 1 Y ^ d := by
      have hleft :
          ((F i).support.card * 2 ^ d) * d ≤
            (S * 2 ^ d) * d :=
        Nat.mul_le_mul_right d
          (Nat.mul_le_mul_right (2 ^ d) (hsupport i))
      have hright :
          (F i).support.card * C * (2 * max 1 (max H R)) ^ d ≤
            S * C * (2 * max 1 (max H R)) ^ d :=
        Nat.mul_le_mul_right _
          (Nat.mul_le_mul_right C (hsupport i))
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hleft hright)

end

end TranslatedDepthSeven
