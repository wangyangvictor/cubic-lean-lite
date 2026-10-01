import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Tensor specialization of a principal-open quotient

This file records the literal commutative-algebra identifications used when a
chart descended over a principal open is reduced to a special fibre.

* iterated scalar extension cancels;
* scalar extension commutes with quotienting, with the extended ideal written
  explicitly;
* scalar extension commutes with localization away from one element; and
* consequently the scalar extension of a localized equation quotient is the
  principal localization of the direct specialized quotient.

All maps are actual algebra equivalences.  The proofs use tensor-product right
exactness and the universal property of localization; no geometric comparison
principle is introduced.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct

universe u v w z

/-- Cancelling an intermediate scalar extension.  In the intended
application, `Rδ` is a principal localization of `R` and `k` is a special
fibre of `Rδ`, but the equivalence only needs the scalar tower. -/
noncomputable def iteratedBaseChangeAlgEquiv
    (R : Type u) (Rδ : Type v) (k : Type w) (T : Type z)
    [CommRing R] [CommRing Rδ] [CommRing k] [CommRing T]
    [Algebra R Rδ] [Algebra R k] [Algebra R T]
    [Algebra Rδ k] [IsScalarTower R Rδ k] :
    k ⊗[Rδ] (Rδ ⊗[R] T) ≃ₐ[k] k ⊗[R] T :=
  Algebra.TensorProduct.cancelBaseChange R Rδ k k T

@[simp]
theorem iteratedBaseChangeAlgEquiv_tmul
    (R : Type u) (Rδ : Type v) (k : Type w) (T : Type z)
    [CommRing R] [CommRing Rδ] [CommRing k] [CommRing T]
    [Algebra R Rδ] [Algebra R k] [Algebra R T]
    [Algebra Rδ k] [IsScalarTower R Rδ k]
    (c : k) (r : Rδ) (t : T) :
    iteratedBaseChangeAlgEquiv R Rδ k T (c ⊗ₜ (r ⊗ₜ t)) =
      (r • c) ⊗ₜ t := by
  rfl

@[simp]
theorem iteratedBaseChangeAlgEquiv_symm_tmul
    (R : Type u) (Rδ : Type v) (k : Type w) (T : Type z)
    [CommRing R] [CommRing Rδ] [CommRing k] [CommRing T]
    [Algebra R Rδ] [Algebra R k] [Algebra R T]
    [Algebra Rδ k] [IsScalarTower R Rδ k]
    (c : k) (t : T) :
    (iteratedBaseChangeAlgEquiv R Rδ k T).symm (c ⊗ₜ t) =
      c ⊗ₜ ((1 : Rδ) ⊗ₜ t) := by
  rfl

section Quotient

variable {R : Type u} {k : Type v} {A : Type w}
  [CommRing R] [CommRing k] [CommRing A]
  [Algebra R k] [Algebra R A]

/-- The scalar extension of the quotient map. -/
noncomputable def baseChangeQuotientMap (I : Ideal A) :
    (k ⊗[R] A) →ₐ[k] (k ⊗[R] (A ⧸ I)) :=
  Algebra.TensorProduct.map (AlgHom.id k k) (Ideal.Quotient.mkₐ R I)

theorem baseChangeQuotientMap_surjective (I : Ideal A) :
    Function.Surjective (baseChangeQuotientMap (R := R) (k := k) I) := by
  change Function.Surjective
    (LinearMap.lTensor k (Ideal.Quotient.mkₐ R I).toLinearMap)
  exact LinearMap.lTensor_surjective k Ideal.Quotient.mk_surjective

/-- The kernel of the scalar-extended quotient map is exactly the extension
of the original ideal. -/
theorem baseChangeQuotientMap_ker (I : Ideal A) :
    RingHom.ker (baseChangeQuotientMap (R := R) (k := k) I) =
      I.map
        (Algebra.TensorProduct.includeRight : A →ₐ[R] k ⊗[R] A) := by
  change RingHom.ker
      (Algebra.TensorProduct.map (AlgHom.id R k)
        (Ideal.Quotient.mkₐ R I)) = _
  rw [Algebra.TensorProduct.lTensor_ker _
    Ideal.Quotient.mk_surjective]
  congr 1
  simpa only [AlgHom.toRingHom_eq_coe] using
    (Ideal.Quotient.mkₐ_ker R I)

/-- Scalar extension commutes with quotienting.  The ideal on the left is
written as the literal image under the right tensor-factor inclusion. -/
noncomputable def baseChangeQuotientAlgEquiv (I : Ideal A) :
    ((k ⊗[R] A) ⧸
        I.map
          (Algebra.TensorProduct.includeRight : A →ₐ[R] k ⊗[R] A))
      ≃ₐ[k] k ⊗[R] (A ⧸ I) :=
  (Ideal.quotientEquivAlgOfEq k
      (baseChangeQuotientMap_ker (R := R) (k := k) I).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (baseChangeQuotientMap_surjective (R := R) (k := k) I))

@[simp]
theorem baseChangeQuotientAlgEquiv_apply_mk
    (I : Ideal A) (x : k ⊗[R] A) :
    baseChangeQuotientAlgEquiv (R := R) (k := k) I
        (Ideal.Quotient.mk _ x) =
      baseChangeQuotientMap (R := R) (k := k) I x := by
  simp [baseChangeQuotientAlgEquiv]

@[simp]
theorem baseChangeQuotientAlgEquiv_apply_mk_tmul
    (I : Ideal A) (c : k) (a : A) :
    baseChangeQuotientAlgEquiv (R := R) (k := k) I
        (Ideal.Quotient.mk _ (c ⊗ₜ a)) =
      c ⊗ₜ Ideal.Quotient.mk I a := by
  rw [baseChangeQuotientAlgEquiv_apply_mk]
  rfl

end Quotient

section Localization

variable {R : Type u} {k : Type v} {A : Type w} {Aₑ : Type z}
  [CommRing R] [CommRing k] [CommRing A] [CommRing Aₑ]
  [Algebra R k] [Algebra R A] [Algebra R Aₑ] [Algebra A Aₑ]
  [IsScalarTower R A Aₑ]

private abbrev ScalarExtendedA := k ⊗[R] A

private abbrev ScalarExtendedLocalization := k ⊗[R] Aₑ

private abbrev SpecializedAway (f : A) :=
  Localization.Away
    (Algebra.TensorProduct.includeRight f :
      ScalarExtendedA (R := R) (k := k) (A := A))

/-- The original algebra maps to the localization of its scalar extension. -/
private noncomputable def algebraToSpecializedAway (f : A) :
    A →ₐ[R] SpecializedAway (R := R) (k := k) (A := A) f :=
  (Algebra.algHom R (ScalarExtendedA (R := R) (k := k) (A := A))
      (SpecializedAway (R := R) (k := k) (A := A) f)).comp
    Algebra.TensorProduct.includeRight

private theorem algebraToSpecializedAway_map_powers_isUnit (f : A) :
    ∀ y : Submonoid.powers f,
      IsUnit (algebraToSpecializedAway (R := R) (k := k) f y) := by
  rintro ⟨y, n, rfl⟩
  rw [map_pow]
  exact (IsLocalization.Away.algebraMap_isUnit
    (Algebra.TensorProduct.includeRight f :
      ScalarExtendedA (R := R) (k := k) (A := A))
      (S := SpecializedAway (R := R) (k := k) (A := A) f)).pow n

/-- The localization factor maps to the specialized localization. -/
private noncomputable def localizationToSpecializedAway
    (f : A) [IsLocalization.Away f Aₑ] :
    Aₑ →ₐ[R] SpecializedAway (R := R) (k := k) (A := A) f :=
  IsLocalization.liftAlgHom
    (A := R) (R := A) (M := Submonoid.powers f) (S := Aₑ)
    (P := SpecializedAway (R := R) (k := k) (A := A) f)
    (f := algebraToSpecializedAway (R := R) (k := k) (A := A) f)
    (algebraToSpecializedAway_map_powers_isUnit
      (R := R) (k := k) (A := A) f)

/-- The forward map in localization/base-change compatibility. -/
private noncomputable def baseChangeLocalizationForward
    (f : A) [IsLocalization.Away f Aₑ] :
    ScalarExtendedLocalization (R := R) (k := k) (Aₑ := Aₑ) →ₐ[k]
      SpecializedAway (R := R) (k := k) (A := A) f :=
  Algebra.TensorProduct.lift
    (Algebra.algHom k k (SpecializedAway (R := R) (k := k) (A := A) f))
    (localizationToSpecializedAway
      (R := R) (k := k) (A := A) (Aₑ := Aₑ) f)
    (fun _ _ ↦ Commute.all _ _)

/-- The natural map from the scalar-extended algebra to the scalar extension
of its localization. -/
private noncomputable def scalarExtendedAlgebraToLocalization :
    ScalarExtendedA (R := R) (k := k) (A := A) →ₐ[k]
      ScalarExtendedLocalization (R := R) (k := k) (Aₑ := Aₑ) :=
  Algebra.TensorProduct.map (AlgHom.id k k)
    (IsScalarTower.toAlgHom R A Aₑ)

private theorem scalarExtendedAlgebraToLocalization_map_powers_isUnit
    (f : A) [IsLocalization.Away f Aₑ] :
    ∀ y : Submonoid.powers
        (Algebra.TensorProduct.includeRight f :
          ScalarExtendedA (R := R) (k := k) (A := A)),
      IsUnit
        (scalarExtendedAlgebraToLocalization
          (R := R) (k := k) (A := A) (Aₑ := Aₑ) y) := by
  rintro ⟨y, n, rfl⟩
  rw [map_pow]
  apply IsUnit.pow
  change IsUnit (1 ⊗ₜ[R] algebraMap A Aₑ f)
  exact (IsLocalization.Away.algebraMap_isUnit f).map
    (Algebra.TensorProduct.includeRight :
      Aₑ →ₐ[R] ScalarExtendedLocalization (R := R) (k := k) (Aₑ := Aₑ))

/-- The inverse map in localization/base-change compatibility. -/
private noncomputable def baseChangeLocalizationBackward
    (f : A) [IsLocalization.Away f Aₑ] :
    SpecializedAway (R := R) (k := k) (A := A) f →ₐ[k]
      ScalarExtendedLocalization (R := R) (k := k) (Aₑ := Aₑ) :=
  IsLocalization.liftAlgHom
    (A := k)
    (R := ScalarExtendedA (R := R) (k := k) (A := A))
    (M := Submonoid.powers
      (Algebra.TensorProduct.includeRight f :
        ScalarExtendedA (R := R) (k := k) (A := A)))
    (S := SpecializedAway (R := R) (k := k) (A := A) f)
    (P := ScalarExtendedLocalization (R := R) (k := k) (Aₑ := Aₑ))
    (f := scalarExtendedAlgebraToLocalization
      (R := R) (k := k) (A := A) (Aₑ := Aₑ))
    (scalarExtendedAlgebraToLocalization_map_powers_isUnit
      (R := R) (k := k) (A := A) (Aₑ := Aₑ) f)

@[simp]
private theorem baseChangeLocalizationBackward_algebraMap
    (f : A) [IsLocalization.Away f Aₑ]
    (x : ScalarExtendedA (R := R) (k := k) (A := A)) :
    baseChangeLocalizationBackward
        (R := R) (k := k) (A := A) (Aₑ := Aₑ) f
        (algebraMap (ScalarExtendedA (R := R) (k := k) (A := A))
          (SpecializedAway (R := R) (k := k) (A := A) f) x) =
      scalarExtendedAlgebraToLocalization
        (R := R) (k := k) (A := A) (Aₑ := Aₑ) x := by
  change IsLocalization.lift _ (algebraMap _ _ x) = _
  rw [IsLocalization.lift_eq]
  rfl

@[simp]
private theorem localizationToSpecializedAway_algebraMap
    (f : A) [IsLocalization.Away f Aₑ] (a : A) :
    localizationToSpecializedAway
        (R := R) (k := k) (Aₑ := Aₑ) f (algebraMap A Aₑ a) =
      algebraMap (ScalarExtendedA (R := R) (k := k))
        (SpecializedAway (R := R) (k := k) f)
        (Algebra.TensorProduct.includeRight a) := by
  change IsLocalization.lift _ (algebraMap A Aₑ a) = _
  rw [IsLocalization.lift_eq]
  rfl

@[simp]
private theorem baseChangeLocalizationForward_includeLeft
    (f : A) [IsLocalization.Away f Aₑ] (c : k) :
    baseChangeLocalizationForward
        (R := R) (k := k) (A := A) (Aₑ := Aₑ) f
        (Algebra.TensorProduct.includeLeft
          (R := R) (S := k) (A := k) (B := Aₑ) c) =
      algebraMap k (SpecializedAway (R := R) (k := k) f) c := by
  change Algebra.TensorProduct.lift
      (Algebra.algHom k k (SpecializedAway (R := R) (k := k) f))
      (localizationToSpecializedAway
        (R := R) (k := k) (Aₑ := Aₑ) f) _
      (c ⊗ₜ[R] (1 : Aₑ)) = _
  rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  rfl

@[simp]
private theorem baseChangeLocalizationForward_includeRight
    (f : A) [IsLocalization.Away f Aₑ] (a : Aₑ) :
    baseChangeLocalizationForward
        (R := R) (k := k) (A := A) (Aₑ := Aₑ) f
        (Algebra.TensorProduct.includeRight
          (R := R) (A := k) (B := Aₑ) a) =
      localizationToSpecializedAway
        (R := R) (k := k) (Aₑ := Aₑ) f a := by
  change Algebra.TensorProduct.lift
      (Algebra.algHom k k (SpecializedAway (R := R) (k := k) f))
      (localizationToSpecializedAway
        (R := R) (k := k) (Aₑ := Aₑ) f) _
      ((1 : k) ⊗ₜ[R] a) = _
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]

@[simp]
private theorem baseChangeLocalizationBackward_localizationToSpecializedAway
    (f : A) [IsLocalization.Away f Aₑ] (a : Aₑ) :
    baseChangeLocalizationBackward
        (R := R) (k := k) (A := A) (Aₑ := Aₑ) f
        (localizationToSpecializedAway
          (R := R) (k := k) (Aₑ := Aₑ) f a) =
      Algebra.TensorProduct.includeRight a := by
  have h :
      ((baseChangeLocalizationBackward
          (R := R) (k := k) (A := A) (Aₑ := Aₑ) f).restrictScalars R).comp
          (localizationToSpecializedAway
            (R := R) (k := k) (Aₑ := Aₑ) f) =
        (Algebra.TensorProduct.includeRight :
          Aₑ →ₐ[R]
            ScalarExtendedLocalization (R := R) (k := k) (Aₑ := Aₑ)) := by
    apply IsLocalization.algHom_ext (Submonoid.powers f)
    apply AlgHom.ext
    intro x
    change baseChangeLocalizationBackward
        (R := R) (k := k) (A := A) (Aₑ := Aₑ) f
        (localizationToSpecializedAway
          (R := R) (k := k) (Aₑ := Aₑ) f (algebraMap A Aₑ x)) =
      Algebra.TensorProduct.includeRight (algebraMap A Aₑ x)
    rw [localizationToSpecializedAway_algebraMap,
      baseChangeLocalizationBackward_algebraMap]
    rfl
  exact DFunLike.congr_fun h a

private theorem baseChangeLocalizationForward_comp_scalarExtendedAlgebraToLocalization
    (f : A) [IsLocalization.Away f Aₑ] :
    (baseChangeLocalizationForward
        (R := R) (k := k) (A := A) (Aₑ := Aₑ) f).comp
        (scalarExtendedAlgebraToLocalization
          (R := R) (k := k) (A := A) (Aₑ := Aₑ)) =
      Algebra.algHom k (ScalarExtendedA (R := R) (k := k))
        (SpecializedAway (R := R) (k := k) f) := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c a =>
      rw [AlgHom.comp_apply]
      change baseChangeLocalizationForward
          (R := R) (k := k) (A := A) (Aₑ := Aₑ) f
          (c ⊗ₜ[R] algebraMap A Aₑ a) =
        algebraMap (ScalarExtendedA (R := R) (k := k))
          (SpecializedAway (R := R) (k := k) f) (c ⊗ₜ[R] a)
      rw [show c ⊗ₜ[R] algebraMap A Aₑ a =
          Algebra.TensorProduct.includeLeft
              (R := R) (S := k) (A := k) (B := Aₑ) c *
            Algebra.TensorProduct.includeRight
              (R := R) (A := k) (B := Aₑ) (algebraMap A Aₑ a) by
          rw [Algebra.TensorProduct.includeLeft_apply,
            Algebra.TensorProduct.includeRight_apply,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
      rw [map_mul, baseChangeLocalizationForward_includeLeft,
        baseChangeLocalizationForward_includeRight,
        localizationToSpecializedAway_algebraMap]
      rw [show c ⊗ₜ[R] a =
          Algebra.TensorProduct.includeLeft
              (R := R) (S := k) (A := k) (B := A) c *
            Algebra.TensorProduct.includeRight
              (R := R) (A := k) (B := A) a by
          rw [Algebra.TensorProduct.includeLeft_apply,
            Algebra.TensorProduct.includeRight_apply,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
      rw [map_mul]
      congr 1

private theorem baseChangeLocalizationForward_comp_backward
    (f : A) [IsLocalization.Away f Aₑ] :
    (baseChangeLocalizationForward
        (R := R) (k := k) (A := A) (Aₑ := Aₑ) f).comp
        (baseChangeLocalizationBackward
          (R := R) (k := k) (A := A) (Aₑ := Aₑ) f) =
      AlgHom.id k (SpecializedAway (R := R) (k := k) f) := by
  apply IsLocalization.algHom_ext (Submonoid.powers
    (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := A) f))
  apply AlgHom.ext
  intro x
  simp only [AlgHom.comp_apply]
  change baseChangeLocalizationForward
      (R := R) (k := k) (A := A) (Aₑ := Aₑ) f
      (baseChangeLocalizationBackward
        (R := R) (k := k) (A := A) (Aₑ := Aₑ) f
        (algebraMap (ScalarExtendedA (R := R) (k := k))
          (SpecializedAway (R := R) (k := k) f) x)) =
    algebraMap (ScalarExtendedA (R := R) (k := k))
      (SpecializedAway (R := R) (k := k) f) x
  rw [baseChangeLocalizationBackward_algebraMap]
  exact DFunLike.congr_fun
    (baseChangeLocalizationForward_comp_scalarExtendedAlgebraToLocalization
      (R := R) (k := k) (A := A) (Aₑ := Aₑ) f) x

private theorem baseChangeLocalizationBackward_comp_forward
    (f : A) [IsLocalization.Away f Aₑ] :
    (baseChangeLocalizationBackward
        (R := R) (k := k) (A := A) (Aₑ := Aₑ) f).comp
        (baseChangeLocalizationForward
          (R := R) (k := k) (A := A) (Aₑ := Aₑ) f) =
      AlgHom.id k
        (ScalarExtendedLocalization (R := R) (k := k) (Aₑ := Aₑ)) := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c a =>
      rw [AlgHom.comp_apply]
      change baseChangeLocalizationBackward
          (R := R) (k := k) (A := A) (Aₑ := Aₑ) f
          (baseChangeLocalizationForward
            (R := R) (k := k) (A := A) (Aₑ := Aₑ) f (c ⊗ₜ[R] a)) =
        c ⊗ₜ[R] a
      rw [show c ⊗ₜ[R] a =
          Algebra.TensorProduct.includeLeft
              (R := R) (S := k) (A := k) (B := Aₑ) c *
            Algebra.TensorProduct.includeRight
              (R := R) (A := k) (B := Aₑ) a by
          rw [Algebra.TensorProduct.includeLeft_apply,
            Algebra.TensorProduct.includeRight_apply,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
      rw [map_mul, baseChangeLocalizationForward_includeLeft,
        baseChangeLocalizationForward_includeRight, map_mul,
        AlgHom.map_algebraMap,
        baseChangeLocalizationBackward_localizationToSpecializedAway]
      rfl

/-- Scalar extension commutes with localization away from one element. -/
noncomputable def baseChangeLocalizationAwayAlgEquiv
    (f : A) [IsLocalization.Away f Aₑ] :
    k ⊗[R] Aₑ ≃ₐ[k]
      Localization.Away
        (Algebra.TensorProduct.includeRight f : k ⊗[R] A) :=
  AlgEquiv.ofAlgHom
    (baseChangeLocalizationForward
      (R := R) (k := k) (A := A) (Aₑ := Aₑ) f)
    (baseChangeLocalizationBackward
      (R := R) (k := k) (A := A) (Aₑ := Aₑ) f)
    (baseChangeLocalizationForward_comp_backward
      (R := R) (k := k) (A := A) (Aₑ := Aₑ) f)
    (baseChangeLocalizationBackward_comp_forward
      (R := R) (k := k) (A := A) (Aₑ := Aₑ) f)

@[simp]
theorem baseChangeLocalizationAwayAlgEquiv_includeLeft
    (f : A) [IsLocalization.Away f Aₑ] (c : k) :
    baseChangeLocalizationAwayAlgEquiv
        (R := R) (k := k) (A := A) (Aₑ := Aₑ) f
        (Algebra.TensorProduct.includeLeft
          (R := R) (S := k) (A := k) (B := Aₑ) c) =
      algebraMap k
        (Localization.Away
          (Algebra.TensorProduct.includeRight f : k ⊗[R] A)) c := by
  exact baseChangeLocalizationForward_includeLeft
    (R := R) (k := k) (A := A) (Aₑ := Aₑ) f c

@[simp]
theorem baseChangeLocalizationAwayAlgEquiv_includeRight_algebraMap
    (f : A) [IsLocalization.Away f Aₑ] (a : A) :
    baseChangeLocalizationAwayAlgEquiv
        (R := R) (k := k) (A := A) (Aₑ := Aₑ) f
        (Algebra.TensorProduct.includeRight (algebraMap A Aₑ a)) =
      algebraMap (k ⊗[R] A)
        (Localization.Away
          (Algebra.TensorProduct.includeRight f : k ⊗[R] A))
        (Algebra.TensorProduct.includeRight a) := by
  change baseChangeLocalizationForward
      (R := R) (k := k) (A := A) (Aₑ := Aₑ) f
      (Algebra.TensorProduct.includeRight (algebraMap A Aₑ a)) = _
  rw [baseChangeLocalizationForward_includeRight,
    localizationToSpecializedAway_algebraMap]

end Localization

section AwayEquiv

variable {k : Type u} {A : Type v} {B : Type w}
  [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]

/-- An algebra equivalence induces an equivalence between corresponding
principal localizations. -/
noncomputable def localizationAwayCongr (e : A ≃ₐ[k] B) (a : A) :
    Localization.Away a ≃ₐ[k]
      Localization.Away (e.toAlgHom a) :=
  AlgEquiv.ofBijective (Localization.awayMapₐ e.toAlgHom a)
    ⟨IsLocalization.Away.mapₐ_injective_of_injective a e.injective,
      IsLocalization.Away.mapₐ_surjective_of_surjective a e.surjective⟩

end AwayEquiv

section SpecializedQuotientChart

variable {R : Type u} {k : Type v} {A : Type w}
  [CommRing R] [CommRing k] [CommRing A]
  [Algebra R k] [Algebra R A]

/-- The scalar extension of a principal localization of an equation quotient
is the principal localization of the direct specialized quotient.  The
localization element on the right is the literal inverse image, through
`baseChangeQuotientAlgEquiv`, of the scalar extension of `chart`. -/
noncomputable def baseChangeLocalizedQuotientAlgEquiv
    (I : Ideal A) (chart : A ⧸ I) :
    k ⊗[R] Localization.Away chart ≃ₐ[k]
      Localization.Away
        ((baseChangeQuotientAlgEquiv (R := R) (k := k) I).symm
          (Algebra.TensorProduct.includeRight chart)) :=
  (baseChangeLocalizationAwayAlgEquiv
      (R := R) (k := k) (A := A ⧸ I)
      (Aₑ := Localization.Away chart) chart).trans
    (localizationAwayCongr
      (baseChangeQuotientAlgEquiv (R := R) (k := k) I).symm
      (Algebra.TensorProduct.includeRight chart))

/-- The complete two-stage specialization used for a descended chart.  First
cancel the principal-open base change `R → Rδ`, and then identify the
special fibre with the principal localization of the direct specialized
quotient. -/
noncomputable def iteratedBaseChangeLocalizedQuotientAlgEquiv
    {Rδ : Type z} [CommRing Rδ]
    [Algebra R Rδ] [Algebra Rδ k] [IsScalarTower R Rδ k]
    (I : Ideal A) (chart : A ⧸ I) :
    k ⊗[Rδ] (Rδ ⊗[R] Localization.Away chart) ≃ₐ[k]
      Localization.Away
        ((baseChangeQuotientAlgEquiv (R := R) (k := k) I).symm
          (Algebra.TensorProduct.includeRight chart)) :=
  (iteratedBaseChangeAlgEquiv R Rδ k
      (Localization.Away chart)).trans
    (baseChangeLocalizedQuotientAlgEquiv
      (R := R) (k := k) I chart)

end SpecializedQuotientChart

end


end TranslatedDepthSeven
