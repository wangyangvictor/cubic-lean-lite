import TranslatedDepthSeven.CharacteristicPolynomialHeight
import Mathlib.RingTheory.Localization.NormTrace

/-!
# Descent of a separator by the algebra norm

For a finite free extension of integral domains, the algebra norm of a
nonzero element is nonzero.  Thus a separator constructed over the finite
extension descends to one literal nonzero element of the base ring.

When the base is an integral multivariate polynomial ring, the descended
element is a literal polynomial.  Its specialization at integral parameters
has the elementary support--coefficient--degree bound recorded below.

The final theorem uses Mathlib's localization base-change formula for the
norm.  After extending the base domain to a fraction field, the image of the
separator has nonzero norm and hence is a unit in the finite free scalar
extension.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped nonZeroDivisors

universe u v w z

/-- A nonzero element of a finite free extension of integral domains has
nonzero algebra norm in the base domain. -/
theorem algebraNorm_ne_zero_of_ne_zero
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDomain S]
    [Module.Free R S] [Module.Finite R S]
    {s : S} (hs : s ≠ 0) :
    Algebra.norm R s ≠ 0 :=
  Algebra.norm_ne_zero_iff.mpr hs

/-- In a finite free algebra over a field, nonvanishing of the algebra norm
forces the element itself to be a unit. -/
theorem isUnit_of_algebraNorm_ne_zero_over_field
    (K : Type u) (A : Type v)
    [Field K] [CommRing A] [Algebra K A]
    [Module.Free K A] [Module.Finite K A]
    (x : A) (hx : Algebra.norm K x ≠ 0) :
    IsUnit x := by
  apply (Algebra.lmul_isUnit_iff (R := K) (A := A)).mp
  apply (LinearMap.isUnit_iff_isUnit_det (Algebra.lmul K A x)).mpr
  rw [← Algebra.norm_apply]
  exact isUnit_iff_ne_zero.mpr hx

/-- For an integral-polynomial base, the norm is simultaneously a nonzero
polynomial and a specialization certificate with a completely literal
height bound. -/
theorem algebraNorm_polynomial_ne_zero_and_eval_natAbs_le
    {τ : Type u} [Fintype τ]
    {S : Type v} [CommRing S] [Algebra (MvPolynomial τ ℤ) S]
    [IsDomain S]
    [Module.Free (MvPolynomial τ ℤ) S]
    [Module.Finite (MvPolynomial τ ℤ) S]
    (s : S) (hs : s ≠ 0) :
    Algebra.norm (MvPolynomial τ ℤ) s ≠ 0 ∧
      ∀ (H : ℕ) (t : τ → ℤ),
        (∀ i, (t i).natAbs ≤ H) →
        (MvPolynomial.eval t
          (Algebra.norm (MvPolynomial τ ℤ) s)).natAbs ≤
          (Algebra.norm (MvPolynomial τ ℤ) s).support.card *
            mvPolynomialCoefficientNatAbsMax
              (Algebra.norm (MvPolynomial τ ℤ) s) *
            max 1 H ^
              (Algebra.norm (MvPolynomial τ ℤ) s).totalDegree := by
  constructor
  · exact algebraNorm_ne_zero_of_ne_zero hs
  · intro H t ht
    let N : MvPolynomial τ ℤ := Algebra.norm (MvPolynomial τ ℤ) s
    simpa [N] using
      (eval_natAbs_le_support_mul_coeff_mul_pow_generic N t
        (fun _m hm ↦
          coeff_natAbs_le_mvPolynomialCoefficientNatAbsMax N hm)
        le_rfl ht)

/-- Localization base change carries the norm of a separator to the norm of
its image.  If the localized base is a field, a nonzero separator therefore
becomes a unit in the finite free localized extension. -/
theorem algebraMap_isUnit_after_fractionFieldLocalization
    {R : Type u} {S : Type v} {K : Type w} {Sₘ : Type z}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDomain S]
    [Module.Free R S] [Module.Finite R S]
    [Field K] [Algebra R K] [IsLocalization R⁰ K]
    [CommRing Sₘ] [Algebra S Sₘ]
    [IsLocalization (Algebra.algebraMapSubmonoid S R⁰) Sₘ]
    [Algebra K Sₘ] [Algebra R Sₘ]
    [IsScalarTower R K Sₘ] [IsScalarTower R S Sₘ]
    [Module.Free K Sₘ] [Module.Finite K Sₘ]
    (s : S) (hs : s ≠ 0) :
    Algebra.norm K (algebraMap S Sₘ s) =
        algebraMap R K (Algebra.norm R s) ∧
      IsUnit (algebraMap S Sₘ s) := by
  have hnorm : Algebra.norm R s ≠ 0 :=
    algebraNorm_ne_zero_of_ne_zero hs
  have hmap : algebraMap R K (Algebra.norm R s) ≠ 0 := by
    simpa using
      (IsLocalization.injective K (M := R⁰) le_rfl).ne hnorm
  have hbaseChange :
      Algebra.norm K (algebraMap S Sₘ s) =
        algebraMap R K (Algebra.norm R s) :=
    Algebra.norm_localization R R⁰ s
  refine ⟨hbaseChange, ?_⟩
  apply isUnit_of_algebraNorm_ne_zero_over_field K Sₘ
    (algebraMap S Sₘ s)
  rwa [hbaseChange]

end

end TranslatedDepthSeven
