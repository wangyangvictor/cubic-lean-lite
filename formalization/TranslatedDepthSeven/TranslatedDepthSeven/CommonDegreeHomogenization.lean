import TranslatedDepthSeven.LinearNormalizationMonomialIndependence
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Putting homogeneous module elements in one degree

A finite homogeneous normalization may initially supply module elements in
different degrees.  Multiplying the element of degree `b_i` by the required
power of the distinguished degree-one normalization coordinate puts every
element in one common degree `b`.  On the affine chart where that coordinate
equals one, this operation does not change any evaluation or height bound.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

universe u v w x

/-- Multiply a homogeneous polynomial by the power of `X₀` needed to reach
the common degree `b`. -/
def commonDegreeHomogenization
    {σ : Type*} {R : Type u} [CommSemiring R]
    {I : Type v} (X₀ : MvPolynomial σ R)
    (G : I → MvPolynomial σ R) (degree : I → ℕ) (b : ℕ)
    (i : I) : MvPolynomial σ R :=
  X₀ ^ (b - degree i) * G i

/-- The displayed homogenization has exactly the common degree. -/
theorem commonDegreeHomogenization_isHomogeneous
    {σ : Type*} {R : Type u} [CommSemiring R]
    {I : Type v} (X₀ : MvPolynomial σ R)
    (G : I → MvPolynomial σ R) (degree : I → ℕ) (b : ℕ)
    (hX₀ : X₀.IsHomogeneous 1)
    (hG : ∀ i, (G i).IsHomogeneous (degree i))
    (hdegree : ∀ i, degree i ≤ b) (i : I) :
    (commonDegreeHomogenization X₀ G degree b i).IsHomogeneous b := by
  have hpow : (X₀ ^ (b - degree i)).IsHomogeneous (b - degree i) := by
    simpa using hX₀.pow (b - degree i)
  have hmul := hpow.mul (hG i)
  simpa only [commonDegreeHomogenization,
    Nat.sub_add_cancel (hdegree i)] using hmul

/-- On the affine chart `X₀=1`, common-degree homogenization changes no
evaluation. -/
theorem eval_commonDegreeHomogenization_of_eq_one
    {σ : Type*} {R : Type u} [CommSemiring R]
    {I : Type v} (X₀ : MvPolynomial σ R)
    (G : I → MvPolynomial σ R) (degree : I → ℕ) (b : ℕ)
    (y : σ → R) (hX₀ : MvPolynomial.eval y X₀ = 1) (i : I) :
    MvPolynomial.eval y
        (commonDegreeHomogenization X₀ G degree b i) =
      MvPolynomial.eval y (G i) := by
  simp [commonDegreeHomogenization, hX₀]

/-- The corresponding scalar operation preserves independence in any
algebra over a domain.  This is the quotient-algebra statement used before
choosing ambient homogeneous lifts. -/
theorem LinearIndependent.algebraMap_pow_mul_to_commonDegree
    (B : Type u) (A : Type w)
    [CommRing B] [IsDomain B] [CommRing A] [Algebra B A]
    (I : Type x) [Fintype I]
    (g : I → A) (hg : LinearIndependent B g)
    (x₀ : B) (hx₀ : x₀ ≠ 0)
    (degree : I → ℕ) (b : ℕ) :
    LinearIndependent B
      (fun i ↦ algebraMap B A (x₀ ^ (b - degree i)) * g i) := by
  exact LinearIndependent.algebraMap_mul_of_ne_zero B A I g hg
    (fun i ↦ x₀ ^ (b - degree i)) (fun _ ↦ pow_ne_zero _ hx₀)

end

end TranslatedDepthSeven
