import TranslatedDepthSeven.HomogeneousProjectiveTransport
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Tangent hyperplanes of homogeneous hypersurfaces

For a homogeneous polynomial this file constructs the literal polar linear
form at a point, proves Euler's identity after evaluation, and shows that a
projective point of the hypersurface lies on its projective tangent
hyperplane.  A nonzero gradient row cuts out a vector hyperplane of the
expected dimension.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators LinearAlgebra.Projectivization

open Finset MvPolynomial

variable {K : Type*} [Field K]

/-- The evaluated first polar of `f` at `h`, as an actual homogeneous linear
polynomial in the direction coordinates. -/
def homogeneousTangentLinearForm {n : ℕ}
    (f : MvPolynomial (Fin n) K) (h : Fin n → K) :
    MvPolynomial (Fin n) K :=
  ∑ i, C (MvPolynomial.eval h (pderiv i f)) * X i

/-- Evaluating the first polar gives the usual gradient pairing. -/
theorem eval_homogeneousTangentLinearForm {n : ℕ}
    (f : MvPolynomial (Fin n) K) (h z : Fin n → K) :
    MvPolynomial.eval z (homogeneousTangentLinearForm f h) =
      ∑ i, MvPolynomial.eval h (pderiv i f) * z i := by
  simp [homogeneousTangentLinearForm]

/-- The first polar is homogeneous of degree one, including when it is the
zero polynomial. -/
theorem homogeneousTangentLinearForm_isHomogeneous {n : ℕ}
    (f : MvPolynomial (Fin n) K) (h : Fin n → K) :
    (homogeneousTangentLinearForm f h).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum univ _ 1
  intro i _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

/-- Euler's homogeneous identity evaluated at the base point. -/
theorem eval_homogeneousTangentLinearForm_self {n d : ℕ}
    (f : MvPolynomial (Fin n) K) (h : Fin n → K)
    (hf : f.IsHomogeneous d) :
    MvPolynomial.eval h (homogeneousTangentLinearForm f h) =
      (d : K) * MvPolynomial.eval h f := by
  have heuler := congrArg (MvPolynomial.eval h) hf.sum_X_mul_pderiv
  simpa [eval_homogeneousTangentLinearForm, nsmul_eq_mul, mul_comm] using heuler

/-- A zero of a homogeneous polynomial lies on its displayed tangent linear
form. -/
theorem eval_homogeneousTangentLinearForm_self_eq_zero {n d : ℕ}
    (f : MvPolynomial (Fin n) K) (h : Fin n → K)
    (hf : f.IsHomogeneous d) (hh : MvPolynomial.eval h f = 0) :
    MvPolynomial.eval h (homogeneousTangentLinearForm f h) = 0 := by
  rw [eval_homogeneousTangentLinearForm_self f h hf, hh, mul_zero]

/-- The gradient pairing as a literal linear map. -/
def homogeneousTangentLinearMap {n : ℕ}
    (f : MvPolynomial (Fin n) K) (h : Fin n → K) :
    (Fin n → K) →ₗ[K] K where
  toFun z := ∑ i, MvPolynomial.eval h (pderiv i f) * z i
  map_add' z w := by
    simp only [Pi.add_apply, mul_add, sum_add_distrib]
  map_smul' a z := by
    simp only [smul_eq_mul, Pi.smul_apply, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Its kernel is the literal affine tangent vector hyperplane. -/
def homogeneousTangentKernel {n : ℕ}
    (f : MvPolynomial (Fin n) K) (h : Fin n → K) :
    Submodule K (Fin n → K) :=
  LinearMap.ker (homogeneousTangentLinearMap f h)

@[simp]
theorem mem_homogeneousTangentKernel_iff {n : ℕ}
    (f : MvPolynomial (Fin n) K) (h z : Fin n → K) :
    z ∈ homogeneousTangentKernel f h ↔
      ∑ i, MvPolynomial.eval h (pderiv i f) * z i = 0 :=
  Iff.rfl

/-- A nonzero gradient coordinate makes the gradient pairing surjective. -/
theorem homogeneousTangentLinearMap_surjective_of_pderiv_ne_zero
    {n : ℕ} (f : MvPolynomial (Fin n) K) (h : Fin n → K)
    {i₀ : Fin n} (hi₀ : MvPolynomial.eval h (pderiv i₀ f) ≠ 0) :
    Function.Surjective (homogeneousTangentLinearMap f h) := by
  intro a
  let z : Fin n → K := fun i ↦
    if i = i₀ then a * (MvPolynomial.eval h (pderiv i₀ f))⁻¹ else 0
  refine ⟨z, ?_⟩
  change ∑ i, MvPolynomial.eval h (pderiv i f) * z i = a
  rw [Finset.sum_eq_single i₀]
  · dsimp [z]
    rw [if_pos rfl]
    field_simp [hi₀]
  · intro j _ hj
    simp [z, hj]
  · intro hi
    exact (hi (Finset.mem_univ i₀)).elim

/-- Hence a nonzero gradient cuts out a vector hyperplane of dimension
`n-1`. -/
theorem finrank_homogeneousTangentKernel_of_pderiv_ne_zero
    {n : ℕ} (f : MvPolynomial (Fin n) K) (h : Fin n → K)
    {i₀ : Fin n} (hi₀ : MvPolynomial.eval h (pderiv i₀ f) ≠ 0) :
    Module.finrank K (homogeneousTangentKernel f h) = n - 1 := by
  have hsurj :=
    homogeneousTangentLinearMap_surjective_of_pderiv_ne_zero f h hi₀
  have hrange : LinearMap.range (homogeneousTangentLinearMap f h) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hrankNullity :=
    (homogeneousTangentLinearMap f h).finrank_range_add_finrank_ker
  have hrangeFinrank :
      Module.finrank K (LinearMap.range (homogeneousTangentLinearMap f h)) = 1 := by
    rw [hrange]
    simp
  rw [hrangeFinrank] at hrankNullity
  have hsum : 1 + Module.finrank K (homogeneousTangentKernel f h) = n := by
    simpa [homogeneousTangentKernel] using hrankNullity
  omega

/-- The literal projective tangent hyperplane at `h`. -/
def homogeneousProjectiveTangentHyperplane {n : ℕ}
    (f : MvPolynomial (Fin n) K) (h : Fin n → K) :
    Set (ℙ K (Fin n → K)) :=
  homogeneousProjectiveHypersurface (homogeneousTangentLinearForm f h)

/-- Every nonzero projective point on a homogeneous hypersurface lies on
its projective tangent hyperplane, by the evaluated Euler identity. -/
theorem projectivePoint_mem_homogeneousProjectiveTangentHyperplane
    {n d : ℕ} (f : MvPolynomial (Fin n) K) (h : Fin n → K)
    (hhne : h ≠ 0) (hf : f.IsHomogeneous d)
    (hh : MvPolynomial.eval h f = 0) :
    Projectivization.mk K h hhne ∈
      homogeneousProjectiveTangentHyperplane f h := by
  rw [homogeneousProjectiveTangentHyperplane]
  rw [mk_mem_homogeneousProjectiveHypersurface_iff _ 1
    (homogeneousTangentLinearForm_isHomogeneous f h)]
  change MvPolynomial.eval h (homogeneousTangentLinearForm f h) = 0
  exact eval_homogeneousTangentLinearForm_self_eq_zero f h hf hh

/-- If an integral affine line lies on a homogeneous integral hypersurface,
then every nonzero rational vector in the span of its base point and direction
defines a projective point of the rational tangent hyperplane.  This is the
literal projective-line containment, with no smoothness assumption. -/
theorem rationalProjectiveLine_mem_tangentHyperplane_of_integral_line
    {n d : ℕ} (f : MvPolynomial (Fin n) ℤ)
    (h z : Fin n → ℤ) (hf : f.IsHomogeneous d)
    (hline : ∀ t : ℤ,
      MvPolynomial.eval (fun i ↦ h i + t * z i) f = 0)
    (a b : ℚ)
    (hv : (fun i ↦ a * (h i : ℚ) + b * (z i : ℚ)) ≠ 0) :
    Projectivization.mk ℚ
        (fun i ↦ a * (h i : ℚ) + b * (z i : ℚ)) hv ∈
      homogeneousProjectiveTangentHyperplane
        (MvPolynomial.map (Int.castRingHom ℚ) f)
        (fun i ↦ (h i : ℚ)) := by
  let fℚ := MvPolynomial.map (Int.castRingHom ℚ) f
  let hℚ : Fin n → ℚ := fun i ↦ (h i : ℚ)
  let zℚ : Fin n → ℚ := fun i ↦ (z i : ℚ)
  have hfℚ : fℚ.IsHomogeneous d := hf.map _
  have hrootInt : MvPolynomial.eval h f = 0 := by
    simpa using hline 0
  have hrootℚ : MvPolynomial.eval hℚ fℚ = 0 := by
    dsimp [fℚ, hℚ]
    rw [eval_map_intCast]
    exact_mod_cast hrootInt
  have hhTangent :
      MvPolynomial.eval hℚ (homogeneousTangentLinearForm fℚ hℚ) = 0 :=
    eval_homogeneousTangentLinearForm_self_eq_zero fℚ hℚ hfℚ hrootℚ
  have hzInt :
      ∑ i, MvPolynomial.eval h (MvPolynomial.pderiv i f) * z i = 0 :=
    eval_starCoefficient_one_eq_zero_of_eval_line_zero f h z hline
  have hzTangent :
      MvPolynomial.eval zℚ (homogeneousTangentLinearForm fℚ hℚ) = 0 := by
    rw [eval_homogeneousTangentLinearForm]
    dsimp [fℚ, hℚ, zℚ]
    simp only [MvPolynomial.pderiv_map, eval_map_intCast]
    exact_mod_cast hzInt
  rw [homogeneousProjectiveTangentHyperplane]
  rw [mk_mem_homogeneousProjectiveHypersurface_iff _ 1
    (homogeneousTangentLinearForm_isHomogeneous fℚ hℚ)]
  change MvPolynomial.eval (fun i ↦ a * hℚ i + b * zℚ i)
    (homogeneousTangentLinearForm fℚ hℚ) = 0
  rw [eval_homogeneousTangentLinearForm]
  have hhSum :
      ∑ i, MvPolynomial.eval hℚ (MvPolynomial.pderiv i fℚ) * hℚ i = 0 := by
    simpa [eval_homogeneousTangentLinearForm] using hhTangent
  have hzSum :
      ∑ i, MvPolynomial.eval hℚ (MvPolynomial.pderiv i fℚ) * zℚ i = 0 := by
    simpa [eval_homogeneousTangentLinearForm] using hzTangent
  calc
    ∑ i, MvPolynomial.eval hℚ (MvPolynomial.pderiv i fℚ) *
          (a * hℚ i + b * zℚ i) =
        ∑ i, (a * (MvPolynomial.eval hℚ (MvPolynomial.pderiv i fℚ) * hℚ i) +
          b * (MvPolynomial.eval hℚ (MvPolynomial.pderiv i fℚ) * zℚ i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = a * (∑ i, MvPolynomial.eval hℚ (MvPolynomial.pderiv i fℚ) * hℚ i) +
        b * (∑ i, MvPolynomial.eval hℚ (MvPolynomial.pderiv i fℚ) * zℚ i) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = 0 := by rw [hhSum, hzSum]; ring

end

end TranslatedDepthSeven
