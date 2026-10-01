import TranslatedDepthSeven.EquationFamilyTangentBaseChange
import TranslatedDepthSeven.FiniteFamilyHomogenization

/-!
# Tangent kernels of generated ideals

This file defines the first-order tangent kernel of an actual polynomial
ideal at a point.  It proves that, at a common zero of a finite equation
family, the tangent kernel of the generated ideal is exactly the simultaneous
Jacobian kernel of the displayed generators.  Thus passing from equations to
their generated ideal introduces no hidden tangent equations.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators

open Finset MvPolynomial

variable {K : Type*} [Field K]

/-- The directional derivative of `f` at `h`, paired with the direction `z`.
This is a scalar-valued linear form in `z`. -/
def directionalDerivativeAt {n : ℕ}
    (h : Fin n → K) (f : MvPolynomial (Fin n) K) (z : Fin n → K) : K :=
  ∑ i, MvPolynomial.eval h (MvPolynomial.pderiv i f) * z i

@[simp]
theorem directionalDerivativeAt_zero {n : ℕ}
    (h z : Fin n → K) :
    directionalDerivativeAt h 0 z = 0 := by
  simp [directionalDerivativeAt]

theorem directionalDerivativeAt_add {n : ℕ}
    (h z : Fin n → K) (f g : MvPolynomial (Fin n) K) :
    directionalDerivativeAt h (f + g) z =
      directionalDerivativeAt h f z + directionalDerivativeAt h g z := by
  simp [directionalDerivativeAt, Finset.sum_add_distrib, add_mul]

theorem directionalDerivativeAt_mul {n : ℕ}
    (h z : Fin n → K) (f g : MvPolynomial (Fin n) K) :
    directionalDerivativeAt h (f * g) z =
      MvPolynomial.eval h f * directionalDerivativeAt h g z +
        MvPolynomial.eval h g * directionalDerivativeAt h f z := by
  simp only [directionalDerivativeAt, MvPolynomial.pderiv_mul,
    MvPolynomial.eval_add, MvPolynomial.eval_mul, add_mul,
    Finset.sum_add_distrib]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem directionalDerivativeAt_add_direction {n : ℕ}
    (h z w : Fin n → K) (f : MvPolynomial (Fin n) K) :
    directionalDerivativeAt h f (z + w) =
      directionalDerivativeAt h f z + directionalDerivativeAt h f w := by
  simp [directionalDerivativeAt, mul_add, Finset.sum_add_distrib]

theorem directionalDerivativeAt_smul_direction {n : ℕ}
    (h z : Fin n → K) (f : MvPolynomial (Fin n) K) (a : K) :
    directionalDerivativeAt h f (a • z) =
      a * directionalDerivativeAt h f z := by
  simp only [directionalDerivativeAt, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- For a fixed ideal and point, the tangent kernel consists of directions
annihilating the first-order part of every polynomial in the ideal. -/
def idealTangentKernel {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (h : Fin n → K) :
    Submodule K (Fin n → K) where
  carrier := {z | ∀ f ∈ I, directionalDerivativeAt h f z = 0}
  zero_mem' := by
    intro f _hf
    simp [directionalDerivativeAt]
  add_mem' := by
    intro z w hz hw f hf
    rw [directionalDerivativeAt_add_direction]
    rw [hz f hf, hw f hf, add_zero]
  smul_mem' := by
    intro a z hz f hf
    rw [directionalDerivativeAt_smul_direction, hz f hf, mul_zero]

/-- The simultaneous tangent kernel of a finite equation family, written
without choosing an ordering of the equations. -/
def finiteFamilyTangentKernel {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) K)) (h : Fin n → K) :
    Submodule K (Fin n → K) where
  carrier := {z | ∀ f ∈ equations, directionalDerivativeAt h f z = 0}
  zero_mem' := by
    intro f _hf
    simp [directionalDerivativeAt]
  add_mem' := by
    intro z w hz hw f hf
    rw [directionalDerivativeAt_add_direction]
    rw [hz f hf, hw f hf, add_zero]
  smul_mem' := by
    intro a z hz f hf
    rw [directionalDerivativeAt_smul_direction, hz f hf, mul_zero]

@[simp]
theorem mem_idealTangentKernel_iff {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (h z : Fin n → K) :
    z ∈ idealTangentKernel I h ↔
      ∀ f ∈ I, directionalDerivativeAt h f z = 0 :=
  Iff.rfl

@[simp]
theorem mem_finiteFamilyTangentKernel_iff {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) K)) (h z : Fin n → K) :
    z ∈ finiteFamilyTangentKernel equations h ↔
      ∀ f ∈ equations, directionalDerivativeAt h f z = 0 :=
  Iff.rfl

/-- At a common zero of the generators, the tangent kernel of their generated
ideal is exactly their simultaneous Jacobian kernel. -/
theorem idealTangentKernel_finiteEquationIdeal {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) K)) (h : Fin n → K)
    (hzero : h ∈ finiteAffineCommonZeroLocus equations) :
    idealTangentKernel (finiteEquationIdeal equations) h =
      finiteFamilyTangentKernel equations h := by
  apply le_antisymm
  · intro z hz f hf
    exact hz f (Ideal.subset_span hf)
  · intro z hz
    let J : Ideal (MvPolynomial (Fin n) K) :=
      { carrier := {f |
          MvPolynomial.eval h f = 0 ∧ directionalDerivativeAt h f z = 0}
        zero_mem' := by simp
        add_mem' := by
          intro f g hf hg
          constructor
          · simp [hf.1, hg.1]
          · rw [directionalDerivativeAt_add, hf.2, hg.2, add_zero]
        smul_mem' := by
          intro f g hg
          constructor
          · simp [hg.1]
          · change directionalDerivativeAt h (f * g) z = 0
            rw [directionalDerivativeAt_mul, hg.1, hg.2]
            simp }
    have hspan : finiteEquationIdeal equations ≤ J := by
      apply Ideal.span_le.mpr
      intro f hf
      constructor
      · exact hzero f hf
      · exact hz f hf
    intro g hg
    exact (hspan hg).2

section IntegralFamily

variable [Algebra ℚ K]

/-- Coefficient extension of a finite integral equation family. -/
def integralEquationFamilyOver {n : ℕ}
    (K : Type*) [Field K] (equations : Finset (MvPolynomial (Fin n) ℤ)) :
    Finset (MvPolynomial (Fin n) K) := by
  classical
  exact equations.image (MvPolynomial.map (Int.castRingHom K))

/-- For the manuscript's integral equations at an integral point, the
standard generated-ideal tangent kernel after coefficient extension is
literally the extended Jacobian kernel already constructed above. -/
theorem idealTangentKernel_mapped_integral_equations {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ)) (h : IntVector n)
    (hzero : ∀ f ∈ equations, MvPolynomial.eval h f = 0) :
    idealTangentKernel
        (finiteEquationIdeal
          (integralEquationFamilyOver K equations))
        (fun i ↦ algebraMap ℚ K (h i : ℚ)) =
      equationFamilyTangentKernelOver (K := K) equations h := by
  classical
  let equationsK : Finset (MvPolynomial (Fin n) K) :=
    integralEquationFamilyOver K equations
  let hK : Fin n → K := fun i ↦ algebraMap ℚ K (h i : ℚ)
  have hzeroK : hK ∈ finiteAffineCommonZeroLocus equationsK := by
    intro g hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
    have hpoint : hK = (fun i ↦ (h i : K)) := by
      funext i
      exact map_intCast (algebraMap ℚ K) (h i)
    rw [hpoint, eval_map_intCast, hzero f hf, Int.cast_zero]
  rw [show integralEquationFamilyOver K equations = equationsK by rfl,
    show (fun i ↦ algebraMap ℚ K (h i : ℚ)) = hK by rfl,
    idealTangentKernel_finiteEquationIdeal equationsK hK hzeroK]
  ext z
  simp only [mem_finiteFamilyTangentKernel_iff,
    mem_equationFamilyTangentKernelOver_iff, directionalDerivativeAt]
  constructor
  · intro hz f
    apply hz (MvPolynomial.map (Int.castRingHom K) f.1)
    exact Finset.mem_image.mpr ⟨f.1, f.2, rfl⟩
  · intro hz g hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
    exact hz ⟨f, hf⟩

end IntegralFamily

end

end TranslatedDepthSeven
