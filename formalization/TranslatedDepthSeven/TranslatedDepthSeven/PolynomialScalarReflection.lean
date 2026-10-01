import TranslatedDepthSeven.ScalarExtensionCoefficientReflection

/-!
# Scalar reflection for finite polynomial families
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators

universe u v w

variable {K : Type u} {E : Type v} {σ : Type w}
  [Field K] [Field E]

/-- Coefficients in an extended-scalar polynomial relation descend when the
base polynomial family is linearly independent. -/
theorem exists_preimage_coefficients_of_linearIndependent_polynomials
    {r : ℕ} (f : K →+* E) (hf : Function.Injective f)
    (b : Fin r → MvPolynomial σ K) (hb : LinearIndependent K b)
    (v : MvPolynomial σ K) (a : Fin r → E)
    (ha : ∑ j, a j • MvPolynomial.map f (b j) = MvPolynomial.map f v) :
    ∃ a₀ : Fin r → K, (fun i ↦ f (a₀ i)) = a := by
  classical
  let S : Finset (σ →₀ ℕ) := Finset.univ.biUnion (fun j ↦ (b j).support)
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let bv : Fin r → Fin (Fintype.card S) → K :=
    fun j i ↦ MvPolynomial.coeff (e.symm i).1 (b j)
  have hbv : LinearIndependent K bv := by
    rw [linearIndependent_iff'] at hb ⊢
    intro t c hzero j hj
    apply hb t c ?_ j hj
    ext m
    by_cases hm : m ∈ S
    · let mi : S := ⟨m, hm⟩
      have hz := congrFun hzero (e mi)
      rw [MvPolynomial.coeff_sum]
      simpa [bv, mi, MvPolynomial.coeff_smul] using hz
    · have hmj : ∀ i, MvPolynomial.coeff m (b i) = 0 := by
        intro i
        apply MvPolynomial.notMem_support_iff.mp
        intro hmi
        apply hm
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hmi⟩
      simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, hmj]
  let vv : Fin (Fintype.card S) → K := fun i ↦
    MvPolynomial.coeff (e.symm i).1 v
  have hav : ∀ i, ∑ j, a j * f (bv j i) = f (vv i) := by
    intro i
    have hcoeff := congrArg (MvPolynomial.coeff (e.symm i).1) ha
    simpa [bv, vv, MvPolynomial.coeff_sum,
      MvPolynomial.coeff_smul, MvPolynomial.coeff_map] using hcoeff
  exact exists_preimage_coefficients_of_linearIndependent_family
    f hf bv hbv vv a hav

end

end TranslatedDepthSeven
