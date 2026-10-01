import CubicTenVariables.SquarefullWeightedSums
import CubicTenVariables.CubicCompositeResidueBound

/-! Reduction-fiber lifting of the literal Hessian-weighted root mass.
The composite root-count theorem has no unproved literature premise. -/

noncomputable section
namespace CubicTenVariables.SquarefullRootMassLifting
open MvPolynomial SquarefreeResidueFactors PolynomialRootPrimeFactorization
open PrimeFrogZeroMass WeightedHessianRootCRT
open scoped BigOperators

/-- Increasing a positive modulus by divisibility increases each vector gcd. -/
theorem vectorGcd_le_of_dvd {n : ℕ} (e d : ℕ) (hd : 0 < d)
    (hed : e ∣ d) (v : Fin n → ℤ) : vectorGcd e v ≤ vectorGcd d v := by
  apply Nat.le_of_dvd (vectorGcd_pos d hd v)
  exact Nat.dvd_gcd ((Nat.gcd_dvd_left e (content v)).trans hed)
    (Nat.gcd_dvd_right e (content v))

/-- The actual congruence fiber over a residue point, using its canonical lift. -/
theorem count_eq_card_reduction {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (c d : ℕ) [NeZero c] [NeZero d] (hdc : d ∣ c) (y : Fin n → ZMod d) :
    count F (integerLift d y) c d hdc =
      (Finset.univ.filter fun x : Fin n → ZMod c =>
        eval₂ (Int.castRingHom (ZMod c)) x F = 0 ∧
          (fun i => ZMod.castHom hdc (ZMod d) (x i)) = y).card := by
  classical
  rw [count_eq_card]
  simp only [integerLift, Int.cast_natCast, ZMod.natCast_zmod_val, funext_iff]

/-- An empty reduced root fiber has literal cardinality zero. -/
theorem count_eq_zero_of_not_root {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (c d : ℕ) [NeZero c] [NeZero d] (hdc : d ∣ c) (y : Fin n → ZMod d)
    (hy : eval₂ (Int.castRingHom (ZMod d)) y F ≠ 0) :
    count F (integerLift d y) c d hdc = 0 := by
  classical
  rw [count_eq_card_reduction, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hx, he⟩ := (Finset.mem_filter.mp hx).2
  apply hy
  have hmap := WeightedCRTAdapters.map_eval₂_int (ZMod.castHom hdc (ZMod d)) F x
  rw [hx, map_zero, he] at hmap
  exact hmap.symm

/-- Exact grouping by reduction, before applying any counting estimate. -/
theorem rootMass_eq_sum_count {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (c d : ℕ) [NeZero c] [NeZero d] (hdc : d ∣ c) :
    SquarefullWeightedSums.rootMass F c d hdc =
      ∑ y : Fin n → ZMod d,
        (count F (integerLift d y) c d hdc : ℝ) * kernelWeight F d y := by
  classical
  let ρ (x : Fin n → ZMod c) : Fin n → ZMod d :=
    fun i => ZMod.castHom hdc (ZMod d) (x i)
  unfold SquarefullWeightedSums.rootMass
  rw [← Finset.sum_fiberwise Finset.univ ρ]
  apply Finset.sum_congr rfl
  intro y _
  rw [count_eq_card_reduction]
  change (∑ x ∈ Finset.univ.filter (fun x => ρ x = y),
      if eval₂ (Int.castRingHom (ZMod c)) x F = 0 then kernelWeight F d (ρ x) else 0) =
    ((Finset.univ.filter fun x =>
      eval₂ (Int.castRingHom (ZMod c)) x F = 0 ∧ ρ x = y).card : ℝ) * kernelWeight F d y
  calc
    _ = ∑ x ∈ Finset.univ.filter (fun x => ρ x = y),
        if eval₂ (Int.castRingHom (ZMod c)) x F = 0 then kernelWeight F d y else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = ∑ x ∈ Finset.univ.filter (fun x =>
        eval₂ (Int.castRingHom (ZMod c)) x F = 0 ∧ ρ x = y), kernelWeight F d y := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : ρ x = y <;>
        by_cases hr : eval₂ (Int.castRingHom (ZMod c)) x F = 0 <;> simp [hx, hr]
    _ = _ := by simp

/-- Composite residue counts with both gcds enlarged from d2 to the full
squarefree divisor. The constant precedes both moduli and every residue. -/
theorem exists_uniform_fiber_bound
    
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : HessianTheorem11.Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (c d : ℕ) [NeZero c] [NeZero d] (_hd : Squarefree d) (hdc : d ∣ c)
        (y : Fin 10 → ZMod d),
        eval₂ (Int.castRingHom (ZMod d)) y F = 0 →
        (count F (integerLift d y) c d hdc : ℝ) ≤
          C * ((c/d : ℕ) : ℝ)^(9+ε) * (rootWeight F d y : ℝ) := by
  obtain ⟨C,hC,hbound⟩ :=
    CubicCompositeResidueBound.exists_composite_root_bound  F hF hA ε hε
  refine ⟨C,hC,?_⟩
  intro c d _ _ hd hdc y hy
  have hk : (d : ℤ) ∣ eval (integerLift d y) F := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, cast_eval_integerLift]
    exact hy
  have hb := hbound c d (NeZero.pos c) hd hdc (integerLift d y) hk
  have he : d2 c d ∣ d := d2_dvd_left c d (NeZero.pos c) hd hdc
  have hgrad : vectorGcd (d2 c d) (fun i => eval (integerLift d y) (pderiv i F)) ≤
      vectorGcd d (fun i => eval (integerLift d y) (pderiv i F)) :=
    vectorGcd_le_of_dvd _ _ (NeZero.pos d) he _
  have hvec : vectorGcd (d2 c d) (integerLift d y) ≤ vectorGcd d (integerLift d y) :=
    vectorGcd_le_of_dvd _ _ (NeZero.pos d) he _
  calc
    _ ≤ C * ((c/d : ℕ) : ℝ)^(9+ε) *
        vectorGcd (d2 c d) (fun i => eval (integerLift d y) (pderiv i F)) *
          vectorGcd (d2 c d) (integerLift d y) := hb
    _ ≤ C * ((c/d : ℕ) : ℝ)^(9+ε) *
        vectorGcd d (fun i => eval (integerLift d y) (pderiv i F)) *
          vectorGcd d (integerLift d y) := by
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left (by exact_mod_cast hgrad)
        exact mul_nonneg (le_trans zero_le_one hC) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      · exact_mod_cast hvec
      · exact Nat.cast_nonneg _
      · positivity
    _ = _ := by rw [rootWeight, Nat.cast_mul]; ring

/-- Literal weighted lifting to the squarefree divisor. No unproved literature
premise remains, and no root or kernel count is supplied. -/
theorem exists_uniform_bound
    
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : HessianTheorem11.Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (c d : ℕ) [NeZero c] [NeZero d], Squarefree d → (hdc : d ∣ c) →
        SquarefullWeightedSums.rootMass F c d hdc ≤
          C * ((c/d : ℕ) : ℝ)^(9+ε) * SquarefullWeightedSums.gcdRootMass F d := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_fiber_bound  F hF hA ε hε
  refine ⟨C,hC,?_⟩
  intro c d _ _ hd hdc
  rw [rootMass_eq_sum_count, SquarefullWeightedSums.gcdRootMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : eval₂ (Int.castRingHom (ZMod d)) y F = 0
  · rw [if_pos hy]
    calc
      _ ≤ (C * ((c/d : ℕ) : ℝ)^(9+ε) * (rootWeight F d y : ℝ)) * kernelWeight F d y :=
        mul_le_mul_of_nonneg_right (hbound c d hd hdc y hy) (kernelWeight_nonneg F d y)
      _ = _ := by ring
  · rw [if_neg hy, mul_zero, count_eq_zero_of_not_root F c d hdc y hy, Nat.cast_zero, zero_mul]

end CubicTenVariables.SquarefullRootMassLifting
