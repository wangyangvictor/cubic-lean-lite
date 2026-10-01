import CubicTenVariables.ReducedAmbientPointCount
import CubicTenVariables.CubicConePointCountBound

/-! Uniform counts for the actual ten-variable cubic and every actual
hyperplane section. The required integrality specialization is proved internally;
the two general literature point-count bounds remain assumed. -/
noncomputable section
namespace CubicTenVariables.ReducedCubicPointCounts
open MvPolynomial HessianTheorem11 PolynomialRestriction Literature

/-- Every nonzero normal is handled by an actual frame over its field of
definition. Its base and vertex are constructed internally by linear algebra. -/
theorem exists_hyperplane_bound
    (spread : CubicPrincipalOpenUniform.Uniform)
    (browning : Literature.BrowningCubicPointCount)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℕ, 1≤D ∧ ∃ C : ℝ, 1≤C ∧
      ∀ p : ℕ, p.Prime → ¬p∣D →
      ∀ (K : Type) [Field K] [Fintype K] [CharP K p]
        (v : Fin 10 → K), v≠0 →
      |(Nat.card {x : Fin 10 → K // eval₂ (Int.castRingHom K) x F=0 ∧
        dotProduct v x=0} : ℝ) - (Fintype.card K : ℝ)^8| ≤
        C * ((Fintype.card K : ℝ)-1) * (Fintype.card K : ℝ)^6 := by
  obtain ⟨D,hD,hgeo⟩ := ReducedFiniteFieldGeometry.exists_uniform_bound spread F hF hA
  obtain ⟨C,hC,hcount⟩ := CubicConePointCountBound.exists_uniform_bound browning 9 (by decide)
  refine ⟨D,hD,C,hC,?_⟩
  intro p hp hpD K _ _ _ v hv
  obtain ⟨hp3,hgeom⟩ := hgeo p hp hpD
  obtain ⟨B,hB,hRange⟩ := HyperplaneFrames.exists_frame v hv
  obtain ⟨hI,hV⟩ := (hgeom K).2.2 B hB
  have h2 : (2 : K)≠0 := (CharP.cast_eq_zero_iff K p 2).not.mpr
    (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  have h3 : (3 : K)≠0 := (CharP.cast_eq_zero_iff K p 3).not.mpr
    (Nat.not_dvd_of_pos_of_lt (by decide) hp3)
  have hc := hcount K (restrict B (map (Int.castRingHom K) F))
    (homogeneous_restrict B _ (hF.map _)) h2 h3 hI (hV.trans (by decide : 4≤9-4))
  have he := AffineConePointCount.hyperplane_zero_card (map (Int.castRingHom K) F) v B hB hRange
  simp only [eval_map] at he
  change |(Nat.card {x : Fin 9 → K // eval x (restrict B (map (Int.castRingHom K) F))=0} : ℝ) - _| ≤ _ at hc
  rw [he] at hc
  norm_num at hc
  exact hc

/-- One exceptional integer and two constants precede every prime and
frequency in the literal prime-field count estimates needed by the sums. -/
theorem exists_prime_bounds
    (spread : CubicPrincipalOpenUniform.Uniform)
    (hk : Literature.HooleyKatzPointCount)
    (browning : Literature.BrowningCubicPointCount)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℕ, 1≤D ∧ ∃ A B : ℝ, 1≤A ∧ 1≤B ∧
      ∀ p : ℕ, (hp : p.Prime) → ¬p∣D →
      letI : Fact p.Prime := ⟨hp⟩
      (|(Nat.card {x : Fin 10 → ZMod p // eval₂ (Int.castRingHom (ZMod p)) x F=0} : ℝ) -
          (p : ℝ)^9| ≤ A * ((p : ℝ)-1) * (p : ℝ)^((13 : ℝ)/2)) ∧
      ∀ v : Fin 10 → ZMod p, v≠0 →
        |(Nat.card {x : Fin 10 → ZMod p // eval₂ (Int.castRingHom (ZMod p)) x F=0 ∧
          dotProduct v x=0} : ℝ) - (p : ℝ)^8| ≤
          B * ((p : ℝ)-1) * (p : ℝ)^6 := by
  obtain ⟨DA,hDA,A,hA',ha⟩ := ReducedAmbientPointCount.exists_prime_bound spread hk F hF hA
  obtain ⟨DB,hDB,B,hB,hb⟩ := exists_hyperplane_bound spread browning F hF hA
  refine ⟨DA*DB,Nat.mul_pos hDA hDB,A,B,hA',hB,?_⟩
  intro p hp hpD
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨ha p hp (fun h => hpD (dvd_mul_of_dvd_left h DB)),?_⟩
  intro v hv
  simpa only [ZMod.card] using
    hb p hp (fun h => hpD (dvd_mul_of_dvd_right h DA)) (ZMod p) v hv

end CubicTenVariables.ReducedCubicPointCounts
