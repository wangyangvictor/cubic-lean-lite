import CubicTenVariables.ReducedFiniteFieldGeometry

/-! The ambient ten-variable point count from a general Hooley--Katz input.
All cubic geometry and specialization hypotheses are supplied by proved
application theorems; the constant precedes primes, fields and coefficients
of extensions of the fixed reduced equation. -/
noncomputable section
namespace CubicTenVariables.ReducedAmbientPointCount
open MvPolynomial HessianTheorem11 Literature

/-- Uniform affine count for the fixed integral cubic over every finite
extension of every good prime field. -/
theorem exists_uniform_bound
    (spread : CubicPrincipalOpenUniform.Uniform)
    (hk : Literature.HooleyKatzPointCount)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℕ, 1≤D ∧ ∃ C : ℝ, 1≤C ∧
      ∀ p : ℕ, p.Prime → ¬p∣D →
      ∀ (K : Type) [Field K] [Fintype K] [CharP K p],
        |(affineZeroCount (map (Int.castRingHom K) F) : ℝ) -
          (Fintype.card K : ℝ)^9| ≤
          C * ((Fintype.card K : ℝ)-1) * (Fintype.card K : ℝ)^((13 : ℝ)/2) := by
  obtain ⟨D,hD,hgeo⟩ := ReducedFiniteFieldGeometry.exists_uniform_bound spread F hF hA
  obtain ⟨C,hC,hcount⟩ := hk 10 3 4 (by decide) (by decide)
  refine ⟨D,hD,C,hC,?_⟩
  intro p hp hpD K _ _ _
  obtain ⟨hI,hS,_⟩ := (hgeo p hp hpD).2 K
  have hc := hcount K (map (Int.castRingHom K) F) (hF.map _) hI hS
  norm_num at hc ⊢
  exact hc

/-- Literal prime-field root count, including the origin. -/
theorem exists_prime_bound
    (spread : CubicPrincipalOpenUniform.Uniform)
    (hk : Literature.HooleyKatzPointCount)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℕ, 1≤D ∧ ∃ C : ℝ, 1≤C ∧
      ∀ p : ℕ, (hp : p.Prime) → ¬p∣D →
      letI : Fact p.Prime := ⟨hp⟩
      |(Nat.card {x : Fin 10 → ZMod p // eval₂ (Int.castRingHom (ZMod p)) x F=0} : ℝ) -
        (p : ℝ)^9| ≤ C * ((p : ℝ)-1) * (p : ℝ)^((13 : ℝ)/2) := by
  obtain ⟨D,hD,C,hC,h⟩ := exists_uniform_bound spread hk F hF hA
  refine ⟨D,hD,C,hC,?_⟩
  intro p hp hpD
  letI : Fact p.Prime := ⟨hp⟩
  simpa only [affineZeroCount,eval_map,ZMod.card] using h p hp hpD (ZMod p)

end CubicTenVariables.ReducedAmbientPointCount
