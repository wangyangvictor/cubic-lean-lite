import CubicTenVariables.ReducedCubicPointCounts
import CubicTenVariables.PrimePointCountTransfer

/-! The required n=10 prime pointwise estimates, with one constant before
all primes and integral frequencies. The two point-count literature propositions
remain unproved; the required integrality interface is proved internally. All cubic geometry,
cone decomposition, point-count adapters, character identities and absorption
of bad primes are proved in this development. -/
noncomputable section
namespace CubicTenVariables.PrimePointwiseBounds
open MvPolynomial HessianTheorem11

/-- The prime pointwise estimate in the project's original complete-sum
normalization, uniformly over every prime and every integral frequency. -/
theorem exists_uniform_bound
    (spread : CubicPrincipalOpenUniform.Uniform)
    (hk : Literature.HooleyKatzPointCount)
    (browning : Literature.BrowningCubicPointCount)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℝ, 1≤C ∧ ∀ p : ℕ, p.Prime → ∀ v : Fin 10 → ℤ,
      ((fun i => (v i : ZMod p))=0 →
        ‖completeCubicSum F p v‖ ≤ C*(p : ℝ)^((17 : ℝ)/2)) ∧
      ((fun i => (v i : ZMod p))≠0 →
        ‖completeCubicSum F p v‖ ≤ C*(p : ℝ)^8) := by
  obtain ⟨D,hD,A,B,hA',hB,hcounts⟩ :=
    ReducedCubicPointCounts.exists_prime_bounds spread hk browning F hF hA
  apply PrimePointCountTransfer.exists_uniform_bound F hF D hD A B
    (zero_le_one.trans hA') (zero_le_one.trans hB)
  intro p hp hpD
  exact hcounts p hp hpD

/-- The manuscript's divisibility formulation, including the equality
S_p(v)=S_p(0) when p divides every coordinate of v. -/
theorem exists_source_bound
    (spread : CubicPrincipalOpenUniform.Uniform)
    (hk : Literature.HooleyKatzPointCount)
    (browning : Literature.BrowningCubicPointCount)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℝ, 1≤C ∧ ∀ p : ℕ, p.Prime → ∀ v : Fin 10 → ℤ,
      ((∀ i, (p : ℤ)∣v i) →
        completeCubicSum F p v=completeCubicSum F p 0 ∧
        ‖completeCubicSum F p v‖ ≤ C*(p : ℝ)^((17 : ℝ)/2)) ∧
      ((¬∀ i, (p : ℤ)∣v i) →
        ‖completeCubicSum F p v‖ ≤ C*(p : ℝ)^8) := by
  obtain ⟨C,hC,h⟩ := exists_uniform_bound spread hk browning F hF hA
  refine ⟨C,hC,?_⟩
  intro p hp v
  letI : Fact p.Prime := ⟨hp⟩
  have he : (fun i => (v i : ZMod p))=0 ↔ ∀ i, (p : ℤ)∣v i := by
    simp only [_root_.funext_iff,Pi.zero_apply,ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro hv
    have hv' := he.mpr hv
    refine ⟨?_,(h p hp v).1 hv'⟩
    rw [PrimeScalarAveraging.completeCubicSum_of_frequency_mod_zero F p v hv',
      PrimeScalarAveraging.completeCubicSum_zero]
  · intro hv
    exact (h p hp v).2 (fun hz => hv (he.mp hz))

end CubicTenVariables.PrimePointwiseBounds
