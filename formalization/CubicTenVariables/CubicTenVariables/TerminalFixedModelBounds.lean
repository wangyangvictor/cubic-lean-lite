import CubicTenVariables.TerminalIntegralClosureModels
import CubicTenVariables.IntegralModelDimension
import CubicTenVariables.FixedEquationDimensionReduction

/-! Dimension and counting bounds for fixed models of the actual geometric
terminal closures. Containment of the reduced form's separately defined bad
loci is not asserted. -/

noncomputable section
namespace CubicTenVariables.TerminalFixedModelBounds
open MvPolynomial HessianTheorem11 TerminalIntegralClosureModels

/-- Constants are fixed before the prime or extension field is chosen.
The count concerns all prime-field solutions of the displayed equations;
the dimension bound also holds over algebraic closures of good prime fields. -/
def Bounds {n m : ℕ} (G : Fin m → MvPolynomial (Fin n) ℤ) (r : ℕ) : Prop :=
  ∃ D C : ℕ, 1 ≤ D ∧ 1 ≤ C ∧
    (∀ p : ℕ, p.Prime →
      Nat.card {x : Fin n → ZMod p //
        ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (G i) = 0} ≤ C*p^r) ∧
    ∀ p : ℕ, p.Prime → ¬ p ∣ D → ∀ (K : Type) [Field K] [CharP K p],
      ringKrullDim (MvPolynomial (Fin n) K ⧸
        FixedEquationNormalization.equationIdeal G K) ≤ (r : Dimension) ∧
      ringKrullDim (MvPolynomial (Fin n) K ⧸ vanishingIdeal K
        {x : Fin n → K | ∀ i, eval₂ (Int.castRingHom K) x (G i) = 0}) ≤ (r : Dimension)

theorem bounds_of_geometric_model {n m r : ℕ}
    (G : Fin m → MvPolynomial (Fin n) ℤ) (Z : Set (GeometricPoint n))
    (hZ : Z.Nonempty)
    (hmodel : Ideal.span (Set.range (fun i => map (Int.castRingHom GeometricField) (G i))) =
      vanishingIdeal GeometricField Z)
    (hdim : affineDimension Z ≤ (r : Dimension)) : Bounds G r := by
  obtain ⟨C,hC,hcount⟩ := IntegralModelDimension.exists_uniform_bound G Z hZ hmodel r hdim
  have hproper := IntegralModelDimension.rationalIdeal_ne_top G Z hZ hmodel
  have hd := (IntegralModelDimension.rational_quotient_dimension_eq G Z hZ hmodel).le.trans hdim
  obtain ⟨D,hD,hbound⟩ :=
    FixedEquationDimensionReduction.exists_good_characteristic_dimension_bound G hproper hd
  exact ⟨D,C,hD,hC,hcount,hbound⟩

/-- Actual integer equations for the full geometric section bad-normal
closure at threshold four, with geometric model dimension at most four in
every good characteristic and O(p^4) model points at every prime. -/
theorem exists_section_model (F : AnisotropicCubic 10) :
    ∃ m : ℕ, ∃ G : Fin m → MvPolynomial (Fin 10) ℤ,
      Ideal.span (Set.range (fun i => map (Int.castRingHom GeometricField) (G i))) =
        vanishingIdeal GeometricField (sectionClosure F.polynomial 4) ∧
      (∀ x : GeometricPoint 10, x ∈ sectionClosure F.polynomial 4 ↔
        ∀ i, eval₂ (Int.castRingHom GeometricField) x (G i) = 0) ∧ Bounds G 4 := by
  obtain ⟨m,G,hideal,hzero⟩ := exists_sectionClosure_equations F.polynomial 4
  exact ⟨m,G,hideal,hzero,bounds_of_geometric_model G _
    ⟨0,zero_mem_nonzeroClosure _⟩ hideal (ten_sectionClosure_dimension F)⟩

/-- Actual integer equations for the full geometric Gauss bad-normal
closure at threshold five, with geometric model dimension at most three in
every good characteristic and O(p^3) model points at every prime. -/
theorem exists_gauss_model (F : AnisotropicCubic 10) :
    ∃ m : ℕ, ∃ G : Fin m → MvPolynomial (Fin 10) ℤ,
      Ideal.span (Set.range (fun i => map (Int.castRingHom GeometricField) (G i))) =
        vanishingIdeal GeometricField (gaussClosure F.polynomial 5) ∧
      (∀ x : GeometricPoint 10, x ∈ gaussClosure F.polynomial 5 ↔
        ∀ i, eval₂ (Int.castRingHom GeometricField) x (G i) = 0) ∧ Bounds G 3 := by
  obtain ⟨m,G,hideal,hzero⟩ := exists_gaussClosure_equations F.polynomial 5
  exact ⟨m,G,hideal,hzero,bounds_of_geometric_model G _
    ⟨0,zero_mem_nonzeroClosure _⟩ hideal (ten_gaussClosure_dimension F)⟩

end CubicTenVariables.TerminalFixedModelBounds
