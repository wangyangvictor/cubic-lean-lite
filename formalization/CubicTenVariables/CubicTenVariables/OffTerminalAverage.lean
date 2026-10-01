import CubicTenVariables.OffTerminalCompleteSumBound
import CubicTenVariables.OffTerminalWeightedSum
import CubicTenVariables.CubeFreeNonzeroAverage

/-! The actual off-terminal cube-free fixed-frequency estimate. The
exceptional set is the literal projective bad-section locus, and all
prime divisors of the common certificate are included in the average. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.OffTerminalAverage
open MvPolynomial HessianTheorem11 ProjectiveMicrolocalData
open BihomogeneousIncidenceFamily ConductorFixedFrequency
open SquarefullModulusDecomposition CubeFreeModulusDecomposition
open scoped BigOperators

/-- One uniform constant for all actual pair sums at nonzero frequencies
outside the literal B4 exceptional set. The certificate is constructed
internally after the frequency is selected. -/
theorem of_data
    (spread : CubicPrincipalOpenUniform.Uniform)
    (hk : Literature.HooleyKatzPointCount)
    (browning : Literature.BrowningCubicPointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    {t : ℕ} (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (f : Fin t → Polynomial 10 10) (N B : ℕ) (hN : 1 ≤ N)
    (hgeo : Geometry F f) (hData : TenMicrolocalIncidence.Conclusion F f N B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ v : Fin 10 → ℤ, v ≠ 0 →
      (fun i => (v i : ℚ)) ∉ OffTerminalFrequencyCertificate.exceptionalSet F →
      ∀ D : ℝ, 1 ≤ D → ∀ Q : Finset (ℕ × ℕ),
      (∀ x ∈ Q, 1 ≤ x.1 ∧ 1 ≤ x.2 ∧ Squarefree x.1 ∧ Squarefree x.2 ∧
        x.1.Coprime x.2 ∧ (x.1 : ℝ)*(x.2 : ℝ)^2 ≤ 2*D) →
      (∑ x ∈ Q, ‖completeCubicSum F (x.1*x.2^2) v‖) ≤
        M*(D*frequencyHeight v)^ε*D^((17 : ℝ)/2) := by
  classical
  obtain ⟨C,d₀,hC,hpoint⟩ := OffTerminalCompleteSumBound.exists_bound
    spread hk browning pointcount F hF hAn f N B hN hgeo hData
  obtain ⟨M,hM,hbound⟩ := OffTerminalWeightedSum.exists_bound C hC d₀ ε hε
  refine ⟨M,hM,?_⟩
  intro v hv hoff D hD Q hQ
  obtain ⟨Δ,hΔ,_hND,hheight,hpointv⟩ := hpoint v hv hoff
  have hH : 1 ≤ frequencyHeight v := by
    dsimp [frequencyHeight]
    linarith [norm_nonneg (fun j => (v j : ℝ))]
  have hvH (i : Fin 10) : |(v i : ℝ)| ≤ frequencyHeight v := by
    have hi := norm_le_pi_norm (fun j => (v j : ℝ)) i
    rw [Real.norm_eq_abs] at hi
    dsimp [frequencyHeight]
    linarith
  calc
    _ ≤ ∑ x ∈ Q, C^(x.1.primeFactors.card+x.2.primeFactors.card)*
        (x.1 : ℝ)^((15 : ℝ)/2)*(x.2 : ℝ)^15*
          (x.1.gcd Δ : ℝ)*(x.2.gcd Δ : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro x hx
      exact hpointv x.1 x.2 (hQ x hx).2.2.1 (hQ x hx).2.2.2.1
        (hQ x hx).2.2.2.2.1
    _ ≤ _ := hbound D (frequencyHeight v) hD hH Δ hΔ
      (hheight (frequencyHeight v) hH hvH) Q
      (fun x hx => ⟨(hQ x hx).1,(hQ x hx).2.1,(hQ x hx).2.2.2.2.2⟩)

/-- The same bound for the literal cube-free modulus window, with every
modulus counted once by its canonical squarefree-times-square factors. -/
theorem cubeFree_of_data
    (spread : CubicPrincipalOpenUniform.Uniform)
    (hk : Literature.HooleyKatzPointCount)
    (browning : Literature.BrowningCubicPointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    {t : ℕ} (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (f : Fin t → Polynomial 10 10) (N B : ℕ) (hN : 1 ≤ N)
    (hgeo : Geometry F f) (hData : TenMicrolocalIncidence.Conclusion F f N B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ v : Fin 10 → ℤ, v ≠ 0 →
      (fun i => (v i : ℚ)) ∉ OffTerminalFrequencyCertificate.exceptionalSet F →
      ∀ D : ℝ, 1 ≤ D →
      (∑ q ∈ CubeFreeNonzeroAverage.window D, ‖completeCubicSum F q v‖) ≤
        M*(D*frequencyHeight v)^ε*D^((17 : ℝ)/2) := by
  classical
  obtain ⟨M,hM,hbound⟩ := of_data spread hk browning pointcount
    F hF hAn f N B hN hgeo hData ε hε
  refine ⟨M,hM,?_⟩
  intro v hv hoff D hD
  let Q : Finset (ℕ × ℕ) := (CubeFreeNonzeroAverage.window D).image (fun q => (d q,c q))
  have hQ : ∀ x ∈ Q,
      1 ≤ x.1 ∧ 1 ≤ x.2 ∧ Squarefree x.1 ∧ Squarefree x.2 ∧
        x.1.Coprime x.2 ∧ (x.1 : ℝ)*(x.2 : ℝ)^2 ≤ 2*D := by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    have hw := (CubeFreeNonzeroAverage.mem_window D q).mp hq
    refine ⟨d_pos q,c_pos q,d_squarefree q,c_squarefree q hw.1,
      coprime_d_c q hw.1,?_⟩
    have he : (q : ℝ) = (d q : ℝ)*(c q : ℝ)^2 := by
      exact_mod_cast eq_d_mul_c_sq q hw.1
    exact he ▸ hw.2.2.le
  have hinj : Set.InjOn (fun q => (d q,c q))
      (↑(CubeFreeNonzeroAverage.window D) : Set ℕ) := by
    intro q hq r hr he
    exact CubeFreeModulusDecomposition.parameters_injOn
      (Nat.pos_of_ne_zero ((CubeFreeNonzeroAverage.mem_window D q).mp hq).1.1)
      (Nat.pos_of_ne_zero ((CubeFreeNonzeroAverage.mem_window D r).mp hr).1.1) he
  calc
    _ = ∑ q ∈ CubeFreeNonzeroAverage.window D, ‖completeCubicSum F (d q*(c q)^2) v‖ := by
      apply Finset.sum_congr rfl
      intro q hq
      exact congrArg (fun k => ‖completeCubicSum F k v‖)
        (eq_d_mul_c_sq q ((CubeFreeNonzeroAverage.mem_window D q).mp hq).1)
    _ = ∑ x ∈ Q, ‖completeCubicSum F (x.1*x.2^2) v‖ :=
      (Finset.sum_image (f := fun x : ℕ × ℕ => ‖completeCubicSum F (x.1*x.2^2) v‖) hinj).symm
    _ ≤ _ := hbound v hv hoff D hD Q hQ

/-- The listed literature hypotheses and proved interfaces suffice for the literal off-B4 estimate.
No incidence data, certificate, or arithmetic bound is supplied. -/
theorem exists_bound
    (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (spread : CubicPrincipalOpenUniform.Uniform)
    (hk : Literature.HooleyKatzPointCount)
    (browning : Literature.BrowningCubicPointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ v : Fin 10 → ℤ, v ≠ 0 →
      (fun i => (v i : ℚ)) ∉ OffTerminalFrequencyCertificate.exceptionalSet F →
      ∀ D : ℝ, 1 ≤ D →
      (∑ q ∈ CubeFreeNonzeroAverage.window D, ‖completeCubicSum F q v‖) ≤
        M*(D*frequencyHeight v)^ε*D^((17 : ℝ)/2) := by
  obtain ⟨t,f,N,B,hN,_hB,hgeo,hData⟩ := TenMicrolocalIncidenceData.exists_data
    microlocal F hF hAn
  exact cubeFree_of_data spread hk browning pointcount F hF hAn
    f N B hN hgeo hData ε hε

end CubicTenVariables.OffTerminalAverage
