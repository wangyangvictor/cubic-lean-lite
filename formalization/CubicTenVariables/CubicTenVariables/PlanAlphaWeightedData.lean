import CubicTenVariables.PlanAlphaWeighted

/-! The manuscript-facing weighted cube-free estimate. Its final statement
uses the listed geometric hypotheses, proved prime-field count interface,
cubic hypotheses, and literal weights, residue majorant and finite summation domain. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PlanAlphaWeightedData
open MvPolynomial HessianTheorem11 NumericalPrimeDepth
open IntegerResidueClasses (residue)
open scoped BigOperators Classical

variable {t N Betti : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {tables : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1)}
  {C : ℝ} {d₀ : ℕ} {h : CoarseBounds F C}

/-- Specialize the finite-sample estimate to the complete modulus-first
double sum over the supplied nonzero frequencies in the translated box. -/
theorem modulus_outer_of_data
    (integrality : CubicPrincipalOpenUniform.Uniform)
    (hk : Literature.HooleyKatzPointCount)
    (browning : Literature.BrowningCubicPointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    (hP : MicrolocalRationalPartition.Conclusion F f N Betti tables)
    (hhom : F.IsHomogeneous 3) (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d₀ h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ D : ℝ, 1 ≤ D →
      ∀ (u : Fin 10 → ℝ) (L : ℝ), 1 ≤ L → ∀ (m : ℕ) [NeZero m],
      ∀ (V : Finset (Fin 10 → ℤ)) (w : (Fin 10 → ℤ) → ℝ)
        (P : (Fin 10 → ZMod m) → ℝ),
      (∀ v ∈ V, v ≠ 0 ∧ ∀ k, |(v k : ℝ)-u k| ≤ L) →
      (∀ v ∈ V, 0 ≤ w v) → (∀ b, 0 ≤ P b) →
      (∀ v ∈ V, w v ≤ P (residue m v)) →
      (∑ q ∈ (CubeFreeNonzeroAverage.window D).filter (fun q => q.Coprime (m*N)),
        ∑ v ∈ V, w v*‖completeCubicSum F q v‖) ≤
        M*(D*(2+‖u‖+L+(m : ℝ)))^ε *
          (min (D^((59 : ℝ)/6)*
            ((1+L/(m : ℝ))/D^((1 : ℝ)/3)+((1+L/(m : ℝ))/D^((1 : ℝ)/3))^9)*(∑ b, P b))
            (D^9*(∑ v ∈ V, w v)) +
           D^((13 : ℝ)/2)*(1+L/(m : ℝ))^((20 : ℝ)/3)*
             (∑ b, P b)^((2 : ℝ)/3)*(∑ v ∈ V, w v)^((1 : ℝ)/3)) := by
  obtain ⟨M,hM,hbound⟩ := PlanAlphaWeighted.of_data
    integrality hk browning pointcount hP hhom hAn hc ε hε
  refine ⟨M,hM,?_⟩
  intro D hD u L hL m hm V w P hV hw hP0 hmajor
  have hb := hbound D hD u L hL m V w P hV hw hP0 hmajor
    (((CubeFreeNonzeroAverage.window D).filter (fun q => q.Coprime (m*N))) ×ˢ V)
    (fun x hx => by
      obtain ⟨hq,hv⟩ := Finset.mem_product.mp hx
      exact ⟨(Finset.mem_filter.mp hq).1,(Finset.mem_filter.mp hq).2,hv⟩)
  simpa only [Finset.sum_product] using hb

/-- Choose the excluded integer before epsilon and every box, modulus,
frequency set or weight. No conductor, partition, depth data or arithmetic
estimate is assumed in this final statement. -/
theorem exists_bound
    (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (degreeSpan : TranslatedDepthSeven.StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCurveWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (salberger : TranslatedDepthSeven.Published.Salberger2023Theorem04)
    (integrality : CubicPrincipalOpenUniform.Uniform)
    (hk : Literature.HooleyKatzPointCount)
    (browning : Literature.BrowningCubicPointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    (F : MvPolynomial (Fin 10) ℤ) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, 1 ≤ M ∧ ∀ D : ℝ, 1 ≤ D →
        ∀ (u : Fin 10 → ℝ) (L : ℝ), 1 ≤ L → ∀ (m : ℕ) [NeZero m],
        ∀ (V : Finset (Fin 10 → ℤ)) (w : (Fin 10 → ℤ) → ℝ)
          (P : (Fin 10 → ZMod m) → ℝ),
        (∀ v ∈ V, v ≠ 0 ∧ ∀ k, |(v k : ℝ)-u k| ≤ L) →
        (∀ v ∈ V, 0 ≤ w v) → (∀ b, 0 ≤ P b) →
        (∀ v ∈ V, w v ≤ P (residue m v)) →
        (∑ q ∈ (CubeFreeNonzeroAverage.window D).filter (fun q => q.Coprime (m*N)),
          ∑ v ∈ V, w v*‖completeCubicSum F q v‖) ≤
          M*(D*(2+‖u‖+L+(m : ℝ)))^ε *
            (min (D^((59 : ℝ)/6)*
              ((1+L/(m : ℝ))/D^((1 : ℝ)/3)+((1+L/(m : ℝ))/D^((1 : ℝ)/3))^9)*(∑ b, P b))
              (D^9*(∑ v ∈ V, w v)) +
             D^((13 : ℝ)/2)*(1+L/(m : ℝ))^((20 : ℝ)/3)*
               (∑ b, P b)^((2 : ℝ)/3)*(∑ v ∈ V, w v)^((1 : ℝ)/3)) := by
  obtain ⟨t,f,N,B,tables,hP,hQ,C,d₀,h,hc⟩ := MicrolocalConductorDepth.exists_data
    microlocal degreeSpan smooth spread weil dichotomy salberger
    integrality hk browning pointcount F hhom hAn
  exact ⟨N,hP.modulus_pos,fun ε hε =>
    modulus_outer_of_data integrality hk browning pointcount hP hhom hAn hc ε hε⟩

end CubicTenVariables.PlanAlphaWeightedData
