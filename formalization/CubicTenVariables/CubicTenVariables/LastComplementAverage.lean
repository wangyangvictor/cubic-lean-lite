import CubicTenVariables.ComplementFrequencyPieces
import CubicTenVariables.OffTerminalAverage
import CubicTenVariables.ConductorPositiveMeanNumerics

/-! The U6 edge of the complementary mean. The actual fourth promoted
part has the proved T^4 progression count, and its B4 exclusion allows
the D^(17/2) fixed-frequency estimate. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LastComplementAverage
open MvPolynomial HessianTheorem11 ProjectiveMicrolocalData
open ConeComponentProgressionCount ConductorFixedFrequency
open MicrolocalPromotedPartition MicrolocalPartitionCounts
open scoped BigOperators

theorem of_data
    (spread : CubicPrincipalOpenUniform.Uniform)
    (hk : Literature.HooleyKatzPointCount)
    (browning : Literature.BrowningCubicPointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    {t N B : ℕ} (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1))
    (hP : MicrolocalRationalPartition.Conclusion F f N B tables)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (D : ℝ) (u : Fin 10 → ℝ) (L : ℝ) (m : ℕ)
      (b : Fin 10 → ℤ), 1 ≤ D → 0 ≤ L → 0 < m →
      (∑ v ∈ points (ComplementFrequencyPieces.piece F f tables 4) u L m b,
        ∑ q ∈ CubeFreeNonzeroAverage.window D, ‖completeCubicSum F q v‖) ≤
        M*(D*(2+‖u‖+L+(m : ℝ)))^ε*(1+L/(m : ℝ))^4*D^((17 : ℝ)/2) := by
  classical
  obtain ⟨K,hK,hcount⟩ := hP.counts.high 4 (Or.inr rfl) (ε/2) (by linarith)
  obtain ⟨A,hA,hfixed⟩ := OffTerminalAverage.cubeFree_of_data
    spread hk browning pointcount F hF hAn f N B hP.modulus_pos hP.geometry hP.incidence
    (ε/2) (by linarith)
  refine ⟨K*A,by nlinarith,?_⟩
  intro D u L m b hD hL hm
  let V := points (ComplementFrequencyPieces.piece F f tables 4) u L m b
  let H : ℝ := 2+‖u‖+L+(m : ℝ)
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hH : 0 < H := by dsimp [H]; positivity
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hT : 0 ≤ 1+L/(m : ℝ) := by positivity
  have hpoint (v : Fin 10 → ℤ) (hv : v ∈ V) :
      (∑ q ∈ CubeFreeNonzeroAverage.window D, ‖completeCubicSum F q v‖) ≤
        A*(D*H)^(ε/2)*D^((17 : ℝ)/2) := by
    have hx := (mem_points (ComplementFrequencyPieces.piece F f tables 4) u L m b v).mp hv
    have hv0 : v ≠ 0 := by
      intro hz
      apply ComplementFrequencyPieces.mem_nonzero tables 4 _ hx.2.2
      funext i
      simp [hz]
    have hoff := ComplementFrequencyPieces.mem_off_exceptional tables 4 (by decide) _ hx.2.2
    have hvH := ConductorPositiveMeanNumerics.height_le u L hL m v hx.1
    have hhv : 0 ≤ frequencyHeight v := by dsimp [frequencyHeight]; positivity
    calc
      _ ≤ A*(D*frequencyHeight v)^(ε/2)*D^((17 : ℝ)/2) := hfixed v hv0 hoff D hD
      _ ≤ A*(D*H)^(ε/2)*D^((17 : ℝ)/2) := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left _ hA0
          exact Real.rpow_le_rpow (mul_nonneg hD0.le hhv)
            (mul_le_mul_of_nonneg_left hvH hD0.le) (by linarith)
        · positivity
  have hc : (V.card : ℝ) ≤ K*H^(ε/2)*(1+L/(m : ℝ))^4 := by
    have hsub : V ⊆ points (part f (promotionFamily (fun i => (tables i).open)) 4) u L m b := by
      intro v hv
      have hx := (mem_points (ComplementFrequencyPieces.piece F f tables 4) u L m b v).mp hv
      apply (mem_points _ u L m b v).mpr
      refine ⟨hx.1,hx.2.1,?_⟩
      have he := (ComplementFrequencyPieces.piece_values tables).2.2.2.2
      rw [he] at hx
      exact hx.2.2.1
    have hcard : (V.card : ℝ) ≤
        ((points (part f (promotionFamily (fun i => (tables i).open)) 4) u L m b).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    apply hcard.trans
    simpa using hcount u L hL m hm b
  have hpower : H^(ε/2)*(D*H)^(ε/2) ≤ (D*H)^ε := by
    calc
      _ ≤ (D*H)^(ε/2)*(D*H)^(ε/2) := by
        apply mul_le_mul_of_nonneg_right
        · exact Real.rpow_le_rpow hH.le (le_mul_of_one_le_left hH.le hD) (by linarith)
        · positivity
      _ = _ := by rw [← Real.rpow_add (mul_pos hD0 hH)]; congr 1; ring
  calc
    _ ≤ ∑ v ∈ V, A*(D*H)^(ε/2)*D^((17 : ℝ)/2) := Finset.sum_le_sum hpoint
    _ = (V.card : ℝ)*(A*(D*H)^(ε/2)*D^((17 : ℝ)/2)) := by simp
    _ ≤ (K*H^(ε/2)*(1+L/(m : ℝ))^4)*(A*(D*H)^(ε/2)*D^((17 : ℝ)/2)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (K*A)*(H^(ε/2)*(D*H)^(ε/2))*(1+L/(m : ℝ))^4*D^((17 : ℝ)/2) := by ring
    _ ≤ (K*A)*(D*H)^ε*(1+L/(m : ℝ))^4*D^((17 : ℝ)/2) := by gcongr

end CubicTenVariables.LastComplementAverage
