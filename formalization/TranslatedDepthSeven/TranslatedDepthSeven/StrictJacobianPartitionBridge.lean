import TranslatedDepthSeven.StrictRootTheorem
import TranslatedDepthSeven.DepthSevenNormalizedJacobianPartition

namespace TranslatedDepthSeven

noncomputable section

/-- Concrete cardinal reduction of the normalized set to its rank-at-most-six
part and a uniform bound for each literal rank-seven Jacobian chart. -/
theorem card_depthSevenNormalized_le_low_add_chartCount_mul
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF lowBound chartBound : ℕ)
    (hlow : (depthSevenNormalizedRankAtMostSixFinset
      p x₀ equations CF).card ≤ lowBound)
    (hchart : ∀ C : IntegralDepthSevenJacobianChartIndex equations,
      (depthSevenNormalizedJacobianChartCell
        p x₀ equations CF C).card ≤ chartBound) :
    (depthSevenNormalizedDisplacementFinset p x₀ equations CF).card ≤
      lowBound + Fintype.card
        (IntegralDepthSevenJacobianChartIndex equations) * chartBound := by
  rw [card_depthSevenNormalizedDisplacementFinset_eq_rankAtMostSix_add_chartCells]
  apply Nat.add_le_add hlow
  calc
    (∑ C : IntegralDepthSevenJacobianChartIndex equations,
        (depthSevenNormalizedJacobianChartCell
          p x₀ equations CF C).card) ≤
        ∑ _C : IntegralDepthSevenJacobianChartIndex equations, chartBound :=
      Finset.sum_le_sum fun C _ ↦ hchart C
    _ = Fintype.card
        (IntegralDepthSevenJacobianChartIndex equations) * chartBound := by
      simp

end

end TranslatedDepthSeven
