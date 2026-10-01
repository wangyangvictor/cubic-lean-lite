import CubicTenVariables.ExponentialSums
import CubicTenVariables.PrimePowerFibers
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Uniform root counts from the absolutely convergent singular series

The normalized prime-power root-count identity is an explicit premise of
this analytic helper. Absolute convergence bounds every prime-power partial
sum by the same sum of norms. Rounding that single real bound upward gives
one natural constant before the prime or lifting level is chosen.
-/

noncomputable section
namespace CubicTenVariables.SingularSeriesUniformBound
open MvPolynomial
open scoped BigOperators

/-- Distinct powers of a prime form a finite subset of the global series,
so their partial sum has norm at most the global sum of norms. -/
theorem norm_prime_power_partial_le {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hconv : SingularSeriesAbsolutelyConvergent F) (p : ℕ) (hp : p.Prime) (s : ℕ) :
    ‖∑ h ∈ Finset.range (s+1), singularSeriesTerm F (p^h)‖ ≤
      ∑' q : ℕ, ‖singularSeriesTerm F q‖ := by
  calc
    _ ≤ ∑ h ∈ Finset.range (s+1), ‖singularSeriesTerm F (p^h)‖ := norm_sum_le _ _
    _ = ∑ q ∈ (Finset.range (s+1)).image (fun h => p^h),
        ‖singularSeriesTerm F q‖ :=
      (Finset.sum_image (f := fun q => ‖singularSeriesTerm F q‖)
        (s := Finset.range (s+1)) (g := fun h => p^h)
        (fun _ _ _ _ h => Nat.pow_right_injective hp.two_le h)).symm
    _ ≤ ∑' q : ℕ, ‖singularSeriesTerm F q‖ :=
      Summable.sum_le_tsum _ (fun _ _ => norm_nonneg _) hconv

/-- The actual unrestricted root count has a single constant uniform in
all primes and all prime-power levels. Both absolute convergence and the
literal normalized-count identity are explicit hypotheses; this helper
asserts neither of them. No lower bound on n is needed by this implication. -/
theorem exists_uniform_root_bound {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hconv : SingularSeriesAbsolutelyConvergent F)
    (hid : ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ s : ℕ,
        ((Finset.univ.filter fun z : Fin n → ZMod (p^s) =>
          eval₂ (Int.castRingHom (ZMod (p^s))) z F = 0).card : ℂ) /
          (p : ℂ)^(s*(n-1)) =
            ∑ h ∈ Finset.range (s+1), singularSeriesTerm F (p^h)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ s : ℕ,
        (Finset.univ.filter fun z : Fin n → ZMod (p^s) =>
          eval₂ (Int.castRingHom (ZMod (p^s))) z F = 0).card ≤ C*p^(s*(n-1)) := by
  obtain ⟨A,hA⟩ := exists_nat_ge (∑' q : ℕ, ‖singularSeriesTerm F q‖)
  have hC : (∑' q : ℕ, ‖singularSeriesTerm F q‖) ≤ ((A+1 : ℕ) : ℝ) :=
    hA.trans (by exact_mod_cast Nat.le_succ A)
  refine ⟨A+1, by omega, ?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro s
  have hnorm := congrArg norm (hid p hp s)
  simp only [norm_div, norm_pow, Complex.norm_natCast] at hnorm
  have hratio :
      ((Finset.univ.filter fun z : Fin n → ZMod (p^s) =>
        eval₂ (Int.castRingHom (ZMod (p^s))) z F = 0).card : ℝ) /
        (p : ℝ)^(s*(n-1)) ≤ ((A+1 : ℕ) : ℝ) := by
    rw [hnorm]
    exact (norm_prime_power_partial_le F hconv p hp s).trans hC
  have hpos : 0 < (p : ℝ)^(s*(n-1)) := pow_pos (by exact_mod_cast hp.pos) _
  have hcount := (div_le_iff₀ hpos).mp hratio
  exact_mod_cast hcount

end CubicTenVariables.SingularSeriesUniformBound
