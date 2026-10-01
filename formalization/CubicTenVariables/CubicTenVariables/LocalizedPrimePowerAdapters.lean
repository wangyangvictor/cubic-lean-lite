import CubicTenVariables.LocalizedFourierCRT
import CubicTenVariables.LocalizedFrequencyComparison
import CubicTenVariables.PrimeLocalizationResidues

/-! The two prime-power clauses of restricted multiplicativity. Above
the defining orbit level, the literal localized sum is exactly the sum
over the orbit's image at the summation level. At lower levels its norm
has a fixed bound independent of the frequency. No geometric or analytic
input is added; even homogeneity is unnecessary for these adapters. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedPrimePowerAdapters
open MvPolynomial PadicUnitOrbit LocalizedFourierCRT PrimitiveCharacterCRT
open scoped BigOperators Classical

variable {n : ℕ}

/-- The actual reduction image of the fixed p-adic unit orbit. The
defining level M and the reduction level k are kept distinct. -/
def orbitResidues (p : ℕ) [Fact p.Prime] (ξ : Fin n → ℤ_[p]) (M k : ℕ) :
    Set (Fin n → ZMod (p^k)) :=
  (fun z : Fin n → ℤ_[p] => fun i => PadicInt.toZModPow k (z i)) '' unitOrbit p ξ M

/-- The source's restricted prime-power sum, with a single positive-sign
standard character at modulus p^k and the literal level-k orbit image. -/
def orbitSum (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime]
    (ξ : Fin n → ℤ_[p]) (M k : ℕ) (v : Fin n → ℤ) : ℂ :=
  ∑ a : (ZMod (p^k))ˣ, ∑ x : Fin n → ZMod (p^k),
    if x ∈ orbitResidues p ξ M k then
      ZMod.stdAddChar ((a : ZMod (p^k))*eval₂ (Int.castRingHom (ZMod (p^k))) x F +
        ∑ i, (v i : ZMod (p^k))*x i)
    else 0

/-- Saturation of the orbit at its defining level identifies its image
at every higher level with the full inverse image of the defining residue set. -/
theorem reduction_mem_orbitResidues_iff (p : ℕ) [Fact p.Prime]
    (ξ : Fin n → ℤ_[p]) (M k : ℕ) (hMk : M ≤ k) (x : Fin n → ZMod (p^k)) :
    (fun i => ZMod.castHom (pow_dvd_pow p hMk) (ZMod (p^M)) (x i)) ∈
      orbitResidues p ξ M M ↔ x ∈ orbitResidues p ξ M k := by
  constructor
  · rintro ⟨y,hy,hyx⟩
    let z : Fin n → ℤ_[p] := fun i => ((x i).val : ℤ_[p])
    have hzk : (fun i => PadicInt.toZModPow k (z i)) = x := by
      funext i
      simp only [z,map_natCast,ZMod.natCast_zmod_val]
    have hzy : ∀ i, PadicInt.toZModPow M (z i) = PadicInt.toZModPow M (y i) := by
      intro i
      rw [←PadicInt.cast_toZModPow M k hMk,congrFun hzk i]
      exact (congrFun hyx i).symm
    exact ⟨z,mem_unitOrbit_of_reduction_eq p ξ M y z hy hzy,hzk⟩
  · rintro ⟨y,hy,hyx⟩
    refine ⟨y,hy,?_⟩
    funext i
    rw [←congrFun hyx i]
    exact (PadicInt.cast_toZModPow M k hMk (y i)).symm

/-- At equal ambient and polynomial moduli, multiplying the two
characters reproduces the single positive-sign character in the source. -/
theorem residueFourierSum_eq_unit_sum (F : MvPolynomial (Fin n) ℤ)
    (q W : ℕ) [NeZero q] (hWq : W ∣ q) (Ω : Set (Fin n → ZMod W))
    (v : Fin n → ZMod q) :
    residueFourierSum F q q W (dvd_refl q) hWq Ω v =
      ∑ a : (ZMod q)ˣ, ∑ x : Fin n → ZMod q,
        if (fun i => ZMod.castHom hWq (ZMod W) (x i)) ∈ Ω then
          ZMod.stdAddChar ((a : ZMod q)*eval₂ (Int.castRingHom (ZMod q)) x F +
            ∑ i, v i*x i)
        else 0 := by
  rw [Finset.sum_comm]
  unfold residueFourierSum
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hxΩ : (fun i => ZMod.castHom hWq (ZMod W) (x i)) ∈ Ω
  · simp only [hxΩ,if_true,ZMod.castHom_self,RingHom.id_apply,characterSum,
      AddChar.map_add_eq_mul,Finset.sum_mul]
  · simp only [hxΩ,if_false,Finset.sum_const_zero]

/-- The exact high-level adapter, valid in every dimension, including
level zero when M = k = 0. -/
theorem localized_eq_orbitSum (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [Fact p.Prime] (ξ : Fin n → ℤ_[p]) (M k : ℕ) (hMk : M ≤ k)
    (v : Fin n → ℤ) :
    localizedCompleteCubicSum F (p^k) (p^M) (orbitResidues p ξ M M) v =
      orbitSum F p ξ M k v := by
  letI : NeZero (Nat.lcm (p^k) (p^M)) :=
    ⟨Nat.lcm_ne_zero (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
      (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)⟩
  rw [localized_eq_residueFourierSum]
  refine (residueFourierSum_congr_modulus_int F (Nat.lcm_eq_left (pow_dvd_pow p hMk))
    _ _ (dvd_refl (p^k)) (pow_dvd_pow p hMk) _ v).trans ?_
  rw [residueFourierSum_eq_unit_sum]
  unfold orbitSum
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro x hx
  rw [reduction_mem_orbitResidues_iff p ξ M k hMk]

/-- The high-level identity specialized to the actual supplied prime
localization data. The residue restriction and p-adic orbit are unchanged. -/
theorem data_localized_eq_orbitSum {p : ℕ} [Fact p.Prime]
    {F : MvPolynomial (Fin 10) ℤ} (D : PrimeLocalizationData p F)
    (k : ℕ) (hMk : D.modulusExponent ≤ k) (v : Fin 10 → ℤ) :
    localizedCompleteCubicSum F (p^k) (p^D.modulusExponent) D.residueSet v =
      orbitSum F p D.center D.modulusExponent k v :=
  localized_eq_orbitSum F p D.center D.modulusExponent k hMk v

/-- The finite low-level range has a uniform bound independent of the
frequency and restriction. This elementary result only needs p ≥ 1. -/
theorem low_level_bound (F : MvPolynomial (Fin n) ℤ) (p M k : ℕ)
    (hp : 1 ≤ p) (hk : k ≤ M) (Ω : Set (Fin n → ZMod (p^M))) (v : Fin n → ℤ) :
    ‖localizedCompleteCubicSum F (p^k) (p^M) Ω v‖ ≤ (p : ℝ)^((n+1)*M) := by
  have hp0 : 0 < p := by omega
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  calc
    _ ≤ ((p^k : ℕ) : ℝ)*(Nat.lcm (p^k) (p^M) : ℝ)^n :=
      LocalizedFrequencyComparison.trivial_bound F (p^k) (p^M)
        (pow_pos hp0 _) (pow_pos hp0 _) Ω v
    _ = (p : ℝ)^k*((p : ℝ)^M)^n := by
      rw [Nat.lcm_eq_right (pow_dvd_pow p hk),Nat.cast_pow,Nat.cast_pow]
    _ ≤ (p : ℝ)^M*((p : ℝ)^M)^n :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hpR hk) (by positivity)
    _ = (p : ℝ)^((n+1)*M) := by
      rw [←pow_succ',←pow_mul]
      rw [Nat.mul_comm M (n+1)]

/-- In ten variables the source's O_p(1) can be the explicit constant
p^(11*M), valid for every frequency and every k below the chosen level. -/
theorem data_low_level_bound {p : ℕ} [Fact p.Prime]
    {F : MvPolynomial (Fin 10) ℤ} (D : PrimeLocalizationData p F)
    (k : ℕ) (hk : k < D.modulusExponent) (v : Fin 10 → ℤ) :
    ‖localizedCompleteCubicSum F (p^k) (p^D.modulusExponent) D.residueSet v‖ ≤
      (p : ℝ)^(11*D.modulusExponent) :=
  low_level_bound F p D.modulusExponent k (Fact.out : p.Prime).one_le hk.le D.residueSet v

end CubicTenVariables.LocalizedPrimePowerAdapters
