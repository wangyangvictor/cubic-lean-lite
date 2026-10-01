import CubicTenVariables.OffTerminalFrequencyCertificate
import CubicTenVariables.PrimePointwiseBounds
import CubicTenVariables.PrimeSquarePointwiseBounds
import CubicTenVariables.CompleteSumMultiplicativity

/-! The actual off-terminal cube-free product estimate. The common
positive integer comes from the literal projective B₄ complement. At its
prime divisors the established all-prime estimates cost p at ordinary
primes and p² at square primes. Exact CRT turns those finite exceptional
products into two gcd factors. No conductor or radical condition is used. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.OffTerminalCompleteSumBound
open MvPolynomial HessianTheorem11
open BihomogeneousIncidenceFamily ProjectiveMicrolocalData
open scoped BigOperators

private theorem exceptional_product_le_gcd (a Δ : ℕ) (ha : a ≠ 0) :
    (∏ p ∈ a.primeFactors, if p ∣ Δ then (p : ℝ) else 1) ≤ (a.gcd Δ : ℝ) := by
  have hg : a.gcd Δ ≠ 0 := (Nat.gcd_pos_of_pos_left Δ (Nat.pos_of_ne_zero ha)).ne'
  have hsub : a.primeFactors.filter (fun p => p ∣ Δ) ⊆ (a.gcd Δ).primeFactors := by
    intro p hp
    obtain ⟨hp,hpΔ⟩ := Finset.mem_filter.mp hp
    exact (Nat.prime_of_mem_primeFactors hp).mem_primeFactors
      (Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) hpΔ) hg
  have hd : (∏ p ∈ a.primeFactors.filter (fun p => p ∣ Δ), p) ∣ a.gcd Δ :=
    (Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p) hsub).trans
      (Nat.prod_primeFactors_dvd (a.gcd Δ))
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hg) hd
  rw [← Finset.prod_filter, ← Nat.cast_prod]
  exact_mod_cast hle

/-- This finite CRT helper assumes only explicit estimates of the actual
local sums. The next theorem obtains every such estimate from the existing
local theorems and the constructed off-terminal certificate. -/
theorem complete_sum_bound {F : MvPolynomial (Fin 10) ℤ} {C : ℝ}
    (hF : F.IsHomogeneous 3) (hC : 1 ≤ C) (v : Fin 10 → ℤ) (Δ : ℕ)
    (hcoarse : ∀ p : ℕ, p.Prime →
      ‖completeCubicSum F p v‖ ≤ C*(p : ℝ)^((17 : ℝ)/2) ∧
      ‖completeCubicSum F (p^2) v‖ ≤ C*(p : ℝ)^17)
    (hgood : ∀ p : ℕ, p.Prime → ¬ p ∣ Δ →
      ‖completeCubicSum F p v‖ ≤ C*(p : ℝ)^((15 : ℝ)/2) ∧
      ‖completeCubicSum F (p^2) v‖ ≤ C*(p : ℝ)^15)
    (a b : ℕ) (ha : Squarefree a) (hb : Squarefree b) (hab : a.Coprime b) :
    ‖completeCubicSum F (a*b^2) v‖ ≤
      C^(a.primeFactors.card+b.primeFactors.card)*(a : ℝ)^((15 : ℝ)/2)*
        (b : ℝ)^15*(a.gcd Δ : ℝ)*(b.gcd Δ : ℝ)^2 := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hprime (p : ℕ) (hp : p.Prime) :
      ‖completeCubicSum F p v‖ ≤ C*(p : ℝ)^((15 : ℝ)/2)*
        (if p ∣ Δ then (p : ℝ) else 1) := by
    by_cases hpΔ : p ∣ Δ
    · rw [if_pos hpΔ]
      have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
      have he : (p : ℝ)^((17 : ℝ)/2) = (p : ℝ)^((15 : ℝ)/2)*(p : ℝ) := by
        rw [show (17 : ℝ)/2 = 15/2+1 by norm_num,Real.rpow_add hp0,Real.rpow_one]
      simpa only [he,mul_assoc] using (hcoarse p hp).1
    · simpa only [if_neg hpΔ,mul_one] using (hgood p hp hpΔ).1
  have hsquare (p : ℕ) (hp : p.Prime) :
      ‖completeCubicSum F (p^2) v‖ ≤ C*(p : ℝ)^15*
        (if p ∣ Δ then (p : ℝ)^2 else 1) := by
    by_cases hpΔ : p ∣ Δ
    · rw [if_pos hpΔ]
      apply (hcoarse p hp).2.trans_eq
      ring
    · simpa only [if_neg hpΔ,mul_one] using (hgood p hp hpΔ).2
  have hp := Finset.prod_le_prod
    (fun p (_ : p ∈ a.primeFactors) => norm_nonneg (completeCubicSum F p v))
    (fun p hp => hprime p (Nat.prime_of_mem_primeFactors hp))
  have hs := Finset.prod_le_prod
    (fun p (_ : p ∈ b.primeFactors) => norm_nonneg (completeCubicSum F (p^2) v))
    (fun p hp => hsquare p (Nat.prime_of_mem_primeFactors hp))
  have hpa : (∏ p ∈ a.primeFactors, (p : ℝ)^((15 : ℝ)/2)) =
      (a : ℝ)^((15 : ℝ)/2) := by
    rw [Real.finset_prod_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
    congr 1
    rw [← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree ha]
  have hpb : (∏ p ∈ b.primeFactors, (p : ℝ)^15) = (b : ℝ)^15 := by
    rw [Finset.prod_pow, ← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree hb]
  have hsquare : (∏ p ∈ b.primeFactors, if p ∣ Δ then (p : ℝ)^2 else 1) =
      (∏ p ∈ b.primeFactors, if p ∣ Δ then (p : ℝ) else 1)^2 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro p _
    split_ifs <;> simp
  simp only [Finset.prod_mul_distrib,Finset.prod_const,hpa] at hp
  simp only [Finset.prod_mul_distrib,Finset.prod_const,hpb,hsquare] at hs
  have hp' : (∏ p ∈ a.primeFactors, ‖completeCubicSum F p v‖) ≤
      C^a.primeFactors.card*(a : ℝ)^((15 : ℝ)/2)*(a.gcd Δ : ℝ) :=
    hp.trans (mul_le_mul_of_nonneg_left (exceptional_product_le_gcd a Δ ha.ne_zero)
      (by positivity))
  have hs' : (∏ p ∈ b.primeFactors, ‖completeCubicSum F (p^2) v‖) ≤
      C^b.primeFactors.card*(b : ℝ)^15*(b.gcd Δ : ℝ)^2 := by
    apply hs.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (Finset.prod_nonneg (fun p _ => by split_ifs <;> positivity))
      (exceptional_product_le_gcd b Δ hb.ne_zero) 2
  rw [CompleteSumMultiplicativity.norm_squarefree_pair_product F hF a b ha hb hab v]
  calc
    _ ≤ (C^a.primeFactors.card*(a : ℝ)^((15 : ℝ)/2)*(a.gcd Δ : ℝ))*
        (C^b.primeFactors.card*(b : ℝ)^15*(b.gcd Δ : ℝ)^2) :=
      mul_le_mul hp' hs' (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

/-- The same constant is fixed before the frequency, certificate and
squarefree coprime factors. Both its polynomial height and every local
factor are bounded with that constant, without any good-prime restriction
on the final modulus. -/
theorem exists_bound (spread : CubicPrincipalOpenUniform.Uniform)
    (hk : Literature.HooleyKatzPointCount) (browning : Literature.BrowningCubicPointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    {t : ℕ} (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (f : Fin t → Polynomial 10 10) (N B : ℕ) (hN : 1 ≤ N)
    (hgeo : Geometry F f) (hData : TenMicrolocalIncidence.Conclusion F f N B) :
    ∃ (C : ℝ) (d : ℕ), 1 ≤ C ∧ ∀ v : Fin 10 → ℤ, v ≠ 0 →
      (fun i => (v i : ℚ)) ∉ OffTerminalFrequencyCertificate.exceptionalSet F →
      ∃ Δ : ℕ, 1 ≤ Δ ∧ N ∣ Δ ∧
        (∀ H : ℝ, 1 ≤ H → (∀ i, |(v i : ℝ)| ≤ H) → (Δ : ℝ) ≤ C*H^d) ∧
        ∀ a b : ℕ, Squarefree a → Squarefree b → a.Coprime b →
          ‖completeCubicSum F (a*b^2) v‖ ≤
            C^(a.primeFactors.card+b.primeFactors.card)*(a : ℝ)^((15 : ℝ)/2)*
              (b : ℝ)^15*(a.gcd Δ : ℝ)*(b.gcd Δ : ℝ)^2 := by
  obtain ⟨Cp,hCp,hp⟩ := PrimePointwiseBounds.exists_uniform_bound spread hk browning F hF hAn
  obtain ⟨Cs,hCs,hs,_⟩ := PrimeSquarePointwiseBounds.of_data pointcount F hF hAn f N B hN hgeo hData
  obtain ⟨Ce,d,hCe,hcert⟩ := OffTerminalFrequencyCertificate.exists_certificate pointcount hF hN hgeo hData
  let C : ℝ := max Cp (max Cs Ce)
  have hC : 1 ≤ C := hCp.trans (le_max_left _ _)
  have hCpC : Cp ≤ C := le_max_left _ _
  have hCsC : Cs ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCeC : Ce ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hcoarse (p : ℕ) (hprime : p.Prime) (v : Fin 10 → ℤ) :
      ‖completeCubicSum F p v‖ ≤ C*(p : ℝ)^((17 : ℝ)/2) ∧
      ‖completeCubicSum F (p^2) v‖ ≤ C*(p : ℝ)^17 := by
    letI : Fact p.Prime := ⟨hprime⟩
    constructor
    · have hlocal : ‖completeCubicSum F p v‖ ≤ Cp*(p : ℝ)^((17 : ℝ)/2) := by
        by_cases hv : (fun i => (v i : ZMod p)) = 0
        · exact (hp p hprime v).1 hv
        · have hpow : (p : ℝ)^8 ≤ (p : ℝ)^((17 : ℝ)/2) := by
            simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le
              (by exact_mod_cast hprime.one_lt.le : (1 : ℝ) ≤ p)
              (by norm_num : (8 : ℝ) ≤ 17/2)
          exact ((hp p hprime v).2 hv).trans
            (mul_le_mul_of_nonneg_left hpow (by linarith))
      exact hlocal.trans (mul_le_mul_of_nonneg_right hCpC (by positivity))
    · exact (hs p v).trans (mul_le_mul_of_nonneg_right hCsC (by positivity))
  refine ⟨C,d,hC,?_⟩
  intro v hv hoff
  obtain ⟨Δ,hΔ,hND,hheight,hlocal⟩ := hcert v hv hoff
  refine ⟨Δ,hΔ,hND,?_,?_⟩
  · intro H hH hvH
    exact (hheight H hH hvH).trans
      (mul_le_mul_of_nonneg_right hCeC (by positivity))
  · intro a b ha hb hab
    apply complete_sum_bound hF hC v Δ (fun p hp => hcoarse p hp v) ?_ a b ha hb hab
    intro p hp hpΔ
    letI : Fact p.Prime := ⟨hp⟩
    exact ⟨((hlocal p hpΔ).1).trans (mul_le_mul_of_nonneg_right hCeC (by positivity)),
      ((hlocal p hpΔ).2).trans (mul_le_mul_of_nonneg_right hCeC (by positivity))⟩

end CubicTenVariables.OffTerminalCompleteSumBound
