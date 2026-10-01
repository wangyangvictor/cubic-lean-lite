import CubicTenVariables.PrimeCoprimeSeries

/-! Remove finitely many prime factors from an absolutely convergent
multiplicative series, retaining an exact identity and positivity. -/

noncomputable section
namespace CubicTenVariables.FiniteCoprimeSeries
open PrimeCoprimeSeries
open scoped BigOperators

def mask (s : Finset ℕ) (f : ℕ → ℂ) (q : ℕ) : ℂ :=
  if ∀ p ∈ s, Nat.Coprime p q then f q else 0

@[simp] theorem mask_empty (f : ℕ → ℂ) : mask ∅ f = f := by
  funext q
  simp [mask]

@[simp] theorem mask_zero (s : Finset ℕ) (f : ℕ → ℂ) (hf : f 0 = 0) :
    mask s f 0 = 0 := by simp [mask, hf]

theorem summable_norm_mask (s : Finset ℕ) (f : ℕ → ℂ)
    (hf : Summable (fun q => ‖f q‖)) : Summable (fun q => ‖mask s f q‖) := by
  apply hf.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro q
  by_cases h : ∀ p ∈ s, Nat.Coprime p q
  · simp only [mask, if_pos h, le_refl]
  · simp only [mask, if_neg h, norm_zero, norm_nonneg]

theorem mask_multiplicative (s : Finset ℕ) (f : ℕ → ℂ)
    (hf : ∀ {a b : ℕ}, Nat.Coprime a b → f (a*b) = f a*f b)
    {a b : ℕ} (hab : Nat.Coprime a b) :
    mask s f (a*b) = mask s f a * mask s f b := by
  have hi : (∀ p ∈ s, Nat.Coprime p (a*b)) ↔
      (∀ p ∈ s, Nat.Coprime p a) ∧ (∀ p ∈ s, Nat.Coprime p b) := by
    simp only [Nat.coprime_mul_iff_right, forall_and]
  by_cases ha : ∀ p ∈ s, Nat.Coprime p a
  · by_cases hb : ∀ p ∈ s, Nat.Coprime p b
    · simp only [mask, if_pos ha, if_pos hb, if_pos (hi.mpr ⟨ha,hb⟩), hf hab]
    · have hn : ¬∀ p ∈ s, Nat.Coprime p (a*b) := fun h => hb (hi.mp h).2
      simp only [mask, if_pos ha, if_neg hb, if_neg hn, mul_zero]
  · have hn : ¬∀ p ∈ s, Nat.Coprime p (a*b) := fun h => ha (hi.mp h).1
    simp only [mask, if_neg ha, if_neg hn, zero_mul]

theorem mask_prime_power (s : Finset ℕ) (hs : ∀ q ∈ s, q.Prime)
    (f : ℕ → ℂ) (p : ℕ) (hp : p.Prime) (hps : p ∉ s) (k : ℕ) :
    mask s f (p^k) = f (p^k) := by
  apply if_pos
  intro q hq
  apply Nat.Coprime.pow_right
  exact (Nat.coprime_primes (hs q hq) hp).mpr (by
    intro h
    subst q
    exact hps hq)

theorem tsum_mask_insert (s : Finset ℕ) (f : ℕ → ℂ) (hf0 : f 0 = 0)
    (p : ℕ) :
    (∑' q, mask (insert p s) f q) = ∑' q : CoprimePart p, mask s f q := by
  have he : (∑' q : CoprimePart p, mask s f q) =
      ∑' q, Set.indicator {q : ℕ | q ≠ 0 ∧ Nat.Coprime p q} (mask s f) q :=
    tsum_subtype {q : ℕ | q ≠ 0 ∧ Nat.Coprime p q} (mask s f)
  rw [he]
  apply tsum_congr
  intro q
  by_cases hq : q = 0
  · subst q
    simp [mask, hf0, Set.indicator]
  · have hi : (∀ t ∈ insert p s, Nat.Coprime t q) ↔
        Nat.Coprime p q ∧ (∀ t ∈ s, Nat.Coprime t q) := by simp only [Finset.forall_mem_insert]
    by_cases hpq : Nat.Coprime p q
    · by_cases hs : ∀ t ∈ s, Nat.Coprime t q
      · simp only [mask, Set.indicator, Set.mem_setOf_eq, hq, not_false_eq_true,
          hpq, and_self, if_true, if_pos hs, if_pos (hi.mpr ⟨hpq,hs⟩)]
        exact (if_pos ⟨hq, hpq⟩).symm
      · have hn : ¬∀ t ∈ insert p s, Nat.Coprime t q := fun h => hs (hi.mp h).2
        simp only [mask, Set.indicator, Set.mem_setOf_eq, hq, not_false_eq_true,
          hpq, and_self, if_true, if_neg hs, if_neg hn]
        simp
    · have hn : ¬∀ t ∈ insert p s, Nat.Coprime t q := fun h => hpq (hi.mp h).1
      simp only [mask, Set.indicator, Set.mem_setOf_eq, hpq, and_false, if_false, if_neg hn]

/-- The exact finite-prime removal identity, justified by absolute
convergence of the original coefficients. -/
theorem tsum_eq_finite_product (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (f : ℕ → ℂ) (hf0 : f 0 = 0)
    (hmul : ∀ {a b : ℕ}, Nat.Coprime a b → f (a*b) = f a*f b)
    (hf : Summable (fun q => ‖f q‖)) :
    (∑' q, f q) = (∏ p ∈ s, ∑' k : ℕ, f (p^k)) * ∑' q, mask s f q := by
  induction s using Finset.induction with
  | empty => simp
  | @insert p s hps ih =>
    have hp := hs p (Finset.mem_insert_self p s)
    have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
    have hi := ih hs'
    have hg := tsum_multiplicative p hp (mask s f) (mask_zero s f hf0)
      (fun hab => mask_multiplicative s f hmul hab) (summable_norm_mask s f hf)
    simp_rw [mask_prime_power s hs' f p hp hps] at hg
    rw [← tsum_mask_insert s f hf0 p] at hg
    rw [hi, hg, Finset.prod_insert hps]
    ring

/-- A positive global sum and nonnegative real local factors force the
coprime subseries to have positive real part. No factor nonvanishing is assumed. -/
theorem masked_tsum_re_pos (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (f : ℕ → ℂ) (hf0 : f 0 = 0)
    (hmul : ∀ {a b : ℕ}, Nat.Coprime a b → f (a*b) = f a*f b)
    (hf : Summable (fun q => ‖f q‖)) (hpos : 0 < (∑' q, f q).re)
    (σ : ℕ → ℝ) (hσ : ∀ p ∈ s, 0 ≤ σ p)
    (hlocal : ∀ p ∈ s, (∑' k : ℕ, f (p^k)) = (σ p : ℂ)) :
    0 < ∏ p ∈ s, σ p ∧ 0 < (∑' q, mask s f q).re := by
  have he := tsum_eq_finite_product s hs f hf0 hmul hf
  have hl : (∏ p ∈ s, ∑' k : ℕ, f (p^k)) = ((∏ p ∈ s, σ p : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl hlocal
  rw [he, hl] at hpos
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hpos
  have hn : 0 ≤ ∏ p ∈ s, σ p := Finset.prod_nonneg hσ
  have hc : 0 < (∑' q, mask s f q).re := by nlinarith
  exact ⟨by nlinarith, hc⟩

end CubicTenVariables.FiniteCoprimeSeries
