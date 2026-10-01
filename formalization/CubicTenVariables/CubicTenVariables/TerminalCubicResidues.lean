import CubicTenVariables.TerminalCubicSum
import Mathlib.Data.Int.GCD

/-! The terminal maximum depends only on the base point modulo gcd(A,T).
The proof uses actual integer representatives and Bezout's identity to
produce an A-translation in ZMod T. No map from a smaller residue ring
into a larger residue ring is used. -/

noncomputable section
namespace CubicTenVariables.TerminalCubicResidues
open MvPolynomial TerminalCubicSum

theorem exists_translation_of_gcd_congr (A T n : ℕ) (y y' : Fin n → ℤ)
    (h : ∀ i, (Nat.gcd A T : ℤ) ∣ y' i - y i) :
    ∃ z : Fin n → ZMod T,
      (fun i => (y' i : ZMod T)) = (fun i => (y i : ZMod T)) + (A : ZMod T) • z := by
  choose k hk using h
  refine ⟨fun i => ((Nat.gcdA A T * k i : ℤ) : ZMod T), ?_⟩
  ext i
  have he : y' i = y i + (A : ℤ) * (Nat.gcdA A T * k i) +
      (T : ℤ) * (Nat.gcdB A T * k i) := by
    have hi := hk i
    rw [Nat.gcd_eq_gcd_ab] at hi
    nlinarith [hi]
  have hc := congrArg (Int.castRingHom (ZMod T)) he
  simpa using hc

/-- The precise base-point modulus asserted in the manuscript. All
integer representatives, including negative ones, are admitted. -/
theorem terminalMax_eq_of_gcd_congr (A T : ℕ) [NeZero T] {n : ℕ}
    (F : MvPolynomial (Fin n) (ZMod T)) (hF : F.IsHomogeneous 3)
    (y y' : Fin n → ℤ) (h : ∀ i, (Nat.gcd A T : ℤ) ∣ y' i - y i) :
    terminalMax T F (A : ZMod T) (fun i => (y' i : ZMod T)) =
      terminalMax T F (A : ZMod T) (fun i => (y i : ZMod T)) := by
  obtain ⟨z, hz⟩ := exists_translation_of_gcd_congr A T n y y' h
  rw [hz, terminalMax_add_smul T F hF]

/-- In particular the value is independent of integer lifts modulo A. -/
theorem terminalMax_eq_of_congr (A T : ℕ) [NeZero T] {n : ℕ}
    (F : MvPolynomial (Fin n) (ZMod T)) (hF : F.IsHomogeneous 3)
    (y y' : Fin n → ℤ) (h : ∀ i, (A : ℤ) ∣ y' i - y i) :
    terminalMax T F (A : ZMod T) (fun i => (y' i : ZMod T)) =
      terminalMax T F (A : ZMod T) (fun i => (y i : ZMod T)) := by
  apply terminalMax_eq_of_gcd_congr A T F hF y y'
  intro i
  have hd : (Nat.gcd A T : ℤ) ∣ (A : ℤ) := by exact_mod_cast Nat.gcd_dvd_left A T
  exact hd.trans (h i)

end CubicTenVariables.TerminalCubicResidues
