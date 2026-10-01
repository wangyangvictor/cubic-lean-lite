import TranslatedDepthSeven.FiniteProjectionResidueCount
import Mathlib.Algebra.Polynomial.Roots

/-!
# Counting finite fibres cut out by one polynomial

This is the literal point-count counterpart of one monic step in a triangular
finite presentation.  In a fibre over `x`, the second coordinate is a root of
one nonzero polynomial `p x`; hence that fibre contains at most
`natDegree (p x)` points.  Summing over the actually occurring first
coordinates gives the corresponding product bound without assuming that the
base field or the base type is finite.
-/

namespace TranslatedDepthSeven

noncomputable section

open Polynomial

variable {X K : Type*} [DecidableEq X] [Field K] [DecidableEq K]

omit [Field K] in
/-- Inside one fibre of the first projection, the second-coordinate map is
injective. -/
theorem prod_snd_injOn_finiteMapFiber_fst
    (S : Finset (X × K)) (x : X) :
    Set.InjOn Prod.snd (↑(finiteMapFiber Prod.fst S x) : Set (X × K)) := by
  intro a ha b hb hab
  have hax : a.1 = x := (mem_finiteMapFiber_iff.mp ha).2
  have hbx : b.1 = x := (mem_finiteMapFiber_iff.mp hb).2
  apply Prod.ext
  · exact hax.trans hbx.symm
  · exact hab

/-- If every point in one first-coordinate fibre has second coordinate a root
of a nonzero polynomial, the fibre cardinality is at most its degree. -/
theorem card_finiteMapFiber_fst_le_natDegree
    (S : Finset (X × K)) (x : X) (p : Polynomial K) (hp : p ≠ 0)
    (hroot : ∀ z ∈ finiteMapFiber Prod.fst S x, p.eval z.2 = 0) :
    (finiteMapFiber Prod.fst S x).card ≤ p.natDegree := by
  let values : Finset K :=
    (finiteMapFiber Prod.fst S x).image Prod.snd
  have hcard : values.card = (finiteMapFiber Prod.fst S x).card := by
    exact Finset.card_image_iff.mpr
      (prod_snd_injOn_finiteMapFiber_fst S x)
  rw [← hcard]
  apply Polynomial.card_le_degree_of_subset_roots
  intro y hy
  have hy' : y ∈ values := by
    exact hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy'
  exact (Polynomial.mem_roots hp).2 (hroot z hz)

/-- A finite set of pairs satisfying a nonzero polynomial equation in every
vertical fibre has cardinality at most the uniform degree times the number of
first coordinates which actually occur. -/
theorem card_pairs_le_degree_mul_card_image_fst
    (S : Finset (X × K)) (p : X → Polynomial K) (D : ℕ)
    (hp : ∀ x, p x ≠ 0)
    (hdegree : ∀ x, (p x).natDegree ≤ D)
    (hroot : ∀ z ∈ S, (p z.1).eval z.2 = 0) :
    S.card ≤ D * (S.image Prod.fst).card := by
  have hsum : S.card =
      ∑ x ∈ S.image Prod.fst,
        (finiteMapFiber Prod.fst S x).card := by
    simpa [finiteMapFiber] using
      (Finset.card_eq_sum_card_fiberwise
        (s := S) (t := S.image Prod.fst) (f := Prod.fst)
        (by
          intro z hz
          exact Finset.mem_image.mpr ⟨z, hz, rfl⟩))
  rw [hsum]
  calc
    (∑ x ∈ S.image Prod.fst,
        (finiteMapFiber Prod.fst S x).card) ≤
        ∑ _x ∈ S.image Prod.fst, D := by
      apply Finset.sum_le_sum
      intro x hx
      exact (card_finiteMapFiber_fst_le_natDegree S x (p x) (hp x)
        (by
          intro z hz
          have hzx := mem_finiteMapFiber_iff.mp hz
          simpa [hzx.2] using hroot z hzx.1)).trans
        (hdegree x)
    _ = D * (S.image Prod.fst).card := by
      simp [Nat.mul_comm]

/-- Monicity is a convenient sufficient condition for the nonvanishing in
the preceding finite-fibre estimate. -/
theorem card_pairs_le_degree_mul_card_image_fst_of_monic
    (S : Finset (X × K)) (p : X → Polynomial K) (D : ℕ)
    (hmonic : ∀ x, (p x).Monic)
    (hdegree : ∀ x, (p x).natDegree ≤ D)
    (hroot : ∀ z ∈ S, (p z.1).eval z.2 = 0) :
    S.card ≤ D * (S.image Prod.fst).card := by
  exact card_pairs_le_degree_mul_card_image_fst S p D
    (fun x ↦ (hmonic x).ne_zero) hdegree hroot

end

end TranslatedDepthSeven
