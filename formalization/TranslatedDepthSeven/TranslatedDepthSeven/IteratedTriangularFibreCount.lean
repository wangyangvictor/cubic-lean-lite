import TranslatedDepthSeven.PolynomialFibreCount

/-!
# Point counts for finite triangular polynomial systems

This file iterates the one-polynomial fibre estimate from
`PolynomialFibreCount`.  Starting with a base point of type `X`, an element of
`TriangularTuple X K n` consists of that base point followed by `n` field
coordinates.  At stage `i`, the polynomial is allowed to depend on the base
point and on precisely the preceding `i` coordinates.

If the stage-`i` polynomials are monic of degree at most `D i`, then any
finite set satisfying all the equations has at most `∏ i, D i` points above
each base point.  The statements below contain the polynomials, equations,
finite set, and degree bounds literally; there is no auxiliary counting
interface.
-/

namespace TranslatedDepthSeven

noncomputable section

open Polynomial

universe u

/-- A base point followed by `n` successively adjoined coordinates. -/
def TriangularTuple (X K : Type u) : ℕ → Type u
  | 0 => X
  | n + 1 => TriangularTuple X K n × K

instance instDecidableEqTriangularTuple
    {X K : Type u} [DecidableEq X] [DecidableEq K] :
    ∀ n, DecidableEq (TriangularTuple X K n)
  | 0 => inferInstance
  | n + 1 =>
      @instDecidableEqProd (TriangularTuple X K n) K
        (instDecidableEqTriangularTuple n) inferInstance

/-- Forget every adjoined coordinate and retain the original base point. -/
def TriangularTuple.base {X K : Type u} :
    ∀ {n : ℕ}, TriangularTuple X K n → X
  | 0, x => x
  | _n + 1, x => x.1.base

@[simp]
theorem TriangularTuple.base_zero {X K : Type u} (x : X) :
    (show TriangularTuple X K 0 from x).base = x := rfl

@[simp]
theorem TriangularTuple.base_succ {X K : Type u} {n : ℕ}
    (x : TriangularTuple X K n × K) :
    (show TriangularTuple X K (n + 1) from x).base = x.1.base := rfl

/-- The literal recursive assertion that every triangular equation vanishes.
For `n+1` coordinates it says that the first `n` equations vanish on the
prefix and that the last coordinate is a root of the last polynomial. -/
def SatisfiesTriangularEquations {X K : Type u} [Semiring K] :
    {n : ℕ} →
      (∀ i : Fin n, TriangularTuple X K i.val → Polynomial K) →
      TriangularTuple X K n → Prop
  | 0, _p, _x => True
  | n + 1, p, x =>
      SatisfiesTriangularEquations (fun i : Fin n ↦ p i.castSucc) x.1 ∧
        (p (Fin.last n) x.1).eval x.2 = 0

@[simp]
theorem satisfiesTriangularEquations_zero {X K : Type u}
    [Semiring K]
    (p : ∀ i : Fin 0, TriangularTuple X K i.val → Polynomial K) (x : X) :
    SatisfiesTriangularEquations p x := trivial

@[simp]
theorem satisfiesTriangularEquations_succ {X K : Type u} {n : ℕ}
    [Semiring K]
    (p : ∀ i : Fin (n + 1), TriangularTuple X K i.val → Polynomial K)
    (x : TriangularTuple X K n × K) :
    SatisfiesTriangularEquations p x ↔
      SatisfiesTriangularEquations (fun i : Fin n ↦ p i.castSucc) x.1 ∧
        (p (Fin.last n) x.1).eval x.2 = 0 := Iff.rfl

variable {X K : Type u} [DecidableEq X] [Field K] [DecidableEq K]

/-- Iterated triangular point count relative to an explicitly supplied finite
set of base points. -/
theorem card_triangularSet_le_prod_degrees_mul_card_base
    (n : ℕ) (B : Finset X) (S : Finset (TriangularTuple X K n))
    (p : ∀ i : Fin n, TriangularTuple X K i.val → Polynomial K)
    (D : Fin n → ℕ)
    (hbase : ∀ x ∈ S, x.base ∈ B)
    (hmonic : ∀ i x, (p i x).Monic)
    (hdegree : ∀ i x, (p i x).natDegree ≤ D i)
    (hzero : ∀ x ∈ S, SatisfiesTriangularEquations p x) :
    S.card ≤ (∏ i, D i) * B.card := by
  induction n generalizing B with
  | zero =>
      simp only [Fin.prod_univ_zero, one_mul]
      exact Finset.card_le_card (fun x hx ↦ hbase x hx)
  | succ n ih =>
      let S' : Finset (TriangularTuple X K n) := S.image Prod.fst
      have hstep : S.card ≤ D (Fin.last n) * S'.card := by
        exact card_pairs_le_degree_mul_card_image_fst_of_monic
          S (fun x ↦ p (Fin.last n) x) (D (Fin.last n))
          (fun x ↦ hmonic (Fin.last n) x)
          (fun x ↦ hdegree (Fin.last n) x)
          (by
            intro x hx
            exact (hzero x hx).2)
      have hprevious :
          S'.card ≤ (∏ i : Fin n, D i.castSucc) * B.card := by
        apply ih B S' (fun i : Fin n ↦ p i.castSucc)
        · intro x hx
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
          exact hbase y hy
        · intro i x
          exact hmonic i.castSucc x
        · intro i x
          exact hdegree i.castSucc x
        · intro x hx
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
          exact (hzero y hy).1
      calc
        S.card ≤ D (Fin.last n) * S'.card := hstep
        _ ≤ D (Fin.last n) *
              ((∏ i : Fin n, D i.castSucc) * B.card) :=
          Nat.mul_le_mul_left _ hprevious
        _ = (∏ i, D i) * B.card := by
          rw [Fin.prod_univ_castSucc]
          ac_rfl

/-- The intrinsic form: the base set is exactly the set of base coordinates
which occur in `S`. -/
theorem card_triangularSet_le_prod_degrees_mul_card_image_base
    (n : ℕ) (S : Finset (TriangularTuple X K n))
    (p : ∀ i : Fin n, TriangularTuple X K i.val → Polynomial K)
    (D : Fin n → ℕ)
    (hmonic : ∀ i x, (p i x).Monic)
    (hdegree : ∀ i x, (p i x).natDegree ≤ D i)
    (hzero : ∀ x ∈ S, SatisfiesTriangularEquations p x) :
    S.card ≤ (∏ i, D i) * (S.image TriangularTuple.base).card := by
  apply card_triangularSet_le_prod_degrees_mul_card_base n
    (S.image TriangularTuple.base) S p D
  · intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · exact hmonic
  · exact hdegree
  · exact hzero

/-- A finite triangular fibre over one fixed base point has cardinality at
most the product of the stage degrees. -/
theorem card_triangularFiber_le_prod_degrees
    (n : ℕ) (S : Finset (TriangularTuple X K n)) (x₀ : X)
    (p : ∀ i : Fin n, TriangularTuple X K i.val → Polynomial K)
    (D : Fin n → ℕ)
    (hbase : ∀ x ∈ S, x.base = x₀)
    (hmonic : ∀ i x, (p i x).Monic)
    (hdegree : ∀ i x, (p i x).natDegree ≤ D i)
    (hzero : ∀ x ∈ S, SatisfiesTriangularEquations p x) :
    S.card ≤ ∏ i, D i := by
  have h := card_triangularSet_le_prod_degrees_mul_card_base n
    {x₀} S p D
    (fun x hx ↦ by simp [hbase x hx]) hmonic hdegree hzero
  simpa using h

end

end TranslatedDepthSeven
