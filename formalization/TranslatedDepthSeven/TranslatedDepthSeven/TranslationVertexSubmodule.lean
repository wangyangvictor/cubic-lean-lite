import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The translation vertex is a linear subspace

For a subset `C` of a vector space, consider the directions `v` such that
every translate `x + t • v` of every `x ∈ C` remains in `C`.  These
directions form a linear subspace.  This is the set-theoretic linearity
assertion used for the affine cone over a projective variety; it needs no
equations, irreducibility, or algebraic-geometry interface.
-/

namespace TranslatedDepthSeven

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The vector-space vertex of a subset: all directions along which the
subset contains the complete affine line through each of its points. -/
def translationVertexSubmodule (C : Set V) : Submodule K V where
  carrier := {v | ∀ x ∈ C, ∀ t : K, x + t • v ∈ C}
  zero_mem' := by
    intro x hx t
    simpa using hx
  add_mem' := by
    intro v w hv hw x hx t
    rw [smul_add, ← add_assoc]
    exact hw (x + t • v) (hv x hx t) t
  smul_mem' := by
    intro a v hv x hx t
    rw [smul_smul]
    exact hv x hx (t * a)

@[simp]
theorem mem_translationVertexSubmodule_iff (C : Set V) (v : V) :
    v ∈ translationVertexSubmodule (K := K) C ↔
      ∀ x ∈ C, ∀ t : K, x + t • v ∈ C :=
  Iff.rfl

/-- Translation by any scalar multiple of a vertex direction preserves the
subset exactly, not merely in one direction. -/
theorem image_add_smul_translationVertex_eq
    (C : Set V) {v : V} (hv : v ∈ translationVertexSubmodule (K := K) C)
    (t : K) :
    (fun x : V ↦ x + t • v) '' C = C := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hv x hx t
  · intro y hy
    let x : V := y + (-t) • v
    have hx : x ∈ C := hv y hy (-t)
    refine ⟨x, hx, ?_⟩
    dsimp [x]
    module

/-- Every two points of the subset differing in a vertex direction remain
in the subset along their whole affine line. -/
theorem affineLine_subset_of_sub_mem_translationVertex
    (C : Set V) {x y : V} (hx : x ∈ C)
    (hxy : y - x ∈ translationVertexSubmodule (K := K) C) :
    ∀ t : K, x + t • (y - x) ∈ C :=
  hxy x hx

section Semilinear

variable {σ σ' : K →+* K} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

/-- A semilinear automorphism preserving the subset carries every vertex
direction to a vertex direction.  This is the formal Galois-stability
calculation; descent of the resulting stable subspace is a separate theorem. -/
theorem SemilinearEquiv.map_mem_translationVertexSubmodule
    (e : V ≃ₛₗ[σ] V) (C : Set V) (hC : e '' C = C)
    {v : V} (hv : v ∈ translationVertexSubmodule (K := K) C) :
    e v ∈ translationVertexSubmodule (K := K) C := by
  intro y hy t
  have hyImage : y ∈ e '' C := hC.symm ▸ hy
  obtain ⟨x, hx, rfl⟩ := hyImage
  have hxLine : x + σ' t • v ∈ C := hv x hx (σ' t)
  have hImage : e (x + σ' t • v) ∈ e '' C :=
    ⟨x + σ' t • v, hxLine, rfl⟩
  rw [hC] at hImage
  simpa [map_add, map_smulₛₗ, RingHomInvPair.comp_apply_eq₂] using hImage

/-- Membership in the translation vertex is invariant under every
semilinear automorphism preserving the subset. -/
theorem SemilinearEquiv.map_mem_translationVertexSubmodule_iff
    (e : V ≃ₛₗ[σ] V) (C : Set V) (hC : e '' C = C) (v : V) :
    e v ∈ translationVertexSubmodule (K := K) C ↔
      v ∈ translationVertexSubmodule (K := K) C := by
  constructor
  · intro hev
    have hsymmC : e.symm '' C = C := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hxImage : x ∈ e '' C := hC.symm ▸ hx
        obtain ⟨z, hz, hzx⟩ := hxImage
        simpa [← hzx] using hz
      · intro hy
        have hey : e y ∈ C := by
          rw [← hC]
          exact ⟨y, hy, rfl⟩
        exact ⟨e y, hey, by simp⟩
    have := SemilinearEquiv.map_mem_translationVertexSubmodule
      (σ := σ') (σ' := σ) e.symm C hsymmC hev
    simpa using this
  · exact SemilinearEquiv.map_mem_translationVertexSubmodule
      (σ := σ) (σ' := σ') e C hC

end Semilinear

end TranslatedDepthSeven
