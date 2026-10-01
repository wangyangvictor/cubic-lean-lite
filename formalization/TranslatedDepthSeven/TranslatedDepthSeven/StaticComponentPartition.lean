import TranslatedDepthSeven.StaticComparison
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A static vertex--edge--persistent partition

Let a finite set of points have, at each vertex of a finite connected graph,
either no geometric component or one component label.  Pointwise connectedness
gives three possibilities: no component at a vertex, different labels across
an edge, or one label at every vertex.  This file sums that literal
trichotomy over the finite point set.

The statement is deliberately static.  It contains no path, stopping time,
or recursively updated state.
-/

namespace TranslatedDepthSeven

noncomputable section

open SimpleGraph

universe u v w

variable {V : Type u} {A : Type v} {B : Type w}
variable {G : SimpleGraph V}

/-- The cardinality of the original point set is bounded by the sum of the
literal vertex-output, edge-intersection, and graph-persistent classes. -/
theorem card_le_sum_vertex_edge_persistent_classes
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [DecidableEq A] [Fintype B] [DecidableEq B]
    (hG : G.Connected) (X : Finset A)
    (label : A → V → Option B) :
    X.card ≤
      (∑ v : V, (X.filter fun x ↦ label x v = none).card) +
      (∑ v : V, ∑ w : V,
        (X.filter fun x ↦ G.Adj v w ∧ label x v ≠ label x w).card) +
      (∑ b : B, (X.filter fun x ↦ ∀ v, label x v = some b).card) := by
  classical
  let vertexClasses : Finset A :=
    Finset.univ.biUnion fun v ↦ X.filter fun x ↦ label x v = none
  let edgeClasses : Finset A :=
    Finset.univ.biUnion fun v ↦
      Finset.univ.biUnion fun w ↦
        X.filter fun x ↦ G.Adj v w ∧ label x v ≠ label x w
  let persistentClasses : Finset A :=
    Finset.univ.biUnion fun b ↦
      X.filter fun x ↦ ∀ v, label x v = some b
  have hcover : X ⊆ vertexClasses ∪ edgeClasses ∪ persistentClasses := by
    intro x hx
    rcases StaticComparison.connected_option_labels hG (label x) with
      ⟨v, hv⟩ | ⟨v, w, hvw, hne⟩ | ⟨b, hb⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr
        ⟨v, Finset.mem_univ v, Finset.mem_filter.mpr ⟨hx, hv⟩⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr
        ⟨v, Finset.mem_univ v, Finset.mem_biUnion.mpr
          ⟨w, Finset.mem_univ w,
            Finset.mem_filter.mpr ⟨hx, hvw, hne⟩⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr
        ⟨b, Finset.mem_univ b, Finset.mem_filter.mpr ⟨hx, hb⟩⟩
  have hvertex : vertexClasses.card ≤
      ∑ v : V, (X.filter fun x ↦ label x v = none).card := by
    exact Finset.card_biUnion_le
  have hedge : edgeClasses.card ≤
      ∑ v : V, ∑ w : V,
        (X.filter fun x ↦ G.Adj v w ∧ label x v ≠ label x w).card := by
    refine Finset.card_biUnion_le.trans ?_
    apply Finset.sum_le_sum
    intro v hv
    exact Finset.card_biUnion_le
  have hpersistent : persistentClasses.card ≤
      ∑ b : B, (X.filter fun x ↦ ∀ v, label x v = some b).card := by
    exact Finset.card_biUnion_le
  calc
    X.card ≤ (vertexClasses ∪ edgeClasses ∪ persistentClasses).card :=
      Finset.card_le_card hcover
    _ ≤ (vertexClasses ∪ edgeClasses).card + persistentClasses.card :=
      Finset.card_union_le (vertexClasses ∪ edgeClasses) persistentClasses
    _ ≤ (vertexClasses.card + edgeClasses.card) + persistentClasses.card :=
      Nat.add_le_add_right
        (Finset.card_union_le vertexClasses edgeClasses) _
    _ ≤
        ((∑ v : V, (X.filter fun x ↦ label x v = none).card) +
          (∑ v : V, ∑ w : V,
            (X.filter fun x ↦ G.Adj v w ∧ label x v ≠ label x w).card)) +
          (∑ b : B,
            (X.filter fun x ↦ ∀ v, label x v = some b).card) :=
      Nat.add_le_add (Nat.add_le_add hvertex hedge) hpersistent
    _ = _ := by omega

/-- The same static estimate without assuming that the ambient type of
component labels is finite.  A persistent nonempty label is already visible
at any fixed base vertex `v0`, so it is enough to sum over the finite image of
the original point set at that vertex. -/
theorem card_le_sum_vertex_edge_persistent_classes_at
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [DecidableEq A] [DecidableEq B]
    (hG : G.Connected) (v0 : V) (X : Finset A)
    (label : A → V → Option B) :
    X.card ≤
      (∑ v : V, (X.filter fun x ↦ label x v = none).card) +
      (∑ v : V, ∑ w : V,
        (X.filter fun x ↦ G.Adj v w ∧ label x v ≠ label x w).card) +
      (∑ o ∈ X.image (fun x ↦ label x v0),
        (X.filter fun x ↦ o ≠ none ∧ ∀ v, label x v = o).card) := by
  classical
  let vertexClasses : Finset A :=
    Finset.univ.biUnion fun v ↦ X.filter fun x ↦ label x v = none
  let edgeClasses : Finset A :=
    Finset.univ.biUnion fun v ↦
      Finset.univ.biUnion fun w ↦
        X.filter fun x ↦ G.Adj v w ∧ label x v ≠ label x w
  let occurringLabels : Finset (Option B) :=
    X.image fun x ↦ label x v0
  let persistentClasses : Finset A :=
    occurringLabels.biUnion fun o ↦
      X.filter fun x ↦ o ≠ none ∧ ∀ v, label x v = o
  have hcover : X ⊆ vertexClasses ∪ edgeClasses ∪ persistentClasses := by
    intro x hx
    rcases StaticComparison.connected_option_labels hG (label x) with
      ⟨v, hv⟩ | ⟨v, w, hvw, hne⟩ | ⟨b, hb⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr
        ⟨v, Finset.mem_univ v, Finset.mem_filter.mpr ⟨hx, hv⟩⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr
        ⟨v, Finset.mem_univ v, Finset.mem_biUnion.mpr
          ⟨w, Finset.mem_univ w,
            Finset.mem_filter.mpr ⟨hx, hvw, hne⟩⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr
        ⟨some b,
          Finset.mem_image.mpr ⟨x, hx, hb v0⟩,
          Finset.mem_filter.mpr ⟨hx, Option.some_ne_none b, hb⟩⟩
  have hvertex : vertexClasses.card ≤
      ∑ v : V, (X.filter fun x ↦ label x v = none).card := by
    exact Finset.card_biUnion_le
  have hedge : edgeClasses.card ≤
      ∑ v : V, ∑ w : V,
        (X.filter fun x ↦ G.Adj v w ∧ label x v ≠ label x w).card := by
    refine Finset.card_biUnion_le.trans ?_
    apply Finset.sum_le_sum
    intro v hv
    exact Finset.card_biUnion_le
  have hpersistent : persistentClasses.card ≤
      ∑ o ∈ X.image (fun x ↦ label x v0),
        (X.filter fun x ↦ o ≠ none ∧ ∀ v, label x v = o).card := by
    exact Finset.card_biUnion_le
  calc
    X.card ≤ (vertexClasses ∪ edgeClasses ∪ persistentClasses).card :=
      Finset.card_le_card hcover
    _ ≤ (vertexClasses ∪ edgeClasses).card + persistentClasses.card :=
      Finset.card_union_le (vertexClasses ∪ edgeClasses) persistentClasses
    _ ≤ (vertexClasses.card + edgeClasses.card) + persistentClasses.card :=
      Nat.add_le_add_right
        (Finset.card_union_le vertexClasses edgeClasses) _
    _ ≤
        ((∑ v : V, (X.filter fun x ↦ label x v = none).card) +
          (∑ v : V, ∑ w : V,
            (X.filter fun x ↦ G.Adj v w ∧ label x v ≠ label x w).card)) +
          (∑ o ∈ X.image (fun x ↦ label x v0),
            (X.filter fun x ↦ o ≠ none ∧ ∀ v, label x v = o).card) :=
      Nat.add_le_add (Nat.add_le_add hvertex hedge) hpersistent
    _ = _ := by omega

end

end TranslatedDepthSeven
