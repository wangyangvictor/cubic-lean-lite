import TranslatedDepthSeven.FiniteEquationComponentLabel
import TranslatedDepthSeven.StaticComponentPartition

/-!
# A static partition for literal polynomial equation families

At every vertex of a finite connected graph, fix a finite family of
polynomial equations.  Each point is labelled by the selected minimal-prime
component of that literal family, or by `none` when it is off the displayed
zero locus.

The finite point set is bounded by three explicit classes: points off a
displayed locus at some vertex, points lying on every displayed locus but
having distinct selected components across an edge, and points having one
persistent selected component at every vertex.  Persistent labels are summed
only over their finite image at one fixed base vertex; no finiteness
assumption is made on the type of all ideals.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial SimpleGraph

universe u v w

variable {K : Type u} {σ : Type v} {V : Type w}
variable [Field K] [Fintype σ]

/-- The points of `X` lying on the literal common zero locus at every graph
vertex. -/
def finiteEquationAllVertexLocusPoints
    [Fintype V]
    (equations : V → Finset (MvPolynomial σ K))
    (X : Finset (σ → K)) : Finset (σ → K) := by
  classical
  exact X.filter fun z ↦
    ∀ v, z ∈ finiteAffineCommonZeroLocus (equations v)

omit [Fintype σ] in
@[simp]
theorem mem_finiteEquationAllVertexLocusPoints_iff
    [Fintype V]
    (equations : V → Finset (MvPolynomial σ K))
    (X : Finset (σ → K)) (z : σ → K) :
    z ∈ finiteEquationAllVertexLocusPoints equations X ↔
      z ∈ X ∧ ∀ v, z ∈ finiteAffineCommonZeroLocus (equations v) := by
  classical
  simp [finiteEquationAllVertexLocusPoints]

/-- The class of points of `X` which are off the displayed zero locus at
the vertex `v`. -/
def finiteEquationOffLocusClass
    (equations : V → Finset (MvPolynomial σ K))
    (X : Finset (σ → K)) (v : V) : Finset (σ → K) := by
  classical
  exact X.filter fun z ↦
    z ∉ finiteAffineCommonZeroLocus (equations v)

omit [Fintype σ] in
@[simp]
theorem mem_finiteEquationOffLocusClass_iff
    (equations : V → Finset (MvPolynomial σ K))
    (X : Finset (σ → K)) (v : V) (z : σ → K) :
    z ∈ finiteEquationOffLocusClass equations X v ↔
      z ∈ X ∧ z ∉ finiteAffineCommonZeroLocus (equations v) := by
  classical
  simp [finiteEquationOffLocusClass]

/-- Points which lie on every displayed locus and whose selected component
labels differ across the ordered edge `(v,w)`. -/
def finiteEquationDistinctComponentEdgeClass
    {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (equations : V → Finset (MvPolynomial σ K))
    (X : Finset (σ → K)) (v w : V) : Finset (σ → K) := by
  classical
  exact (finiteEquationAllVertexLocusPoints equations X).filter fun z ↦
    G.Adj v w ∧
      selectedFiniteEquationComponent (equations v) z ≠
        selectedFiniteEquationComponent (equations w) z

@[simp]
theorem mem_finiteEquationDistinctComponentEdgeClass_iff
    {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (equations : V → Finset (MvPolynomial σ K))
    (X : Finset (σ → K)) (v w : V) (z : σ → K) :
    z ∈ finiteEquationDistinctComponentEdgeClass (G := G) equations X v w ↔
      z ∈ X ∧
      (∀ u, z ∈ finiteAffineCommonZeroLocus (equations u)) ∧
      G.Adj v w ∧
      selectedFiniteEquationComponent (equations v) z ≠
        selectedFiniteEquationComponent (equations w) z := by
  classical
  simp [finiteEquationDistinctComponentEdgeClass, and_assoc]

/-- Points on every displayed locus with the same specified nonempty
selected component label at every vertex. -/
def finiteEquationPersistentComponentClass
    [Fintype V]
    (equations : V → Finset (MvPolynomial σ K))
    (X : Finset (σ → K))
    (o : Option (Ideal (MvPolynomial σ K))) : Finset (σ → K) := by
  classical
  exact (finiteEquationAllVertexLocusPoints equations X).filter fun z ↦
    o ≠ none ∧
      ∀ v, selectedFiniteEquationComponent (equations v) z = o

@[simp]
theorem mem_finiteEquationPersistentComponentClass_iff
    [Fintype V]
    (equations : V → Finset (MvPolynomial σ K))
    (X : Finset (σ → K))
    (o : Option (Ideal (MvPolynomial σ K))) (z : σ → K) :
    z ∈ finiteEquationPersistentComponentClass equations X o ↔
      z ∈ X ∧
      (∀ u, z ∈ finiteAffineCommonZeroLocus (equations u)) ∧
      o ≠ none ∧
      ∀ v, selectedFiniteEquationComponent (equations v) z = o := by
  classical
  simp [finiteEquationPersistentComponentClass, and_assoc]

/-- The finite image of the all-loci point set under the selected component
label at the fixed base vertex. -/
def finiteEquationPersistentLabelsAtBasepoint
    [Fintype V]
    (equations : V → Finset (MvPolynomial σ K))
    (X : Finset (σ → K)) (v₀ : V) :
    Finset (Option (Ideal (MvPolynomial σ K))) := by
  classical
  exact (finiteEquationAllVertexLocusPoints equations X).image
    (fun z ↦ selectedFiniteEquationComponent (equations v₀) z)

/-- Literal vertex--edge--persistent cardinality partition for finite
polynomial equation families.  The last sum runs over the finite image of
the all-loci point set at `v₀`, rather than over all ideals. -/
theorem card_le_sum_offLocus_distinctComponentEdge_persistent
    {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.Connected) (v₀ : V)
    (equations : V → Finset (MvPolynomial σ K))
    (X : Finset (σ → K)) :
    X.card ≤
      (∑ v : V, (finiteEquationOffLocusClass equations X v).card) +
      (∑ v : V, ∑ w : V,
        (finiteEquationDistinctComponentEdgeClass
          (G := G) equations X v w).card) +
      (∑ o ∈ finiteEquationPersistentLabelsAtBasepoint equations X v₀,
        (finiteEquationPersistentComponentClass equations X o).card) := by
  classical
  let Y : Finset (σ → K) :=
    finiteEquationAllVertexLocusPoints equations X
  let label : (σ → K) → V → Option (Ideal (MvPolynomial σ K)) :=
    fun z v ↦ selectedFiniteEquationComponent (equations v) z
  let offUnion : Finset (σ → K) :=
    Finset.univ.biUnion fun v ↦ finiteEquationOffLocusClass equations X v
  have hcover : X ⊆ offUnion ∪ Y := by
    intro z hz
    by_cases hall : ∀ v, z ∈ finiteAffineCommonZeroLocus (equations v)
    · exact Finset.mem_union_right _
        ((mem_finiteEquationAllVertexLocusPoints_iff equations X z).2
          ⟨hz, hall⟩)
    · apply Finset.mem_union_left
      simp only [not_forall] at hall
      obtain ⟨v, hv⟩ := hall
      exact Finset.mem_biUnion.mpr
        ⟨v, Finset.mem_univ v,
          (mem_finiteEquationOffLocusClass_iff equations X v z).2
            ⟨hz, hv⟩⟩
  have hoffUnion : offUnion.card ≤
      ∑ v : V, (finiteEquationOffLocusClass equations X v).card := by
    exact Finset.card_biUnion_le
  have hsplit : X.card ≤
      (∑ v : V, (finiteEquationOffLocusClass equations X v).card) +
        Y.card := by
    calc
      X.card ≤ (offUnion ∪ Y).card := Finset.card_le_card hcover
      _ ≤ offUnion.card + Y.card := Finset.card_union_le _ _
      _ ≤ (∑ v : V,
          (finiteEquationOffLocusClass equations X v).card) + Y.card :=
        Nat.add_le_add_right hoffUnion _
  have hstatic :=
    card_le_sum_vertex_edge_persistent_classes_at
      (B := Ideal (MvPolynomial σ K)) hG v₀ Y label
  have hnone : ∀ v : V,
      (Y.filter fun z ↦ label z v = none).card = 0 := by
    intro v
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hzY := (Finset.mem_filter.mp hz).1
    have hzNone := (Finset.mem_filter.mp hz).2
    have hzLocus :=
      ((mem_finiteEquationAllVertexLocusPoints_iff equations X z).1 hzY).2 v
    exact
      ((selectedFiniteEquationComponent_eq_none_iff (equations v) z).1
        hzNone) hzLocus
  have hY : Y.card ≤
      (∑ v : V, ∑ w : V,
        (finiteEquationDistinctComponentEdgeClass
          (G := G) equations X v w).card) +
      (∑ o ∈ finiteEquationPersistentLabelsAtBasepoint equations X v₀,
        (finiteEquationPersistentComponentClass equations X o).card) := by
    simpa [Y, label, hnone,
      finiteEquationDistinctComponentEdgeClass,
      finiteEquationPersistentComponentClass,
      finiteEquationPersistentLabelsAtBasepoint] using hstatic
  exact hsplit.trans (by
    simpa [Nat.add_assoc] using
      Nat.add_le_add_left hY
        (∑ v : V, (finiteEquationOffLocusClass equations X v).card))

/-- Every point in a distinct-component edge class determines two genuinely
distinct selected minimal-prime ideals, and lies in the affine zero locus of
their supremum. -/
theorem exists_distinct_selected_components_and_mem_sup_zeroLocus_of_mem_edgeClass
    {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (equations : V → Finset (MvPolynomial σ K))
    (X : Finset (σ → K)) {v w : V} {z : σ → K}
    (hz : z ∈ finiteEquationDistinctComponentEdgeClass
      (G := G) equations X v w) :
    ∃ Qv Qw : Ideal (MvPolynomial σ K),
      Qv ≠ Qw ∧
      selectedFiniteEquationComponent (equations v) z = some Qv ∧
      selectedFiniteEquationComponent (equations w) z = some Qw ∧
      z ∈ affineIdealZeroLocus (Qv ⊔ Qw) := by
  classical
  have hmem :=
    (mem_finiteEquationDistinctComponentEdgeClass_iff
      (G := G) equations X v w z).1 hz
  have hvLocus := hmem.2.1 v
  have hwLocus := hmem.2.1 w
  have hne := hmem.2.2.2
  have hvNone :
      selectedFiniteEquationComponent (equations v) z ≠ none := by
    intro hv
    exact ((selectedFiniteEquationComponent_eq_none_iff
      (equations v) z).1 hv) hvLocus
  have hwNone :
      selectedFiniteEquationComponent (equations w) z ≠ none := by
    intro hw
    exact ((selectedFiniteEquationComponent_eq_none_iff
      (equations w) z).1 hw) hwLocus
  obtain ⟨Qv, hQv⟩ := Option.ne_none_iff_exists'.1 hvNone
  obtain ⟨Qw, hQw⟩ := Option.ne_none_iff_exists'.1 hwNone
  have hQne : Qv ≠ Qw := by
    intro hEq
    apply hne
    rw [hQv, hQw, hEq]
  exact ⟨Qv, Qw, hQne, hQv, hQw,
    mem_affineIdealZeroLocus_sup_of_two_selected_components
      (equations v) (equations w) z hQv hQw⟩

end

end TranslatedDepthSeven
