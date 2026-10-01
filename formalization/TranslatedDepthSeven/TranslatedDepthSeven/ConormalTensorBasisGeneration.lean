import TranslatedDepthSeven.ConormalNakayama
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# From a residue-field basis to generators of a local ideal

This file isolates the last purely Nakayama-theoretic step in the local
component argument.  If elements of a finite ideal become a basis after
tensoring the ideal with the residue field, then they generate the ideal.

No assertion here derives the residue-field basis from smoothness,
codimension, or a Jacobian minor.  That geometric-to-conormal step is
separate.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- A family in a finite ideal which becomes a residue-field basis after
tensoring generates that ideal.  This is the direct module form of the
conormal Nakayama argument. -/
theorem ideal_eq_span_range_of_residueTensor_basis
    (I : Ideal R) (hIfg : I.FG) {ι : Type*} (g : ι → I)
    (b : Module.Basis ι (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] I))
    (hb : ∀ i, (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] g i = b i) :
    Ideal.span (Set.range fun i ↦ (g i : R)) = I := by
  letI : Module.Finite R I :=
    Module.finite_def.mpr ((Submodule.fg_top I).mpr hIfg)
  have hspan : Submodule.span R (Set.range g) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis g b hb
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (g i).2
  · intro x hx
    let xI : I := ⟨x, hx⟩
    have hxspan : xI ∈ Submodule.span R (Set.range g) := by
      rw [hspan]
      trivial
    let Jsub : Submodule R R :=
      (Ideal.span (Set.range fun i ↦ (g i : R)) : Ideal R)
    let M : Submodule R I :=
      Jsub.comap (I : Submodule R R).subtype
    have hgen : Set.range g ⊆ M := by
      rintro _ ⟨i, rfl⟩
      change (g i : R) ∈ Jsub
      exact Ideal.subset_span ⟨i, rfl⟩
    have hle : Submodule.span R (Set.range g) ≤ M :=
      Submodule.span_le.mpr hgen
    have hxM : xI ∈ M := hle hxspan
    change x ∈ Ideal.span (Set.range fun i ↦ (g i : R))
    exact hxM

/-- Finite-index version of
`ideal_eq_span_range_of_residueTensor_basis`. -/
theorem ideal_eq_span_fin_of_residueTensor_basis
    (I : Ideal R) (hIfg : I.FG) {r : ℕ} (g : Fin r → I)
    (b : Module.Basis (Fin r) (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] I))
    (hb : ∀ i, (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] g i = b i) :
    Ideal.span (Set.range fun i ↦ (g i : R)) = I :=
  ideal_eq_span_range_of_residueTensor_basis I hIfg g b hb

/-- It is enough that the residue-field tensor of the ideal has dimension
`r` and that the `r` displayed classes are linearly independent.  This is
the exact form needed after a Jacobian minor supplies independence and a
separate smooth-codimension argument supplies the dimension equality. -/
theorem ideal_eq_span_fin_of_residueTensor_finrank_and_linearIndependent
    (I : Ideal R) (hIfg : I.FG) {r : ℕ} (g : Fin r → I)
    (hfinrank : Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] I) = r)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i ↦ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] g i)) :
    Ideal.span (Set.range fun i ↦ (g i : R)) = I := by
  letI : Module.Finite R I :=
    Module.finite_def.mpr ((Submodule.fg_top I).mpr hIfg)
  let v : Fin r → (IsLocalRing.ResidueField R ⊗[R] I) :=
    fun i ↦ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] g i
  have hli_v : LinearIndependent (IsLocalRing.ResidueField R) v := hli
  have hspan : Submodule.span (IsLocalRing.ResidueField R) (Set.range v) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli_v, Fintype.card_fin]
    exact hfinrank.symm
  let b : Module.Basis (Fin r) (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] I) :=
    Module.Basis.mk hli_v hspan.ge
  apply ideal_eq_span_fin_of_residueTensor_basis I hIfg g b
  intro i
  change v i = b i
  simp [b, v]

/-- A nonzero selected minor of any linear image of the residue-field
conormal classes supplies the linear independence required by the preceding
theorem.  In the polynomial application, `d` is the first-differential map
and the displayed matrix is the selected Jacobian matrix. -/
theorem ideal_eq_span_fin_of_residueTensor_finrank_and_selectedMinor
    (I : Ideal R) (hIfg : I.FG) {r N : ℕ} (g : Fin r → I)
    (hfinrank : Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] I) = r)
    (d : (IsLocalRing.ResidueField R ⊗[R] I) →ₗ[IsLocalRing.ResidueField R]
      (Fin N → IsLocalRing.ResidueField R))
    (cols : Fin r → Fin N)
    (hminor : Matrix.det (Matrix.of (fun i j ↦
      d ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] g i) (cols j))) ≠ 0) :
    Ideal.span (Set.range fun i ↦ (g i : R)) = I := by
  let v : Fin r → (IsLocalRing.ResidueField R ⊗[R] I) :=
    fun i ↦ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] g i
  let restrictCols :
      (Fin N → IsLocalRing.ResidueField R) →ₗ[IsLocalRing.ResidueField R]
        (Fin r → IsLocalRing.ResidueField R) :=
    LinearMap.funLeft (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R) cols
  have hliImage : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i ↦ restrictCols (d (v i))) := by
    have hrows := Matrix.linearIndependent_rows_of_det_ne_zero hminor
    simpa only [Matrix.row, Matrix.of_apply, v, restrictCols,
      LinearMap.funLeft_apply] using hrows
  have hli : LinearIndependent (IsLocalRing.ResidueField R) v := by
    apply LinearIndependent.of_comp (restrictCols.comp d)
    simpa only [LinearMap.coe_comp, Function.comp_apply] using hliImage
  exact ideal_eq_span_fin_of_residueTensor_finrank_and_linearIndependent
    I hIfg g hfinrank hli

end

end TranslatedDepthSeven
