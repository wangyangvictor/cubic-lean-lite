import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! Finite-level local systems on the actual small étale site.

The model is a specified module. The constant object is Mathlib's
`constantSheaf`, i.e. the sheafification of the constant presheaf; it is
not the constant presheaf. Local triviality means isomorphism to that
sheaf on an actual covering sieve, after restriction to slice sites.
No lisse predicate or cohomology theorem is supplied as an input.

The generic module model also permits finite quotient modules of a fixed
adic coefficient ring. Local trivializations are asserted separately at
each level; this definition does not impose a common cover on a tower.

For a scheme in universe `u`, module values and the coefficient ring in
universe `u+1` give sheafification from Mathlib's proved instances. A
smaller coefficient ring may be lifted once with `ULift`. -/

set_option autoImplicit false
noncomputable section
universe u v w

namespace CubicTenVariables.EtaleTorsionLocalSystem
open CategoryTheory AlgebraicGeometry

section GenericSite
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {R : Type w} [CommRing R]
variable [HasWeakSheafify J (ModuleCat.{w} R)]

/-- Triviality on an object of the site is an actual isomorphism of
sheaves on its slice site, not merely an isomorphism of section modules. -/
def TrivialOn (F : Sheaf J (ModuleCat.{w} R)) (M : ModuleCat.{w} R) (U : C) : Prop :=
  Nonempty ((J.overPullback (ModuleCat.{w} R) U).obj F ≅
    (J.overPullback (ModuleCat.{w} R) U).obj
      ((constantSheaf J (ModuleCat.{w} R)).obj M))

/-- A module sheaf is locally constant with the specified module model
when an actual covering sieve of every site object trivializes it. -/
def LocallyConstantModel (F : Sheaf J (ModuleCat.{w} R)) (M : ModuleCat.{w} R) : Prop :=
  ∀ U : C, ∃ S : Sieve U, S ∈ J U ∧
    ∀ ⦃V : C⦄ (f : V ⟶ U), S f → TrivialOn J F M V

/-- A globally constant sheaf is trivial on every object. -/
theorem constant_trivialOn (M : ModuleCat.{w} R) (U : C) :
    TrivialOn J ((constantSheaf J (ModuleCat.{w} R)).obj M) M U :=
  ⟨Iso.refl _⟩

/-- The maximal covering sieve proves that the genuine constant sheaf
is locally constant with its displayed model. -/
theorem constant_locallyConstantModel (M : ModuleCat.{w} R) :
    LocallyConstantModel J ((constantSheaf J (ModuleCat.{w} R)).obj M) M := by
  intro U
  exact ⟨⊤, J.top_mem U, fun _ _ _ => constant_trivialOn J M _⟩

/-- A global isomorphism of sheaves preserves local triviality. -/
theorem trivialOn_of_iso {F G : Sheaf J (ModuleCat.{w} R)}
    (e : F ≅ G) (M : ModuleCat.{w} R) (U : C)
    (h : TrivialOn J F M U) : TrivialOn J G M U := by
  obtain ⟨a⟩ := h
  exact ⟨(J.overPullback (ModuleCat.{w} R) U).mapIso e.symm ≪≫ a⟩

/-- Local constancy is invariant under actual sheaf isomorphisms. -/
theorem locallyConstantModel_of_iso {F G : Sheaf J (ModuleCat.{w} R)}
    (e : F ≅ G) (M : ModuleCat.{w} R)
    (h : LocallyConstantModel J F M) : LocallyConstantModel J G M := by
  intro U
  obtain ⟨S,hS,htriv⟩ := h U
  exact ⟨S,hS,fun _ f hf => trivialOn_of_iso J e M _ (htriv f hf)⟩

/-- Replacing the model by an isomorphic module preserves triviality. -/
theorem trivialOn_model_iso (F : Sheaf J (ModuleCat.{w} R))
    {M N : ModuleCat.{w} R} (e : M ≅ N) (U : C)
    (h : TrivialOn J F M U) : TrivialOn J F N U := by
  obtain ⟨a⟩ := h
  exact ⟨a ≪≫ (J.overPullback (ModuleCat.{w} R) U).mapIso
    ((constantSheaf J (ModuleCat.{w} R)).mapIso e)⟩

/-- Local constancy depends on the isomorphism class of the model. -/
theorem locallyConstantModel_model_iso (F : Sheaf J (ModuleCat.{w} R))
    {M N : ModuleCat.{w} R} (e : M ≅ N)
    (h : LocallyConstantModel J F M) : LocallyConstantModel J F N := by
  intro U
  obtain ⟨S,hS,htriv⟩ := h U
  exact ⟨S,hS,fun _ f hf => trivialOn_model_iso J F e _ (htriv f hf)⟩

end GenericSite

section SmallEtale
variable (X : Scheme.{u}) (R : Type (u+1)) [CommRing R]

/-- Module sheaves on the actual Mathlib small étale topology. -/
abbrev ModuleSheaf := Sheaf X.smallEtaleTopology (ModuleCat.{u+1} R)

/-- Restricting the genuine constant sheaf gives the genuine constant
sheaf on the slice site. This follows from Mathlib's proved compatibility
of sheafification with continuous, cocontinuous site functors. -/
def restrictConstantIso (M : ModuleCat.{u+1} R) (U : X.Etale) :
    (X.smallEtaleTopology.overPullback (ModuleCat.{u+1} R) U).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u+1} R)).obj M) ≅
      (constantSheaf (X.smallEtaleTopology.over U) (ModuleCat.{u+1} R)).obj M :=
  ((Over.forget U).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{u+1} R) (X.smallEtaleTopology.over U) X.smallEtaleTopology).app
      ((Functor.const X.Etaleᵒᵖ).obj M) |>.symm

/-- The local comparison is literally with the constant sheaf on the
restricted étale site, not with a constant section presheaf. -/
theorem trivialOn_iff_constant_slice (F : ModuleSheaf X R)
    (M : ModuleCat.{u+1} R) (U : X.Etale) :
    TrivialOn X.smallEtaleTopology F M U ↔
      Nonempty ((X.smallEtaleTopology.overPullback (ModuleCat.{u+1} R) U).obj F ≅
        (constantSheaf (X.smallEtaleTopology.over U) (ModuleCat.{u+1} R)).obj M) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e ≪≫ restrictConstantIso X R M U⟩
  · rintro ⟨e⟩
    exact ⟨e ≪≫ (restrictConstantIso X R M U).symm⟩

/-- An expanded characterization using actual covering sieves and the
constant sheaf of the model on each member's slice site. -/
theorem locallyConstantModel_iff_constant_slices (F : ModuleSheaf X R)
    (M : ModuleCat.{u+1} R) :
    LocallyConstantModel X.smallEtaleTopology F M ↔
      ∀ U : X.Etale, ∃ S : Sieve U, S ∈ X.smallEtaleTopology U ∧
        ∀ ⦃V : X.Etale⦄ (f : V ⟶ U), S f →
          Nonempty ((X.smallEtaleTopology.overPullback (ModuleCat.{u+1} R) V).obj F ≅
            (constantSheaf (X.smallEtaleTopology.over V) (ModuleCat.{u+1} R)).obj M) := by
  constructor
  · intro h U
    obtain ⟨S,hS,htriv⟩ := h U
    exact ⟨S,hS,fun V f hf =>
      (trivialOn_iff_constant_slice X R F M V).mp (htriv f hf)⟩
  · intro h U
    obtain ⟨S,hS,htriv⟩ := h U
    exact ⟨S,hS,fun V f hf =>
      (trivialOn_iff_constant_slice X R F M V).mpr (htriv f hf)⟩

/-- The finite-free coefficient model of the displayed rank. -/
def freeModel (rank : ℕ) : ModuleCat.{u+1} R := ModuleCat.of R (Fin rank → R)

/-- The actual constant finite-free étale sheaf. -/
def constantFree (rank : ℕ) : ModuleSheaf X R :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u+1} R)).obj (freeModel R rank)

/-- The finite coefficient module underlying the model has exactly
`Nat.card R ^ rank` elements. This does not assert finiteness of arbitrary
section modules over disconnected étale objects. -/
theorem card_freeModel [Finite R] (rank : ℕ) :
    Nat.card (freeModel R rank) = Nat.card R ^ rank := by
  change Nat.card (Fin rank → R) = _
  letI : Fintype R := Fintype.ofFinite R
  simp [Nat.card_eq_fintype_card]

/-- A finite-level étale local system of specified rank over a fixed
finite coefficient ring. The condition is an actual locally trivial
module sheaf, with no external predicate. -/
structure FiniteFreeLocalSystem [Finite R] (rank : ℕ) where
  sheaf : ModuleSheaf X R
  locallyFree : LocallyConstantModel X.smallEtaleTopology sheaf (freeModel R rank)

/-- The constant finite-free sheaf is a local system of the same rank. -/
def constantSystem [Finite R] (rank : ℕ) : FiniteFreeLocalSystem X R rank where
  sheaf := constantFree X R rank
  locallyFree := constant_locallyConstantModel X.smallEtaleTopology (freeModel R rank)

/-- The underlying sheaf of the constant system is the sheafification of
the literal constant finite-free module presheaf. -/
theorem constantSystem_sheaf [Finite R] (rank : ℕ) :
    (constantSystem X R rank).sheaf =
      (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u+1} R)).obj
        ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of R (Fin rank → R))) := rfl

end SmallEtale
end CubicTenVariables.EtaleTorsionLocalSystem
