import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! A genuine geometric point of the small étale site.

The underlying functor is defined using actual scheme morphisms from
`Spec Ω`, not an arbitrary site point or a family of numerical stalks.
The one explicit literature proposition supplies its site-point conditions.
References: Stacks, Lemma 59.29.4 (03PQ), Lemma 59.29.5 (03PR), and
Lemma 59.29.7 (04FM):
https://stacks.math.columbia.edu/tag/03PQ
https://stacks.math.columbia.edu/tag/03PR
https://stacks.math.columbia.edu/tag/04FM
The initially-small condition records the usual affine finite-presentation
model of pointed étale neighbourhoods required by Mathlib's universe-polymorphic
stalk construction. It is a size-bookkeeping interpretation, not a verbatim
universe-indexed assertion in those lemmas. The site-size conventions and
affine-site comparison are discussed in Stacks Section 59.20 (03X7) and
Section 34.4 (0214), especially Lemma 34.4.12:
https://stacks.math.columbia.edu/tag/03X7
https://stacks.math.columbia.edu/tag/0214
No conservativity, Frobenius action, adic comparison or trace formula is
asserted here; in particular Stacks Theorem 59.29.10 is not an input.
-/

set_option autoImplicit false
noncomputable section
universe u v w

open CategoryTheory AlgebraicGeometry Opposite Limits

namespace CubicTenVariables.GeometricEtalePoint

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- The actual set of lifts of a geometric point to an étale `X`-scheme. -/
def fiber (xbar : Spec (CommRingCat.of Ω) ⟶ X) : X.Etale ⥤ Type u where
  obj U := {f : Spec (CommRingCat.of Ω) ⟶ U.left // f ≫ U.hom = xbar}
  map {U V} f := fun a => ⟨a.val ≫ f.left, by
    change a.val ≫ (f.left ≫ V.hom) = xbar
    have hf : f.left ≫ V.hom = U.hom :=
      CategoryTheory.Over.w ((Scheme.Etale.forget X).map f)
    rw [hf]
    exact a.property⟩
  map_id U := by
    funext a
    apply Subtype.ext
    exact Category.comp_id a.val
  map_comp f g := by
    funext a
    apply Subtype.ext
    exact (Category.assoc a.val f.left g.left).symm

@[simp] theorem fiber_obj (xbar : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Etale) :
    (fiber xbar).obj U =
      {f : Spec (CommRingCat.of Ω) ⟶ U.left // f ≫ U.hom = xbar} := rfl

@[simp] theorem fiber_map_val (xbar : Spec (CommRingCat.of Ω) ⟶ X)
    {U V : X.Etale} (f : U ⟶ V) (a : (fiber xbar).obj U) :
    ((fiber xbar).map f a).val = a.val ≫ f.left := rfl

end CubicTenVariables.GeometricEtalePoint

namespace CubicTenVariables.Literature

/-- Standard geometric-point theorem for the literal small-étale fiber
functor. This is a proposition to be supplied explicitly, with no inhabitant
or axiom declared. The three conjuncts are exactly Mathlib's point conditions. -/
def GeometricEtalePointConditions : Prop :=
  ∀ (X : Scheme.{u}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (xbar : Spec (CommRingCat.of Ω) ⟶ X),
    IsCofiltered (GeometricEtalePoint.fiber xbar).Elements ∧
    InitiallySmall.{u} (GeometricEtalePoint.fiber xbar).Elements ∧
    ∀ (U : X.Etale) (S : Sieve U), S ∈ X.smallEtaleTopology U →
      ∀ a : (GeometricEtalePoint.fiber xbar).obj U,
        ∃ (V : X.Etale) (f : V ⟶ U), S f ∧
          ∃ b : (GeometricEtalePoint.fiber xbar).obj V,
            (GeometricEtalePoint.fiber xbar).map f b = a

end CubicTenVariables.Literature

namespace CubicTenVariables.GeometricEtalePoint

variable (lit : Literature.GeometricEtalePointConditions.{u})
variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
variable (xbar : Spec (CommRingCat.of Ω) ⟶ X)

/-- The site point whose underlying functor is definitionally the genuine
geometric fiber functor. Only its standard geometric properties are input. -/
def point : GrothendieckTopology.Point.{u} X.smallEtaleTopology where
  fiber := fiber xbar
  isCofiltered := (lit X Ω xbar).1
  initiallySmall := (lit X Ω xbar).2.1
  jointly_surjective S hS a := by
    obtain ⟨V,f,hf,b,hb⟩ := (lit X Ω xbar).2.2 _ S hS a
    exact ⟨V,f,hf,b,hb⟩

@[simp] theorem point_fiber : (point lit xbar).fiber = fiber xbar := rfl

variable (A : Type v) [Category.{w} A] [HasColimitsOfSize.{u,u} A]

/-- The actual étale stalk functor, obtained from the filtered colimit of
sections on étale neighbourhoods of `xbar`. -/
def stalkFunctor : Sheaf X.smallEtaleTopology A ⥤ A :=
  (point lit xbar).sheafFiber

/-- The stalk is literally the colimit over the opposite category of actual
étale lifts of the chosen geometric point. -/
theorem stalkFunctor_obj (F : Sheaf X.smallEtaleTopology A) :
    (stalkFunctor lit xbar A).obj F =
      letI : HasColimitsOfShape (fiber xbar).Elementsᵒᵖ A :=
        inferInstanceAs (HasColimitsOfShape (point lit xbar).fiber.Elementsᵒᵖ A)
      colimit ((CategoryOfElements.π (fiber xbar)).op ⋙ F.val) := rfl

/-- The germ of a section at a specified lift of the geometric point. -/
def germ (F : Sheaf X.smallEtaleTopology A) (U : X.Etale)
    (a : (fiber xbar).obj U) : F.val.obj (op U) ⟶ (stalkFunctor lit xbar A).obj F :=
  (point lit xbar).toPresheafFiber U a F.val

/-- Restricting a section along a pointed étale neighbourhood preserves its germ. -/
theorem germ_restrict (F : Sheaf X.smallEtaleTopology A)
    {U V : X.Etale} (f : U ⟶ V) (a : (fiber xbar).obj U) :
    F.val.map f.op ≫ germ lit xbar A F U a =
      germ lit xbar A F V ((fiber xbar).map f a) :=
  (point lit xbar).toPresheafFiber_w f a F.val

end CubicTenVariables.GeometricEtalePoint
