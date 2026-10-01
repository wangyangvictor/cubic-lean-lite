import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-! Quotient-compatible inverse systems of genuine module sheaves.

For a fixed commutative coefficient ring R and element π, level n has
coefficients modulo π^(n+1). Adjacent reduction is a cokernel in the
category of sheaves, not a quotient of sections on every object. This
algebraic definition does not assert that R is a complete DVR, or that
the system is constructible/lisse. Those are separate conditions.

The actual small étale site is used in `EtaleTower`. No ordinary inverse
limit sheaf is identified with the adic system or with its geometric stalk.
No cohomology, weights, trace formula or Xu dichotomy is assumed here.
-/

set_option autoImplicit false
noncomputable section
universe u v w
namespace CubicTenVariables.AdicSheafSystem
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Type w} [CommRing R]

/-- Scalar multiplication as an actual natural endomorphism of a module sheaf. -/
def scalar (F : Sheaf J (ModuleCat.{w} R)) (r : R) : F ⟶ F :=
  Sheaf.Hom.mk
    { app := fun U => ModuleCat.ofHom (r • LinearMap.id)
      naturality := by
        intro U V f
        ext x
        exact ((F.val.map f).hom.map_smul r x).symm }

@[simp] theorem scalar_app (F : Sheaf J (ModuleCat.{w} R)) (r : R)
    (U : Cᵒᵖ) (x : F.val.obj U) :
    ((scalar F r).val.app U) x = r • x := rfl

theorem scalar_naturality {F G : Sheaf J (ModuleCat.{w} R)}
    (f : F ⟶ G) (r : R) : scalar F r ≫ f = f ≫ scalar G r := by
  ext U x
  exact (f.val.app U).hom.map_smul r x

@[simp] theorem scalar_zero (F : Sheaf J (ModuleCat.{w} R)) : scalar F 0 = 0 := by
  ext U x
  change (0 : R) • x = 0
  exact zero_smul R x

@[simp] theorem scalar_one (F : Sheaf J (ModuleCat.{w} R)) : scalar F 1 = 𝟙 F := by
  ext U x
  simp

theorem scalar_add (F : Sheaf J (ModuleCat.{w} R)) (r s : R) :
    scalar F (r+s) = scalar F r + scalar F s := by
  ext U x
  exact add_smul r s x

theorem scalar_mul (F : Sheaf J (ModuleCat.{w} R)) (r s : R) :
    scalar F (r*s) = scalar F s ≫ scalar F r := by
  ext U x
  exact mul_smul r s x

/-- Adjacent transitions are universal sheaf quotients by π^(n+1).
The resulting torsion and epimorphism properties are proved below. -/
structure Tower (J : GrothendieckTopology C) (R : Type w) [CommRing R] (π : R) where
  level : ℕ → Sheaf J (ModuleCat.{w} R)
  transition : ∀ n, level (n+1) ⟶ level n
  relation : ∀ n, scalar (level (n+1)) (π^(n+1)) ≫ transition n = 0
  reduction : ∀ n, IsColimit (CokernelCofork.ofπ (transition n) (relation n))

variable {π : R} (T : Tower J R π)

instance transition_epi (n : ℕ) : Epi (T.transition n) :=
  epi_of_isColimit_cofork (T.reduction n)

/-- Each level is annihilated by the correct power, as a sheaf morphism. -/
theorem level_torsion (n : ℕ) : scalar (T.level n) (π^(n+1)) = 0 := by
  apply (cancel_epi (T.transition n)).mp
  rw [← scalar_naturality, T.relation, comp_zero]

/-- In particular the coefficient action is zero on every section; no
surjectivity assertion about section maps is made. -/
theorem level_section_torsion (n : ℕ) (U : Cᵒᵖ) (x : (T.level n).val.obj U) :
    π^(n+1) • x = 0 := by
  have h := congrArg (fun f : T.level n ⟶ T.level n => (f.val.app U) x)
    (level_torsion T n)
  exact h

/-- The universal reduction map factors every morphism annihilated by
the same scalar, in the sheaf category itself. -/
def descend (n : ℕ) {G : Sheaf J (ModuleCat.{w} R)}
    (f : T.level (n+1) ⟶ G)
    (hf : scalar (T.level (n+1)) (π^(n+1)) ≫ f = 0) : T.level n ⟶ G :=
  (CokernelCofork.IsColimit.desc' (T.reduction n) f hf).val

theorem transition_descend (n : ℕ) {G : Sheaf J (ModuleCat.{w} R)}
    (f : T.level (n+1) ⟶ G)
    (hf : scalar (T.level (n+1)) (π^(n+1)) ≫ f = 0) :
    T.transition n ≫ descend T n f hf = f :=
  (CokernelCofork.IsColimit.desc' (T.reduction n) f hf).property

theorem descend_unique (n : ℕ) {G : Sheaf J (ModuleCat.{w} R)}
    (f : T.level (n+1) ⟶ G)
    (hf : scalar (T.level (n+1)) (π^(n+1)) ≫ f = 0)
    (g : T.level n ⟶ G) (hg : T.transition n ≫ g = f) : g = descend T n f hf := by
  apply (cancel_epi (T.transition n)).mp
  rw [hg,transition_descend]

/-- Specialization to the genuine small étale site of a scheme. -/
abbrev EtaleTower (X : AlgebraicGeometry.Scheme.{u}) (R : Type w) [CommRing R] (π : R) :=
  Tower (AlgebraicGeometry.Scheme.smallEtaleTopology X) R π

end CubicTenVariables.AdicSheafSystem
