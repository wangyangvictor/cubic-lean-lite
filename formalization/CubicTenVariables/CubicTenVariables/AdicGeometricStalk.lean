import CubicTenVariables.GeometricEtalePoint
import CubicTenVariables.AdicSheafSystem
import CubicTenVariables.EtaleTorsionLocalSystem
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! Finite-level geometric stalks of the actual adic sheaf system.
The stalk is the filtered colimit over genuine pointed étale neighbourhoods.
Scalar actions, torsion and quotient transitions are proved for these
modules; no ordinary inverse-limit sheaf is identified with an adic stalk.
The sole literature premise is the previously specified geometric-point
condition for the actual small étale fiber functor. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
universe u

namespace CubicTenVariables.AdicGeometricStalk
open CategoryTheory Limits AlgebraicGeometry Opposite

variable (lit : Literature.GeometricEtalePointConditions.{u})
variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
variable (xbar : Spec (CommRingCat.of Ω) ⟶ X)
variable {R : Type (u+1)} [CommRing R]

/-- The genuine geometric stalk functor on module sheaves. -/
abbrev stalkFunctor : Sheaf X.smallEtaleTopology (ModuleCat.{u+1} R) ⥤ ModuleCat.{u+1} R :=
  GeometricEtalePoint.stalkFunctor lit xbar (ModuleCat.{u+1} R)

/-- The functor's image of a sheaf scalar is the actual R-linear scalar
endomorphism of its geometric stalk. -/
theorem map_scalar (F : Sheaf X.smallEtaleTopology (ModuleCat.{u+1} R)) (r : R) :
    (stalkFunctor lit xbar).map (AdicSheafSystem.scalar F r) =
      ModuleCat.ofHom (r • LinearMap.id) := by
  apply (GeometricEtalePoint.point lit xbar).presheafFiber_hom_ext
  intro U a
  change (GeometricEtalePoint.point lit xbar).toPresheafFiber U a F.val ≫
      (GeometricEtalePoint.point lit xbar).presheafFiber.map
        (AdicSheafSystem.scalar F r).val =
    (GeometricEtalePoint.point lit xbar).toPresheafFiber U a F.val ≫
      ModuleCat.ofHom (r • LinearMap.id)
  rw [(GeometricEtalePoint.point lit xbar).toPresheafFiber_naturality]
  ext x
  exact ((GeometricEtalePoint.point lit xbar).toPresheafFiber U a F.val).hom.map_smul r x

local instance forget_preservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{u,u} (forget (ModuleCat.{u+1} R)) :=
  preservesFilteredColimitsOfSize_shrink.{u,u+1,u,u+1} (forget (ModuleCat.{u+1} R))

instance preservesColimits : PreservesColimitsOfSize.{u,u} (stalkFunctor lit xbar (R := R)) := by
  dsimp only [stalkFunctor, GeometricEtalePoint.stalkFunctor]
  infer_instance

local instance preservesSmallColimits : PreservesColimitsOfSize.{0,0} (stalkFunctor lit xbar (R := R)) :=
  preservesSmallestColimits_of_preservesColimits (stalkFunctor lit xbar)

instance preservesZeroMorphisms : (stalkFunctor lit xbar (R := R)).PreservesZeroMorphisms where
  map_zero F G := by
    apply (GeometricEtalePoint.point lit xbar).presheafFiber_hom_ext
    intro U a
    change (GeometricEtalePoint.point lit xbar).toPresheafFiber U a F.val ≫
        (GeometricEtalePoint.point lit xbar).presheafFiber.map (0 : F ⟶ G).val =
      (GeometricEtalePoint.point lit xbar).toPresheafFiber U a F.val ≫ 0
    rw [(GeometricEtalePoint.point lit xbar).toPresheafFiber_naturality]
    ext x
    exact ((GeometricEtalePoint.point lit xbar).toPresheafFiber U a G.val).hom.map_zero

variable {π : R} (T : AdicSheafSystem.EtaleTower X R π)

/-- Level n is the actual geometric stalk of the sheaf at that level. -/
abbrev level (n : ℕ) : ModuleCat.{u+1} R := (stalkFunctor lit xbar).obj (T.level n)

/-- The stalk transition is induced by the actual sheaf transition. -/
abbrev transition (n : ℕ) : level lit xbar T (n+1) ⟶ level lit xbar T n :=
  (stalkFunctor lit xbar).map (T.transition n)

/-- The sheaf's scalar annihilation gives literal scalar annihilation of
every element of its geometric stalk. -/
theorem level_torsion (n : ℕ) (x : level lit xbar T n) : π^(n+1) • x = 0 := by
  have h := congrArg (fun f : T.level n ⟶ T.level n => (stalkFunctor lit xbar).map f)
    (AdicSheafSystem.level_torsion T n)
  dsimp only at h
  rw [map_scalar, Functor.map_zero] at h
  exact congrArg (fun f : level lit xbar T n ⟶ level lit xbar T n => f x) h

/-- The displayed scalar relation is preserved on stalks. -/
theorem relation (n : ℕ) :
    ModuleCat.ofHom (π^(n+1) • (LinearMap.id : level lit xbar T (n+1) →ₗ[R]
      level lit xbar T (n+1))) ≫ transition lit xbar T n = 0 := by
  rw [← map_scalar lit xbar (T.level (n+1)) (π^(n+1))]
  change (stalkFunctor lit xbar).map _ ≫ (stalkFunctor lit xbar).map _ = 0
  rw [← Functor.map_comp, T.relation, Functor.map_zero]

/-- Adjacent finite-level stalks retain the actual universal quotient by
π^(n+1), because the geometric-point sheaf fiber preserves colimits. -/
def reduction (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (transition lit xbar T n) (relation lit xbar T n)) := by
  have h := isColimitCoforkMapOfIsColimit' (stalkFunctor lit xbar)
    (T.relation n) (T.reduction n)
  exact CokernelCofork.isColimitOfIsColimitOfIff' h _ (fun _ φ => by
    rw [map_scalar])

instance transition_epi (n : ℕ) : Epi (transition lit xbar T n) :=
  epi_of_isColimit_cofork (reduction lit xbar T n)

/-- These stalk transition maps are genuinely surjective on elements.
No corresponding surjectivity of arbitrary section maps is claimed. -/
theorem transition_surjective (n : ℕ) : Function.Surjective (transition lit xbar T n) :=
  (ModuleCat.epi_iff_surjective _).mp (transition_epi lit xbar T n)

/-- Universal descent of a linear map from a stalk, when it annihilates
the displayed scalar relation. -/
def descend (n : ℕ) {M : ModuleCat.{u+1} R} (f : level lit xbar T (n+1) ⟶ M)
    (hf : ModuleCat.ofHom (π^(n+1) • (LinearMap.id : level lit xbar T (n+1) →ₗ[R]
      level lit xbar T (n+1))) ≫ f = 0) : level lit xbar T n ⟶ M :=
  (CokernelCofork.IsColimit.desc' (reduction lit xbar T n) f hf).val

theorem transition_descend (n : ℕ) {M : ModuleCat.{u+1} R}
    (f : level lit xbar T (n+1) ⟶ M)
    (hf : ModuleCat.ofHom (π^(n+1) • (LinearMap.id : level lit xbar T (n+1) →ₗ[R]
      level lit xbar T (n+1))) ≫ f = 0) :
    transition lit xbar T n ≫ descend lit xbar T n f hf = f :=
  (CokernelCofork.IsColimit.desc' (reduction lit xbar T n) f hf).property

theorem descend_unique (n : ℕ) {M : ModuleCat.{u+1} R}
    (f : level lit xbar T (n+1) ⟶ M)
    (hf : ModuleCat.ofHom (π^(n+1) • (LinearMap.id : level lit xbar T (n+1) →ₗ[R]
      level lit xbar T (n+1))) ≫ f = 0)
    (g : level lit xbar T n ⟶ M) (hg : transition lit xbar T n ≫ g = f) :
    g = descend lit xbar T n f hf := by
  apply (cancel_epi (transition lit xbar T n)).mp
  rw [hg,transition_descend]

end CubicTenVariables.AdicGeometricStalk
