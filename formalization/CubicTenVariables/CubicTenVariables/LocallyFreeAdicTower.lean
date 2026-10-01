import CubicTenVariables.AdicSheafQuotients
import CubicTenVariables.EtaleTorsionLocalSystem
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! Locally free quotient-compatible systems on the actual small étale
site. The coefficient ring and its element are fixed, and no discrete
valuation or completeness property is asserted. Every level has its own
étale trivializing covers. The constant example is constructed using
genuine sheaf cokernels, not pointwise quotients of section modules. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
universe u v w
namespace CubicTenVariables.LocallyFreeAdicTower
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EtaleTorsionLocalSystem

/-- The literal coefficient ideal at level `n`. -/
def coefficientIdeal {R : Type w} [CommRing R] (π : R) (n : ℕ) : Ideal R :=
  Ideal.span {π^(n+1)}

/-- The finite-rank quotient coefficient model, regarded throughout as
a module over the fixed ring `R`. Finiteness is not asserted for an
arbitrary coefficient ring. -/
def quotientModel (R : Type w) [CommRing R] (π : R) (rank n : ℕ) : ModuleCat.{w} R :=
  ModuleCat.of R (Fin rank → R ⧸ coefficientIdeal π n)

/-- An actual quotient-compatible étale tower locally modelled on the
specified finite-rank quotients. Trivializing covers may depend on `n`. -/
structure Data (X : Scheme.{u}) (R : Type (u+1)) [CommRing R] (π : R) (rank : ℕ) where
  tower : AdicSheafSystem.EtaleTower X R π
  locallyFree : ∀ n, LocallyConstantModel X.smallEtaleTopology (tower.level n)
    (quotientModel R π rank n)

section ConstantSheaf
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {R : Type w} [CommRing R]
variable [HasSheafify J (ModuleCat.{w} R)]

/-- Scalar multiplication as a module-category morphism. -/
def moduleScalar (M : ModuleCat.{w} R) (r : R) : M ⟶ M :=
  ModuleCat.ofHom (r • LinearMap.id)

/-- Constant sheafification preserves the actual scalar action. This is
proved from its adjunction and linearity of the unit components. -/
theorem constant_map_scalar (M : ModuleCat.{w} R) (r : R) :
    (constantSheaf J (ModuleCat.{w} R)).map (moduleScalar M r) =
      AdicSheafSystem.scalar ((constantSheaf J (ModuleCat.{w} R)).obj M) r := by
  let P := (Functor.const Cᵒᵖ).obj M
  let a : P ⟶ P := (Functor.const Cᵒᵖ).map (moduleScalar M r)
  apply ((sheafificationAdjunction J (ModuleCat.{w} R)).homEquiv P
    ((constantSheaf J (ModuleCat.{w} R)).obj M)).injective
  change toSheafify J P ≫ (sheafifyMap J a) =
    toSheafify J P ≫ (AdicSheafSystem.scalar
      ((constantSheaf J (ModuleCat.{w} R)).obj M) r).val
  rw [← toSheafify_naturality]
  ext U x
  exact ((toSheafify J P).app U).hom.map_smul r x

end ConstantSheaf

section FreeModule
variable (R : Type w) [CommRing R]

/-- The range of scalar multiplication on a finite free module is the
coordinatewise principal ideal. -/
theorem range_scalar_free (rank : ℕ) (r : R) :
    LinearMap.range (r • (LinearMap.id : (Fin rank → R) →ₗ[R] (Fin rank → R))) =
      Submodule.pi Set.univ (fun _ : Fin rank => (Ideal.span {r} : Ideal R)) := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    intro i _
    exact Ideal.mem_span_singleton.mpr ⟨y i,rfl⟩
  · intro hx
    have h (i : Fin rank) : ∃ a : R, r * a = x i := by
      obtain ⟨a,ha⟩ := Ideal.mem_span_singleton.mp (hx i (Set.mem_univ i))
      exact ⟨a,ha.symm⟩
    choose y hy using h
    exact ⟨y,funext hy⟩

/-- The scalar cokernel is explicitly the product of the actual ring
quotients, as a module over the original coefficient ring. -/
def freeCokernelIso (rank : ℕ) (r : R) :
    cokernel (moduleScalar (ModuleCat.of R (Fin rank → R)) r) ≅
      ModuleCat.of R (Fin rank → R ⧸ (Ideal.span {r} : Ideal R)) :=
  ModuleCat.cokernelIsoRangeQuotient _ ≪≫
    ((Submodule.quotEquivOfEq _ _ (range_scalar_free R rank r)).trans
      (Submodule.quotientPi (fun _ : Fin rank => (Ideal.span {r} : Ideal R)))).toModuleIso

end FreeModule

section Etale
variable (X : Scheme.{u}) (R : Type (u+1)) [CommRing R] (π : R) (rank : ℕ)

/-- The quotient of a constant finite-free sheaf is the genuine constant
sheaf on the corresponding quotient module. -/
def constantLevelIso (n : ℕ) :
    (AdicSheafQuotients.tower (constantFree X R rank) π).level n ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u+1} R)).obj
        (quotientModel R π rank n) := by
  let K := constantSheaf X.smallEtaleTopology (ModuleCat.{u+1} R)
  letI : PreservesColimits K := by dsimp [K, constantSheaf]; infer_instance
  letI : K.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_initial_object (F := K)
  let f := moduleScalar (freeModel R rank) (π^(n+1))
  have h : K.map f = AdicSheafSystem.scalar (constantFree X R rank) (π^(n+1)) :=
    constant_map_scalar X.smallEtaleTopology (freeModel R rank) _
  exact (cokernelIsoOfEq h.symm) ≪≫ (PreservesCokernel.iso K f).symm ≪≫
    K.mapIso (freeCokernelIso R rank (π^(n+1)))

/-- A nonvacuous locally free adic tower: successive sheaf quotients of
the constant finite-free sheaf. Its transition compatibility is the
proved sheaf-cokernel property from `AdicSheafQuotients`. -/
def constantTower : Data X R π rank where
  tower := AdicSheafQuotients.tower (constantFree X R rank) π
  locallyFree n := locallyConstantModel_of_iso X.smallEtaleTopology
    (constantLevelIso X R π rank n).symm (quotientModel R π rank n)
    (constant_locallyConstantModel X.smallEtaleTopology (quotientModel R π rank n))

/-- The underlying compatible system is literally the existing sheaf
quotient tower. -/
theorem constantTower_tower : (constantTower X R π rank).tower =
    AdicSheafQuotients.tower (constantFree X R rank) π := rfl

/-- The levelwise annihilator is the specified power, by the genuine
sheaf quotient compatibility; this is not a statement of surjectivity on
all section modules. -/
theorem level_torsion (T : Data X R π rank) (n : ℕ) :
    AdicSheafSystem.scalar (T.tower.level n) (π^(n+1)) = 0 :=
  AdicSheafSystem.level_torsion T.tower n

end Etale
end CubicTenVariables.LocallyFreeAdicTower
