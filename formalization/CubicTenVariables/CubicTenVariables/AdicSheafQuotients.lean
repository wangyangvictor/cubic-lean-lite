import CubicTenVariables.AdicSheafSystem
import Mathlib.CategoryTheory.Sites.Abelian

/-! Every module sheaf has a genuine quotient-compatible tower of sheaf
quotients by successive powers of π. All quotient universal properties
are in the sheaf category. Constructibility and lissity are not asserted
for an arbitrary starting sheaf. -/

set_option autoImplicit false
noncomputable section
universe u v w
namespace CubicTenVariables.AdicSheafQuotients
open CategoryTheory CategoryTheory.Limits AdicSheafSystem

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Type w} [CommRing R]
variable [HasCokernels (Sheaf J (ModuleCat.{w} R))]
variable (F : Sheaf J (ModuleCat.{w} R)) (π : R)

abbrev level (n : ℕ) := cokernel (scalar F (π^(n+1)))
abbrev quotientMap (n : ℕ) : F ⟶ level F π n := cokernel.π (scalar F (π^(n+1)))

theorem next_power_zero (n : ℕ) :
    scalar F (π^(n+1+1)) ≫ quotientMap F π n = 0 := by
  rw [pow_succ,scalar_mul,Category.assoc,cokernel.condition,comp_zero]

abbrev transition (n : ℕ) : level F π (n+1) ⟶ level F π n :=
  cokernel.desc (scalar F (π^(n+1+1))) (quotientMap F π n) (next_power_zero F π n)

theorem quotientMap_transition (n : ℕ) :
    quotientMap F π (n+1) ≫ transition F π n = quotientMap F π n :=
  cokernel.π_desc _ _ _

theorem transition_relation (n : ℕ) :
    scalar (level F π (n+1)) (π^(n+1)) ≫ transition F π n = 0 := by
  apply (cancel_epi (quotientMap F π (n+1))).mp
  rw [← Category.assoc,← scalar_naturality,Category.assoc,quotientMap_transition,
    cokernel.condition,comp_zero]

def quotient_reduction (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (transition F π n) (transition_relation F π n)) := by
  apply CokernelCofork.IsColimit.ofπ'
  intro G f hf
  have hz : scalar F (π^(n+1)) ≫ (quotientMap F π (n+1) ≫ f) = 0 := by
    rw [← Category.assoc,scalar_naturality,Category.assoc,hf,comp_zero]
  refine ⟨cokernel.desc (scalar F (π^(n+1))) (quotientMap F π (n+1) ≫ f) hz,?_⟩
  apply (cancel_epi (quotientMap F π (n+1))).mp
  rw [← Category.assoc,quotientMap_transition,cokernel.π_desc]

/-- The sheaf quotients of a fixed sheaf form an actual adic tower. -/
def tower : AdicSheafSystem.Tower J R π where
  level := level F π
  transition := transition F π
  relation := transition_relation F π
  reduction := quotient_reduction F π

@[simp] theorem tower_level (n : ℕ) :
    (tower F π).level n = cokernel (scalar F (π^(n+1))) := rfl

end CubicTenVariables.AdicSheafQuotients
