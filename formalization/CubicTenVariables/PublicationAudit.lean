import CubicTenVariables
import HessianTheorem11
import TranslatedDepthSeven
import Lean.Util.CollectAxioms

/-! Audit all project theorems imported by the three public roots, and verify
the exact conditional main theorem signature. Mathematical proposition
arguments remain hypotheses; the audit does not discharge them. -/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut own := 0
  let mut geometry := 0
  let mut counting := 0
  let mut state : CollectAxioms.State := {}
  for (name, info) in env.constants.toList do
    if (`CubicTenVariables).isPrefixOf name || (`HessianTheorem11).isPrefixOf name ||
        (`TranslatedDepthSeven).isPrefixOf name then
      match info with
      | .thmInfo _ =>
        if (`CubicTenVariables).isPrefixOf name then own := own + 1
        else if (`HessianTheorem11).isPrefixOf name then geometry := geometry + 1
        else counting := counting + 1
        let (_, next) := ((CollectAxioms.collect name).run env).run state
        state := next
        for ax in state.axioms do
          unless allowed.contains ax do
            throwError "Unapproved axiom {ax} while auditing theorem {name}"
      | .axiomInfo _ => throwError "Custom project axiom found: {name}"
      | _ => pure ()
  logInfo m!"PUBLICATION AUDIT PASSED: {own} cubic, {geometry} Hessian, {counting} translated/counting theorems."
  logInfo "Only propext, Classical.choice and Quot.sound permitted. Main theorem remains conditional on seven explicit mathematical inputs."

example
    (microlocal : CubicTenVariables.Literature.ProjectiveMicrolocalCertificate)
    (degreeSpan : TranslatedDepthSeven.StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (weil : CubicTenVariables.Literature.AffinePlaneCurveWeil)
    (dichotomy : CubicTenVariables.Literature.ProperHyperplaneWeightDichotomy)
    (salberger : TranslatedDepthSeven.Published.Salberger2023Theorem04)
    (hk : CubicTenVariables.Literature.HooleyKatzPointCount)
    (browning : CubicTenVariables.Literature.BrowningCubicPointCount) :
    CubicTenVariables.MainTheorem :=
  CubicTenVariables.Theorem11ReducedLiterature.main
    microlocal degreeSpan weil dichotomy salberger hk browning

example : CubicTenVariables.HypersurfaceTheorem ↔ CubicTenVariables.MainTheorem :=
  CubicTenVariables.hypersurface_iff_main

example : CubicTenVariables.MainTheorem ↔ CubicTenVariables.IntegerTenVariableTheorem :=
  CubicTenVariables.main_iff_integerTen

example : CubicTenVariables.MainTheorem ↔ CubicTenVariables.SymmetricTenVariableTheorem :=
  CubicTenVariables.main_iff_symmetricTen
