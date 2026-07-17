import ProbabilityApproximation
import Mathlib.Util.AssertNoSorry

open Lean Elab Command

/-- Reject nonstandard axioms in the reviewed public release foundation.

The project extends Mathlib's existing `ProbabilityTheory` namespace, so this audit deliberately
uses an explicit registry rather than scanning every declaration with that prefix. Add a reviewed
public theorem to the registry only after its proof and public role have been audited. -/
elab "#audit_probability_approximation" : command => do
  let declarations := #[
    ``ProbabilityTheory.uniformBerryEsseen_thirdMoment,
    ``ProbabilityTheory.nonuniformBerryEsseen,
    ``ProbabilityTheory.exists_bentkus_identity_covariance_constant,
    ``ProbabilityTheory.exists_bentkus_convex_set_constant
  ]
  let allowed := NameSet.ofList [``propext, ``Classical.choice, ``Quot.sound]
  let mut sorryOffenders := #[]
  let mut unexpected := #[]
  for name in declarations do
    let axioms ← Lean.collectAxioms name
    if axioms.contains ``sorryAx then
      sorryOffenders := sorryOffenders.push name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        unexpected := unexpected.push (name, axiomName)
  unless sorryOffenders.isEmpty do
    throwError "sorryAx found in reviewed public declarations: {sorryOffenders.toList}"
  unless unexpected.isEmpty do
    throwError "nonstandard axioms found in reviewed public declarations: {unexpected.toList}"
  logInfo m!"axiom audit ok: {declarations.size} reviewed public declarations"

#audit_probability_approximation
