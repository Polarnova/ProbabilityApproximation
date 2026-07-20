/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximationBlueprint.Site
import VersoBlueprint.PreviewManifest
import ProbabilityApproximationBlueprint.Blueprint

def main (args : List String) : IO UInt32 := do
  let profile ← BlueprintSite.readProfile
  let probabilityRevision ←
    BlueprintSite.sourceRevision "PROBABILITY_APPROXIMATION_SOURCE_REVISION" "v0.9.6"
  let mathlibRevision ← BlueprintSite.sourceRevision "MATHLIB_SOURCE_REVISION" "v4.32.0"
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc ProbabilityApproximationBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
    (config := BlueprintSite.renderConfig profile #[
      .github
        "ProbabilityApproximation/"
        "Polarnova/ProbabilityApproximation"
        probabilityRevision,
      .github "Mathlib/" "leanprover-community/mathlib4" mathlibRevision
    ])
