/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import Lake

open Lake DSL

require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint" @ "v4.32.0"
require ProbabilityApproximation from ".."

package ProbabilityApproximationBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

input_file referencesBib where
  path := "ProbabilityApproximationBlueprint/references.bib"
  text := true

@[default_target]
lean_lib ProbabilityApproximationBlueprint where
  extraDepTargets := #[`referencesBib]

lean_exe «blueprint-gen» where
  root := `ProbabilityApproximationBlueprintMain
