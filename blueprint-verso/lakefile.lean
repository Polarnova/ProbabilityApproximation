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
  packagesDir := "../.lake/packages"
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

input_file referencesBib where
  path := "ProbabilityApproximationBlueprint/references.bib"
  text := true

target referencesBibStamp pkg : System.FilePath := do
  let bibliography ← referencesBib.fetch
  let stamp := pkg.buildDir / "references.bib.stamp"
  buildFileAfterDep (text := true) stamp bibliography fun bibliographyPath => do
    let sourcesOlean :=
      pkg.buildDir / "lib" / "lean" /
        "ProbabilityApproximationBlueprint" / "Sources.olean"
    let sourcesIlean :=
      pkg.buildDir / "lib" / "lean" /
        "ProbabilityApproximationBlueprint" / "Sources.ilean"
    removeFileIfExists sourcesOlean
    removeFileIfExists sourcesIlean
    IO.FS.writeFile stamp (← IO.FS.readFile bibliographyPath)

@[default_target]
lean_lib ProbabilityApproximationBlueprint where
  extraDepTargets := #[`referencesBibStamp]

lean_exe «blueprint-gen» where
  root := `ProbabilityApproximationBlueprintMain
