/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import VersoManual
import VersoBlueprint.PreviewManifest
import ProbabilityApproximationBlueprint.Book

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc ProbabilityApproximationBlueprint.Book)
    args
    (extensionImpls := by exact extension_impls%)
