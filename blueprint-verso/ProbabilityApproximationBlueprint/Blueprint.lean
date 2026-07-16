/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import ProbabilityApproximationBlueprint.Scalar
import ProbabilityApproximationBlueprint.ConvexGeometry
import ProbabilityApproximationBlueprint.Flagships

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Quantitative Normal Approximation in Lean" =>

ProbabilityApproximation develops quantitative Gaussian approximation in
[Lean 4](https://github.com/leanprover/lean4) and
[Mathlib](https://github.com/leanprover-community/mathlib4).  The curated graph exposes the
mathematically significant steps of the two proofs: the Chen--Shao scalar residual argument and
the convex-geometric smoothing route to Bentkus's theorem.

The site is generated with [Verso Blueprint](https://github.com/leanprover/verso-blueprint).

{include 0 ProbabilityApproximationBlueprint.Scalar}

{include 0 ProbabilityApproximationBlueprint.ConvexGeometry}

{include 0 ProbabilityApproximationBlueprint.Flagships}

{blueprint_graph}
