/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import ProbabilityApproximationBlueprint.Scalar
import ProbabilityApproximationBlueprint.ConvexGeometry
import ProbabilityApproximationBlueprint.Flagships

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Quantitative Normal Approximation in Lean" =>

Asher Yan with Codex

This volume records the mathematical statements and proof architecture of the
ProbabilityApproximation library.  It covers the scalar nonuniform Berry--Esseen theorem,
the convex-geometric and Gaussian-analytic inputs to Bentkus's multivariate theorem, and the
two release targets.

{include 0 ProbabilityApproximationBlueprint.Scalar}

{include 0 ProbabilityApproximationBlueprint.ConvexGeometry}

{include 0 ProbabilityApproximationBlueprint.Flagships}
