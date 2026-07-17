/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import Verso
import VersoManual
import VersoBlueprint
import ProbabilityApproximationBlueprint.NonuniformBerryEsseen
import ProbabilityApproximationBlueprint.ConvexSetApproximation
import ProbabilityApproximationBlueprint.References

open Verso.Genre
open Verso.Genre.Manual
open Informal
open ProbabilityApproximationBlueprint.Sources

#doc (Manual) "Berry–Esseen Bounds for Independent Sums" =>

This volume gives kernel-checked proofs of two quantitative central limit theorems.  For centered
independent real summands of unit total variance it proves the nonuniform estimate
$$`
\left|\mathbb P\!\left[\sum_iX_i\le x\right]-\Phi(x)\right|
\le\frac{C\sum_i\mathbb E|X_i|^3}{1+|x|^3}.
`
For centered independent random vectors with positive-definite total covariance $`S`, it proves
Bentkus's bound over all measurable convex sets,
$$`
\left|\mathbb P\!\left[\sum_iX_i\in A\right]-N(0,S)(A)\right|
\le C d^{1/4}\sum_i\mathbb E\|S^{-1/2}X_i\|^3.
`

The exposition develops the proofs from their mathematical prerequisites: Stein's equation,
concentration and truncation for the scalar theorem; convex distance, Gaussian boundary measure,
Ball's perimeter estimate, Gaussian replacement, induction, and whitening for the multivariate
theorem.  The 65-node dependency graph groups 345 kernel-checked declarations into these
mathematical milestones.

{include 0 ProbabilityApproximationBlueprint.NonuniformBerryEsseen}

{include 0 ProbabilityApproximationBlueprint.ConvexSetApproximation}

{references}
