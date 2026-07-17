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

This volume develops two quantitative central limit theorems.  Let $`X_1,\ldots,X_n` be
independent centered real random variables with unit total variance, and put
$`W=\sum_iX_i` and $`\beta_3=\sum_i\mathbb E|X_i|^3`.  The nonuniform
Berry--Esseen theorem gives a universal constant $`C>0` such that
$$`
\left|\Pr(W\le x)-\Phi(x)\right|
\le\frac{C\beta_3}{1+|x|^3},
\qquad x\in\mathbb R.
`
For independent centered random vectors in $`\mathbb R^d`, put $`W=\sum_iX_i`,
$`\Sigma=\operatorname{Cov}(W)`, and
$`\beta=\sum_i\mathbb E\lVert\Sigma^{-1/2}X_i\rVert_2^3`.  If $`\Sigma` is
positive definite and $`Z\sim\mathcal N_d(0,\Sigma)`, Bentkus's theorem gives a universal
constant $`C>0` such that
$$`
\sup_{A\in\mathcal C_d}\left|\Pr(W\in A)-\Pr(Z\in A)\right|
\le C d^{1/4}\beta,
`
where $`\mathcal C_d` is the class of Borel convex subsets of $`\mathbb R^d`.

The exposition develops the proofs from their mathematical prerequisites: Stein's equation,
concentration and truncation for the scalar theorem; convex distance, Gaussian boundary measure,
Ball's perimeter estimate, Gaussian replacement, induction, and whitening for the multivariate
theorem.

{include 0 ProbabilityApproximationBlueprint.NonuniformBerryEsseen}

{include 0 ProbabilityApproximationBlueprint.ConvexSetApproximation}

{references}
