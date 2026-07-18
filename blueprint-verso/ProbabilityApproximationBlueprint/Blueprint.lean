/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import ProbabilityApproximationBlueprint.NonuniformBerryEsseen
import ProbabilityApproximationBlueprint.ConvexSetApproximation
import ProbabilityApproximationBlueprint.References

open Verso.Genre
open Verso.Genre.Manual
open Informal
open ProbabilityApproximationBlueprint.Sources

#doc (Manual) "Berry–Esseen Bounds for Independent Sums" =>

ProbabilityApproximation formalizes two quantitative central limit theorems in
[Lean 4](https://github.com/leanprover/lean4) and
[Mathlib](https://github.com/leanprover-community/mathlib4).  The first is a nonuniform
Berry--Esseen theorem for independent centered real summands.  With $`W=\sum_iX_i`, unit total
variance, and $`\beta_3=\sum_i\mathbb E|X_i|^3`, there is a universal constant $`C>0`
such that
$$`
\left|\Pr(W\le x)-\Phi(x)\right|
\le\frac{C\beta_3}{1+|x|^3},
\qquad x\in\mathbb R.
`
The proof follows the Stein-equation, concentration, one-sided-truncation, residual, and reflection
argument of {Citations.citet chenShao2005}[].

The second is Bentkus's multivariate Lyapunov bound.  For independent centered random vectors, put
$`W=\sum_iX_i`, $`\Sigma=\operatorname{Cov}(W)`, and
$`\beta=\sum_i\mathbb E\lVert\Sigma^{-1/2}X_i\rVert_2^3`.  If $`\Sigma` is positive
definite and $`Z\sim\mathcal N_d(0,\Sigma)`, then
$$`
\sup_{A\in\mathcal C_d}\left|\Pr(W\in A)-\Pr(Z\in A)\right|
\le C d^{1/4}\beta,
`
where $`\mathcal C_d` is the class of Borel convex subsets of $`\mathbb R^d`.
Its proof combines convex-distance smoothing, signed-distance coarea, Ball's Gaussian perimeter
estimate, Gaussian replacement, an identity-covariance induction, and covariance-square-root
whitening {Citations.citep ball1993 bentkus2004}[].

The chapters below present the scalar and multivariate arguments in mathematical order. For
continuous reading and offline use, the complete text is also available as a
[PDF](berry-esseen-bounds.pdf).

{include 0 ProbabilityApproximationBlueprint.NonuniformBerryEsseen}

{include 0 ProbabilityApproximationBlueprint.ConvexSetApproximation}

{references}

{blueprint_graph}
