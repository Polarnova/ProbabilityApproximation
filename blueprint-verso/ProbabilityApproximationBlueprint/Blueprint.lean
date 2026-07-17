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
Berry--Esseen theorem for independent centered real summands: after normalizing the total variance
to one, the distribution-function error at $`x` is bounded by
$$`
\frac{C\sum_i\mathbb E|X_i|^3}{1+|x|^3}.
`
The proof follows the Stein-equation, concentration, one-sided-truncation, residual, and reflection
argument of {Citations.citet chenShao2005}[].

The second is Bentkus's multivariate Lyapunov bound.  For independent centered random vectors with
positive-definite total covariance $`S`, it controls every measurable convex event by
$$`
C d^{1/4}\sum_i\mathbb E\|S^{-1/2}X_i\|^3.
`
Its proof combines convex-distance smoothing, signed-distance coarea, Ball's Gaussian perimeter
estimate, Gaussian replacement, an identity-covariance induction, and covariance-square-root
whitening {Citations.citep ball1993 bentkus2004}[].

The chapters below present these arguments in mathematical order.  Their 65 theorem nodes are
associated with 345 kernel-checked Lean declarations and connected by 97 reviewed proof
dependencies.  Local measurability, integrability, coercion, and algebraic lemmas remain in the
Lean implementation rather than interrupting the exposition.  The site is generated with
[Verso Blueprint](https://github.com/leanprover/verso-blueprint).

{include 0 ProbabilityApproximationBlueprint.NonuniformBerryEsseen}

{include 0 ProbabilityApproximationBlueprint.ConvexSetApproximation}

{references}

{blueprint_graph}
