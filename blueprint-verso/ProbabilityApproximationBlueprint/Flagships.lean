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

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Release flagships" =>

:::theorem "nonuniform-berry-esseen" (lean := "ProbabilityTheory.nonuniformBerryEsseen") (uses := "scalar-release-reduction") (tags := "flagship, source-bikelis, source-chen-shao-2005, scalar, fidelity-exact")
*Finite-third-moment nonuniform Berry--Esseen theorem.* There is an absolute constant
$`C>0` with the following property. Let $`I` be a finite index set, let
$`(\Omega,\mathcal F,\mathbb P)` be a probability space, and let
$`(X_i)_{i\in I}` be independent measurable real-valued random variables satisfying
$$`
\mathbb E X_i=0,
\qquad
\mathbb E|X_i|^3<\infty,
\qquad
\sum_{i\in I}\operatorname{Var}(X_i)=1.
`
Writing
$$`
W=\sum_{i\in I}X_i,
\qquad
\gamma=\sum_{i\in I}\mathbb E|X_i|^3,
`
for every $`x\in\mathbb R` one has
$$`
\left|\mathbb P[W\le x]-\Phi(x)\right|
\le
\frac{C\gamma}{1+|x|^3},
`
where $`\Phi` is the distribution function of a standard normal random variable.
:::

This finite-third-moment form is historically due to Bikelis; Chen--Shao,
*A non-uniform Berry--Esseen bound via Stein's method* (2001), Theorem 2.2 and
the discussion following it, printed pp. 238--239, proves the stronger truncated-moment
version.  The proof route formalized here follows Chen--Shao,
*Stein's method for normal approximation* (2005), Section 6.2, printed pp. 44--48.
The universal central $`R_{2,2}` estimate and the atom-safe reflection step are both
included in the associated kernel-checked declaration.

:::theorem "bentkus-convex-set" (uses := "bentkus-standardized-induction, bentkus-whitening-one-set-transport") (tags := "flagship, source-bentkus-2004, multivariate, convex-set, fidelity-frozen, source-open")
*Bentkus's Lyapunov bound for convex sets.* There is an absolute constant $`C>0` with the
following property. Let $`d,n\in\mathbb N` with $`d>0`, let
$`X_1,\ldots,X_n` be independent measurable random vectors in $`\mathbb R^d` such that
$$`
\mathbb E X_i=0,
\qquad
\mathbb E\|X_i\|^3<\infty,
`
and set $`W=\sum_{i=1}^n X_i`. Suppose that the covariance matrix
$`S=\operatorname{Cov}(W)` is positive definite, and let $`G` be a centered Gaussian
random vector with covariance matrix $`S`. Then for every measurable convex set
$`A\subseteq\mathbb R^d`,
$$`
\left|\mathbb P[W\in A]-\mathbb P[G\in A]\right|
\le
C d^{1/4}\sum_{i=1}^n
\mathbb E\left\|S^{-1/2}X_i\right\|^3.
`
:::

This is Bentkus, *A Lyapunov type bound in $`\mathbb R^d`* (Russian original
2004; English translation 2005), Theorem 1.1 and equation (1.1), printed pp. 400--401.
The matrix $`S` here is the total covariance; $`S^{-1/2}` is the paper's inverse of
the positive covariance square root.  The whitening and one-set covariance transport are
kernel-checked.  The node has no Lean association until the standardized induction and
its full Gaussian shell input are also kernel-checked.
