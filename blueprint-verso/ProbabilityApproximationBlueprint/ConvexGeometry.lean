/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import ProbabilityApproximation.ConvexGeometry.ParallelSets
import ProbabilityApproximation.ConvexGeometry.SmoothCutoff
import ProbabilityApproximation.Bentkus.GaussianCompanions
import ProbabilityApproximation.Bentkus.GaussianCompanionMoments
import ProbabilityApproximation.Bentkus.CovarianceAlgebra
import ProbabilityApproximation.Bentkus.GaussianDensityDerivatives
import ProbabilityApproximation.Bentkus.GaussianDensityIntegrationByParts
import ProbabilityApproximation.Bentkus.GaussianIntegrationByParts
import ProbabilityApproximation.Bentkus.InductionBranches
import ProbabilityApproximation.Bentkus.LeaveOneOutWhitening
import ProbabilityApproximation.Bentkus.CutoffDerivativeGaussianIBP
import ProbabilityApproximation.Bentkus.AngleCalculus
import ProbabilityApproximation.Bentkus.ParameterClosure
import ProbabilityApproximation.Bentkus.ProbabilitySpaceTransport
import ProbabilityApproximation.Bentkus.Rotation
import ProbabilityApproximation.Bentkus.SmoothingInequality
import ProbabilityApproximation.Bentkus.TaylorRemainder
import ProbabilityApproximation.Bentkus.Whitening
import ProbabilityApproximation.ConvexGeometry.BallProjectionArea
import ProbabilityApproximation.ConvexGeometry.BallCauchyProjection
import ProbabilityApproximation.ConvexGeometry.BallRadialMajorant
import ProbabilityApproximation.ConvexGeometry.BallRadialGammaBound
import ProbabilityApproximation.ConvexGeometry.BallRadialMass
import ProbabilityApproximation.ConvexGeometry.BallSphereMoments
import ProbabilityApproximation.ConvexGeometry.BallSphereHausdorff
import ProbabilityApproximation.ConvexGeometry.BallSphericalRearrangement
import ProbabilityApproximation.ConvexGeometry.GaussianShell
import ProbabilityApproximation.ConvexGeometry.GaussianShellCoarea
import ProbabilityApproximation.ConvexGeometry.ScalarCoarea

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The convex-set route" =>

Throughout this section $`E=\mathbb R^d` has its Euclidean norm.  For
$`A\subseteq E`, write
$$`
d_A(x)=\inf_{a\in A}\|x-a\|,\qquad
A^\varepsilon=\{x:d_A(x)<\varepsilon\}.
`

:::lemma_ "convex-parallel-sets" (lean := "ProbabilityTheory.thickening_isConvexSet, ProbabilityTheory.cthickening_isConvexSet, ProbabilityTheory.measurableSet_thickening, ProbabilityTheory.measurableSet_cthickening, ProbabilityTheory.thickening_vadd, ProbabilityTheory.cthickening_vadd") (tags := "bentkus, convex-geometry, parallel-sets, source-bentkus-2004, fidelity-generalized-radii")
*Convex parallel sets.* If $`A\subseteq\mathbb R^d` is convex, then its open
parallel set $`A^\varepsilon` is convex for every $`\varepsilon\in\mathbb R`; its closed
parallel set $`\{x:d_A(x)\le\varepsilon\}` is convex whenever $`\varepsilon\ge0`.
Both parallel sets are measurable, and for every $`v\in\mathbb R^d`,
$$`
(v+A)^\varepsilon=v+A^\varepsilon
`
with the analogous identity for closed parallel sets.
:::

These are the set-theoretic facts used in Vidmantas Bentkus,
*A Lyapunov type bound in $`\mathbb R^d`* (Russian original 2004), condition (ii)
and the neighborhood notation preceding Theorem 1.2, printed pp. 401--402.
The formal open-thickening theorem is harmlessly generalized to all real radii.

:::theorem "metric-projection" (lean := "ProbabilityTheory.existsUnique_isNearestPoint, ProbabilityTheory.metricProjection, ProbabilityTheory.metricProjection_variational, ProbabilityTheory.metricProjection_firmlyNonexpansive, ProbabilityTheory.metricProjection_lipschitzWith, ProbabilityTheory.metricProjection_residual_lipschitzWith") (tags := "bentkus, convex-geometry, projection, source-bentkus-2003, fidelity-exact")
*Metric projection onto a closed convex set.* Let $`A\subseteq\mathbb R^d` be
nonempty, closed, and convex.  For every $`x` there is a unique point $`p_A(x)\in A`
such that $`\|x-p_A(x)\|=d_A(x)`.  It satisfies
$$`
\langle x-p_A(x),a-p_A(x)\rangle\le0\quad(a\in A)
`
and, for all $`x,y`,
$$`
\|p_A(x)-p_A(y)\|^2
\le\langle x-y,p_A(x)-p_A(y)\rangle.
`
Consequently both $`p_A` and the residual map $`x\mapsto x-p_A(x)` are
$`1`-Lipschitz.
:::

This packages the Euclidean projection geometry used in Bentkus,
*On the dependence of the Berry--Esseen bound on dimension* (2003), Lemma 2.2,
printed pp. 389--390.  The paper states the resulting distance-gradient inequalities;
the projection formulation records the complete geometric mechanism used by the
formal proof.

:::theorem "squared-distance-calculus" (lean := "ProbabilityTheory.squaredInfDist_remainder_bound, ProbabilityTheory.hasFDerivAt_squaredInfDist, ProbabilityTheory.hasFDerivAt_infDist_of_notMem, ProbabilityTheory.norm_fderiv_infDist_of_notMem") (uses := "metric-projection") (tags := "bentkus, convex-geometry, distance, source-bentkus-2003, fidelity-explicit-frechet-form")
*Differentiability of distance to a convex set.* Under the hypotheses of the preceding
node, for every $`x,h\in\mathbb R^d`,
$$`
\left|d_A(x+h)^2-d_A(x)^2
-2\langle x-p_A(x),h\rangle\right|\le3\|h\|^2.
`
Thus $`d_A^2` is Fréchet differentiable everywhere with
$$` D(d_A^2)(x)[h]=2\langle x-p_A(x),h\rangle. `
If $`x\notin A`, then $`d_A` is Fréchet differentiable at $`x`,
$$`
Dd_A(x)[h]
=\left\langle\frac{x-p_A(x)}{d_A(x)},h\right\rangle,
\qquad \|Dd_A(x)\|=1.
`
:::

This is the distance calculus behind Vidmantas Bentkus, *On the dependence of the
Berry--Esseen bound on dimension* (2003), Lemma 2.2, equations (2.5)--(2.9),
printed pp. 389--390.  The formal statement makes the derivative a bounded
linear functional and supplies an explicit quadratic remainder.

:::theorem "bentkus-smooth-cutoff" (lean := "ProbabilityTheory.bentkusProfile, ProbabilityTheory.bentkusCutoff, ProbabilityTheory.hasFDerivAt_bentkusCutoff, ProbabilityTheory.bentkusCutoff_eq_one_of_mem, ProbabilityTheory.bentkusCutoff_eq_zero_of_le_infDist, ProbabilityTheory.norm_fderiv_bentkusCutoff_le, ProbabilityTheory.norm_fderiv_bentkusCutoff_sub_le, ProbabilityTheory.contDiff_bentkusCutoff") (uses := "squared-distance-calculus") (tags := "bentkus, convex-geometry, smoothing, source-bentkus-2003, source-bentkus-2004, fidelity-exact-constants")
*Bentkus's continuously differentiable distance cutoff.* Let $`A\subseteq\mathbb R^d`
be nonempty, closed, and convex, and let $`\varepsilon>0`.  There is a continuously
differentiable function $`\varphi_{\varepsilon,A}:\mathbb R^d\to[0,1]` of the form
$$`
\varphi_{\varepsilon,A}(x)=\psi(d_A(x)/\varepsilon)
`
such that
$$`
\varphi_{\varepsilon,A}=1\ \hbox{on }A,\qquad
\varphi_{\varepsilon,A}=0\ \hbox{when }d_A(x)\ge\varepsilon,
`
and, for every $`x,y\in\mathbb R^d`,
$$`
\|D\varphi_{\varepsilon,A}(x)\|\le\frac2\varepsilon,
\qquad
\|D\varphi_{\varepsilon,A}(x)-D\varphi_{\varepsilon,A}(y)\|
\le\frac{8}{\varepsilon^2}\|x-y\|.
`
:::

This is Vidmantas Bentkus, *On the dependence of the Berry--Esseen bound on
dimension* (2003), Lemma 2.3, equations (2.10)--(2.12), printed pp. 390--391, and the
same cutoff imported in Bentkus, *A Lyapunov type bound in $`\mathbb R^d`* (2004),
Lemma 2.2, equation (2.2), printed p. 402.  The formal profile is the paper's
piecewise quadratic $`\psi`; endpoint
values are included explicitly.

:::theorem "gaussian-companions-and-transport" (lean := "ProbabilityTheory.covarianceMatrix, ProbabilityTheory.covarianceMatrix_posSemidef, ProbabilityTheory.dotProduct_covarianceMatrix_mulVec, ProbabilityTheory.gaussianCompanion, ProbabilityTheory.summandCovarianceMatrix, ProbabilityTheory.gaussianCompanionMeasureOf, ProbabilityTheory.iIndepFun_gaussianCompanion_of, ProbabilityTheory.integral_gaussianCompanion_of_eq_zero, ProbabilityTheory.memLp_three_gaussianCompanion_of, ProbabilityTheory.covarianceBilin_map_gaussianCompanion_of, ProbabilityTheory.independentLawProduct, ProbabilityTheory.isProbabilityMeasure_independentLawProduct, ProbabilityTheory.iIndepFun_independentLawProduct, ProbabilityTheory.map_coordinate_independentLawProduct, ProbabilityTheory.map_family_eq_independentLawProduct, ProbabilityTheory.map_sum_eq_map_sum_independentLawProduct, ProbabilityTheory.bentkusReplacementMeasure, ProbabilityTheory.replacementOriginal, ProbabilityTheory.replacementGaussian, ProbabilityTheory.indepFun_replacement_blocks, ProbabilityTheory.indepFun_replacementOriginal_replacementGaussian, ProbabilityTheory.map_replacementOriginal, ProbabilityTheory.map_replacementGaussian, ProbabilityTheory.measurePreserving_replacementOriginal, ProbabilityTheory.measurePreserving_replacementGaussian, ProbabilityTheory.memLp_replacementOriginal, ProbabilityTheory.memLp_three_replacementGaussian, ProbabilityTheory.integral_replacementOriginal_eq, ProbabilityTheory.integral_replacementGaussian_eq_zero, ProbabilityTheory.covarianceBilin_replacementGaussian_eq_replacementOriginal, ProbabilityTheory.iIndepFun_replacementOriginal, ProbabilityTheory.iIndepFun_replacementGaussian") (tags := "bentkus, gaussian-replacement, probability-transport, source-bentkus-2004, fidelity-canonical-product-realization")
*Gaussian companions and canonical probability-space transport.* Let
$`X_i:\Omega\to\mathbb R^d` be a finite measurable family on a probability space
$`(\Omega,\mu)`, put $`\nu_i=\mathcal L_\mu(X_i)`, and let $`\Sigma_i` be the matrix
of the covariance bilinear form of $`\nu_i`.  Then $`\Sigma_i` is positive semidefinite,
and the canonical Gaussian product
$$`
\Gamma=\bigotimes_i N(0,\Sigma_i)
`
has independent coordinate variables $`Y_i` that are centered, belong to $`L^3`, and
satisfy
$$`
\operatorname{Cov}(Y_i)[u,v]
=\operatorname{Cov}_{\nu_i}[u,v]\qquad(u,v\in\mathbb R^d).
`
The marginal-law product $`\nu=\bigotimes_i\nu_i` is a probability measure whose
coordinate variables $`\widetilde X_i` are independent.  If the original $`X_i` are
independent, then
$$`
\mathcal L_\mu((X_i)_i)=\nu,\qquad
\mathcal L_\mu\!\left(\sum_iX_i\right)
=\mathcal L_\nu\!\left(\sum_i\widetilde X_i\right).
`
Finally, the product $`\nu\otimes\Gamma` carries the two coordinate families
$`(\widetilde X_i)_i` and $`(Y_i)_i` on one probability space.  Each family is
mutually independent, the two coordinate blocks are independent, and hence every
$`\widetilde X_i` is independent of every $`Y_j`.  On this product space the original
coordinate retains law $`\nu_i`, the Gaussian coordinate retains law $`N(0,\Sigma_i)`,
and their covariance bilinear forms agree.
:::

This is the canonical-space realization of the Gaussian companions $`Y_i`, the
leave-one-out variables in equation (3.2), and the joint enlargement implicit in the
telescoping/rotation setup (3.2)--(3.5) of Vidmantas Bentkus,
*A Lyapunov type bound in $`\mathbb R^d`* (2004), printed pp. 403--404.  The source
simply assumes all variables exist independently in the aggregate; the formal statement
constructs the required marginal and Gaussian product spaces and allows singular
individual covariance matrices.  It does not yet assert the rotation identity (3.4).

:::lemma_ "gaussian-fourth-moment-control" (lean := "ProbabilityTheory.integral_norm_pow_four_multivariateGaussian_le") (tags := "bentkus, gaussian-replacement, moments, source-bentkus-2004, fidelity-explicit-sufficient-bound")
*Dimension-free fourth-moment control for a Gaussian vector.* Let $`S` be a positive
semidefinite $`d\times d` real matrix and let $`Y\sim N(0,S)`.  Then
$$`
\mathbb E\|Y\|^4\le 3\bigl(\mathbb E\|Y\|^2\bigr)^2.
`
No nonsingularity assumption is imposed on $`S`.
:::

This is an explicit sufficient estimate for the dimension-free Gaussian moment comparison
used by Vidmantas Bentkus, *A Lyapunov type bound in $`\mathbb R^d`* (2004), in the
discussion following equation (3.35), printed p. 408.  Bentkus records the resulting
third-moment comparison with an implicit absolute constant; the displayed fourth-moment
bound is the formal route used to make that constant explicit.

:::lemma_ "gaussian-companion-second-moment-match" (lean := "ProbabilityTheory.integral_norm_sq_replacementGaussian_eq_replacementOriginal") (uses := "gaussian-companions-and-transport") (tags := "bentkus, gaussian-replacement, moments, source-bentkus-2004, fidelity-exact")
*Exact second-moment matching on the replacement space.* Let $`X_i` be measurable,
centered, square-integrable random vectors in $`\mathbb R^d`.  On the canonical
replacement space, let $`\widetilde X_i` have the law of $`X_i` and let
$`Y_i\sim N(0,\operatorname{Cov}(X_i))` be its independent Gaussian companion.  Then
$$`
\mathbb E\|Y_i\|^2=\mathbb E\|\widetilde X_i\|^2.
`
The covariance, and hence the Gaussian law, may be singular.
:::

This is the norm-moment consequence of the covariance matching used by Vidmantas Bentkus,
*A Lyapunov type bound in $`\mathbb R^d`* (2004), immediately after equation (3.35),
printed p. 408, where the equality $`\mathbb E\lvert Y\rvert^2=
\mathbb E\lvert X\rvert^2` is invoked explicitly.

:::theorem "gaussian-companion-third-moment-comparison" (lean := "ProbabilityTheory.gaussianCompanionThirdMomentConstant, ProbabilityTheory.integral_norm_pow_three_multivariateGaussian_covarianceMatrix_le, ProbabilityTheory.integral_norm_pow_three_replacementGaussian_le") (uses := "gaussian-fourth-moment-control, gaussian-companion-second-moment-match") (tags := "bentkus, gaussian-replacement, moments, source-bentkus-2004, fidelity-explicit-absolute-constant")
*Third-moment comparison for a covariance-matched Gaussian.* Let $`X` be a centered
$`L^3` random vector in $`\mathbb R^d`, and let
$`Y\sim N(0,\operatorname{Cov}(X))`.  With the absolute constant $`C_G=27`, one has
$$`
\mathbb E\|Y\|^3\le C_G\,\mathbb E\|X\|^3.
`
Equivalently, for each coordinate pair $`(\widetilde X_i,Y_i)` on the canonical
replacement space,
$$`
\mathbb E\|Y_i\|^3\le 27\,\mathbb E\|\widetilde X_i\|^3.
`
:::

Vidmantas Bentkus, *A Lyapunov type bound in $`\mathbb R^d`* (2004), uses
$`\mathbb E\lvert Y\rvert^3\ll\mathbb E\lvert X\rvert^3` after equation (3.35),
printed p. 408, and reuses the same absolute-moment control in equations (3.39)--(3.40),
printed p. 409.  The formal statement replaces the source's implicit constant by the
conservative explicit value $`27`.

:::lemma_ "gaussian-companion-mixed-moment" (lean := "ProbabilityTheory.integral_norm_sq_replacementOriginal_mul_norm_replacementGaussian_le") (uses := "gaussian-companions-and-transport, gaussian-companion-second-moment-match") (tags := "bentkus, gaussian-replacement, moments, source-bentkus-2004, fidelity-explicit-holder-bound")
*Mixed original--Gaussian moment bound.* Under the preceding centered $`L^3`
hypotheses, the independent canonical pair $`(\widetilde X_i,Y_i)` satisfies
$$`
\mathbb E\bigl[\|\widetilde X_i\|^2\|Y_i\|\bigr]
\le \mathbb E\|\widetilde X_i\|^3.
`
:::

This is the Hölder estimate used immediately before equation (3.30) in Vidmantas
Bentkus, *A Lyapunov type bound in $`\mathbb R^d`* (2004), printed p. 407.  The source
writes the estimate with $`X` and its covariance-matched Gaussian $`Y`; the formal
statement records it on the canonical independent replacement space.

:::theorem "bentkus-rotation-cancellation" (lean := "ProbabilityTheory.bentkusRotated, ProbabilityTheory.bentkusRotatedDeriv, ProbabilityTheory.integral_bentkusRotated_eq_zero, ProbabilityTheory.integral_bentkusRotatedDeriv_eq_zero, ProbabilityTheory.bentkusRotated_bilin_bentkusRotatedDeriv, ProbabilityTheory.integral_bilin_bentkusRotated_bentkusRotatedDeriv_eq_zero, ProbabilityTheory.integral_bilin_replacementRotated_replacementRotatedDeriv_eq_zero") (uses := "gaussian-companions-and-transport") (tags := "bentkus, gaussian-replacement, rotation, source-bentkus-2004, fidelity-low-order-cancellation")
*Rotation and low-order moment cancellation.* Let $`X,Y` be independent random
vectors in a real Banach space $`E`, assume that they are integrable and centered, and
let $`B:E\times E\to\mathbb R` be a continuous bilinear form for which
$`B(X,X)` and $`B(Y,Y)` are integrable.  If
$$`
\mathbb E B(X,X)=\mathbb E B(Y,Y),
`
then, for every $`\alpha\in\mathbb R`, the rotation and its angular derivative
$$`
X_\alpha=\cos\alpha\,X+\sin\alpha\,Y,\qquad
X'_\alpha=-\sin\alpha\,X+\cos\alpha\,Y
`
are centered and satisfy the quadratic cancellation
$$`
\mathbb E B(X_\alpha,X'_\alpha)=0.
`
Pointwise, the bilinear term expands as
$$`
B(X_\alpha,X'_\alpha)
=-\cos\alpha\sin\alpha\,B(X,X)
+\cos^2\alpha\,B(X,Y)
-\sin^2\alpha\,B(Y,X)
+\sin\alpha\cos\alpha\,B(Y,Y).
`
In particular, for every centered measurable $`L^3` summand $`X_i`, the canonical
pair consisting of its marginal-law coordinate and its covariance-matched Gaussian
companion satisfies this cancellation for every continuous bilinear $`B`.
:::

This is the low-order rotation layer introduced immediately before equation (3.4) in
Vidmantas Bentkus, *A Lyapunov type bound in $`\mathbb R^d`* (2004), and the
linear/bilinear cancellation asserted in equation (3.5), printed p. 404.  Independence
kills the two mixed expectations and the matched second moment
kills the remaining pair.  The full telescoping identity (3.4) and its third-order
remainder estimates are still part of the open induction node below.

:::theorem "covariance-additivity-and-leave-one-out" (lean := "ProbabilityTheory.covarianceBilin_map_finsetSum_eq_sum, ProbabilityTheory.covarianceBilin_map_sum_eq_sum, ProbabilityTheory.bentkusLeaveOneOut, ProbabilityTheory.covarianceBilin_map_sum_eq_leaveOneOut_add, ProbabilityTheory.bentkusLeaveOneOutCovarianceMatrix, ProbabilityTheory.covarianceBilin_leaveOneOut_eq_inner_sub, ProbabilityTheory.bentkusLeaveOneOutCovarianceMatrix_eq_one_sub") (uses := "gaussian-companions-and-transport") (tags := "bentkus, covariance, leave-one-out, source-bentkus-2004, fidelity-exact")
*Covariance additivity and the leave-one-out identity.* Let $`X_1,\ldots,X_n` be
independent square-integrable random vectors in $`\mathbb R^d`.  For every set of
indices $`J` and every $`u,v\in\mathbb R^d`, one has
$$`
\operatorname{Cov}\!\left(\sum_{i\in J}X_i\right)[u,v]
=\sum_{i\in J}\operatorname{Cov}(X_i)[u,v].
`
Writing
$$`
W=\sum_iX_i,\qquad U_k=\sum_{i\ne k}X_i,
`
it follows that
$$`
\operatorname{Cov}(W)
=\operatorname{Cov}(U_k)+\operatorname{Cov}(X_k).
`
Consequently, if $`\operatorname{Cov}(W)=I_d`, and if $`P_k^2` denotes the covariance
matrix of $`U_k` while $`\Sigma_k` denotes that of $`X_k`, then
$$`
P_k^2=I_d-\Sigma_k.
`
No individual covariance matrix is required to be nonsingular.
:::

This is the covariance algebra in Vidmantas Bentkus, *A Lyapunov type bound in
$`\mathbb R^d`* (2004), equation (3.2) and the paragraph immediately following it,
printed p. 403.  The formal subsum identity is stated at the
level of covariance bilinear forms; the last display is its coordinate-matrix form and
is exactly the paper's $`P_k^2=I-\operatorname{cov}X_k` notation.

:::theorem "bentkus-whitening-covariance-identity" (lean := "ProbabilityTheory.bentkusWhiteningMatrix_mul_self, ProbabilityTheory.bentkusWhiteningCLM_covariance_comp") (tags := "bentkus, whitening, covariance, source-bentkus-2004, fidelity-exact-positive-square-root")
*Whitening a positive-definite covariance.* Let $`S` be a positive-definite real
$`d\times d` matrix, let $`R=S^{1/2}` be its positive square root, and set
$`T=R^{-1}=S^{-1/2}`.  Then
$$`
TST=I_d.
`
Equivalently, regarding these matrices as continuous linear maps,
$$`
T\bigl(S(Tx)\bigr)=x\qquad(x\in\mathbb R^d).
`
:::

Vidmantas Bentkus, *A Lyapunov type bound in $`\mathbb R^d`* (2004), defines the
positive covariance square root $`C` by $`C^2=\operatorname{Cov}(S_n)` in the notation
preceding Theorem 1.1, printed p. 400, and uses $`C^{-1}` in the normalization following
equation (3.1), printed p. 403.  The formal statement makes the resulting
$`C^{-1}C^2C^{-1}=I` identity explicit.

:::theorem "bentkus-whitening-gaussian-pushforward" (lean := "ProbabilityTheory.bentkusWhiteningMatrix, ProbabilityTheory.bentkusWhiteningCLM, ProbabilityTheory.bentkusWhiteningEquiv, ProbabilityTheory.map_multivariateGaussian_bentkusWhiteningEquiv, ProbabilityTheory.map_stdGaussian_bentkusWhiteningEquiv_symm") (uses := "bentkus-whitening-covariance-identity") (tags := "bentkus, whitening, gaussian-transport, source-bentkus-2004, fidelity-exact-pushforward")
*Gaussian pushforward under whitening.* Under the preceding hypotheses, let
$`T=S^{-1/2}` and let $`R=S^{1/2}`.  These maps are mutually inverse continuous linear
equivalences, and their Gaussian pushforwards satisfy
$$`
T_\#N(0,S)=N(0,I_d),
\qquad
R_\#N(0,I_d)=N(0,S).
`
:::

This is the Gaussian part of the rescaling $`S_n\mapsto C^{-1}S_n` and
$`Z\mapsto C^{-1}Z` in Vidmantas Bentkus, *A Lyapunov type bound in
$`\mathbb R^d`* (2004), immediately after equation (3.1), printed p. 403; the
covariance-square-root notation is introduced before Theorem 1.1, printed p. 400.

:::theorem "bentkus-identity-covariance-contract" (lean := "ProbabilityTheory.bentkusWhitenedSummand, ProbabilityTheory.sum_bentkusWhitenedSummand, ProbabilityTheory.iIndepFun_bentkusWhitenedSummand, ProbabilityTheory.integral_bentkusWhitenedSummand_eq_zero, ProbabilityTheory.covarianceBilin_map_sum_bentkusWhitenedSummand_eq_inner, ProbabilityTheory.BentkusIdentityCovarianceBound") (uses := "bentkus-whitening-covariance-identity") (tags := "bentkus, whitening, standardized-theorem, source-bentkus-2004, fidelity-exact-contract")
*The identity-covariance theorem contract.* Let $`X_1,\ldots,X_n` be independent,
centered $`L^3` random vectors, suppose that their sum $`W` has positive-definite
covariance $`S`, and put $`\widehat X_i=S^{-1/2}X_i`.  Then
$$`
\sum_i\widehat X_i=S^{-1/2}W,
`
the family $`(\widehat X_i)_i` remains independent and centered, and
$$`
\operatorname{Cov}\!\left(\sum_i\widehat X_i\right)=I_d.
`
For a fixed constant $`C`, the identity-covariance contract asserts that every such
normalized family and every measurable convex $`B\subseteq\mathbb R^d` satisfy
$$`
\left|\mathbb P\!\left[\sum_i\widehat X_i\in B\right]-
N(0,I_d)(B)\right|
\le C d^{1/4}\sum_i\mathbb E\|\widehat X_i\|^3.
`
:::

This is the standardized estimate (3.1) and the rescaling paragraph immediately after it
in Vidmantas Bentkus, *A Lyapunov type bound in $`\mathbb R^d`* (2004), printed
p. 403.  The formal contract isolates precisely the identity-covariance theorem that the
induction must supply; it does not assume that induction has been proved.

:::theorem "bentkus-whitening-one-set-transport" (lean := "ProbabilityTheory.bentkusWhitenedSet, ProbabilityTheory.isConvexSet_bentkusWhitenedSet, ProbabilityTheory.map_sum_apply_bentkusWhitenedSet, ProbabilityTheory.stdGaussian_apply_bentkusWhitenedSet, ProbabilityTheory.bentkus_convex_set_whitening_reduction") (uses := "bentkus-whitening-gaussian-pushforward, bentkus-identity-covariance-contract") (tags := "bentkus, whitening, convex-set-transport, source-bentkus-2004, fidelity-exact-one-set-reduction")
*One-set transport from the standardized estimate.* Let $`S` be positive definite,
$`T=S^{-1/2}`, $`W=\sum_iX_i`, and $`B=T(A)`.  An invertible linear map preserves
convexity, and the two event identities are
$$`
\mathbb P[TW\in B]=\mathbb P[W\in A],
\qquad
N(0,I_d)(B)=N(0,S)(A).
`
Consequently, any identity-covariance bound at the single set $`B` transports to
$$`
\left|\mathbb P[W\in A]-N(0,S)(A)\right|
\le C d^{1/4}\sum_i\mathbb E\|S^{-1/2}X_i\|^3.
`
:::

Vidmantas Bentkus, *A Lyapunov type bound in $`\mathbb R^d`* (2004), uses invariance
of the set class under invertible symmetric linear maps in condition (i), printed p. 401,
and applies the transformation $`C^{-1}` immediately after equation (3.1), printed
p. 403.  This node is the one-set form of that reduction and yields exactly the
normalization in Theorem 1.1, equation (1.1), printed p. 400.

:::theorem "gaussian-signed-distance-eikonal" (lean := "ProbabilityTheory.setSignedDistance, ProbabilityTheory.ae_norm_fderiv_setSignedDistance_eq_one") (uses := "squared-distance-calculus") (tags := "bentkus, gaussian-geometry, signed-distance, source-raic-2019, fidelity-exact-eikonal")
*Signed distance and its eikonal identity.* Let $`A\subsetneq\mathbb R^d` be a
nonempty convex set and define
$$`
\delta_A(x)=d(x,A)-d(x,A^c)
=\begin{cases}
-d(x,A^c),&x\in A,\\
d(x,A),&x\notin A.
\end{cases}
`
Then $`\delta_A` is Fréchet differentiable at Lebesgue-almost every point and
$$`
\|D\delta_A(x)\|=1
`
at almost every such point.
:::

Martin Raič, *A multivariate Berry--Esseen theorem with explicit constants* (2019),
defines the signed distance on printed pp. 2825--2826 and proves the almost-everywhere
differentiability and eikonal conclusions in Proposition 3.3(2)--(3), printed p. 2844.
The formal statement uses Fréchet derivatives on Euclidean space.

:::lemma_ "gaussian-signed-distance-level-frontiers" (lean := "ProbabilityTheory.signedDistance_level_pos_eq_frontier_cthickening, ProbabilityTheory.signedDistance_level_neg_eq_frontier_innerParallel, ProbabilityTheory.signedDistance_level_zero_eq_frontier") (uses := "gaussian-signed-distance-eikonal, convex-parallel-sets") (tags := "bentkus, gaussian-geometry, signed-distance, parallel-frontiers, source-raic-2019, fidelity-explicit-boundary-conventions")
*Signed-distance fibers are parallel-set frontiers.* Under the preceding hypotheses,
for $`t>0`, $`t=0`, and $`t<0`, respectively,
$$`
\begin{aligned}
\{x:\delta_A(x)=t\}
  &=\partial\{x:d(x,\overline A)\le t\},\\
\{x:\delta_A(x)=0\}&=\partial A,\\
\{x:\delta_A(x)=t\}
  &=\partial\{x\in A:B(x,-t)\subseteq A\}.
\end{aligned}
`
Here the outer parallel set is closed and the ball in the inner parallel set is open.
:::

This is Martin Raič, *A multivariate Berry--Esseen theorem with explicit constants*
(2019), Proposition 3.3(4), printed p. 2844, with the positive and negative cases written
separately to expose the exact outer-closure and open-ball conventions used by the
setwise smoothing inequality.

:::lemma_ "gaussian-shell-signed-distance-slabs" (lean := "ProbabilityTheory.stdGaussian_frontier_eq_zero, ProbabilityTheory.outerShell_closed_eq_signedDistance_preimage_Ioc, ProbabilityTheory.innerShell_eq_inter_signedDistance_preimage_Ioc, ProbabilityTheory.stdGaussian_outer_shell_eq_signedDistance_slab, ProbabilityTheory.stdGaussian_inner_shell_eq_signedDistance_slab") (uses := "gaussian-signed-distance-eikonal, convex-parallel-sets") (tags := "bentkus, gaussian-geometry, signed-distance, shells, source-raic-2019, fidelity-exact-null-boundary-conventions")
*Outer and inner shells as signed-distance slabs.* Let $`A\subsetneq\mathbb R^d`
be nonempty and convex, let $`\gamma_d=N(0,I_d)`, and let $`\varepsilon\ge0`.
The convex frontier is Gaussian-null, and
$$`
\begin{aligned}
\{x:d(x,\overline A)\le\varepsilon\}\setminus\overline A
  &=\delta_A^{-1}((0,\varepsilon]),\\
A\setminus\{x\in A:B(x,\varepsilon)\subseteq A\}
  &=A\cap\delta_A^{-1}((-\varepsilon,0]).
\end{aligned}
`
Consequently the omitted boundary has no effect on mass and
$$`
\begin{aligned}
\gamma_d\bigl(\{x:d(x,\overline A)\le\varepsilon\}\setminus A\bigr)
  &=\gamma_d\bigl(\delta_A^{-1}((0,\varepsilon])\bigr),\\
\gamma_d\bigl(A\setminus\{x\in A:B(x,\varepsilon)\subseteq A\}\bigr)
  &=\gamma_d\bigl(\delta_A^{-1}((-\varepsilon,0])\bigr).
\end{aligned}
`
:::

Martin Raič, *A multivariate Berry--Esseen theorem with explicit constants* (2019),
introduces the signed-distance neighborhoods on printed pp. 2825--2826 and uses precisely these
positive and negative slabs in the proof of Proposition 3.1, printed pp. 2844--2845, before
applying the coarea formula.  The formal identities retain equality boundaries and discharge
the convex-frontier null set explicitly.

:::theorem "gaussian-affine-codimension-one-slicing" (lean := "ProbabilityTheory.stdGaussian_eq_withDensity_standardGaussianDensityReal, ProbabilityTheory.lintegral_standardGaussianDensityReal_eq_one, ProbabilityTheory.euclideanVolume_eq_lintegral_codimOneSections, ProbabilityTheory.lintegral_eq_lintegral_codimOneSections, ProbabilityTheory.stdGaussian_apply_eq_lintegral_codimOneSections, ProbabilityTheory.standardGaussianDensity_affineHyperplane, ProbabilityTheory.standardGaussianDensity_affineHyperplane_le_one") (tags := "bentkus, gaussian-geometry, affine-slicing, coarea, source-ball-1993, source-raic-2019, fidelity-normalized-affine-coarea")
*Normalized affine codimension-one slicing.* Put
$$`
\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}.
`
Then $`N(0,I_d)=\phi_d\,\lambda_d` and $`\int\phi_d\,d\lambda_d=1`.  If
$`v\ne0`, $`p\in\mathbb R^d`, and
$$`
H_t=p+tv+v^\perp,
`
then every measurable $`B\subseteq\mathbb R^d` and every nonnegative measurable
$`w` satisfy
$$`
\begin{aligned}
\lambda_d(B)
  &=\|v\|\int_{\mathbb R}\mathcal H^{d-1}(B\cap H_t)\,dt,\\
\int_{\mathbb R^d}w\,d\lambda_d
  &=\|v\|\int_{\mathbb R}\int_{H_t}w\,d\mathcal H^{d-1}\,dt,\\
N(0,I_d)(B)
  &=\|v\|\int_{\mathbb R}\int_{B\cap H_t}\phi_d\,d\mathcal H^{d-1}\,dt.
\end{aligned}
`
The Hausdorff measure is normalized so that top-dimensional measure is Euclidean volume.
Moreover, if $`u\in\mathbb R^{n+1}` is a unit vector, then
$$`
\int_{au+u^\perp}\phi_{n+1}(y)\,d\mathcal H^n(y)
=\phi_1(a)\le1.
`
:::

Keith Ball, *The reverse isoperimetric problem for Gaussian measure* (1993), uses
codimension-one projections and Gaussian surface integrals in the proof of Theorem 4,
printed pp. 415--419.  Martin Raič, *A multivariate Berry--Esseen theorem with explicit
constants* (2019), states the general area/coarea input as Proposition 3.2 and Corollary
3.1, printed pp. 2843--2844, and applies it in Proposition 3.1, printed pp. 2843--2845.
This node supplies the
Mathlib-normalized affine specialization; it is not the still-open nonlinear coarea formula
for signed distance.

:::theorem "lipschitz-area-formula" (lean := "ProbabilityTheory.lintegral_image_eq_lintegral_normDet_fderivWithin_mul_of_lipschitzOnWith, ProbabilityTheory.lintegral_image_eq_lintegral_normDet_fderivWithin_mul_of_comp_eq_id") (tags := "geometric-measure-theory, area-formula, source-raic-2019, source-federer-1969, fidelity-injective-weighted-specialization")
*Weighted area formula for an injective Lipschitz chart.* Let $`U` and $`V` be
finite-dimensional real inner-product spaces, put $`m=\dim U`, and let
$`\varphi:S\subseteq U\to V` be Lipschitz and one-to-one on a measurable set $`S`.
For every nonnegative measurable weight $`g:V\to[0,\infty]`,
$$`
\int_{\varphi(S)}g(y)\,d\mathcal H^m(y)
=\int_S J_m(D\varphi|_S)(x)\,g(\varphi(x))\,dx.
`
Here $`D\varphi|_S` is the within derivative and $`J_m` is its absolute
$`m`-dimensional Jacobian.  In particular, if a Lipschitz inverse chart $`\varphi`
has a linear left inverse $`P` on $`S`, so that $`P(\varphi(x))=x`, the same identity
applies without separately assuming full rank: differentiating the composition makes
$`D\varphi|_S` injective almost everywhere.
:::

This is the injective weighted specialization of Federer, *Geometric Measure Theory*
(1969), Corollary 3.2.32.  Martin Raič, *A multivariate Berry--Esseen theorem with
explicit constants* (2019), records the area formula as Proposition 3.2, printed
pp. 2843--2844, and uses it both for coarea and for the boundary projection estimate.

:::theorem "scalar-coarea-formula" (lean := "ProbabilityTheory.scalarJacobian, ProbabilityTheory.scalarCoareaFiber, ProbabilityTheory.ScalarCoareaFormula, ProbabilityTheory.LipschitzWith.scalarCoareaFormula, ProbabilityTheory.ScalarCoareaFormula.setLIntegral_slab, ProbabilityTheory.ScalarCoareaFormula.setLIntegral_slab_of_ae_norm_fderiv_eq_one, ProbabilityTheory.LipschitzWith.scalarCoarea_setLIntegral_slab, ProbabilityTheory.LipschitzWith.setLIntegral_slab_of_ae_norm_fderiv_eq_one") (uses := "lipschitz-area-formula") (tags := "geometric-measure-theory, coarea, source-raic-2019, source-federer-1969, fidelity-measurable-ennreal-weighted-formula")
*Weighted scalar coarea formula.* Let $`d\in\mathbb N`, let
$`f:\mathbb R^d\to\mathbb R` be globally Lipschitz, and let
$`w:\mathbb R^d\to[0,\infty]` be Borel measurable.  Put
$$`
J_f(x)=\|Df(x)\|,
\qquad
Q_{f,w}(t)=\int_{f^{-1}(\{t\})}w(x)\,d\mathcal H^{d-1}(x),
`
where $`Df(x)` is taken to be zero at points where $`f` is not differentiable and
$`d-1` is the natural-number predecessor.  Then
$$`
\int_{\mathbb R^d}J_f(x)w(x)\,dx
=\int_{\mathbb R}Q_{f,w}(t)\,dt.
`
For every $`a,b\in\mathbb R`, the exact half-open slab form is
$$`
\int_{f^{-1}((a,b])}J_f(x)w(x)\,dx
=\int_{(a,b]}Q_{f,w}(t)\,dt.
`
If $`\|Df(x)\|=1` for Lebesgue-almost every $`x`, this reduces to
$$`
\int_{f^{-1}((a,b])}w(x)\,dx
=\int_{(a,b]}Q_{f,w}(t)\,dt.
`
:::

Herbert Federer, *Geometric Measure Theory* (1969), Corollary 3.2.32, supplies the
area/coarea theorem.  Martin Raič, *A multivariate Berry--Esseen theorem with explicit
constants* (2019), states the measurable-fiber theorem as Proposition 3.2, printed
pp. 2843--2844, and its scalar coarea specialization as Corollary 3.1, printed p. 2844.
Raič combines it with the almost-everywhere unit gradient of signed distance in
Proposition 3.3 and the proof of Proposition 3.1, printed pp. 2844--2845.  The formal
result uses nonnegative extended-valued weights, includes the exact $`(a,b]` convention,
and also proves the dimension-zero endpoint under the displayed predecessor convention.

:::theorem "gaussian-signed-distance-coarea-profiles" (lean := "ProbabilityTheory.standardGaussianBoundaryContent, ProbabilityTheory.outerGaussianBoundaryProfile, ProbabilityTheory.innerGaussianBoundaryProfile, ProbabilityTheory.outerGaussianBoundaryProfile_eq_levelLIntegral, ProbabilityTheory.innerGaussianBoundaryProfile_eq_levelLIntegral, ProbabilityTheory.stdGaussian_outer_shell_eq_lintegral_outerGaussianBoundaryProfile, ProbabilityTheory.stdGaussian_inner_shell_eq_lintegral_innerGaussianBoundaryProfile, ProbabilityTheory.ballGaussianPerimeterConstant, ProbabilityTheory.stdGaussian_shell_pair_le_ball_of_boundaryContent") (uses := "gaussian-signed-distance-level-frontiers, gaussian-shell-signed-distance-slabs, scalar-coarea-formula") (tags := "bentkus, gaussian-geometry, signed-distance, coarea, perimeter-reduction, source-raic-2019, fidelity-exact-half-open-profile-identities")
*Signed-distance coarea identities for Gaussian shell profiles.* Let
$`A\subsetneq\mathbb R^d` be nonempty and convex, put
$$`
\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2},
\qquad
P_\gamma(C)=\int_{\partial C}\phi_d(x)\,d\mathcal H^{d-1}(x),
`
where $`\mathcal H^{d-1}` is normalized so that top-dimensional Hausdorff measure
is Euclidean volume.  For $`t>0` and $`t<0`, respectively, define
$$`
p_A^+(t)=P_\gamma\!\left(\{x:d(x,\overline A)\le t\}\right),
\qquad
p_A^-(t)=P_\gamma\!\left(\{x:B(x,-t)\subseteq A\}\right),
`
with open balls in the inner parallel set.  If $`\delta_A` is signed distance, then
$$`
\begin{aligned}
p_A^+(t)&=\int_{\{x:\delta_A(x)=t\}}\phi_d(x)\,d\mathcal H^{d-1}(x)
&& (t>0),\\
p_A^-(t)&=\int_{\{x:\delta_A(x)=t\}}\phi_d(x)\,d\mathcal H^{d-1}(x)
&& (t<0).
\end{aligned}
`
Consequently, for every $`\varepsilon\ge0`, the exact half-open disintegrations are
$$`
\begin{aligned}
\gamma_d\!\left(\{x:d(x,\overline A)\le\varepsilon\}\setminus A\right)
  &=\int_{(0,\varepsilon]}p_A^+(t)\,dt,\\
\gamma_d\!\left(A\setminus\{x:B(x,\varepsilon)\subseteq A\}\right)
  &=\int_{(-\varepsilon,0]}p_A^-(t)\,dt.
\end{aligned}
`
In particular, if every convex $`C\subseteq\mathbb R^d` satisfies
$`P_\gamma(C)\le K_d` for $`K_d=4d^{1/4}`, then each of these two shell masses is
at most $`K_d\varepsilon`.
:::

Martin Raič, *A multivariate Berry--Esseen theorem with explicit constants* (2019),
Proposition 3.1 defines the boundary and shell suprema and derives both profile
disintegrations, printed pp. 2843--2845.  Corollary 3.1 gives the scalar coarea formula,
and Proposition 3.3 identifies $`\|\nabla\delta_A\|=1` almost everywhere and
$`\{\delta_A=t\}=\partial A^t`, both printed p. 2844.  The two displayed outer and
inner equalities occur in the proof of Proposition 3.1 on printed p. 2845.  The node
specializes Raič's continuous density to $`\phi_d`, retains the precise equality-boundary
conventions, and records the direct perimeter-to-shell implication.

:::theorem "intrinsic-sphere-hausdorff-normalization" (lean := "ProbabilityTheory.standardSphereHausdorffMeasure, ProbabilityTheory.map_subtype_standardSphereHausdorffMeasure, ProbabilityTheory.lintegral_standardSphereHausdorffMeasure_eq_ambient, ProbabilityTheory.standardSphereHausdorffMeasure_apply_univ_eq_ambient, ProbabilityTheory.standardSphereHausdorffMeasure_apply_univ, ProbabilityTheory.euclideanHausdorffMeasure_unitSphere, ProbabilityTheory.isFiniteMeasure_standardSphereHausdorffMeasure, ProbabilityTheory.standardSphereHausdorffMeasure_ne_zero, ProbabilityTheory.standardSphereHausdorffMeasure_apply_univ_ne_zero, ProbabilityTheory.measurePreserving_linearIsometryEquivUnitSphere_euclideanHausdorffMeasure") (uses := "scalar-coarea-formula") (tags := "bentkus, gaussian-geometry, sphere, hausdorff-measure, rotation, source-ball-1993, fidelity-exact-intrinsic-ambient-normalization")
*Intrinsic Hausdorff measure on the Euclidean unit sphere.* Let
$`S^{d-1}=\{x\in\mathbb R^d:\|x\|=1\}`, let
$`\iota:S^{d-1}\hookrightarrow\mathbb R^d` be inclusion, and let
$`\mathcal H^{d-1}_S` and $`\mathcal H^{d-1}_E` denote Euclidean Hausdorff
measure on the sphere as a metric space and on the ambient space, respectively.  Then
$$`
\iota_\#\mathcal H^{d-1}_S
=\mathcal H^{d-1}_E\!\restriction S^{d-1}.
`
Thus, for every nonnegative Borel function $`F:\mathbb R^d\to[0,\infty]`,
$$`
\int_{S^{d-1}}F(\theta)\,d\mathcal H^{d-1}_S(\theta)
=\int_{S^{d-1}}F(x)\,d\mathcal H^{d-1}_E(x).
`
If $`d\ge1` and $`\kappa_d=\lambda_d(B(0,1))`, then
$$`
\mathcal H^{d-1}_S(S^{d-1})=d\kappa_d.
`
This measure is finite, is nonzero when $`d\ge1`, and every linear isometry
$`U:\mathbb R^d\to\mathbb R^d` preserves it:
$$`
(U|_{S^{d-1}})_\#\mathcal H^{d-1}_S=\mathcal H^{d-1}_S.
`
:::

Keith Ball, *The reverse isoperimetric problem for Gaussian measure* (1993),
equation (1) and the centered-ball evaluation immediately following it, printed
pp. 411--412, use codimension-one Hausdorff measure and the factor
$`r^{d-1}d\kappa_d`, which fixes the displayed surface-area normalization.
Lemma 3 introduces rotation-invariant probability on the sphere, printed p. 414,
and Theorem 4, equations (2)--(3), printed pp. 415--416, passes between spherical
averaging and Hausdorff surface projection.  The intrinsic-to-ambient pushforward
identity makes that normalization explicit; the rotation statement is valid more
generally for every Hausdorff dimension on any real inner-product space.

:::theorem "ball-projection-jacobian-charts" (lean := "ProbabilityTheory.exists_unit_supportingNormal, ProbabilityTheory.hyperplaneOrthogonalProjection, ProbabilityTheory.normDet_hyperplaneOrthogonalProjection, ProbabilityTheory.supportingNormalPairs, ProbabilityTheory.transverseSupportingNormalPoints_eq_iUnion_patches, ProbabilityTheory.injOn_orthogonalProjectionOnto_positiveSupportingNormalPatch, ProbabilityTheory.injOn_orthogonalProjectionOnto_negativeSupportingNormalPatch, ProbabilityTheory.orthogonalProjectionPatchInverse, ProbabilityTheory.exists_unit_normal_fderivWithin_patchInverse_normDet_mul_eq_one, ProbabilityTheory.lipschitzOnWith_orthogonalProjectionPatchInverse_positivePatch, ProbabilityTheory.lipschitzOnWith_orthogonalProjectionPatchInverse_negativePatch") (uses := "lipschitz-area-formula") (tags := "bentkus, gaussian-geometry, perimeter, projection, source-ball-1993, fidelity-explicit-graph-charts")
*Projection Jacobians and supporting-normal charts.* Let $`d\ge2` and
$`u,\theta\in S^{d-1}`.
The orthogonal projection $`P_{u,\theta}:u^\perp\to\theta^\perp` satisfies
$$`
J_{d-1}P_{u,\theta}=|\langle\theta,u\rangle|.
`
If $`C\subseteq\mathbb R^d` is a compact convex body, every $`x\in\partial C`
admits an outward supporting unit normal $`u`, meaning
$$` \langle y-x,u\rangle\le0\quad\text{for every }y\in C. `
For fixed $`\theta`, the boundary points with
$`\langle\theta,u\rangle\ne0` are the countable union of the two families
$$`
\langle\theta,u\rangle\ge a,
\qquad
\langle\theta,u\rangle\le-a,
\qquad a>0.
`
On each such patch, projection onto $`\theta^\perp` is one-to-one and its inverse
$`\psi` is Lipschitz.  At every differentiability point of $`\psi` with unit normal
$`u` to its image tangent hyperplane,
$$`
|\langle\theta,u\rangle|\,J_{d-1}D\psi=1.
`
:::

This is the projection identity and graph decomposition in Keith Ball,
*The reverse isoperimetric problem for Gaussian measure* (1993), equations (2)--(3)
and the paragraph immediately following them, printed p. 416, in the proof of
Theorem 4.  The strict positive and negative patches make the inverse charts and their
Jacobian cancellation explicit.  Composing these charts with the preceding weighted area
formula gives the surface-projection identity used in Ball's argument.

:::theorem "ball-cauchy-projection-formula" (lean := "ProbabilityTheory.lintegral_unitSphere_orthogonalProjection_mul_absInner_ambient, ProbabilityTheory.lintegral_unitSphere_orthogonalProjection_mul_absInner") (uses := "intrinsic-sphere-hausdorff-normalization, ball-projection-jacobian-charts") (tags := "bentkus, gaussian-geometry, sphere, projection, cauchy-formula, source-ball-1993, fidelity-exact-weighted-two-hemisphere-formula")
*Weighted Cauchy projection formula for the Euclidean sphere.* Let $`d\ge2`, let
$`v\in S^{d-1}`, write $`P_v:\mathbb R^d\to v^\perp` for orthogonal projection,
and let $`g:v^\perp\to[0,\infty]` be Borel measurable.  With intrinsic
codimension-one Hausdorff measure on $`S^{d-1}` and Euclidean volume on $`v^\perp`,
$$`
\int_{S^{d-1}}g(P_v\theta)|\langle\theta,v\rangle|
  \,d\mathcal H^{d-1}(\theta)
=2\int_{B_{v^\perp}(0,1)}g(z)\,dz.
`
Equivalently, the same left-hand integral may be written over the unit sphere as an
ambient subset with ambient $`\mathcal H^{d-1}`.  The factor $`2` is exact: the two
strict hemispheres each project one-to-one onto the open unit ball, while the equator
has zero integrand.
:::

Keith Ball, *The reverse isoperimetric problem for Gaussian measure* (1993),
Theorem 4 constructs the projection measure in equation (2), then observes that almost
every line in a fixed direction meets a convex boundary at most twice, printed
pp. 415--416.  The infinitesimal surface-projection factor
$`|\langle\theta,v\rangle|` is equation (3), printed p. 416.  Applied to the Euclidean
ball, the two projection charts give the exact weighted Cauchy formula above, including
its intrinsic-Hausdorff and ambient-restriction forms.

:::theorem "ball-spherical-projection-average" (lean := "ProbabilityTheory.standardSphereProbability, ProbabilityTheory.map_linearIsometryEquivUnitSphere_standardSphereProbability, ProbabilityTheory.measurePreserving_linearIsometryEquivUnitSphere_standardSphereProbability, ProbabilityTheory.integral_inner_sq_standardSphereProbability, ProbabilityTheory.integral_abs_inner_standardSphereProbability_le") (tags := "bentkus, gaussian-geometry, perimeter, sphere-average, source-ball-1993, fidelity-exact-normalized-moments")
*Spherical projection average.* Let $`\sigma_{d-1}` be rotation-invariant probability
measure on $`S^{d-1}`.  For $`d\ge1` and $`u\in\mathbb R^d`,
$$`
\int_{S^{d-1}}\langle\theta,u\rangle^2\,d\sigma_{d-1}(\theta)
=\frac{\|u\|^2}{d},
`
and hence
$$`
\int_{S^{d-1}}|\langle\theta,u\rangle|\,d\sigma_{d-1}(\theta)
\le\frac{\|u\|}{\sqrt d}.
`
The measure is invariant under every linear isometry of $`\mathbb R^d`.
:::

Keith Ball, *The reverse isoperimetric problem for Gaussian measure* (1993), averages
the projection inequality over $`S^{d-1}` immediately before equation (4), printed
p. 416, in the proof of Theorem 4.  The displayed second moment is the rotation-invariant
covariance calculation underlying Ball's $`d^{-1/2}` factor; Cauchy--Schwarz gives the
absolute first-moment inequality.

:::theorem "ball-spherical-rearrangement" (lean := "ProbabilityTheory.ballSphericalRearrangement_absInner") (tags := "bentkus, gaussian-geometry, perimeter, rearrangement, source-ball-1993, fidelity-applied-continuous-g-equals-identity")
*Ball's spherical rearrangement inequality in the applied form.* Let $`d\ge1`, let
$`\sigma_{d-1}` be rotation-invariant probability measure on $`S^{d-1}`, and let
$`F:\mathbb R\to\mathbb R` be continuous and nondecreasing on $`[0,\infty)`.
If $`u,v\in S^{d-1}` are orthogonal, $`0\le\alpha\le\pi/2`, and
$$`
w_\alpha=\cos(\alpha)u+\sin(\alpha)v,
`
then
$$`
\int_{S^{d-1}}F(|\langle\theta,u\rangle|)
  |\langle\theta,v\rangle|\,d\sigma_{d-1}(\theta)
\le
\int_{S^{d-1}}F(|\langle\theta,u\rangle|)
  |\langle\theta,w_\alpha\rangle|\,d\sigma_{d-1}(\theta).
`
:::

Keith Ball, *The reverse isoperimetric problem for Gaussian measure* (1993), Lemma 3
and its circle-fiber proof, printed pp. 414--415, treats two arbitrary nondecreasing
functions on $`[0,1]`.  The result recorded here is the exact continuous
$`G(t)=t` specialization used in Theorem 4: on printed p. 416, immediately after
equation (3), Ball takes $`F(t)=f(r\sqrt{1-t^2})`, which is nondecreasing because the
radial density $`f` is nonincreasing, and concludes that the spherical integral is
minimized when the position and normal directions are perpendicular.

:::lemma_ "ball-radial-gamma-peak" (lean := "ProbabilityTheory.exp_neg_half_mul_rpow_le_peak, ProbabilityTheory.ball_radial_gamma_peak_le") (tags := "bentkus, gaussian-geometry, perimeter, radial-estimate, source-ball-1993, fidelity-exact-one-over-pi")
*Radial Gaussian peak and Gamma bound.* For every integer $`n\ge3` and every $`t\ge0`,
$$`
e^{-t^2/2}t^{n-2}
\le e^{-(n-2)/2}(n-2)^{(n-2)/2}.
`
Moreover,
$$`
\frac{e^{-(n-2)/2}(n-2)^{(n-2)/2}}
 {2^{n/2-1}\Gamma((n-1)/2)\sqrt\pi}
\le\frac1\pi.
`
:::

These are the one-dimensional maximum and the normalized Gamma estimate in the last
paragraph of Keith Ball, *The reverse isoperimetric problem for Gaussian measure* (1993),
printed p. 419, completing the analytic estimate in the proof of Theorem 4.  The second
inequality retains Ball's exact $`1/\pi` constant in every dimension $`n\ge3`.

:::theorem "ball-radial-majorant" (lean := "ProbabilityTheory.ballGaussianNormalization, ProbabilityTheory.ballRadialAuxIntegrand, ProbabilityTheory.ballRadialAux, ProbabilityTheory.ballRadialMajorant, ProbabilityTheory.continuous_ballRadialMajorant, ProbabilityTheory.ballRadialMajorant_nonneg, ProbabilityTheory.ballRadialMajorant_eq_zero_of_sqrt_two_mul_le, ProbabilityTheory.antitoneOn_ballRadialMajorant, ProbabilityTheory.ballRadialProjectionTransform, ProbabilityTheory.ballRadialAux_projection_eq_standardGaussian, ProbabilityTheory.standardGaussianDensityReal_le_ballRadialMajorant_projection, ProbabilityTheory.ballRadialMassCoefficient, ProbabilityTheory.ballRadialPolarFactor, ProbabilityTheory.ballRadialPolarFactor_mul_normalization, ProbabilityTheory.integral_ballRadialMajorant_rpow_le, ProbabilityTheory.integral_ballRadialMajorant_norm_le, ProbabilityTheory.lintegral_ballRadialMajorant_norm_le, ProbabilityTheory.lintegral_ballRadialMajorant_norm_le_of_finrank") (uses := "ball-radial-gamma-peak") (tags := "bentkus, gaussian-geometry, perimeter, radial-majorant, source-ball-1993, fidelity-exact-construction-projection-and-mass")
*Ball's radial projection majorant.* For $`n\ge2`, put
$$`
a_n=(\sqrt{2\pi})^{-n},\qquad
h_n(t)=a_n\int_0^{\pi/2}
  (n-1-t^2\sin^2\theta)\sin^{n-2}\theta\,
  e^{-t^2\sin^2\theta/2}\,d\theta,
\qquad f_n(t)=\max\{h_n(t),0\}.
`
Then $`f_n` is continuous on $`\mathbb R`, nonnegative everywhere, nonincreasing on
$`[0,\infty)`, and
$$`
t\ge\sqrt{2n}\quad\Longrightarrow\quad f_n(t)=0.
`
For a radial function $`q:\mathbb R\to\mathbb R`, define its spherical projection by
$$`
(T_nq)(r)=\frac2\pi\int_0^{\pi/2}q(r\sin\theta)
  \sin^{n-1}\theta\,d\theta.
`
For every $`r\in\mathbb R`, the signed auxiliary function has the exact projection
identity and its positive part gives the Gaussian majorization
$$`
(T_nh_n)(r)=a_ne^{-r^2/2}
\le (T_nf_n)(r).
`
Finally, set
$$`
c_n=\left(2^{n/2-1}\Gamma\!\left(\frac{n-1}{2}\right)\sqrt\pi\right)^{-1},
\qquad
p_n=(n-1)\,\operatorname{vol}_{n-1}(B_{n-1}(0,1)).
`
The polar normalization is exact, $`p_na_n=c_n`, and the one-dimensional and
Euclidean mass bounds are
$$`
\frac{c_n}{a_n}\int_{(0,\infty)}f_n(t)t^{n-2}\,dt
\le 2n^{1/4},
\qquad
\int_{\mathbb R^{n-1}}f_n(\|x\|)\,dx
\le 2n^{1/4}.
`
The same nonnegative-integral bound holds on every finite-dimensional real inner-product
space of dimension $`n-1`.
:::

Keith Ball, *The reverse isoperimetric problem for Gaussian measure* (1993), reduces
Theorem 4 to the projection majorization in equation (4), defines the signed inverse
transform by equations (5)--(6), and takes its positive part, printed p. 417.  The
power-series calculation following equation (7), also on printed p. 417, proves the
required monotonicity; the zero-location estimate and polar mass identity are on printed
p. 418.  The two-part integral estimate and normalized Gamma peak close
$`\mu(\mathbb R^{n-1})\le2n^{1/4}` on printed pp. 418--419.  The formal result separates
the construction, the exact signed projection, the positive-part majorization, the
compact positive-radius support, and both normalized forms of the mass estimate.

:::theorem "gaussian-convex-shell" (uses := "gaussian-affine-codimension-one-slicing, gaussian-signed-distance-coarea-profiles, ball-cauchy-projection-formula, ball-spherical-rearrangement, ball-radial-majorant") (tags := "bentkus, gaussian-geometry, perimeter, source-ball-1993, source-raic-2019, source-open, fidelity-frozen")
*Gaussian shell bound for convex sets.* There is an absolute constant $`c>0` such
that, for every $`d\ge1`, every measurable convex $`A\subseteq\mathbb R^d`, and
every $`\varepsilon>0`, if $`G\sim N(0,I_d)`, then
$$`
\mathbb P[G\in A^\varepsilon\setminus A]
\le c\,d^{1/4}\varepsilon,
`
and the same bound holds for the inner shell
$`A\setminus\{x\in A:B(x,\varepsilon)\subseteq A\}`.
:::

The classical source is Keith Ball, *The reverse isoperimetric problem for Gaussian
measure* (1993), main Gaussian-perimeter bound, *Discrete & Computational Geometry*
10, pp. 411--420; Bentkus (2004) quotes the consequence as equation (1.4), printed
p. 401.  Martin Raič, *A multivariate Berry--Esseen theorem with explicit constants*
(2019), Proposition 1.1 and Theorem 1.2, printed p. 2826, gives a modern shell/perimeter
bridge and the sharper explicit bound.  The signed-distance coarea identities and their
perimeter-to-shell consequence, together with normalized affine slicing, are recorded in the
preceding nodes.  This node remains source-open because Ball's $`d\ge2` convex-body boundary
estimate has not yet been assembled from the weighted Cauchy projection formula, spherical
rearrangement, and radial majorant in one production declaration.

:::lemma_ "bentkus-smoothing-inequality" (lean := "ProbabilityTheory.convexInnerParallel, ProbabilityTheory.mem_convexInnerParallel_iff_ball_subset, ProbabilityTheory.convexInnerParallel_subset, ProbabilityTheory.convexInnerParallel_isConvexSet, ProbabilityTheory.closure_isConvexSet, ProbabilityTheory.convexSetCutoff, ProbabilityTheory.convexSetCutoff_nonneg, ProbabilityTheory.convexSetCutoff_le_one, ProbabilityTheory.convexSetCutoff_eq_one_of_mem, ProbabilityTheory.convexSetCutoff_eq_zero_of_notMem_cthickening, ProbabilityTheory.convexSetCutoff_inner_eq_zero_of_notMem, ProbabilityTheory.contDiff_convexSetCutoff, ProbabilityTheory.norm_fderiv_convexSetCutoff_le, ProbabilityTheory.norm_fderiv_convexSetCutoff_sub_le, ProbabilityTheory.bentkus_convexSet_smoothingInequality") (uses := "bentkus-smooth-cutoff") (tags := "bentkus, smoothing, source-bentkus-2004, fidelity-explicit-boundary-convention")
*Setwise Bentkus smoothing inequality.* Let $`\mu,\nu` be probability measures on
$`\mathbb R^d`, let $`A` be measurable and convex, and let $`\varepsilon>0`.  Define
the closed outer parallel set and the inner core by
$$`
A^+_\varepsilon=\{x:d(x,\overline A)\le\varepsilon\},\qquad
A^-_\varepsilon=\{x:B(x,\varepsilon)\subseteq A\},
`
where $`B(x,\varepsilon)` is the open ball.  The inner core is closed, convex, and
contained in $`A`.  There are total cutoffs $`\varphi_A` and $`\varphi_{A^-_\varepsilon}`
with values in $`[0,1]`, equal to $`1` on their indexing set and equal to $`0`
respectively off $`A^+_\varepsilon` and off $`A`.  They are continuously differentiable and
obey
$$`
\|D\varphi(x)\|\le\frac2\varepsilon,\qquad
\|D\varphi(x)-D\varphi(y)\|
\le\frac8{\varepsilon^2}\|x-y\|.
`
Moreover,
$$`
\begin{aligned}
|\mu(A)-\nu(A)|\le{}&
\max\!\left\{
\left|\int\varphi_A\,d\mu-\int\varphi_A\,d\nu\right|,
\left|\int\varphi_{A^-_\varepsilon}\,d\mu-
       \int\varphi_{A^-_\varepsilon}\,d\nu\right|
\right\}\\
&+\max\!\left\{
\nu(A^+_\varepsilon\setminus A),
\nu(A\setminus A^-_\varepsilon)
\right\}.
\end{aligned}
`
:::

This is the setwise form of Vidmantas Bentkus, *A Lyapunov type bound in
$`\mathbb R^d`* (2004), Lemma 2.1, combined with the cutoff of Lemma 2.2,
equation (2.2), printed p. 402.  The paper takes the outer neighborhood
$`\{d_A\le\varepsilon\}` and defines its inner neighborhood using a closed ball.  The
formal inner core instead uses an open ball, equivalently the complement of the open
$`\varepsilon`-thickening of $`A^c`; this keeps the equality boundary in the displayed
inner shell.  Empty and nonclosed convex sets are handled by the total cutoff and
$`\overline A` explicitly.

:::lemma_ "density-derivative-integral-bound" (lean := "ProbabilityTheory.bentkus_lipschitz_schwartz_integral_fderiv_bound") (tags := "bentkus, analysis, integration-by-parts, source-bentkus-2004, fidelity-schwartz-exact")
*Derivative integral against a Lipschitz function.* Let $`E` be a finite-dimensional
real normed vector space with a Haar measure $`\lambda`, let $`p:E\to\mathbb R` be a
Schwartz function, and suppose that $`f:E\to\mathbb R` is $`a`-Lipschitz.  Then, for
every $`h\in E`,
$$`
\left|\int_E f(y)\,Dp(y)[h]\,d\lambda(y)\right|
\le a\|h\|\int_{\operatorname{tsupp}f}|p(y)|\,d\lambda(y).
`
:::

This is Vidmantas Bentkus, *A Lyapunov type bound in $`\mathbb R^d`* (2004),
Lemma 2.3, equations (2.3)--(2.4), printed pp. 402--403.  The paper's hypothesis that
$`p` and all of its derivatives decay faster than every inverse power is represented
exactly by the Schwartz class; the formal theorem follows the paper's difference-quotient
argument and does not assume that the Lipschitz factor is differentiable.

:::theorem "gaussian-density-third-derivative" (lean := "ProbabilityTheory.standardGaussianDensityNormalization, ProbabilityTheory.standardGaussianDensity, ProbabilityTheory.standardGaussianDensityD1, ProbabilityTheory.standardGaussianDensityD2, ProbabilityTheory.standardGaussianDensityD3, ProbabilityTheory.hasFDerivAt_standardGaussianDensity, ProbabilityTheory.fderiv_standardGaussianDensity_apply, ProbabilityTheory.fderiv_standardGaussianDensityD1_apply, ProbabilityTheory.fderiv_standardGaussianDensityD2_apply, ProbabilityTheory.gaussianThirdHermiteContraction, ProbabilityTheory.standardGaussianDensityD3_sameDirection, ProbabilityTheory.fderiv_standardGaussianDensityD2_sameDirection, ProbabilityTheory.integrable_gaussianThirdHermiteContraction_stdGaussian, ProbabilityTheory.standardGaussianFourthMoment, ProbabilityTheory.standardGaussianFourthMoment_nonneg, ProbabilityTheory.integral_inner_pow_four_stdGaussian, ProbabilityTheory.integral_inner_sq_stdGaussian, ProbabilityTheory.integral_abs_inner_stdGaussian_le_norm, ProbabilityTheory.integral_abs_gaussianThirdHermiteContraction_le") (tags := "bentkus, gaussian-analysis, density-derivatives, source-bentkus-2004, fidelity-explicit-absolute-constant")
*Gaussian density derivatives and the cubic-contraction bound.* Let $`E` be a
finite-dimensional real inner-product space, let $`m=\dim E`, and set
$$`
\rho(x)=(2\pi)^{-m/2}e^{-\|x\|^2/2}.
`
Its first three directional Fréchet derivatives are
$$`
\begin{aligned}
D\rho(x)[h]
  &=-\langle x,h\rangle\rho(x),\\
D^2\rho(x)[h,k]
  &=(\langle x,h\rangle\langle x,k\rangle-\langle h,k\rangle)\rho(x),\\
D^3\rho(x)[h,k,l]
  &=\bigl(-\langle x,h\rangle\langle x,k\rangle\langle x,l\rangle
     +\langle h,k\rangle\langle x,l\rangle
     +\langle h,l\rangle\langle x,k\rangle
     +\langle k,l\rangle\langle x,h\rangle\bigr)\rho(x).
\end{aligned}
`
In particular,
$$`
D^3\rho(x)[w,w,g]=\rho(x)H_{w,g}(x),
`
where
$$`
H_{w,g}(x)=2\langle w,g\rangle\langle x,w\rangle
+\|w\|^2\langle x,g\rangle
-\langle x,g\rangle\langle x,w\rangle^2.
`
The contraction $`H_{w,g}` is integrable under the standard Gaussian law $`\gamma_E`.
Writing $`m_4=\int_{\mathbb R}t^4\,dN(0,1)(t)`, one has the dimension-free estimate
$$`
\int_E|H_{w,g}(x)|\,d\gamma_E(x)
\le(3+\sqrt{m_4})\,\|w\|^2\|g\|.
`
:::

This supplies the exact Gaussian analytic input to the integration-by-parts estimate in
Vidmantas Bentkus, *A Lyapunov type bound in $`\mathbb R^d`* (2004), Lemma 2.3,
equations (2.3)--(2.4), printed pp. 402--403.  The
twice-equal third derivative is equation (3.21), printed p. 405, and the absolute
Gaussian integral estimate is the dimension-free content used in (3.22)--(3.23),
printed pp. 405--406.  The general Lipschitz integration-by-parts lemma itself remains
the separate node immediately above.

:::theorem "gaussian-density-ibp" (lean := "ProbabilityTheory.integrable_standardGaussianDensityD1_volume, ProbabilityTheory.integral_fderiv_mul_standardGaussianDensity_eq_neg, ProbabilityTheory.bentkus_lipschitz_standardGaussianDensityD1_integral_D2_bound") (uses := "density-derivative-integral-bound, gaussian-density-third-derivative") (tags := "bentkus, gaussian-analysis, integration-by-parts, source-bentkus-2004, fidelity-exact-gaussian-specialization")
*Gaussian integration by parts localized to the support of a Lipschitz factor.* Put
$$` \rho(y)=(2\pi)^{-d/2}e^{-\|y\|^2/2}. `
The directional derivative $`D\rho(\cdot)[w]` is Lebesgue integrable.  If
$`f:\mathbb R^d\to\mathbb R` is globally Lipschitz and differentiable, then
$$`
\int_{\mathbb R^d}Df(y)[h]\rho(y)\,dy
=-\int_{\mathbb R^d}f(y)D\rho(y)[h]\,dy.
`
Moreover, if $`f` is $`L`-Lipschitz, then, for all $`w,h\in\mathbb R^d`,
$$`
\left|\int_{\mathbb R^d}f(y)D^2\rho(y)[w,h],dy\right|
\le L\|h\|
\int_{\operatorname{tsupp}f}|D\rho(y)[w]|\,dy.
`
:::

This is Vidmantas Bentkus, *A Lyapunov type bound in $`\mathbb R^d`* (2004),
Lemma 2.3, equations (2.3)--(2.4), printed pp. 402--403.  The first identity is the
Gaussian-density integration-by-parts step used in equation (3.32), printed p. 407;
the final estimate specializes Lemma 2.3 to $`p=D\rho(\cdot)[w]`.

:::theorem "cutoff-derivative-shell-ibp" (lean := "ProbabilityTheory.convexSetCutoffDirectionalPullback, ProbabilityTheory.lipschitzWith_convexSetCutoffDirectionalPullback, ProbabilityTheory.tsupport_convexSetCutoffDirectionalPullback_subset, ProbabilityTheory.convexSetCutoffDirectionalPullback_D2_bound, ProbabilityTheory.convexSetCutoffDirectionalPullback_D2_shell_bound") (uses := "bentkus-smoothing-inequality, gaussian-density-ibp") (tags := "bentkus, gaussian-replacement, cutoff, integration-by-parts, source-bentkus-2004, fidelity-exact-closed-shell-support")
*Pulled-back cutoff derivative and its shell-localized bound.* Let $`A` be closed and
convex, $`\varepsilon>0`, and let $`\varphi_A` be the Bentkus cutoff.  For
$`a,x\in\mathbb R^d` and a linear map $`L`, set
$$`
q(u)=D\varphi_A(a+Lu)[x].
`
Then $`q` is $`8\|L\|\|x\|/\varepsilon^2`-Lipschitz and
$$`
\operatorname{tsupp}q\subseteq
\{u:a+Lu\in A^+_\varepsilon\setminus\operatorname{int}A\}.
`
Consequently, for all $`w,h\in\mathbb R^d`,
$$`
\begin{aligned}
\left|\int q(u)D^2\rho(u)[w,h],du\right|
\le{}&\frac{8\|L\|\|x\|\|h\|}{\varepsilon^2}\\
&\cdot\int_{\{u:a+Lu\in A^+_\varepsilon\setminus\operatorname{int}A\}}
|D\rho(u)[w]|\,du.
\end{aligned}
`
:::

This is the deterministic integration-by-parts step in Vidmantas Bentkus,
*A Lyapunov type bound in $`\mathbb R^d`* (2004), equation (3.32), printed p. 407,
with the shell placement used in equations (3.30)--(3.34), printed pp. 407--408.
The topological support retains the boundary of $`A`, hence the exact shell removes only
$`\operatorname{int}A`.

:::lemma_ "bentkus-taylor-remainders" (lean := "ProbabilityTheory.abs_firstOrderTaylorRemainder_le, ProbabilityTheory.norm_twoShiftTaylorRemainder_le") (tags := "bentkus, gaussian-replacement, taylor, source-bentkus-2004, fidelity-sharp-quadratic-remainder")
*First-order and two-shift Taylor remainders.* Let $`E` be a real normed vector space,
let $`f:E\to\mathbb R` be continuously differentiable, and suppose that $`Df` is
$`L`-Lipschitz.  Then
$$`
|f(x+h)-f(x)-Df(x)[h]|\le\frac L2\|h\|^2.
`
For two shifts $`v,w\in E`, freezing the derivative at $`x` gives
$$`
\left|(f(x+v+w)-f(x+v))-Df(x)[w]\right|
\le L\|w\|\left(\|v\|+\frac{\|w\|}{2}\right).
`
:::

This is the integral Taylor estimate used in Vidmantas Bentkus,
*A Lyapunov type bound in $`\mathbb R^d`* (2004), equation (3.28), printed p. 407,
before the centering and covariance cancellations are applied.  The first inequality keeps
the exact $`1/2` obtained by integrating the linear derivative increment.

:::theorem "gaussian-density-second-order-remainder" (lean := "ProbabilityTheory.integral_abs_standardGaussianDensityD3_volume_le, ProbabilityTheory.integrable_standardGaussianDensityD3_volume, ProbabilityTheory.bentkus_abs_integral_bounded_mul_standardGaussianDensityD3_sub_le, ProbabilityTheory.bentkus_standardGaussianDensityD1_secondOrderRemainder_integral_bound") (uses := "gaussian-density-third-derivative") (tags := "bentkus, gaussian-analysis, gaussian-replacement, taylor, source-bentkus-2004, fidelity-explicit-dimension-free-remainder")
*Integrated second-order remainder for the first Gaussian-density derivative.* Let
$`\rho` be the standard Gaussian density on $`\mathbb R^d`, and let
$`\varphi:\mathbb R^d\to\mathbb R` be measurable with $`|\varphi|\le1`.  For all
$`a,w,g\in\mathbb R^d`,
$$`
\left|\int\varphi(x)D^3\rho(x-a)[w,w,g],dx\right|
\le(3+\sqrt{m_4})\|w\|^2\|g\|,
`
where $`m_4=\int t^4\,dN(0,1)(t)`.  Consequently, for every $`h,g\in\mathbb R^d`,
$$`
\begin{aligned}
\bigg|\int\varphi(x)\big(&D\rho(x-h)[g]-D\rho(x)[g]\\
&+D^2\rho(x)[h,g]\big)\,dx\bigg|
\le\frac{3+\sqrt{m_4}}2\|h\|^2\|g\|.
\end{aligned}
`
:::

This is the cancellation-ready Taylor estimate in Vidmantas Bentkus,
*A Lyapunov type bound in $`\mathbb R^d`* (2004), equations (3.19)--(3.23),
printed pp. 405--406.  The factor $`1/2` is the integral of the second-order Taylor
kernel, while the dimension-free constant is the absolute cubic Hermite contraction.

:::lemma_ "bentkus-angle-integrals" (lean := "ProbabilityTheory.intervalIntegral_cos_div_sin_sq, ProbabilityTheory.intervalIntegral_cos_div_sin_sq_le_inv, ProbabilityTheory.intervalIntegral_cos_div_sin_sq_arcsin, ProbabilityTheory.intervalIntegral_cos_zero_arcsin") (tags := "bentkus, gaussian-replacement, induction, angle-splitting, source-bentkus-2004, fidelity-exact-antiderivatives-and-arcsine-substitution")
*Exact trigonometric integrals for Bentkus's angle split.* If
$`0<\gamma\le\pi/2`, then
$$`
\int_\gamma^{\pi/2}\frac{\cos\alpha}{\sin^2\alpha}\,d\alpha
=\frac1{\sin\gamma}-1
\le\frac1{\sin\gamma}.
`
Consequently, if $`0<\varepsilon\le1` and
$`\gamma=\arcsin\varepsilon`, then
$$`
\int_{\arcsin\varepsilon}^{\pi/2}
  \frac{\cos\alpha}{\sin^2\alpha}\,d\alpha
=\varepsilon^{-1}-1.
`
For $`0\le\varepsilon\le1`, the complementary small-angle mass is exactly
$$`
\int_0^{\arcsin\varepsilon}\cos\alpha\,d\alpha=\varepsilon.
`
:::

Vidmantas Bentkus, *A Lyapunov type bound in $`\mathbb R^d`* (2004), splits the
rotation at $`\gamma` in equations (3.11)--(3.15), printed pp. 404--405.  In the proof
of (3.13), the integral $`\int_0^\gamma\cos\alpha\,d\alpha` occurs immediately after
equation (3.33), printed p. 407.  In the proof of (3.14), equations (3.39)--(3.40) are
followed by the bound on
$`\int_\gamma^{\pi/2}\cos\alpha/\sin^2\alpha\,d\alpha`, printed p. 409.
Bentkus chooses $`\sin\gamma=\varepsilon` after equation (3.8), printed p. 404; the
node retains the exact antiderivatives before taking the inequalities used in the paper.

:::lemma_ "bentkus-parameter-closure" (lean := "ProbabilityTheory.bentkus_parameter_closure") (tags := "bentkus, gaussian-replacement, induction, scalar-closure, source-bentkus-2004, fidelity-exact-smoothing-scale")
*Closure of the smoothing parameter.* Let $`C\ge1`, $`d\ge1`, $`\beta>0`, and
$`\Delta\le1`.  Suppose
$$`
K(2\sqrt C+1)\le C
`
and, whenever $`\beta\sqrt C<1`,
$$`
\Delta\le Kd^{1/4}
\left(\beta\sqrt C+\beta+
\frac{C\beta^2}{\beta\sqrt C}\right).
`
Then
$$` \Delta\le Cd^{1/4}\beta. `
:::

This is the scalar calculation in Vidmantas Bentkus,
*A Lyapunov type bound in $`\mathbb R^d`* (2004), equations (3.9)--(3.10), printed
p. 404.  It chooses $`\varepsilon=\beta\sqrt C`; the complementary branch
$`\varepsilon\ge1` closes directly from $`\Delta\le1`.

:::lemma_ "bentkus-trivial-induction-branches" (lean := "ProbabilityTheory.sum_integral_norm_sq_eq_dimension_of_identityCovariance, ProbabilityTheory.dimension_cube_le_card_mul_thirdMomentSum_sq, ProbabilityTheory.small_cardinality_thirdMomentSum_lower, ProbabilityTheory.probability_error_le_M_mul_thirdMomentSum_of_small_cardinality, ProbabilityTheory.large_secondMoment_thirdMoment_lower") (uses := "covariance-additivity-and-leave-one-out") (tags := "bentkus, gaussian-replacement, induction, moments, source-bentkus-2004, fidelity-explicit-trivial-branches")
*The small-cardinality and large-summand induction branches.* Let
$`X_1,\ldots,X_n` be independent centered $`L^3` random vectors in $`\mathbb R^d`,
assume that $`\operatorname{Cov}(\sum_iX_i)=I_d`, and put
$$`
\beta=\sum_i\mathbb E\|X_i\|^3.
`
Then
$$`
\sum_i\mathbb E\|X_i\|^2=d,
\qquad
d^3\le n\beta^2.
`
If $`d>0`, $`M\ge0`, and $`n\le d^3M^2`, then $`1\le M\beta`; hence, for every
probability measure $`\nu` on $`\mathbb R^d` and every set $`A`,
$$`
\left|\mathbb P\!\left[\sum_iX_i\in A\right]-\nu(A)\right|\le M\beta.
`
Separately, if one summand satisfies
$`\mathbb E\|X_k\|^2\ge\tfrac14`, then
$$`
1\le8\,\mathbb E\|X_k\|^3.
`
:::

These are the two trivial branches at the start of Section 3 in Vidmantas Bentkus,
*A Lyapunov type bound in $`\mathbb R^d`* (2004), printed p. 403.  The first is the
Hölder calculation and $`\Delta\le1` argument immediately after equation (3.1) for
$`n\le d^3M^2`; the second is the large-individual-covariance exclusion immediately
before equation (3.2).  The formal node isolates exactly the moment consequences used
before the nontrivial Taylor induction begins.

:::lemma_ "bentkus-leave-one-out-whitening" (lean := "ProbabilityTheory.bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter, ProbabilityTheory.norm_bentkusWhiteningCLM_leaveOneOut_apply_le_two, ProbabilityTheory.norm_bentkusWhiteningCLM_leaveOneOut_apply_pow_three_le, ProbabilityTheory.integral_norm_bentkusWhiteningCLM_leaveOneOut_pow_three_le") (uses := "covariance-additivity-and-leave-one-out, bentkus-whitening-covariance-identity") (tags := "bentkus, gaussian-replacement, leave-one-out, whitening, source-bentkus-2004, fidelity-explicit-small-moment-branch")
*Leave-one-out whitening in the small-second-moment branch.* Under identity total
covariance, fix $`k` and suppose that
$$`
\mathbb E\|X_k\|^2<\frac14.
`
If $`U_k=\sum_{i\ne k}X_i` and $`S_k=\operatorname{Cov}(U_k)`, then $`S_k` is
positive definite.  Its inverse square root $`T_k=S_k^{-1/2}` satisfies
$$`
\|T_kx\|\le2\|x\|,
\qquad
\|T_kx\|^3\le8\|x\|^3.
`
Consequently, for every $`L^3` random vector $`Z` on any measure space,
$$`
\int\|T_kZ\|^3\le8\int\|Z\|^3.
`
:::

This is the small-individual-covariance branch introduced after equation (3.2) in
Vidmantas Bentkus, *A Lyapunov type bound in $`\mathbb R^d`* (2004), printed
pp. 403--404.  The paper writes $`P_k^2=\operatorname{Cov}(U_k)` and
$`Q_k=P_k^{-1}` and, after excluding the large-covariance trivial case, assumes
$`\|Q_k\|\le2`; the formal statement derives that bound and records the resulting
third-moment factor $`2^3=8` explicitly.

:::theorem "bentkus-standardized-induction" (uses := "gaussian-convex-shell, bentkus-smoothing-inequality, density-derivative-integral-bound, gaussian-density-ibp, cutoff-derivative-shell-ibp, bentkus-taylor-remainders, gaussian-density-second-order-remainder, bentkus-angle-integrals, bentkus-parameter-closure, bentkus-rotation-cancellation, covariance-additivity-and-leave-one-out, gaussian-companion-third-moment-comparison, gaussian-companion-mixed-moment, bentkus-trivial-induction-branches, bentkus-leave-one-out-whitening") (tags := "bentkus, gaussian-replacement, induction, source-bentkus-2004, source-open, fidelity-frozen")
*Identity-covariance convex-set replacement bound.* There is an absolute constant
$`C>0` such that, for every $`d\ge1` and every finite independent family of
measurable random vectors $`Y_i\in\mathbb R^d` satisfying
$$`
\mathbb EY_i=0,\qquad
\sum_i\operatorname{Cov}(Y_i)=I_d,\qquad
\sum_i\mathbb E\|Y_i\|^3<\infty,
`
one has, for every measurable convex $`A\subseteq\mathbb R^d`,
$$`
\left|\mathbb P\!\left[\sum_iY_i\in A\right]-
\mathbb P[G\in A]\right|
\le C d^{1/4}\sum_i\mathbb E\|Y_i\|^3,
\qquad G\sim N(0,I_d).
`
:::

This is the standardized core of Vidmantas Bentkus, *A Lyapunov type bound in
$`\mathbb R^d`* (2004), Theorem 1.1, equation (1.1), printed p. 400, proved
through Theorem 1.2 and the induction/Taylor replacement
argument beginning with equation (3.1), printed pp. 403--410.  The node remains
source-open; the smooth cutoff alone is not the replacement theorem.
