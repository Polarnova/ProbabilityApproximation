/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import Verso
import VersoManual
import VersoBlueprint
import ProbabilityApproximationBlueprint.Citations
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
import ProbabilityApproximation.Bentkus.Induction
import ProbabilityApproximation.ConvexGeometry.BallProjectionArea
import ProbabilityApproximation.ConvexGeometry.BallCauchyProjection
import ProbabilityApproximation.ConvexGeometry.BallSphericalProjection
import ProbabilityApproximation.ConvexGeometry.BallGaussianPerimeter
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
open ProbabilityApproximationBlueprint.Sources

#doc (Manual) "Normal approximation over convex sets" =>

Throughout this section $`E=\mathbb R^d` has its Euclidean norm.  For
$`A\subseteq E`, write
$$`
d_A(x)=\inf_{a\in A}\|x-a\|,\qquad
A^\varepsilon=\{x:d_A(x)<\varepsilon\}.
`

The proof has four layers.  Convex distance produces smooth indicator approximations; signed
distance and coarea reduce Gaussian shells to boundary measure; Ball's projection argument bounds
that boundary measure by the sharp order $`d^{1/4}`; and a Gaussian replacement induction,
followed by covariance whitening, proves the multivariate limit theorem.

# Convex distance and smooth cutoffs

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

These are the set-theoretic facts used in {Citations.citet bentkus2004}[], condition (ii)
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

This packages the Euclidean projection geometry used in {Citations.citet bentkus2003}[], Lemma 2.2,
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

This is the distance calculus behind Lemma 2.2, equations (2.5)--(2.9), of
{Citations.citet bentkus2003}[],
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

This is Lemma 2.3, equations (2.10)--(2.12), of {Citations.citet bentkus2003}[],
printed pp. 390--391, and the
same cutoff imported in {Citations.citet bentkus2004}[],
Lemma 2.2, equation (2.2), printed p. 402.  The formal profile is the paper's
piecewise quadratic $`\psi`; endpoint
values are included explicitly.

# Gaussian companions and rotation

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
telescoping/rotation setup (3.2)--(3.5) of {Citations.citet bentkus2004}[], printed pp. 403--404.  The source
simply assumes all variables exist independently in the aggregate; the formal statement
constructs the required marginal and Gaussian product spaces and allows singular
individual covariance matrices.  It deliberately stops before the rotation identity (3.4),
which is recorded in the rotation nodes below.

:::lemma_ "gaussian-fourth-moment-control" (lean := "ProbabilityTheory.integral_norm_pow_four_multivariateGaussian_le") (tags := "bentkus, gaussian-replacement, moments, source-bentkus-2004, fidelity-explicit-sufficient-bound")
*Dimension-free fourth-moment control for a Gaussian vector.* Let $`S` be a positive
semidefinite $`d\times d` real matrix and let $`Y\sim N(0,S)`.  Then
$$`
\mathbb E\|Y\|^4\le 3\bigl(\mathbb E\|Y\|^2\bigr)^2.
`
No nonsingularity assumption is imposed on $`S`.
:::

This is an explicit sufficient estimate for the dimension-free Gaussian moment comparison
used by {Citations.citet bentkus2004}[], in the
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

This is the norm-moment consequence of the covariance matching used by {Citations.citet bentkus2004}[], immediately after equation (3.35),
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

{Citations.citet bentkus2004}[], uses
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
{Citations.citet bentkus2004}[], printed p. 407.  The source
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
{Citations.citet bentkus2004}[], and the
linear/bilinear cancellation asserted in equation (3.5), printed p. 404.  Independence
kills the two mixed expectations and the matched second moment
kills the remaining pair.  The full telescoping identity (3.4) and its third-order
remainder estimates are assembled in the rotation and standardized-induction nodes below.

:::theorem "bentkus-rotation-fubini" (lean := "ProbabilityTheory.bentkusRotationCoordinateIntegrand, ProbabilityTheory.bentkusGaussianReferenceCoordinateIntegrand, ProbabilityTheory.bentkusRotatedSum_eq_leaveOneOut_add, ProbabilityTheory.integrable_bentkusCoordinateIntegrands, ProbabilityTheory.intervalIntegrable_integral_bentkusCoordinateIntegrands, ProbabilityTheory.integrable_intervalIntegral_bentkusRotationCoordinate, ProbabilityTheory.integrable_intervalIntegral_bentkusGaussianReferenceCoordinate, ProbabilityTheory.intervalIntegral_integral_bentkusRotationCoordinate_swap, ProbabilityTheory.intervalIntegral_integral_bentkusGaussianReferenceCoordinate_swap, ProbabilityTheory.integral_sum_intervalIntegral_bentkusRotationCoordinate_eq") (uses := "gaussian-companions-and-transport, bentkus-rotation-cancellation, covariance-additivity-and-leave-one-out, bentkus-smoothing-inequality") (tags := "bentkus, gaussian-replacement, rotation, fubini, source-bentkus-2004, fidelity-explicit-integrability")
*Coordinate rotation integrands and justified exchange of expectations.*  On the
canonical replacement space $`(\widetilde X_i,Y_i)_{i\in I}`, put
$$`
Z_\alpha=\sum_i(\cos\alpha\,\widetilde X_i+\sin\alpha\,Y_i),
\qquad
Z'_{k,\alpha}=-\sin\alpha\,\widetilde X_k+\cos\alpha\,Y_k,
`
and let $`V_k=\sum_{i\ne k}Y_i`.  For a convex set
$`A\subseteq\mathbb R^d`, $`\varepsilon>0`, and the Bentkus cutoff
$`\varphi=\varphi_{\varepsilon,A}`, define
$$`
T_k(\alpha)=D\varphi(Z_\alpha)[Z'_{k,\alpha}],
\qquad
R_k(\alpha)=D\varphi\!\left(V_k+\cos\alpha\,\widetilde X_k+
\sin\alpha\,Y_k\right)[Z'_{k,\alpha}].
`
The rotated sum splits pointwise into its leave-one-out base and exposed coordinate:
$$`
Z_\alpha=
\cos\alpha\sum_{i\ne k}\widetilde X_i+
\sin\alpha\sum_{i\ne k}Y_i+
\cos\alpha\,\widetilde X_k+
\sin\alpha\,Y_k.
`
If the original coordinates are measurable and belong to $`L^3`, then on every
bounded angle interval both coordinate integrands are jointly integrable with respect
to angle and the replacement law.  Consequently,
$$`
\int_a^b\mathbb E T_k(\alpha)\,d\alpha
=\mathbb E\int_a^bT_k(\alpha)\,d\alpha,
\qquad
\int_a^b\mathbb E R_k(\alpha)\,d\alpha
=\mathbb E\int_a^bR_k(\alpha)\,d\alpha.
`
If $`a\le b`, finite summation may also be interchanged:
$$`
\mathbb E\left[\sum_k\int_a^bT_k(\alpha)\,d\alpha\right]
=\sum_k\int_a^b\mathbb E T_k(\alpha)\,d\alpha.
`
:::

{Citations.citet bentkus2004}[], introduces
the uniform rotation and leave-one-out sums immediately before equation (3.4),
printed pp. 403--404; equations (3.4)--(3.5), printed p. 404, give the coordinate
representation and low-order cancellations.  The actual and fully Gaussian reference
contributions are the terms split in equations (3.11)--(3.12), also printed p. 404.
The paper writes the angle expectations compactly; the formal statement makes their
joint integrability and every Fubini interchange explicit.

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

This is the covariance algebra in equation (3.2) and the paragraph immediately following it
in {Citations.citet bentkus2004}[],
printed p. 403.  The formal subsum identity is stated at the
level of covariance bilinear forms; the last display is its coordinate-matrix form and
is exactly the paper's $`P_k^2=I-\operatorname{cov}X_k` notation.

# Whitening and covariance normalization

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

{Citations.citet bentkus2004}[], defines the
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
$`Z\mapsto C^{-1}Z` immediately after equation (3.1) in {Citations.citet bentkus2004}[],
printed p. 403; the
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
in {Citations.citet bentkus2004}[], printed
p. 403.  The formal contract isolates precisely the identity-covariance theorem that the
induction must supply; it does not assume that induction has been proved.

:::theorem "bentkus-whitening-one-set-transport" (lean := "ProbabilityTheory.bentkusWhitenedSet, ProbabilityTheory.isConvexSet_bentkusWhitenedSet, ProbabilityTheory.map_sum_apply_bentkusWhitenedSet, ProbabilityTheory.stdGaussian_apply_bentkusWhitenedSet, ProbabilityTheory.bentkus_convex_set_whitening_reduction, ProbabilityTheory.bentkus_convex_set_bound_of_identity_covariance_bound, ProbabilityTheory.exists_bentkus_convex_set_constant_of_identity_covariance_bound") (uses := "bentkus-whitening-gaussian-pushforward, bentkus-identity-covariance-contract") (tags := "bentkus, whitening, convex-set-transport, source-bentkus-2004, fidelity-exact-one-set-reduction")
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

{Citations.citet bentkus2004}[], uses invariance
of the set class under invertible symmetric linear maps in condition (i), printed p. 401,
and applies the transformation $`C^{-1}` immediately after equation (3.1), printed
p. 403.  This node is the one-set form of that reduction and yields exactly the
normalization in Theorem 1.1, equation (1.1), printed p. 400.

# Signed distance and coarea

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

{Citations.citet raic2019}[],
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

This is Proposition 3.3(4) of {Citations.citet raic2019}[], printed p. 2844, with the positive
and negative cases written
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

{Citations.citet raic2019}[],
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

{Citations.citet ball1993}[] uses
codimension-one projections and Gaussian surface integrals in the proof of Theorem 4,
printed pp. 415--419.  {Citations.citet raic2019}[] states the general area/coarea input as
Proposition 3.2 and Corollary
3.1, printed pp. 2843--2844, and applies it in Proposition 3.1, printed pp. 2843--2845.
This node supplies the
Mathlib-normalized affine specialization; the nonlinear coarea formula for signed distance
is recorded in the next node.

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

This is the injective weighted specialization of Corollary 3.2.32 in
{Citations.citet federer1969}[].  {Citations.citet raic2019}[] records the area formula as Proposition 3.2, printed
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

Corollary 3.2.32 of {Citations.citet federer1969}[] supplies the area/coarea theorem.
{Citations.citet raic2019}[] states the measurable-fiber theorem as Proposition 3.2, printed
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

{Citations.citet raic2019}[],
Proposition 3.1 defines the boundary and shell suprema and derives both profile
disintegrations, printed pp. 2843--2845.  Corollary 3.1 gives the scalar coarea formula,
and Proposition 3.3 identifies $`\|\nabla\delta_A\|=1` almost everywhere and
$`\{\delta_A=t\}=\partial A^t`, both printed p. 2844.  The two displayed outer and
inner equalities occur in the proof of Proposition 3.1 on printed p. 2845.  The node
specializes Raič's continuous density to $`\phi_d`, retains the precise equality-boundary
conventions, and records the direct perimeter-to-shell implication.

# Ball's Gaussian perimeter theorem

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

{Citations.citet ball1993}[],
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

This is the projection identity and graph decomposition in {Citations.citet ball1993}[], equations (2)--(3)
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

{Citations.citet ball1993}[],
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

{Citations.citet ball1993}[], averages
the projection inequality over $`S^{d-1}` immediately before equation (4), printed
p. 416, in the proof of Theorem 4.  The displayed second moment is the rotation-invariant
covariance calculation underlying Ball's $`d^{-1/2}` factor; Cauchy--Schwarz gives the
absolute first-moment inequality.

:::theorem "ball-spherical-rearrangement" (lean := "ProbabilityTheory.ballSphericalRearrangement_absInner_of_measure, ProbabilityTheory.ballSphericalRearrangement_absInner") (uses := "ball-spherical-projection-average") (tags := "bentkus, gaussian-geometry, perimeter, rearrangement, source-ball-1993, fidelity-applied-continuous-g-equals-identity")
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

{Citations.citet ball1993}[], Lemma 3
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
paragraph of {Citations.citet ball1993}[],
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

{Citations.citet ball1993}[], reduces
Theorem 4 to the projection majorization in equation (4), defines the signed inverse
transform by equations (5)--(6), and takes its positive part, printed p. 417.  The
power-series calculation following equation (7), also on printed p. 417, proves the
required monotonicity; the zero-location estimate and polar mass identity are on printed
p. 418.  The two-part integral estimate and normalized Gamma peak close
$`\mu(\mathbb R^{n-1})\le2n^{1/4}` on printed pp. 418--419.  The formal result separates
the construction, the exact signed projection, the positive-part majorization, the
compact positive-radius support, and both normalized forms of the mass estimate.

:::theorem "ball-spherical-density-majorization" (lean := "ProbabilityTheory.ballSphericalRadialProfile, ProbabilityTheory.normalizedHausdorff_lintegral_ballSphericalRadialProfile_absInner_orthogonal, ProbabilityTheory.lintegral_ballSphericalRearrangement_radialProfile, ProbabilityTheory.ofReal_ballRadialProjectionTransform_le_normalizedHausdorff_lintegral, ProbabilityTheory.ofReal_ballGaussianRadialDensity_le_normalizedHausdorff_lintegral, ProbabilityTheory.standardGaussianDensityReal_mul_norm_le_sphere_ballRadialMajorant_absInner") (uses := "intrinsic-sphere-hausdorff-normalization, ball-cauchy-projection-formula, ball-spherical-rearrangement, ball-radial-majorant") (tags := "bentkus, gaussian-geometry, perimeter, spherical-projection, source-ball-1993, fidelity-exact-pointwise-vector-form")
*Spherical majorization of Gaussian density times a normal magnitude.* Let $`d\ge2`,
let $`x,N\in\mathbb R^d`, and write $`P_\theta` for orthogonal projection onto
$`\theta^\perp`.  If $`f_d` is Ball's radial majorant, $`\phi_d` is standard Gaussian
density, and $`\mathcal H^{d-1}_S` is intrinsic Hausdorff measure on $`S^{d-1}`, then
$$`
\phi_d(x)\|N\|
\le
\frac{1}{\mathcal H^{d-1}_S(S^{d-1})}
\int_{S^{d-1}} f_d(\|P_\theta x\|)
  |\langle\theta,N\rangle|\,d\mathcal H^{d-1}_S(\theta).
`
The statement also includes the exact orthogonal-direction identity with Ball's
one-dimensional transform and the monotone spherical rearrangement inequality that
extends it to an arbitrary normal direction.  No normalization assumption is made on $`N`.
:::

{Citations.citet ball1993}[], derives the
spherical density inequality in equation (3), applies Lemma 3 to reduce arbitrary position
and normal directions to the orthogonal case, and rewrites that case as equation (4), printed
pp. 416--417.  Equations (5)--(7) construct the monotone radial majorant used here, printed
pp. 417--418.  The formal statement packages these steps in the pointwise vector form required
by the boundary area formula.

:::theorem "ball-boundary-projection-area" (lean := "ProbabilityTheory.ballBoundaryCoordinateDirection, ProbabilityTheory.ballBoundaryCoordinatePiece, ProbabilityTheory.ballBoundaryCoordinateChartDomain, ProbabilityTheory.ballBoundaryCoordinateChart, ProbabilityTheory.ballBoundaryCoordinateProjectedChart, ProbabilityTheory.lintegral_ballBoundaryCoordinatePiece_eq_chart, ProbabilityTheory.ae_exists_unit_normal_ballBoundaryCoordinateChart, ProbabilityTheory.exists_ballBoundaryCoordinateProjectedChart_multiplicity_partition, ProbabilityTheory.lintegral_frontier_eq_tsum_ballBoundaryCoordinateCharts, ProbabilityTheory.ballBoundaryProjectionFiber, ProbabilityTheory.ae_encard_ballBoundaryProjectionFiber_le_two, ProbabilityTheory.tsum_lintegral_ballBoundaryCoordinateProjectedChart_le_two_mul, ProbabilityTheory.tsum_lintegral_ballBoundaryCoordinateProjectedChart_ballRadialMajorant_le") (uses := "ball-projection-jacobian-charts, ball-radial-majorant") (tags := "bentkus, gaussian-geometry, perimeter, boundary-projection, source-ball-1993, fidelity-exact-normal-free-chart-form")
*Weighted boundary projection area and the factor-two line multiplicity.* Let $`d\ge2`,
let $`C\subseteq\mathbb R^d` be a compact convex body with nonempty interior, and let
$`\theta\in S^{d-1}`.  There is a finite disjoint family of Lipschitz graph charts
$`\varphi_j:T_j\to\partial C`.  For every nonnegative measurable
$`w:\theta^\perp\to[0,\infty]`,
$$`
\sum_j\int_{T_j}
  J_{d-1}(P_\theta\circ D\varphi_j(z))\,
  w(P_\theta\varphi_j(z))\,dz
\le 2\int_{\theta^\perp}w(y)\,dy.
`
The chart Jacobian is the normal-free representative of
$`|\langle\theta,n_C\rangle|\,d\mathcal H^{d-1}`.  In particular, with Ball's radial
majorant $`f_d`,
$$`
\sum_j\int_{T_j}
  J_{d-1}(P_\theta\circ D\varphi_j(z))\,
  f_d(\|P_\theta\varphi_j(z)\|)\,dz
\le 4d^{1/4}.
`
:::

{Citations.citet ball1993}[], introduces
the projected comparison measure in equation (2), printed p. 415, and observes that almost
every line in a fixed direction meets the boundary of a convex body at most twice, yielding
the factor $`2`, printed p. 416 in the proof of Theorem 4.  The radial mass estimate
$`\mu(\mathbb R^{d-1})\le2d^{1/4}` is completed on printed pp. 418--419.  The formal
statement expresses the same projection argument through a finite disjoint chart cover and
the equal-rank area formula, avoiding any measurable choice of an outward normal.

:::theorem "ball-gaussian-perimeter" (lean := "ProbabilityTheory.standardGaussianBoundaryContent_le_one_of_interior_eq_empty, ProbabilityTheory.standardGaussianBoundaryContent_le_of_isBounded_case, ProbabilityTheory.standardGaussianBoundaryContent_le_of_convexBody_case_all, ProbabilityTheory.standardGaussianBoundaryContent_le_ballGaussianPerimeterConstant_of_convexBody_case, ProbabilityTheory.standardGaussianBoundaryContent_le_ballGaussianPerimeterConstant_compactBody, ProbabilityTheory.standardGaussianBoundaryContent_le_ballGaussianPerimeterConstant") (uses := "gaussian-affine-codimension-one-slicing, ball-spherical-density-majorization, ball-boundary-projection-area") (tags := "bentkus, gaussian-geometry, perimeter, source-ball-1993, fidelity-domain-completed-exact-constant")
*Ball's Gaussian perimeter theorem.* Let $`d\ge2` and let
$`C\subseteq\mathbb R^d` be convex.  With
$$`
P_\gamma(C)=\int_{\partial C}(2\pi)^{-d/2}e^{-\|x\|^2/2}\,
  d\mathcal H^{d-1}(x),
\qquad K_d=4d^{1/4},
`
one has
$$` P_\gamma(C)\le K_d. `
The conclusion holds without assuming that $`C` is closed, bounded, or
full-dimensional.  For a compact convex body with nonempty interior it follows from the
spherical density and boundary projection estimates above; closure, increasing compact
truncation, affine slicing, and the empty-interior case complete the domain.
:::

This is {Citations.citet ball1993}[],
Theorem 4, printed pp. 415--419, with its explicit constant $`4d^{1/4}`.  Ball states the
theorem for convex bodies.  The formal theorem retains that source theorem as the compact
full-dimensional core and extends it to every convex set by the exact boundary-content
reductions described in the statement; the codimension-one case uses normalized affine
slicing, while higher-codimension boundaries have zero $`\mathcal H^{d-1}` measure.

:::theorem "gaussian-convex-shell" (lean := "ProbabilityTheory.stdGaussian_shell_pair_le_ball_of_boundaryContent_all, ProbabilityTheory.stdGaussian_shell_pair_le_ball_of_convexBody_boundaryContent, ProbabilityTheory.stdGaussian_shell_pair_le_ball") (uses := "gaussian-signed-distance-coarea-profiles, ball-gaussian-perimeter") (tags := "bentkus, gaussian-geometry, perimeter, shells, source-ball-1993, source-raic-2019, fidelity-explicit-constant-all-dimensions")
*Explicit Gaussian shell bounds for convex sets.* Let $`d\in\mathbb N`, let
$`A\subseteq\mathbb R^d` be convex, and let $`\varepsilon\ge0`.  Put
$`K_d=4d^{1/4}` and let $`\gamma_d` be standard Gaussian measure.  Then
$$`
\gamma_d\!\left(\{x:d(x,\overline A)\le\varepsilon\}\setminus A\right)
\le K_d\varepsilon,
`
and, with open balls in the inner core,
$$`
\gamma_d\!\left(A\setminus
  \{x:B(x,\varepsilon)\subseteq A\}\right)
\le K_d\varepsilon.
`
These statements include dimensions zero and one as well as empty, full, unbounded, and
lower-dimensional convex sets.
:::

{Citations.citet ball1993}[], Theorem 4,
printed pp. 415--419, supplies the boundary-content constant in dimensions at least two.
{Citations.citet raic2019}[],
Proposition 3.1 and its proof, printed pp. 2843--2845, derive the outer and inner shell
integrals from Gaussian boundary content by signed-distance coarea.  {Citations.citet bentkus2004}[], uses the resulting
$`O(d^{1/4}\varepsilon)` estimate as equation (1.4), printed p. 401.  The formal theorem
keeps the exact half-open boundary conventions and supplies the elementary zero- and
one-dimensional endpoints.

# Smoothing convex indicators

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

This is the setwise form of Lemma 2.1 in {Citations.citet bentkus2004}[], combined with the
cutoff of Lemma 2.2,
equation (2.2), printed p. 402.  The paper takes the outer neighborhood
$`\{d_A\le\varepsilon\}` and defines its inner neighborhood using a closed ball.  The
formal inner core instead uses an open ball, equivalently the complement of the open
$`\varepsilon`-thickening of $`A^c`; this keeps the equality boundary in the displayed
inner shell.  Empty and nonclosed convex sets are handled by the total cutoff and
$`\overline A` explicitly.

# Gaussian density calculus

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

This is {Citations.citet bentkus2004}[],
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
{Citations.citet bentkus2004}[], Lemma 2.3,
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

This is {Citations.citet bentkus2004}[],
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

This is the deterministic integration-by-parts step in {Citations.citet bentkus2004}[], equation (3.32), printed p. 407,
with the shell placement used in equations (3.30)--(3.34), printed pp. 407--408.
The topological support retains the boundary of $`A`, hence the exact shell removes only
$`\operatorname{int}A`.

# Taylor remainders and angle splitting

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

This is the integral Taylor estimate used in {Citations.citet bentkus2004}[], equation (3.28), printed p. 407,
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

This is the cancellation-ready Taylor estimate in {Citations.citet bentkus2004}[], equations (3.19)--(3.23),
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

{Citations.citet bentkus2004}[], splits the
rotation at $`\gamma` in equations (3.11)--(3.15), printed pp. 404--405.  In the proof
of (3.13), the integral $`\int_0^\gamma\cos\alpha\,d\alpha` occurs immediately after
equation (3.33), printed p. 407.  In the proof of (3.14), equations (3.39)--(3.40) are
followed by the bound on
$`\int_\gamma^{\pi/2}\cos\alpha/\sin^2\alpha\,d\alpha`, printed p. 409.
Bentkus chooses $`\sin\gamma=\varepsilon` after equation (3.8), printed p. 404; the
node retains the exact antiderivatives before taking the inequalities used in the paper.

:::lemma_ "bentkus-coordinate-piece-assembly" (lean := "ProbabilityTheory.pi_div_two_sub_arcsin_le_two, ProbabilityTheory.intervalIntegral_eq_small_add_difference_add_reference, ProbabilityTheory.bentkus_largeAngle_integral_le_of_cos_div_sin_sq_envelope, ProbabilityTheory.bentkus_coordinate_bounds_sum, ProbabilityTheory.fin_sum_succAbove_le_sum_univ, ProbabilityTheory.bentkus_three_coordinate_pieces") (uses := "bentkus-angle-integrals") (tags := "bentkus, gaussian-replacement, induction, angle-splitting, scalar-assembly, source-bentkus-2004, fidelity-explicit-constant-bookkeeping")
*Three-piece angle decomposition and coordinate summation.*  If $`F` is
interval-integrable on $`[0,\gamma]` and $`[\gamma,b]`, and $`R` is
interval-integrable on $`[\gamma,b]`, then
$$`
\int_0^bF
=\int_0^\gamma F+
\int_\gamma^b(F-R)+
\int_\gamma^bR.
`
For $`0<\varepsilon\le1`, if $`K\ge0` and
$$`
|F(\alpha)|\le K\frac{\cos\alpha}{\sin^2\alpha}
\quad\text{for }\alpha\in(\arcsin\varepsilon,\pi/2],
`
then
$$`
\left|\int_{\arcsin\varepsilon}^{\pi/2}F(\alpha)\,d\alpha\right|
\le\frac K\varepsilon,
\qquad
\frac\pi2-\arcsin\varepsilon\le2.
`
Suppose a coordinate contribution satisfies $`T=S+L+R` and, for nonnegative
$`d_{1/4},q,\beta_k,K_L,K_R`,
$$`
|S|\le K_Sd_{1/4}(1+q)\beta_k,\quad
|L|\le K_Ld_{1/4}q\beta_k,\quad
|R|\le K_Rd_{1/4}\beta_k.
`
Then
$$`
|T|\le(K_S+K_L+K_R)d_{1/4}(1+q)\beta_k.
`
Moreover, if $`\beta=\sum_k\beta_k`, $`\varepsilon>0`, and
$$`
|T_k|\le Kd_{1/4}
\left(1+\frac{C\beta}{\varepsilon}\right)\beta_k,
`
then
$$`
\left|\sum_kT_k\right|
\le Kd_{1/4}\left(\beta+\frac{C\beta^2}{\varepsilon}\right).
`
Deleting one nonnegative coordinate cannot increase the corresponding finite sum:
$$` \sum_{i\ne k}\beta_i\le\sum_i\beta_i. `
:::

This is the scalar assembly behind {Citations.citet bentkus2004}[], Section 3, printed p. 404.
The small-angle, large-angle difference, and Gaussian-reference estimates are
equations (3.13)--(3.15); they combine to equation (3.6), summation over coordinates
gives equation (3.7), and insertion into the smoothing inequality gives equations
(3.8)--(3.9).  The displayed decomposition and omitted-coordinate inequality make
explicit the bookkeeping compressed in the paper.

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

This is the scalar calculation in {Citations.citet bentkus2004}[], equations (3.9)--(3.10), printed
p. 404.  It chooses $`\varepsilon=\beta\sqrt C`; the complementary branch
$`\varepsilon\ge1` closes directly from $`\Delta\le1`.

# The identity-covariance replacement induction

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

These are the two trivial branches at the start of Section 3 in {Citations.citet bentkus2004}[], printed p. 403.  The first is the
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
{Citations.citet bentkus2004}[], printed
pp. 403--404.  The paper writes $`P_k^2=\operatorname{Cov}(U_k)` and
$`Q_k=P_k^{-1}` and, after excluding the large-covariance trivial case, assumes
$`\|Q_k\|\le2`; the formal statement derives that bound and records the resulting
third-moment factor $`2^3=8` explicitly.

:::theorem "bentkus-standardized-induction" (lean := "ProbabilityTheory.exists_bentkus_identity_covariance_constant") (uses := "gaussian-convex-shell, bentkus-smoothing-inequality, density-derivative-integral-bound, gaussian-density-ibp, cutoff-derivative-shell-ibp, bentkus-taylor-remainders, gaussian-density-second-order-remainder, bentkus-angle-integrals, bentkus-rotation-fubini, bentkus-coordinate-piece-assembly, bentkus-parameter-closure, bentkus-rotation-cancellation, covariance-additivity-and-leave-one-out, gaussian-companion-third-moment-comparison, gaussian-companion-mixed-moment, bentkus-trivial-induction-branches, bentkus-leave-one-out-whitening, bentkus-identity-covariance-contract") (tags := "bentkus, gaussian-replacement, induction, source-bentkus-2004, fidelity-exact-identity-covariance")
*Identity-covariance convex-set replacement bound.* There is an absolute constant
$`C>0` such that, for every $`d,n\in\mathbb N` with $`d>0`, every probability
space $`(\Omega,\mathcal F,\mu)`, and every family
$`X_i:\Omega\to\mathbb R^d` indexed by $`i\in\operatorname{Fin}(n)` satisfying
$`X_i\in L^3(\mu)`, mutual independence, and
$`\int_\Omega X_i\,d\mu=0`, if $`W=\sum_iX_i` has identity covariance in the
bilinear sense
$$`
\operatorname{Cov}_{\mu\circ W^{-1}}(x,y)=\langle x,y\rangle
\qquad\text{for every }x,y\in\mathbb R^d,
`
one has, for every measurable convex $`A\subseteq\mathbb R^d`,
$$`
\left|(\mu\circ W^{-1})(A)-\gamma_d(A)\right|
\le C d^{1/4}\sum_{i\in\operatorname{Fin}(n)}
  \int_\Omega\|X_i(\omega)\|^3\,d\mu(\omega),
`
where $`\gamma_d` is standard Gaussian measure on $`\mathbb R^d`.
:::

This is the identity-covariance specialization of {Citations.citet bentkus2004}[], Theorem 1.2, printed p. 401,
and the standardized setup in equation (3.1), printed p. 403.  The leave-one-out
induction begins with equation (3.2), printed p. 403; the rotation and replacement
estimates in equations (3.4)--(3.15) occupy printed pp. 404--405, and the proof
continues through printed p. 409.  Bentkus leaves the absolute constant unspecified;
the associated declaration selects one through explicit kernel-checked bookkeeping.

# Bentkus's convex-set theorem

:::theorem "bentkus-convex-set" (lean := "ProbabilityTheory.exists_bentkus_convex_set_constant") (uses := "bentkus-standardized-induction, bentkus-whitening-one-set-transport") (tags := "principal-theorem, source-bentkus-2004, multivariate, convex-set, fidelity-exact")
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

This is Theorem 1.1 and equation (1.1) of {Citations.citet bentkus2004}[], printed
pp. 400--401.  The matrix $`S` here is the total covariance; $`S^{-1/2}` is the
paper's inverse of the positive covariance square root.  The associated declaration first proves
the standardized replacement theorem and then transports it through covariance-square-root
whitening.
