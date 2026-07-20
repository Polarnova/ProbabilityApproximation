/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import Verso
import VersoManual
import VersoBlueprint
import ProbabilityApproximationBlueprint.Citations
import ProbabilityApproximation.ChenShao.NonuniformBerryEsseen
import ProbabilityApproximation.ChenShao.UpperTruncatedIndicator
import ProbabilityApproximation.ChenShao.SteinProductIncrement
import ProbabilityApproximation.ChenShao.UpperTruncatedSteinBounds
import ProbabilityApproximation.ChenShao.UpperTruncatedExpectedKernel

open Verso.Genre
open Verso.Genre.Manual
open Informal
open ProbabilityApproximationBlueprint.Sources

#doc (Manual) "Nonuniform Berry--Esseen bounds" =>

Let $`\Phi(x)=\Pr(Z\le x)` for a standard normal random variable $`Z`.  In this
section $`I` is finite, $`(\Omega,\mathcal F,\mathbb P)` is a probability space, and
$`(X_i)_{i\in I}` is an independent measurable real-valued family.  We write
$`W=\sum_iX_i` and $`\gamma=\sum_i\mathbb E|X_i|^3` whenever the moments exist.

The proof proceeds from the half-line Stein equation through concentration, one-sided truncation,
and an exact residual decomposition.  The final reflection step converts the positive-threshold
estimate into a bound on the whole real line.

# The half-line Stein equation

:::definition "indicator-stein-solution" (parent := "probability-scalar") (lean := "ProbabilityTheory.steinSolution, ProbabilityTheory.steinSolutionDeriv, ProbabilityTheory.stein_equation, ProbabilityTheory.steinSolution_nonneg, ProbabilityTheory.abs_mul_steinSolution_le_one, ProbabilityTheory.abs_steinSolutionDeriv_le_two, ProbabilityTheory.abs_steinSolution_le_sqrt_two_pi_div_two") (tags := "scalar, stein, source-chen-shao-2005, fidelity-exact")
*Indicator Stein solution.* For $`z,w\in\mathbb R`, put
$$`
h_z(w)=\mathbf 1_{\{w\le z\}}-\Phi(z),\qquad
f_z(w)=e^{w^2/2}\int_{-\infty}^{w}h_z(t)e^{-t^2/2}\,dt.
`
The function $`f_z` is continuous and nonnegative.  At every $`w\ne z` it is
differentiable and satisfies
$$` f'_z(w)-wf_z(w)=h_z(w). `
With the everywhere-defined representative
$`f'_z(w)=wf_z(w)+h_z(w)`, one has, for every $`z,w\in\mathbb R`,
$$`
|wf_z(w)|\le1,\qquad |f'_z(w)|\le2,
\qquad 0\le f_z(w)\le\frac{\sqrt{2\pi}}2.
`
:::

This is the half-line specialization of {Citations.citet chenShao2005}[], Section 2.2, Lemma 2.2 and
equations (2.3)--(2.9), printed pp. 10--11.  The displayed integral fixes the same
$`(-\infty,z]` convention as the library CDF.

:::theorem "nonuniform-stein-derivative-bounds" (parent := "probability-scalar") (lean := "ProbabilityTheory.steinSolutionDeriv_of_le, ProbabilityTheory.steinSolutionDeriv_of_gt, ProbabilityTheory.abs_steinSolutionDeriv_le_two_mul_tail, ProbabilityTheory.abs_steinSolutionDeriv_le_majorant_of_abs_le_half, ProbabilityTheory.cdf_sub_eq_integral_steinSolutionDeriv_sub_Wf") (uses := "indicator-stein-solution") (tags := "scalar, stein, nonuniform, source-chen-shao-2005, fidelity-exact-tail-majorants")
*Tail-sensitive derivative bounds and the integrated Stein equation.*  Write
$`\Phi` for the standard Gaussian distribution function.  The derivative of the
indicator Stein solution has the two exact forms
$$`
\begin{aligned}
f'_x(w)
  &=(1-\Phi(x))
    \left(1+w\sqrt{2\pi}\,e^{w^2/2}\Phi(w)\right),
    &&w\le x,\\
f'_x(w)
  &=\Phi(x)
    \left(w\sqrt{2\pi}\,e^{w^2/2}(1-\Phi(w))-1\right),
    &&x<w.
\end{aligned}
`
In particular, if $`x>0` and $`w\le0`, then
$$` |f'_x(w)|\le2(1-\Phi(x)), `
while, if $`x\ge2` and $`|w|\le x/2`, then
$$`
|f'_x(w)|
\le(1-\Phi(x))
  \left(1+\sqrt{2\pi}\,\frac x2 e^{x^2/8}\right).
`
Finally, for a finite sum $`W=\sum_iX_i` of measurable square-integrable variables,
$$`
\Pr(W\le x)-\Phi(x)
=\mathbb E f'_x(W)-\mathbb E[Wf_x(W)].
`
:::

The two closed forms are the half-line specialization of {Citations.citet chenShao2005}[], equation (8.3),
printed p. 54, derived from the solution in equation (2.3), printed pp. 9--10.
The Mills bounds in equation (8.1) and sign estimates in equations (8.4)--(8.5),
printed pp. 54--55, give the displayed tail majorants; the $`|w|\le x/2`
specialization is used in the proof of equation (6.17), printed p. 46.  The
integrated identity is equation (1.4), printed p. 4, and the first equality in the
residual expansion (6.16), printed p. 46.

# Uniform approximation and leave-one-out concentration

:::lemma_ "uniform-leave-one-out-concentration" (parent := "probability-scalar") (tags := "scalar, concentration, source-chen-shao-2001, fidelity-explicit-constants-without-smallness") (lean := "ProbabilityTheory.concentration_leaveOneOut")
*Uniform leave-one-out concentration.* Suppose
$`\mathbb EX_i=0`, $`\mathbb E X_i^2<\infty`, and
$`\sum_i\operatorname{Var}(X_i)=1`.  If $`\gamma<\infty`, then, for
$`W^{(i)}=W-X_i`, every $`i\in I`, and all $`a\le b`,
$$`
\Pr(a\le W^{(i)}\le b)
\le \sqrt2\,(b-a)+2(\sqrt2+1)\gamma.
`
:::

The proof follows the concentration-kernel argument of {Citations.citet chenShao2001}[], Section 3,
especially Proposition 3.2 and equations (3.2)--(3.6), printed pp. 239--241.
The constants above follow without the paper's additional small-truncation hypothesis; under that
hypothesis, Chen--Shao obtain the sharper coefficients $`1.5` and $`3.3\delta`.

:::theorem "uniform-third-moment-berry-esseen" (parent := "probability-scalar") (lean := "ProbabilityTheory.thirdMomentBerryEsseenConstant, ProbabilityTheory.uniformBerryEsseen_thirdMoment") (uses := "indicator-stein-solution, uniform-leave-one-out-concentration") (tags := "scalar, berry-esseen, source-chen-shao-2005, fidelity-explicit-constant")
*Uniform third-moment Berry--Esseen theorem.* Suppose
$`\mathbb EX_i=0`, $`\mathbb E|X_i|^3<\infty`, and
$`\sum_i\operatorname{Var}(X_i)=1`.  Then, for every $`x\in\mathbb R`,
$$`
\left|\Pr(W\le x)-\Phi(x)\right|\le30\gamma.
`
:::

Combining the concentration inequality with the Stein residual estimate in the manner of
{Citations.citet chenShao2005}[], Sections 5.1--5.2, printed pp. 31--35, gives the
constant $`30`. The sharper constant $`4.1` in {Citations.citet chenShao2001}[],
Theorem 2.1, printed pp. 237--238, belongs to their truncated-moment bound.

# Exponential concentration

:::lemma_ "bennett-hoeffding-mgf" (parent := "probability-scalar") (lean := "ProbabilityTheory.mgf_finsetSum_le_exp_bennett, ProbabilityTheory.measure_finsetSum_ge_le_exp_bennett") (tags := "scalar, concentration, mgf, source-chen-shao-2005, fidelity-generalized-parameter-form")
*Bennett--Hoeffding moment-generating-function bound.* Let $`J` be finite and let
$`(\eta_j)_{j\in J}` be independent measurable random variables with finite second
moments.  Suppose $`\mathbb E\eta_j\le0`, $`\eta_j\le\alpha` almost surely,
$`\alpha>0`, and
$$` \sum_{j\in J}\mathbb E\eta_j^2\le B^2. `
Then, for every $`t\ge0`,
$$`
\mathbb E\exp\!\left(t\sum_{j\in J}\eta_j\right)
\le
\exp\!\left(\frac{e^{t\alpha}-1-t\alpha}{\alpha^2}B^2\right).
`
Consequently, for every $`x\in\mathbb R`,
$$`
\Pr\left(\sum_{j\in J}\eta_j\ge x\right)
\le
\exp\!\left(-tx+\frac{e^{t\alpha}-1-t\alpha}{\alpha^2}B^2\right).
`
:::

This is Lemma 6.2 and equation (6.2) of {Citations.citet chenShao2005}[], together with
its Chernoff consequence,
printed pp. 40--41. Keeping $`t` as a parameter and
optimizing it recovers the paper's equations (6.3)--(6.4).

:::proposition "exponential-leave-one-out-concentration" (parent := "probability-scalar") (lean := "ProbabilityTheory.chenShao_exponentialConcentration_upperTruncated") (uses := "bennett-hoeffding-mgf") (tags := "scalar, concentration, upper-truncation, source-chen-shao-2005, fidelity-corrected-explicit-constants")
*Exponential concentration for the upper-truncated leave-one-out sum.* Define
$`\bar X_j=X_j\mathbf 1_{\{X_j\le1\}}` and
$`\bar W^{(i)}=\sum_{j\ne i}\bar X_j`.  Suppose
$`\mathbb EX_j=0`, $`\mathbb E X_j^2<\infty`,
$`\sum_j\operatorname{Var}(X_j)=1`, and $`\gamma<\infty`.  Then, for every
$`i\in I` and all $`a\le b`,
$$`
\Pr(a\le\bar W^{(i)}\le b)
\le e^{-a/2}\bigl(24(b-a)+48\gamma\bigr).
`
:::

This is the exponentially weighted conclusion of {Citations.citet chenShao2005}[], Proposition 6.1, equation (6.1),
with the proof on printed pp. 41--43.  The paper prints constants
$`5,7`. Accounting explicitly for the one-sided truncation drift gives the
coefficients $`24,48`; the displayed exchange equality in the source omits this drift.

# One-sided truncation

:::proposition "one-sided-truncation-comparison" (parent := "probability-scalar") (lean := "ProbabilityTheory.upperTruncatedFamily, ProbabilityTheory.upperTruncatedSum, ProbabilityTheory.measureReal_sumX_upperTail_le_upperTruncatedTail_add, ProbabilityTheory.abs_cdf_sumX_sub_gaussian_le_upperTruncated_add") (tags := "scalar, upper-truncation, source-chen-shao-2005, fidelity-explicit-constant")
*Comparison with one-sided truncation.* Suppose
$`\mathbb EX_i=0`, $`\mathbb E|X_i|^3<\infty`,
$`\sum_i\operatorname{Var}(X_i)=1`, and $`\gamma\le1`.  Put
$`\bar X_i=X_i\mathbf1_{\{X_i\le1\}}` and $`\bar W=\sum_i\bar X_i`.
For every $`z\ge2`,
$$`
\Pr(W>z)
\le \Pr(\bar W>z)+\frac{45\gamma}{1+z^3},
`
and hence
$$`
|\Pr(W\le z)-\Phi(z)|
\le |\Pr(\bar W\le z)-\Phi(z)|+\frac{45\gamma}{1+z^3}.
`
:::

The event decomposition is in Section 6.2, equations (6.13)--(6.14), of
{Citations.citet chenShao2005}[], printed
p. 44.  The displayed $`45` is the explicit constant proved by
the large-jump and leave-one-out estimates.

# Stein exchange and residual decomposition

:::theorem "upper-truncated-stein-exchange" (parent := "probability-scalar") (lean := "ProbabilityTheory.stein_identity_sum_leaveOneOut_noncentered, ProbabilityTheory.stein_identity_upperTruncatedSum") (uses := "indicator-stein-solution, one-sided-truncation-comparison") (tags := "scalar, stein, upper-truncation, source-chen-shao-2005, fidelity-exact-noncentered-form")
*Noncentered Stein exchange for the upper-truncated sum.* Let
$`Y_i=\bar X_i`, $`\bar W=\sum_iY_i`, and
$`\bar W^{(i)}=\bar W-Y_i`.  Define
$$`
K_i(t)=\mathbb E\!\left[|Y_i|
  \mathbf1_{\{\min(0,Y_i)\le t\le\max(0,Y_i)\}}\right].
`
If the $`X_i` have finite second moments, then, for every $`z\in\mathbb R`,
$$`
\mathbb E[\bar W f_z(\bar W)]
=\sum_i\int_{\mathbb R}\mathbb E[f'_z(\bar W^{(i)}+t)]K_i(t)\,dt
+\sum_i\mathbb EY_i\,\mathbb E[f_z(\bar W^{(i)})].
`
:::

This is the noncentered form of the exchange used in Section 6.2, equation
(6.16), of {Citations.citet chenShao2005}[],
printed p. 45.  Retaining the second sum is essential:
one-sided truncation generally makes $`\mathbb EY_i<0`.

:::theorem "upper-truncated-residual-decomposition" (parent := "probability-scalar") (lean := "ProbabilityTheory.upperTruncatedMissingSecondMoment, ProbabilityTheory.upperTruncatedR1, ProbabilityTheory.upperTruncatedR2, ProbabilityTheory.upperTruncatedR3, ProbabilityTheory.upperTruncatedMissingSecondMoment_le_thirdMomentSum, ProbabilityTheory.cdf_upperTruncatedSum_sub_gaussian_eq_R1_add_R2_add_R3") (uses := "nonuniform-stein-derivative-bounds, upper-truncated-stein-exchange") (tags := "scalar, stein, residuals, source-chen-shao-2005, fidelity-exact")
*The $`R_1+R_2+R_3` identity.* Set
$$`
q=1-\sum_i\mathbb E\bar X_i^2,\qquad
T=\sum_i\int_{\mathbb R}\mathbb E[f'_z(\bar W^{(i)}+t)]K_i(t)\,dt,
`
and
$$`
M=\sum_i\mathbb E\bar X_i\,\mathbb E[f_z(\bar W^{(i)})].
`
Define
$$`
R_1=q\,\mathbb E f'_z(\bar W),\qquad
R_2=(1-q)\mathbb E f'_z(\bar W)-T,\qquad R_3=-M.
`
If $`\mathbb EX_i=0`, $`\sum_i\operatorname{Var}(X_i)=1`, and
$`\gamma<\infty`, then $`0\le q\le\gamma`; moreover, without the centering and
variance assumptions needed for that bound, the exact identity
$$`
\Pr(\bar W\le z)-\Phi(z)=R_1+R_2+R_3
`
holds whenever the coordinates have finite second moments.
:::

This is Section 6.2, equation (6.16), of {Citations.citet chenShao2005}[], printed p. 45,
with the
missing second-moment mass and nonzero truncated means made explicit.

# Estimates for the residual terms

:::lemma_ "upper-truncated-r1-r3-bounds" (parent := "probability-scalar") (lean := "ProbabilityTheory.abs_upperTruncatedR1_le, ProbabilityTheory.abs_upperTruncatedR3_le") (uses := "bennett-hoeffding-mgf, upper-truncated-residual-decomposition") (tags := "scalar, stein, residuals, source-chen-shao-2005, fidelity-explicit-constant")
*Exponential bounds for $`R_1` and $`R_3`.* Under the centered, unit-total-variance,
finite-third-moment hypotheses above, for every $`z\ge2`,
$$`
|R_1|\le8e^{-z/2}\gamma,\qquad |R_3|\le8e^{-z/2}\gamma.
`
:::

These are explicit versions of {Citations.citet chenShao2005}[], Section 6.2, equations
(6.17)--(6.18), printed p. 45. The source records an unspecified absolute constant;
the estimates above give $`8` in both inequalities.

:::theorem "upper-truncated-r2-expected-kernel" (parent := "probability-scalar") (lean := "ProbabilityTheory.upperTruncatedExpectedKernel, ProbabilityTheory.integral_upperTruncatedExpectedKernel, ProbabilityTheory.upperTruncatedR2_eq_sum_integral_expectedKernel, ProbabilityTheory.upperTruncatedR21, ProbabilityTheory.upperTruncatedR22, ProbabilityTheory.upperTruncatedR2_eq_R21_add_R22") (uses := "upper-truncated-residual-decomposition") (tags := "scalar, stein, expected-kernel, source-chen-shao-2005, fidelity-exact")
*Deterministic expected-kernel representation and split of $`R_2`.* For
$`K_i(t)=\mathbb E[|\bar X_i|\mathbf1_{\{\min(0,\bar X_i)\le t\le
\max(0,\bar X_i)\}}]`, one has
$$` \int_{\mathbb R}K_i(t)\,dt=\mathbb E\bar X_i^2. `
Writing $`F=\mathbb E f'_z(\bar W)`, the residual is
$$`
R_2=\sum_i\int_{\mathbb R}
\bigl(F-\mathbb E f'_z(\bar W^{(i)}+t)\bigr)K_i(t)\,dt.
`
Using $`f'_z(w)=wf_z(w)+\mathbf1_{\{w\le z\}}-\Phi(z)` splits this exactly as
$`R_2=R_{2,1}+R_{2,2}`, where
$$`
R_{2,1}=\sum_i\int
\bigl(\Pr(\bar W\le z)-\Pr(\bar W^{(i)}+t\le z)\bigr)K_i(t)\,dt
`
and
$$`
R_{2,2}=\sum_i\int
\bigl(\mathbb E[\bar Wf_z(\bar W)]
-\mathbb E[(\bar W^{(i)}+t)f_z(\bar W^{(i)}+t)]\bigr)K_i(t)\,dt.
`
:::

This is the split immediately after equation (6.18) in {Citations.citet chenShao2005}[], Section 6.2,
printed pp. 45--46.  Fubini and leave-one-out independence supply
the deterministic kernels in the display.

:::lemma_ "upper-truncated-indicator-residual" (parent := "probability-scalar") (lean := "ProbabilityTheory.abs_upperTruncatedR21_le_exp_thirdMomentSum") (uses := "exponential-leave-one-out-concentration, upper-truncated-r2-expected-kernel") (tags := "scalar, concentration, residuals, source-chen-shao-2005, fidelity-explicit-constant")
*Indicator part of $`R_2`.* Under the centered, unit-total-variance,
finite-third-moment hypotheses, for every $`z\in\mathbb R`,
$$` |R_{2,1}|\le168e^{-z/2}\gamma. `
:::

Applying the two orientations of the conditional interval estimate in
Section 6.2, equations (6.19) and (6.21)--(6.22), of {Citations.citet chenShao2005}[],
printed p. 46 gives the stated bound. The source uses an unspecified constant; the
preceding concentration estimate gives $`168`.

:::lemma_ "stein-product-increment" (parent := "probability-scalar") (lean := "ProbabilityTheory.steinProductDeriv, ProbabilityTheory.mul_steinSolution_sub_eq_integral_steinProductDeriv, ProbabilityTheory.steinProductIncrementConstant, ProbabilityTheory.abs_integral_steinProductIncrement_upperTruncated_le_abs_add") (uses := "nonuniform-stein-derivative-bounds, bennett-hoeffding-mgf") (tags := "scalar, stein, residuals, source-chen-shao-2005, fidelity-explicit-constant")
*Stein-product increment estimate.* Let $`g_z(w)=(wf_z(w))'` away from $`z`, with
the everywhere-defined representative obtained from the two one-sided formulas.
There is an explicit absolute constant $`C_{\mathrm{inc}}>0` such that, under the
centered and unit-total-variance hypotheses, for every $`i\in I`, $`z\ge2`, and
$`s,t\le1`,
$$`
\left|\mathbb E\bigl[(\bar W^{(i)}+t)f_z(\bar W^{(i)}+t)
-(\bar W^{(i)}+s)f_z(\bar W^{(i)}+s)\bigr]\right|
\le C_{\mathrm{inc}}e^{-z/2}(|s|+|t|).
`
In addition,
$$`
bf_z(b)-af_z(a)=\int_a^b g_z(u)\,du
`
for every $`a,b\in\mathbb R`, including intervals crossing $`z`.
:::

This is Lemma 6.5 and equations (6.23)--(6.24) of {Citations.citet chenShao2005}[],
printed pp. 46--48.
Here
$`C_{\mathrm{inc}}=C_{\mathrm{low}}+3(\sqrt{2\pi}/2+2)e^2e^{e^2-3}`.

:::lemma_ "upper-truncated-product-residual" (parent := "probability-scalar") (lean := "ProbabilityTheory.integral_upperTruncatedSteinProduct_eq_iterated_leaveOneOut, ProbabilityTheory.abs_upperTruncatedR22_le_exp_thirdMomentSum") (uses := "upper-truncated-r2-expected-kernel, stein-product-increment") (tags := "scalar, stein, residuals, source-chen-shao-2005, fidelity-explicit-constant")
*Stein-product part of $`R_2`.* Leave-one-out independence gives, for every $`i`,
$$`
\mathbb E[\bar Wf_z(\bar W)]
=\mathbb E_{\bar X_i}\mathbb E_{\bar W^{(i)}}
[(\bar W^{(i)}+\bar X_i)f_z(\bar W^{(i)}+\bar X_i)].
`
Consequently, under the centered, unit-total-variance, finite-third-moment
hypotheses and for every $`z\ge2`,
$$`
|R_{2,2}|\le \frac32 C_{\mathrm{inc}}e^{-z/2}\gamma.
`
:::

This completes the integration step in {Citations.citet chenShao2005}[], Section 6.2, equation (6.20),
printed p. 46.  The factor $`3/2` is the sum of the exact first absolute moment of
the expected kernel, $`1/2`, and the product of its total mass with the coordinate
first moment, bounded by $`1`.

# The central nonuniform estimate

:::theorem "upper-truncated-central-decay" (parent := "probability-scalar") (lean := "ProbabilityTheory.upperTruncatedNonuniformConstant, ProbabilityTheory.upperTruncatedNonuniformConstant_nonneg, ProbabilityTheory.abs_cdf_upperTruncatedSum_sub_gaussian_le_exp_thirdMomentSum") (uses := "upper-truncated-r1-r3-bounds, upper-truncated-indicator-residual, upper-truncated-product-residual") (tags := "scalar, central-estimate, source-chen-shao-2005, fidelity-explicit-constant")
*Central exponential estimate for the upper-truncated sum.* There is an absolute
constant
$$` A=184+\frac32 C_{\mathrm{inc}}\ge0 `
such that, for every finite independent measurable family with
$`\mathbb EX_i=0`, $`\mathbb E|X_i|^3<\infty`, and
$`\sum_i\operatorname{Var}(X_i)=1`, for every $`z\ge2`,
$$`
\left|\Pr(\bar W\le z)-\Phi(z)\right|
\le A e^{-z/2}\gamma.
`
:::

This is the finite-third-moment specialization of the conclusion assembled in
Section 6.2, equations (6.16)--(6.24), of {Citations.citet chenShao2005}[], printed pp. 45--48.
The four explicit contributions are $`8` from $`R_1`, $`8` from $`R_3`,
$`168` from $`R_{2,1}`, and $`(3/2)C_{\mathrm{inc}}` from $`R_{2,2}`.

# Reflection and the nonuniform theorem

:::theorem "nonuniform-reflection-reduction" (parent := "probability-scalar") (lean := "ProbabilityTheory.nonuniformReductionConstant, ProbabilityTheory.nonuniformReductionConstant_pos, ProbabilityTheory.cdf_gaussian_error_le_of_nonneg_of_map_neg, ProbabilityTheory.nonuniformBerryEsseen_nonnegative_of_upperTruncated_decay, ProbabilityTheory.exists_nonuniformBerryEsseen_of_upperTruncated_decay") (uses := "uniform-third-moment-berry-esseen, one-sided-truncation-comparison, upper-truncated-central-decay") (tags := "scalar, reduction, reflection, source-chen-shao-2005, fidelity-exact")
*Reduction from upper-truncated decay to the nonuniform theorem.* Suppose an
absolute $`A\ge0` satisfies the central exponential estimate in the preceding node for
all finite families.  Then there is an absolute
$`C=270+54A>0` such that every centered independent family with finite third moments
and unit total variance satisfies, for all $`x\in\mathbb R`,
$$`
\left|\Pr(W\le x)-\Phi(x)\right|
\le\frac{C\gamma}{1+|x|^3}.
`
:::

The positive-threshold argument follows {Citations.citet chenShao2005}[], Section 6.2, printed pp. 44--48:
the uniform theorem handles bounded $`x`, the truncation comparison
handles large jumps, and $`e^{-x/2}\le54/(1+x^3)` for $`x\ge2`.  Reflection of the
law supplies negative thresholds with the atom-safe $`(-x)+\varepsilon` limit required
by the closed-half-line CDF convention.

:::theorem "nonuniform-berry-esseen" (parent := "probability-scalar") (lean := "ProbabilityTheory.nonuniformBerryEsseen") (uses := "nonuniform-reflection-reduction") (tags := "principal-theorem, source-bikelis-1966, source-chen-shao-2005, scalar, fidelity-exact")
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
\left|\Pr(W\le x)-\Phi(x)\right|
\le
\frac{C\gamma}{1+|x|^3},
`
where $`\Phi` is the distribution function of a standard normal random variable.
:::

This finite-third-moment form goes back to {Citations.citet bikelis1966}[]. Theorem 2.2 and
the discussion following it in {Citations.citet chenShao2001}[], printed pp. 238--239, prove
the stronger truncated-moment version. The proof presented here follows Section 6.2 of
{Citations.citet chenShao2005}[], printed pp. 44--48, including the universal $`R_{2,2}`
estimate and an atom-safe reflection argument.
