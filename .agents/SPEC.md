# ProbabilityApproximation formalization specification

Status: engineering agreement; release theorem statements frozen; both principal theorems proved.

Baseline: Lean `v4.32.0`, Mathlib `v4.32.0`.

Primary consumers: Mathlib and FABL Chapter 5.

## 1. Decision and scope

This work is a standalone Lean library, provisionally named `ProbabilityApproximation`. It is not
an internal `FABL/Chapter05/ProbabilityLemmas` implementation directory. The mathematical results
are general probability infrastructure and should be developed independently, reviewed on their
own terms, and eventually offered upstream to Mathlib.

The library has exactly two principal targets:

1. The finite-third-moment nonuniform Berry--Esseen theorem used by O'Donnell's Chapter 5.
2. Bentkus's complete non-i.i.d. finite-dimensional Berry--Esseen theorem over all measurable
   convex sets and arbitrary positive-definite total covariance.

Chen--Shao's stronger nonuniform truncated theorem under only finite second moments remains a
desirable future strengthening, but it is not a release blocker for the Chapter 5 consumer.

The two results are parallel. Neither is a proof dependency of the other:

- The scalar nonuniform target is one-dimensional, tests half-lines through a CDF, and gives decay
  in the threshold.
- Bentkus is finite-dimensional, uniform in the location of the set, and tests every measurable
  convex set.
- Setting `d = 1` in Bentkus yields a uniform scalar estimate, not Chen--Shao's nonuniform decay.
- A scalar uniform or nonuniform theorem does not imply a multidimensional convex-set theorem.

They may share Mathlib-native Gaussian calculus, measure transport, moments, and integration by
parts. They must not be connected by a false theorem dependency merely to make a graph look
linear.

### 1.1 Current deliverable

Production Lean may contain only proved declarations. Do not add a `.lean` file containing `sorry`,
`axiom`, or a statement-only production declaration. Add each frozen declaration together with a
complete proof, or keep its experiment outside the production source tree.

### 1.2 Non-goals

The project does not initially aim to formalize:

- every version of Berry--Esseen in the literature;
- the best known scalar numerical constant;
- an abstract theory of all Stein operators;
- general Rosenthal inequalities for arbitrary exponents;
- a bundled theory of every class of test sets;
- Littlewood--Offord or other Chapter 5 anti-concentration results;
- a replacement probability hierarchy parallel to Mathlib;
- a compatibility layer for pre-`v4.32.0` convexity APIs.

## 2. Consumer and Blueprint boundary

FABL must not import this library until the relevant theorem is proved, the external library has a
versioned revision, and the consumer import has passed an axiom audit.

ProbabilityApproximation's own Blueprint records the curated internal proof architecture. Its
65 mathematical nodes cover the recognizable Stein, concentration, truncation, residual,
convex-geometric, Gaussian-perimeter, shell, rotation, induction, and whitening milestones leading
to the release theorems. It does not expose every production declaration: proof-local
measurability, integrability, coercion, reindexing, and algebraic bookkeeping remain below the
Blueprint boundary.

FABL is a downstream consumer and has a deliberately narrower boundary. When integration happens,
FABL receives exactly these two Blueprint-visible external support nodes:

- `ProbabilityTheory.nonuniformBerryEsseen`;
- `ProbabilityTheory.exists_bentkus_convex_set_constant`.

FABL does not reproduce the external repository's internal DAG. Other genuine Chapter 5 book items
remain visible in FABL's normal chapter inventory; this two-node rule concerns only the imported
ProbabilityApproximation interface. The stronger truncated Chen--Shao theorem may later share the
scalar node if completed, but it must not block or replace the book-facing declaration. If its
formal proof reveals an independently recognizable mathematical milestone, the external
ProbabilityApproximation Blueprint may instead admit that milestone under its normal curation rule;
FABL's two-node import boundary remains unchanged.

If the exact book statement is a specialization, FABL should prove a thin local corollary from the
external theorem. The Blueprint may associate both the complete external theorem and the thin
book-facing declaration with the same mathematical node. It must not restate or duplicate the long
external proof.

## 3. Mathlib `v4.32.0` audit and representation policy

The latest baseline materially simplifies the project. The following are already in Mathlib and
must be used directly:

| Mathematical object | Required Mathlib API |
|---|---|
| Scalar normal law | `gaussianReal 0 1` |
| Scalar CDF | `cdf`, `cdf_eq_real` |
| Finite-dimensional standard normal | `stdGaussian` |
| Gaussian with covariance matrix | `multivariateGaussian 0 S` |
| Centered covariance bilinear form | `covarianceBilin` |
| Gaussian covariance computation | `covarianceBilin_multivariateGaussian` |
| Independence | `iIndepFun`, `IndepFun` |
| Moment hypotheses | `MemLp` |
| Positive-definite covariance | `Matrix.PosDef` |
| Matrix square root and inverse | `CFC.sqrt`, matrix inverse, `Matrix.inv_sqrt` |
| Euclidean linear map of a matrix | `toEuclideanCLM` |
| Convex-set predicate | `Convexity.IsConvexSet` |
| Law transport | `Measure.map`, `MeasurePreserving`, `HasLaw` |

The audit did not find a Mathlib theorem for Berry--Esseen, Chen--Shao, Bentkus, Gaussian convex
perimeter, a Gaussian Stein equation, or the required convex-set smoothing estimate.

### 3.1 Convexity is new-API only

All new public and internal geometry must use `Convexity.IsConvexSet`. Do not define an
`IsConvexSet ↔ Convex` bridge, do not offer a duplicate theorem using the legacy `Convex` predicate,
and do not introduce a bundled `ConvexSet` dependency.

If a specific Mathlib lemma has not yet migrated from legacy `Convex`, the coding agent must:

1. search for a new-API replacement;
2. prefer proving the needed fact directly with `Convexity.IsConvexSet` primitives;
3. if unavoidable, perform a one-off conversion inside that proof only;
4. avoid exporting the conversion as project API;
5. consider upstreaming the missing new-API lemma.

### 3.2 Gaussian integration by parts and the Riemann repository

The code under
[`jonwashburn/riemann/Riemann/Mathlib/Probability/Distributions`](https://github.com/jonwashburn/riemann/tree/main/Riemann/Mathlib/Probability/Distributions)
may be inspected as a proof prototype for Gaussian density and integration-by-parts leaves. It is
not a dependency and must not appear in `lakefile.toml`.

Its possible contribution is narrow:

- formulas for Gaussian density derivatives;
- scalar or finite-dimensional Gaussian integration by parts;
- examples of discharging differentiability and integrability side conditions.

It does not supply convex geometry, Ball's perimeter theorem, a coarea bridge, Bentkus's cutoff,
probability-space enlargement, Chen--Shao concentration, or Bentkus's induction. Any useful proof
must be ported to current Mathlib objects behind a Mathlib-native theorem statement. No Riemann
type or namespace may leak into either principal theorem.

### 3.3 Important covariance distinction

Use `covarianceBilin`, which is centered. Do not use Mathlib's current `covarianceOperator` in the
Bentkus statement: its source documentation explicitly describes it as an uncentered covariance
operator.

## 4. Frozen target A: nonuniform Berry--Esseen

The release target is the finite-third-moment nonuniform form used by O'Donnell. The already proved
`uniformBerryEsseen_thirdMoment`, with universal constant `30`, satisfies the ordinary uniform
Berry--Esseen dependency. Chen--Shao 2001, Theorems 2.1 and 2.2, are stronger future targets because
they assume only finite second moments and use truncated moments.

The release name, quantifier order, moment strength, denominator, and CDF representation in Section
4.3 are immutable unless a statement-fidelity review approves a change.

### 4.1 Optional exact uniform truncated strengthening

```lean
theorem chenShao_uniformBerryEsseen_truncated
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (h_memLp : ∀ i, MemLp (X i) 2 μ)
    (h_variance : (∑ i, variance (X i) μ) = 1) :
    ∀ x : ℝ,
      |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤
        (41 / 10 : ℝ) * ∑ i,
          ((∫ ω in {ω | 1 < |X i ω|}, (X i ω) ^ 2 ∂μ) +
            ∫ ω in {ω | |X i ω| ≤ 1}, |X i ω| ^ 3 ∂μ)
```

This is Chen--Shao 2001, Theorem 2.1, with the exact constant `4.1 = 41 / 10`. It is not a Blueprint
target or release blocker. The Chapter 5 release path uses the proved full-third-moment uniform
theorem with constant `30`; the exact truncated result is retained only as a future strengthening.

### 4.2 Optional complete nonuniform truncated strengthening

```lean
theorem chenShao_nonuniformBerryEsseen_truncated :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ι → Ω → ℝ),
        (∀ i, Measurable (X i)) →
        iIndepFun X μ →
        (∀ i, ∫ ω, X i ω ∂μ = 0) →
        (∀ i, MemLp (X i) 2 μ) →
        (∑ i, variance (X i) μ) = 1 →
        ∀ x : ℝ,
          |cdf (μ.map fun ω ↦ ∑ i, X i ω) x -
              cdf (gaussianReal 0 1) x| ≤
            C * ∑ i,
              ((∫ ω in {ω | 1 + |x| < |X i ω|},
                  (X i ω) ^ 2 ∂μ) / (1 + |x|) ^ 2 +
                (∫ ω in {ω | |X i ω| ≤ 1 + |x|},
                  |X i ω| ^ 3 ∂μ) / (1 + |x|) ^ 3)
```

Future-strengthening interpretation:

- `C` is outside every type, probability space, finite index type, family, and threshold. It is an
  absolute universal constant.
- The family is indexed by an arbitrary finite type, not only `Fin n`.
- `cdf` uses `Iic`, so the left side is the paper's `P(W ≤ x)` convention.
- The theorem assumes `MemLp 2`, not `MemLp 3`.
- The first truncation is strict `1 + |x| < |Xᵢ|`; the second is non-strict
  `|Xᵢ| ≤ 1 + |x|`. Together they partition the sample space.
- The paper normalizes `Var(W) = 1`. The Lean statement uses
  `∑ i, variance (X i) μ = 1`; independence proves the equivalence. This is an explicit
  representation bridge, not a strengthening.
- The project must not invent another CDF or a project-specific moment record.

### 4.3 Frozen finite-third-moment release theorem

```lean
theorem nonuniformBerryEsseen :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ι → Ω → ℝ),
        (∀ i, Measurable (X i)) →
        iIndepFun X μ →
        (∀ i, ∫ ω, X i ω ∂μ = 0) →
        (∀ i, MemLp (X i) 3 μ) →
        (∑ i, variance (X i) μ) = 1 →
        ∀ x : ℝ,
          |cdf (μ.map fun ω ↦ ∑ i, X i ω) x -
              cdf (gaussianReal 0 1) x| ≤
            C * (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) /
              (1 + |x| ^ 3)
```

This is the scalar release target. It may be proved directly from the finite-third-moment branches
or derived later from the optional stronger theorem. For the latter route, let `r = 1 + |x|`. On
the tail `r < |Xᵢ|`,

```text
Xᵢ² / r² ≤ |Xᵢ|³ / r³.
```

Combining the tail with the complementary truncated third moment gives the full third moment over
`r³`. Finally `(1 + |x|)³ ≥ 1 + |x|³`. O'Donnell's notes attribute this finite-third-moment
nonuniform form historically to Bikelis.

The completed `uniformBerryEsseen_thirdMoment` at constant `30` supplies the bounded-threshold
branch.  The proved release theorem obtains the nonuniform decay for large `|x|` directly from
the finite-third-moment Chen--Shao route; it does not require closing the exact `41 / 10`
truncated theorem first.

### 4.4 What this target does not claim

The release theorem has an unspecified absolute constant. The proved uniform constant `30` is
sufficient for O'Donnell's `O(γ)` uses; obtaining the sharper numerical constant mentioned in the
book is a different project. The optional exact uniform truncated target keeps Chen--Shao's `4.1`.

## 5. Frozen target B: Bentkus

The following statement has been elaboration-checked against Mathlib `v4.32.0`. It represents
Bentkus 2004, Theorem 1.1: independent but not necessarily identically distributed summands,
arbitrary positive finite dimension, positive-definite total covariance, and all measurable convex
sets.

```lean
import Mathlib.Analysis.Matrix.Order
import Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Geometry.Convex.Set
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.Basic

open MeasureTheory Matrix
open scoped MatrixOrder RealInnerProductSpace

namespace ProbabilityTheory

local instance {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

/-- Bentkus's multivariate Berry--Esseen theorem for measurable convex sets. -/
theorem exists_bentkus_convex_set_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d n : ℕ} (_hd : 0 < d)
        {Ω : Type*} [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Fin n → Ω → EuclideanSpace ℝ (Fin d))
        (S : Matrix (Fin d) (Fin d) ℝ),
        (∀ i, MemLp (X i) 3 μ) →
        iIndepFun X μ →
        (∀ i, ∫ ω, X i ω ∂μ = 0) →
        S.PosDef →
        (∀ x y,
          covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y =
            x ⬝ᵥ S *ᵥ y) →
        ∀ A : Set (EuclideanSpace ℝ (Fin d)),
          MeasurableSet A →
          Convexity.IsConvexSet ℝ A →
          |((μ.map (fun ω ↦ ∑ i, X i ω)) A).toReal -
              (multivariateGaussian 0 S A).toReal| ≤
            C * (d : ℝ) ^ (1 / 4 : ℝ) *
              ∑ i, ∫ ω,
                ‖(toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) (X i ω)‖ ^ 3 ∂μ

end ProbabilityTheory
```

Frozen interpretation:

- The matrix `S` is the paper's total covariance `C²`; it is not the paper's random sum, also
  denoted `S` in prose.
- `(CFC.sqrt S)⁻¹` is the paper's `C⁻¹ = (C²)⁻¹/²`. Replacing it by `S⁻¹` would be mathematically
  wrong.
- `multivariateGaussian 0 S` is the centered Gaussian law with the same covariance.
- The pointwise assertion for every `A` is equivalent to bounding the supremum over the convex-set
  class, while avoiding an irrelevant supremum API in the public theorem.
- Both probabilities are converted from `ENNReal` to `ℝ` before subtraction. `ENNReal` subtraction
  is truncated and cannot represent a signed Berry--Esseen error.
- `MeasurableSet A` is necessary. Set-theoretic convexity alone does not make an arbitrary set a
  valid measurable event.
- `S.PosDef` supplies symmetry/Hermitianity, positive semidefiniteness, and invertibility.
- Individual summand covariance matrices may be singular. Only the total covariance is positive
  definite.
- `n = 0` needs no separate exclusion: with `d > 0`, the covariance identity and `S.PosDef` cannot
  both hold for an empty sum.
- Bentkus 2004 asserts an unspecified absolute constant. The number `400` belongs to Bentkus 2003's
  i.i.d. result and must not be inserted here.

## 6. Repository architecture

The repository has one public facade and mathematically cohesive proof modules.  The compact tree
below records the stable mathematical boundaries; individual proof-bearing modules within these
directories may be more finely divided when a complete reusable theorem cluster warrants it:

```text
ProbabilityApproximation.lean
ProbabilityApproximation/
  Stein/
    IndicatorSolution.lean
  ChenShao/
    ... scalar concentration, truncation, Stein, and release modules ...
  ConvexGeometry/
    ... parallel sets, cutoff, coarea, and Ball perimeter modules ...
  Bentkus/
    ... companions, Gaussian calculus, and whitening modules ...
    Induction/
      IdentityCovarianceReduction.lean
      GaussianDensityComparison.lean
      SplitGaussianShell.lean
      SmallAngleEstimate.lean
      LargeAngleEstimate.lean
    Induction.lean
```

The layout rules are:

- `ProbabilityApproximation.lean` is a small consumer facade.
- Do not create `Common`, `Utils`, `ToMathlib`, or numbered fragment files.
- Keep paper-specific bookkeeping `private` when it can live in the final proof module.
- Extract a public helper only if it is mathematically coherent and genuinely reusable, such as a
  Gaussian integration-by-parts theorem or a Gaussian convex-shell bound.
- Do not expose constants named only `C₁`, `R3`, `aux_7`, or by equation number.
- If a proof cluster must cross module boundaries, give it a mathematical namespace and a stable
  statement; otherwise keep the cluster in one cohesive file.
- The implementation namespace `ProbabilityTheory.BentkusInduction` contains only the cross-stage
  contracts needed by the five proof-bearing induction modules. The six Blueprint-visible
  Gaussian-remainder and theorem endpoints remain in `ProbabilityTheory` with stable public names.
- `ProbabilityApproximation.Bentkus.Induction` is the stable consumer entry point and owns the
  angle assembly, smooth/shell composition, ordinary induction closure, and both existential
  endpoints; it is not a duplicate theorem facade.
- The public facade should emphasize the two principal theorems and the proved uniform theorem. It
  should not advertise proof scaffolding.

## 7. Chen--Shao proof plan

### 7.1 Mathlib-native probability leaves

Close these before beginning the main estimates:

1. Measurability of `W := fun ω ↦ ∑ i, X i ω`.
2. The probability-measure instance for `μ.map W`.
3. Bridges between `cdf`, `Measure.real (Iic x)`, and preimages under `Measure.map`.
4. `MemLp 2` consequences for expectation, variance, truncation, and centering.
5. Measurability and integrability of all displayed truncated integrands.
6. `iIndepFun.comp` for truncated variables.
7. Independence of `Xᵢ` and leave-one-out sums.
8. Variance additivity under independence and the equivalence of the chosen normalization with
   `Var(W) = 1`.

This is not bookkeeping trivia. Mathlib's Bochner integral is defined even for a non-integrable
function, with fallback behavior that would not mean the paper's expectation. Every use of a
displayed integral must carry the correct integrability proof.

### 7.2 Gaussian and Stein analytic trunk

Follow Chen--Shao 2005, Sections 2.1--2.3 and Appendix Section 8 for details that the 2001 paper
cites or compresses:

1. Use `gaussianPDFReal 0 1` and `cdf (gaussianReal 0 1)`; do not redefine `φ` or `Φ` as competing
   public objects.
2. Prove Gaussian symmetry, no-atoms/continuity, and the Mills-ratio inequalities used in (8.1).
3. Define the indicator Stein solution `f_z` exactly as in (2.2)--(2.3).
4. Prove the Stein equation with the correct pointwise exception/convention at `z`.
5. Prove the bounds collected in 2005 Lemma 2.2, including bounds on `f_z`, `f'_z`, and `w f_z(w)`.
6. Formalize the kernel identity `Kᵢ(t)` and formulas (2.16)--(2.19).
7. Build the required interval-integral and Fubini/Tonelli bridges.

The 2001 proof cites Stein 1986, pages 22--28, for several of these facts. Prefer the more explicit
2005 derivations, using Stein 1986 only as an audit source.

### 7.3 Optional exact uniform truncated branch

This section is a future strengthening and does not block the Chapter 5 release.

Follow Chen--Shao 2001, Sections 3--4:

1. Formalize elementary facts (F1) and (F2).
2. Prove Lemma 3.1, the lower-deviation expectation bound for a nonnegative independent sum.
3. Define the local proof quantities `α`, `β`, and `δ` privately.
4. Prove Proposition 3.2:

   ```text
   P(a ≤ W⁽ⁱ⁾ ≤ b) ≤ 1.5 (b - a) + 3.3 δ
   ```

   under the paper's small-error condition.
5. Establish the truncated Stein identity (4.1).
6. Reproduce the `R₁ + R₂ + R₃ + R₄` decomposition (4.3).
7. Separate the large-error branch, handled by a trivial tail estimate, from the small-error
   branch controlled by Proposition 3.2 and the Stein bounds.
8. Prove both sides of the CDF error and close the exact `41 / 10` constant.

### 7.4 Release nonuniform concentration branch

Follow Chen--Shao 2005, Section 6.1, which directly matches the finite-third-moment release target:

1. Define the one-sided truncation `ξ̄ᵢ = ξᵢ 1_{ξᵢ ≤ 1}` and its leave-one-out sum.
2. Prove the Bennett--Hoeffding MGF inequality, Lemma 6.2, including the `t = 1/2` specialization.
3. Formalize the exponential ramp (6.6) and the mixed kernel `M_j(t)` used in (6.7).
4. Prove the kernel-mass lower bound corresponding to (6.8) and the centered-fluctuation estimate
   corresponding to (6.10). Any correction for the positive tail removed by `ξ̄ᵢ` must remain
   explicit; do not copy a compressed paper equality if its truncation correction is omitted.
5. Close Proposition 6.1 in the absolute-constant form

   ```text
   P(a ≤ W̄⁽ⁱ⁾ ≤ b) ≤ exp (-a / 2) * (C₁ * (b - a) + C₂ * γ).
   ```

The exact printed constants `5` and `7` are not part of the frozen API. A rigorously proved pair of
absolute constants is sufficient. Chen--Shao 2001, Proposition 3.4, remains relevant to the
optional finite-second-moment strengthening, not to the release dependency path.

### 7.5 Final scalar release branch

Follow Chen--Shao 2005, Section 6.2, Theorem 6.4:

1. Use the proved `p = 3` moment inequality to control the original sum and every leave-one-out
   partial sum.
2. For `γ ≤ 1` and large nonnegative `z`, compare the original upper tail to the one-sided
   truncated upper tail as in (6.13)--(6.14); bound the exceptional large-coordinate events by
   third-moment Markov and independence.
3. Derive the noncentered truncated Stein identity and reproduce the three residuals `R₁`, `R₂`,
   and `R₃` in (6.16).
4. Control `R₁` and `R₃` by the Stein-solution/Mills bounds and the Bennett MGF estimate.
5. Split `R₂` into the indicator jump and `w f_z(w)` increment. Apply Proposition 6.1 to the first
   part and prove the analogue of Lemma 6.5 for the second.
6. Convert the resulting `C exp (-z / 2) γ` estimate to `C γ / (1 + z³)`. Use the constant-`30`
   uniform theorem for bounded `z` and the trivial probability bound for `γ ≥ 1`.
7. Apply the same nonnegative-threshold result to the negated family. For `x < 0`, pass from strict
   reflected complements to `Iic x` by continuity from above; do not assume the summand law has no
   atoms.

The last step cannot be a careless one-line symmetry rewrite. Reflection turns a weak CDF event
into a strict tail. A safe Lean route applies the reflected result at `-x - ε`, sends `ε ↓ 0`, and
uses continuity from above plus continuity of the Gaussian CDF.

### 7.6 Chapter 5 specialization phase

After `nonuniformBerryEsseen` is closed:

1. specialize to normalized weighted Rademacher sums;
2. prove the exact O'Donnell Exercise 5.31(d) form required by FABL;
3. retain the constant-`30` theorem as the ordinary uniform API.

Chen--Shao 2005, Theorem 6.4 is the primary proof route for the finite-third-moment release theorem.
The stronger 2001 truncated theorem remains optional.

## 8. Bentkus proof plan

Bentkus 2004 is not self-contained. Its non-i.i.d. induction depends on smoothing and geometric
machinery developed in Bentkus 2003, and its `d^(1/4)` dependence ultimately comes from Ball's
Gaussian perimeter theorem. Raič 2019 supplies a careful modern perimeter-to-shell bridge.

### 8.1 Convex geometry and parallel sets

1. Work only with `Convexity.IsConvexSet`.
2. Fix open/closed conventions for outer enlargement and inner erosion before proving estimates:
   distinguish `Metric.thickening`, `Metric.cthickening`, and signed-distance level sets.
3. Prove convexity, measurability, translation behavior, and invertible-linear-map transport for the
   chosen parallel sets.
4. Build the finite-dimensional nearest-point and distance regularity needed by the cutoff:
   uniqueness for a closed convex set, Lipschitz distance, signed distance, and the necessary
   differentiability statements.

Never switch between `< ε` and `≤ ε` by simplification. Boundary nullity must be proved at the exact
place where it is used.

### 8.2 Ball perimeter and the shell theorem

Formalize Ball 1993, Theorem 4, with the exact domain audit. The paper directly treats convex
bodies in dimension at least two. The final theorem also needs explicit handling of:

- `d = 1`;
- `∅` and `univ`;
- unbounded convex sets;
- lower-dimensional convex sets;
- approximation of general measurable convex sets.

Then follow Raič 2019, Proposition 3.1 and its supporting results to obtain the outer and inner
Gaussian shell estimates

```text
γ_d(A^ε ∖ A) ≤ 4 d^(1/4) ε,
γ_d(A ∖ A^-ε) ≤ 4 d^(1/4) ε.
```

Mathlib does not presently provide this exact signed-distance shell theorem as one declaration.
Keep the finite-dimensional area/projection input and the one-dimensional signed-distance coarea
argument isolated as independently reviewable theorem clusters suitable for upstreaming.

### 8.3 Smooth convex cutoff

Follow Bentkus 2003's distance-function construction and Bentkus 2004, Lemma 2.2. For `ε > 0`
construct a `C¹` cutoff satisfying

```text
0 ≤ φ ≤ 1,
φ = 1 on A,
φ = 0 outside A^ε,
‖Dφ‖ ≤ 2 / ε,
‖Dφ(x) - Dφ(y)‖ ≤ 8 ‖x-y‖ / ε².
```

Mathlib's continuous/Lipschitz thickened indicator is not a substitute: the Bentkus Taylor
estimates need derivative and Lipschitz-gradient control.

Use the cutoff to prove Bentkus 2004, Lemma 2.1, converting convex-set probability error into a
smooth expectation error plus Gaussian shell terms.

### 8.4 Gaussian calculus

Establish the Mathlib-native finite-dimensional Gaussian facts needed in Section 3:

1. density representations for `stdGaussian` and transported `multivariateGaussian`;
2. first through third Fréchet derivatives of the density or the exact contracted forms used in
   Bentkus;
3. directional Gaussian moment bounds;
4. second- and third-order Taylor remainder estimates;
5. Gaussian integration by parts, especially (3.16);
6. Bentkus 2004, Lemma 2.3, transferring density derivatives against a shell-supported Lipschitz
   function.

This is the only area where the Riemann code may save work. Port results individually and prove
them against `stdGaussian`/`multivariateGaussian`; never add the repository as a dependency.

### 8.5 Gaussian companions and probability-space transport

For every summand construct a centered Gaussian companion `Yᵢ` with the same covariance as `Xᵢ`.
Each individual covariance may be positive semidefinite and singular. Prove the matched-covariance
third-moment comparison needed by the paper.

Do not assume the user's probability space already supports independent Gaussian variables or a
uniform angle. Move the original family to a canonical law/product space, take products with the
Gaussian laws and the angle law, and transport the final statement back. No atomless or
"sufficiently rich probability space" hypothesis may enter the principal theorem.

### 8.6 Rotation and non-i.i.d. induction

First prove the identity-total-covariance form. Follow Bentkus 2004, Section 3:

1. set up induction on the number of summands;
2. close the small-`n` and large-individual-covariance trivial branches;
3. construct leave-one-out sums and covariance inverses;
4. let `α` be uniform on `[0, π/2]`, with `p = cos α`, `q = sin α`;
5. rotate `Xᵢ` toward its Gaussian companion and prove (3.4)--(3.5);
6. use equality of first and second moments to cancel low-order Taylor terms;
7. split the angle range and prove the estimates corresponding to (3.13), (3.14), and (3.15);
8. invoke the induction hypothesis only after correctly whitening the leave-one-out family;
9. choose `sin γ = ε`;
10. use the paper's exact parameter choice `ε = β * sqrt M`, not `sqrt (β / M)`;
11. choose a sufficiently large universal `M` to close the final inequality.

The parameter choice in step 10 is visible on Bentkus 2004, p. 404, immediately after (3.9). It is
easy for OCR or informal notes to reverse the scaling; the coding agent must keep the scanned page
open when closing this calculation.

### 8.7 Whitening wrapper

After the identity-covariance theorem is proved, derive the frozen general theorem:

1. set `B = (CFC.sqrt S)⁻¹`;
2. map every summand by `B`;
3. prove that the total covariance becomes the identity using `covarianceBilin` and the matrix square
   root/inverse API;
4. transport measurability and `Convexity.IsConvexSet` through the invertible linear map;
5. identify the transformed third moment with the displayed normalized moment;
6. transport `stdGaussian` back to `multivariateGaussian 0 S`.

This wrapper is the only place the public covariance matrix should be inverted. Do not assume each
summand covariance is invertible.

## 9. Source package and PDF acquisition

All papers should be downloaded into an ignored local directory such as `references/papers/` or
`tmp/references/`. Do not commit copyrighted PDFs. Preserve descriptive filenames and record the
source URL in the coding task.

### 9.1 Mandatory Chen--Shao sources

1. **Chen and Shao 2001, "A non-uniform Berry--Esseen bound via Stein's method"**

   - [Author PDF](https://cpb-us-w2.wpmucdn.com/blog.nus.edu.sg/dist/3/10976/files/2019/01/P25-12vbxv4.pdf)
   - [DOI](https://doi.org/10.1007/PL00008782)
   - Formalize Theorems 2.1 and 2.2, Lemma 3.1, Propositions 3.2 and 3.4, Sections 4--5, and the
     paper's final appendix/section.

2. **Chen and Shao 2005, "Stein's method for normal approximation"**

   - [Author PDF](https://blog.nus.edu.sg/louischen/files/2019/01/IMS4-pp-1-59-2hma1np.pdf)
   - Use Sections 2.1--2.3, Sections 6.1--6.2, and Appendix Section 8 for detailed Stein-solution,
     Mills-ratio, concentration, and finite-third-moment proofs.

3. **O'Donnell 2021, _Analysis of Boolean Functions_**

   - [arXiv page](https://arxiv.org/abs/2105.10386)
   - [PDF](https://arxiv.org/pdf/2105.10386)
   - Use Section 5.2, Exercise 5.31(d), Exercise 5.33, and the Chapter 5 notes. This is the normative
     FABL consumer statement, not the source for the long probability proofs.

### 9.2 Mandatory Bentkus sources

4. **Bentkus 2004/2005, "A Lyapunov-type bound in R^d"**

   - [MathNet article](https://www.mathnet.ru/eng/tvp230)
   - [MathNet PDF endpoint](https://www.mathnet.ru/php/getFT.phtml?jrnid=tvp&paperid=230&what=fullt)
   - [English DOI](https://doi.org/10.1137/S0040585X97981123)
   - [Original DOI](https://doi.org/10.4213/tvp230)
   - This is the normative source for Theorems 1.1--1.2 and the non-i.i.d. induction in Section 3.

   Page guide for the original pagination:

   - pp. 400--402: definitions, final theorem, abstract set-class engine, smoothing lemmas;
   - pp. 403--404: covariance normalization, induction, companions, rotation, (3.1)--(3.15);
   - pp. 404--406: Gaussian branch, integration by parts, Taylor and density derivatives;
   - pp. 406--408: small-angle and induction/shell estimates;
   - pp. 408--410: middle branch and final cancellations.

5. **Bentkus 2003, "On the dependence of the Berry--Esseen bound on dimension"**

   - [DOI](https://doi.org/10.1016/S0378-3758(02)00094-0)
   - [MPIM archive](https://archive.mpim-bonn.mpg.de/id/eprint/853/)
   - [CERN record](https://cds.cern.ch/record/735778)
   - [CERN PostScript](https://cds.cern.ch/record/735778/files/sis-2004-211.ps)
   - Convert the official PostScript with `ps2pdf` if a PDF is required locally.
   - Use it for convex distance regularity, the `C¹` cutoff, smoothing machinery, and the i.i.d.
     predecessor argument. Do not attempt to obtain the non-i.i.d. theorem by applying its i.i.d.
     main theorem.

6. **Ball 1993, "The Reverse Isoperimetric Problem for Gaussian Measure"**

   - [GDZ PDF](https://gdz.sub.uni-goettingen.de/download/pdf/PPN362609810_0010/LOG_0035.pdf)
   - [DOI](https://doi.org/10.1007/BF02573986)
   - Formalize Lemma 3 and Theorem 4, especially pp. 414--419. Audit and extend the paper's domain
     before claiming the final measurable-convex-set shell result.

7. **Raič 2019, "A multivariate Berry--Esseen theorem with explicit constants"**

   - [arXiv page](https://arxiv.org/abs/1802.06475)
   - [arXiv PDF](https://arxiv.org/pdf/1802.06475)
   - [Author PDF](https://osebje.famnit.upr.si/~martin.raic/Raziskovanje/Dat/BEJ1072_FINAL.pdf)
   - [DOI](https://doi.org/10.3150/18-BEJ1072)
   - Use Section 3, especially Proposition 3.1 and its area/coarea and signed-distance support, to
     make the Ball-perimeter-to-shell step rigorous. Do not silently replace the Bentkus proof by
     Raič's separate Stein proof.

### 9.3 Optional audit source

8. **Stein 1986, _Approximate Computation of Expectations_**

   - [Project Euclid edition](https://projecteuclid.org/eBooks/institute-of-mathematical-statistics-lecture-notes-monograph-series/Approximate-computation-of-expectations/toc/10.1214/lnms/1215466568)
   - Chen--Shao 2001 cites pp. 22--28. Chen--Shao 2005 supplies enough expanded detail that this
     should remain an audit source rather than a hard proof dependency.

There is no need to download Petrov 1995, the full Rosenthal 1970 paper, or the Bikelis 1966
original for the initial implementation. Use the explicit fourth-moment expansion above and cite
Bikelis only for historical attribution.

## 10. Coding-agent task decomposition

Every task must name one declaration or one tightly coupled theorem cluster, its allowed files,
immutable statement choices, proof source pages, prerequisites, scratch build command, and exact
completion criteria. Parallel agents must not edit the same module.

### 10.0 Proof construction style

When implementing proofs, coding agents must follow these rules (orthogonal to the phase list below):

- **Incremental tactics.** Write proofs step by step: one tactic, or one tightly scoped local lemma,
  at a time. Do not generate an entire multi-step proof script in one shot.
- **Elegant and brief.** Prefer short local proofs. Avoid unnecessary helpers, scaffolding modules,
  and verbose rewrite chains when a single Mathlib fact closes the goal.
- **Mathlib first.** Before inventing a project-local lemma, search Mathlib (and the required APIs in
  §3) for an existing theorem that applies; reuse it rather than duplicating Mathlib content. See
  also §3.1 for the convexity migration search order.

Recommended sequence:

### Phase A: scalar foundation

- **A1 -- law/CDF bridge:** `cdf`, `Measure.map`, finite sums, integrability, variance additivity.
- **A2 -- indicator Stein solution:** Chen--Shao 2005 Sections 2 and 8.
- **A3 -- uniform concentration foundation:** the existing concentration leaves used by the
  constant-`30` theorem.
- **A4 -- accepted uniform theorem:** `uniformBerryEsseen_thirdMoment` with constant `30` (complete).
- **A5 -- nonuniform concentration:** finite-third-moment form of the required large-threshold estimates.
- **A6 -- scalar principal theorem:** `nonuniformBerryEsseen`, including atom-safe negative
  thresholds.
- **A7 -- Chapter 5 specialization:** normalized weighted Rademacher sums and Exercise 5.31(d).
- **A8 -- optional strengthening:** Chen--Shao Proposition 3.2 and Theorems 2.1--2.2 with
  truncated moments.

### Phase B: convex geometry and Gaussian foundation

- **B1 -- new convex API parallel sets:** only `Convexity.IsConvexSet`.
- **B2 -- Ball theorem:** exact convex-body theorem plus domain completion.
- **B3 -- coarea/shell bridge:** Raič Proposition 3.1 cluster, packaged for upstream review.
- **B4 -- smooth cutoff:** Bentkus 2003 and 2004 Lemma 2.2.
- **B5 -- finite-dimensional Gaussian calculus:** density derivatives, Taylor, and IBP.
- **B6 -- Gaussian companions:** PSD individual covariances and third moments on a canonical product
  probability space.

### Phase C: Bentkus assembly

- **C1 -- smoothing inequality:** Bentkus 2004 Lemmas 2.1--2.3.
- **C2 -- rotation identity:** equations (3.4)--(3.5) and moment cancellations.
- **C3 -- induction branches:** estimates (3.13)--(3.15) with exact parameter choices.
- **C4 -- identity-covariance theorem:** finish Theorem 1.2 for convex sets.
- **C5 -- whitening wrapper:** prove the frozen general-covariance public theorem.

### Phase D: independent audits

- **D1 -- statement fidelity:** compare every hypothesis, quantifier, event convention, covariance,
  and constant with the papers.
- **D2 -- axiom/import audit:** ensure no hidden classical axiom beyond Lean's accepted foundations,
  no `sorry`, no project axiom, no Riemann dependency, and no untracked source module.
- **D3 -- consumer audit:** import the release into a clean FABL worktree and prove only the thin
  Chapter 5 specializations.

## 11. Risk register and stop rules

| Risk | Required response |
|---|---|
| Coarea/area formula missing from Mathlib | Isolate the finite-dimensional theorem actually needed; prepare it for upstream review before Bentkus assembly. |
| Ball only treats convex bodies and `d ≥ 2` | Prove all extension cases explicitly; never strengthen the principal theorem's assumptions. |
| Individual covariance is singular | Use PSD Gaussian companions; never add per-summand `PosDef`. |
| Original probability space cannot host auxiliaries | Move to canonical product laws; never assume atomless or rich source spaces. |
| Bochner integral is written without integrability | Stop and close the `MemLp`/integrability leaf before continuing. |
| Legacy `Convex` theorem encountered | Search new API, prove directly, or convert locally; do not create a bridge API. |
| OCR changes Bentkus parameters | Check the scan. In particular, p. 404 chooses `ε = β sqrt M`. |
| Gaussian IBP proof becomes a dependency tangle | Port a narrow Mathlib-native theorem; do not add the Riemann repository. |
| Chen--Shao negative-threshold reflection ignores atoms | Use an epsilon limit and measure continuity. |
| A generic paper constant changes from line to line | Give helper constants separate local names and explicitly combine them at the final theorem. |
| A proof of the optional complete truncated Chen theorem requires `MemLp 3` | Reject that strengthening route; the optional theorem deliberately assumes only `MemLp 2`. |
| A proposed Bentkus result uses `400` | Reject it unless the target is explicitly changed to an i.i.d. or Raič theorem. |

If blocked, the coding agent must report the exact Lean goal, searched Mathlib declarations,
paper equation, attempted proof shapes, and the smallest missing mathematical lemma. It must not
weaken a target statement, add a density assumption, or leave speculative public APIs behind.

## 12. Verification and completion gates

A principal theorem is complete only when all of the following pass:

1. The frozen signature elaborates without modification.
2. The proof contains no `sorry`, `admit`, project `axiom`, `unsafe`, or `native_decide`.
3. The package root imports every production module.
4. A clean `lake build` succeeds under the pinned stable Lean/Mathlib version.
5. `#print axioms` for both principal theorems shows only the accepted foundational axioms already
   used by Mathlib.
6. An independent statement audit checks quantifier order, moment strength, CDF boundary,
   covariance convention, set measurability, convexity, whitening, and constant scope.
7. The scalar principal theorem proves O'Donnell's finite-third-moment nonuniform bound, and its weighted
   Rademacher specialization is available to FABL.
8. The Bentkus general-covariance result is proved from the normalized theorem by a verified
   whitening transport.
9. The project has no dependency on FABL or the Riemann repository.
10. A clean FABL consumer imports the external facade and its Blueprint exposes only the two
    principal probability-approximation nodes.

The release handoff must state the exact dependency revision, clone/update commands, public import
path, two declaration names, and the results of the build, forbidden-token, and axiom audits.
