# ProbabilityApproximation contributor contract

## Required reading and sources of truth

Read `SPEC.md` before planning, formalizing, or reviewing either release theorem. The specification
freezes the public signatures, representation choices, proof-source routing, and the distinction
between release blockers and optional Chen--Shao strengthenings.

The project has three maintained sources of truth:

1. The cited papers determine the complete mathematical statements and proof obligations.
2. Production declarations under `ProbabilityApproximation/**/*.lean` determine formal statements
   and kernel-checked proofs.
3. Verso sources under `blueprint-verso/ProbabilityApproximationBlueprint/**/*.lean` present a
   curated mathematical dependency graph, including both release flagships and the important
   intermediate results that explain their proofs.

Never silently weaken a theorem, add an assumption, change a normalization, or replace its domain.
Any deliberate generalization or representation bridge must be documented in the public
declaration and outside the mathematical statement block in the Blueprint.

## Release surface

The library has exactly two release flagship results:

- `ProbabilityTheory.nonuniformBerryEsseen`;
- `ProbabilityTheory.exists_bentkus_convex_set_constant`.

They are mathematically parallel: there is no dependency edge between the scalar and multivariate
routes. A one-dimensional specialization of Bentkus gives a uniform convex-set bound; it does not
supply the threshold decay in the scalar nonuniform theorem.

The repository Blueprint may expose a curated subset of mathematically recognizable intermediate
results: the Stein equation, concentration and truncation milestones, the residual decomposition,
the metric-projection/distance calculus, the Bentkus cutoff and smoothing inequality, Gaussian
companions, canonical probability-space transport, the low-order rotation cancellation, and the
Gaussian density derivative/contraction bound, covariance additivity and leave-one-out identity,
the Gaussian-companion second/third/mixed moment comparisons, covariance-square-root whitening,
signed-distance eikonal and level-frontier geometry, and outer/inner shell-slab identities, together
with the Lipschitz--Schwartz integration-by-parts bound, the trivial small-cardinality and
large-summand induction branches, leave-one-out whitening, normalized affine codimension-one
slicing, Ball's supporting-normal projection charts and exact Jacobian cancellation, the
rotation-invariant spherical moments, the radial Gaussian/Gamma peak, the Gaussian specialization
of integration by parts, the shell-localized cutoff derivative, the two Taylor remainder estimates,
the integrated second-order Gaussian-density remainder, the scalar parameter closure, and the major
perimeter/nonlinear-coarea and nontrivial replacement steps. Do not expose proof-local integrability,
coercion, measurability, or algebraic bookkeeping merely because its formal proof is substantial.

The exact `41 / 10` truncated uniform theorem and the finite-second-moment nonuniform Chen--Shao
theorem are optional strengthenings. They do not block the two frozen release targets and do not
create additional Blueprint nodes.

## Representation contract

- Use Mathlib's `Measure`, `Measure.map`, `cdf`, `gaussianReal`, `multivariateGaussian`, `MemLp`,
  `iIndepFun`, `covarianceBilin`, `Matrix.PosDef`, `CFC.sqrt`, and `toEuclideanCLM` directly.
- All convex-set APIs use `Convexity.IsConvexSet`. Do not add a legacy `Convex` public theorem, an
  exported compatibility bridge, or a bundled convex-set dependency.
- In the Bentkus theorem, `S` is the total covariance and the normalized summands use
  `(CFC.sqrt S)⁻¹`. Replacing this with `S⁻¹` changes the theorem.
- Convert both event measures from `ENNReal` to `ℝ` before subtraction.
- Individual summand covariances may be singular; only the total covariance is positive definite.
- The scalar theorem uses the existing CDF convention based on `Iic` and denominator
  `1 + |x| ^ 3`.

## Existing-theorem reuse gate

Before adding a declaration:

1. Search existing project modules with `rg` and `#check`.
2. Search the imported environment with `#check`, `#find`, `exact?`, `apply?`, and `rw?`.
3. Search `.lake/packages/mathlib/Mathlib` for an exact or more general result.
4. Specialize or add a narrow pure adapter before implementing a duplicate theorem.
5. Add a project lemma only for a demonstrated gap, and ensure it is used by the proof that
   motivated it.

The `jonwashburn/riemann` repository is reference-only proof prior art for Gaussian calculus. It is
not a dependency, and none of its types or namespaces may leak into public declarations.

## Proof and module policy

- Production Lean must contain no `sorry`, `admit`, project-defined `axiom`, `unsafe`, or
  `native_decide`.
- Do not introduce a declaration whose body is a placeholder or whose assumptions conceal a
  missing proof step.
- Do not disable heartbeat limits globally or add a global simplifier attribute for one proof.
- Keep mathematical definitions and proofs pure. Rendering, validation, PDF extraction, and CI
  belong at the repository edge.
- Organize modules by complete mathematical role. Keep single-use helpers with their theorem
  cluster and avoid `Core`, `Common`, `Utils`, numbered fragments, and thin forwarding modules.
- The root `ProbabilityApproximation.lean` must import every production module that belongs to the
  verified library.
- Module documentation must distinguish proved results, active gaps, and optional future work
  without claiming closure from scaffolding alone.

When parallel agents share a checkout, do not edit the same production module concurrently. Compile
an experimental source to temporary `.olean` and `.ilean` outputs before promoting it through Lake
if another task depends on the last green build artifact.

## Blueprint contract

Every Blueprint node has a complete human-readable mathematical statement containing its domains,
hypotheses, quantifiers, normalizations, and conclusion. Source and representation commentary stays
outside statement blocks. Each node carries precise source prose naming authors, title, year,
section/theorem/lemma/equation, and printed page where the source permits it.

An unfinished theorem has no `lean :=` association and carries the `source-open` tag. Never attach
a placeholder declaration or an unrelated weaker theorem to manufacture a formalized status. Add
an association and remove `source-open` only after the production declaration passes its narrow
build and fidelity review. The strict manifest baseline is derived from the curated sources and is
validated by `scripts/validate_manifest.py`; update that validator in the same change whenever a
node, declaration association, or reviewed dependency edge changes. Do not maintain a parallel
status ledger.

The scalar nonuniform flagship is associated with its proved declaration. The Bentkus whitening
and one-set transport are formalized, but the flagship and its genuinely unfinished
dimension-at-least-two Gaussian-perimeter/nonlinear-coarea and standardized-replacement
dependencies remain source-open. Never invent an edge between the scalar and multivariate routes
to make the graph connected.

Use the official Verso Blueprint UI and default `blueprint` theme. Do not replace its declaration
status, dependency, summary, or graph controls. Generated HTML, manifests, preview caches, and graph
data under `blueprint-verso/_out/` are build artifacts and must never be edited or committed.

## Build and verification flow

Run dependency setup only after the first clone or an intentional toolchain or dependency change:

```bash
lake update
lake exe cache get
cd blueprint-verso
lake update
lake exe cache get
```

During proof work, build the narrowest affected production module. Before handoff, run from the
repository root:

```bash
lake build ProbabilityApproximation
./.github/scripts/forbidden_tokens.sh
./.github/scripts/audit_axioms.sh
cd blueprint-verso
./scripts/site.sh build
```

During Blueprint editing, build the statement module before rendering the site:

```bash
cd blueprint-verso
lake build +ProbabilityApproximationBlueprint.Scalar
lake build +ProbabilityApproximationBlueprint.ConvexGeometry
lake build +ProbabilityApproximationBlueprint.Flagships
```

`site.sh build` runs the statement-style check, Blueprint library build, HTML render, strict
manifest validator, and `vbp check`. Inspect generated HTML through `site.sh serve`, not `file://`.
Run `./scripts/site.sh pdf` and inspect the rendered book whenever mathematical prose or displayed
formula layout changes materially.

## Version-control boundaries

- Never commit source PDFs, `.lake/`, temporary proof files, `.DS_Store`, browser QA output, or
  generated Blueprint `_out/` artifacts.
- Track production and Verso sources, toolchain files, Lake configuration and manifests, CI,
  validation scripts, README, AGENTS, SPEC, and LICENSE.
- Do not stage, commit, push, add a remote, or rewrite history unless the user explicitly requests
  it.
- Before a release commit, inspect the full staged file list and verify that every flagship status
  agrees across production Lean, Blueprint, manifest expectations, README, and AGENTS.
