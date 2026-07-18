# ProbabilityApproximation contributor contract

## Required reading and sources of truth

Read `.agents/SPEC.md` before planning, formalizing, or reviewing either principal theorem. The
specification records the public signatures, representation choices, proof-source routing, and the
distinction between the completed theorem surface and optional Chen--Shao strengthenings.

The project has three maintained sources of truth:

1. The cited papers determine the complete mathematical statements and proof obligations.
2. Production declarations under `ProbabilityApproximation/**/*.lean` determine formal statements
   and kernel-checked proofs.
3. Verso sources under `blueprint-verso/ProbabilityApproximationBlueprint/**/*.lean` present the
   curated mathematical milestone DAG and associate its nodes with compiled production
   declarations.

Never silently weaken a theorem, add an assumption, change a normalization, or replace its domain.
Any deliberate generalization or representation bridge must be documented in the public
declaration and outside the mathematical statement block in the Blueprint.

## Principal theorems

The library has two principal results:

- `ProbabilityTheory.nonuniformBerryEsseen`;
- `ProbabilityTheory.exists_bentkus_convex_set_constant`.

Both declarations are proved and kernel-checked. They are mathematically parallel: there is no
dependency edge between the scalar and multivariate routes. A one-dimensional specialization of
Bentkus gives a uniform convex-set bound; it does not supply the threshold decay in the scalar
nonuniform theorem.

The Bentkus implementation has three mathematical layers:

1. The convex-geometric layer develops signed distance, parallel sets, Ball's supporting-normal
   projection argument, the Gaussian perimeter estimate, and the resulting outer/inner shell bound.
2. The standardized probabilistic layer proves the identity-total-covariance replacement induction,
   including Gaussian companions, rotation, smoothing, Taylor remainders, leave-one-out
   normalization, and parameter closure.
3. The public transport layer applies covariance-square-root whitening, Gaussian pushforward, and
   convex-event transport to obtain `exists_bentkus_convex_set_constant` for positive-definite total
   covariance.

The repository Blueprint is organized as two mathematical chapters.
`NonuniformBerryEsseen.lean` develops the half-line Stein equation, concentration, one-sided
truncation, residual estimates, and reflection before stating the nonuniform theorem.
`ConvexSetApproximation.lean` develops convex distance, signed-distance coarea, Ball's Gaussian
perimeter theorem, shell bounds, Gaussian replacement, the identity-covariance induction, and
whitening before stating Bentkus's theorem. `references.bib` is the sole bibliography database;
`BibTeX.lean` parses it, `Sources.lean` registers its citation keys, `Citations.lean` links each
author--year citation to its bibliography entry in HTML and PDF, and `References.lean`
automatically renders the complete reference list.

This curated graph is not a declaration dump. A node must express a recognizable mathematical
result, group a coherent theorem cluster, and materially explain the route to a release theorem.
Proof-local measurability, integrability, coercion, reindexing, and algebraic bookkeeping remain
outside the graph even when their Lean proofs are long. The scalar and multivariate routes remain
parallel: there is no dependency edge between the two principal theorems.

FABL has a narrower consumer boundary. Its Chapter 5 Blueprint should import only the two external
theorem interfaces, not reproduce this repository's internal proof DAG.

The exact `41 / 10` truncated uniform theorem and the finite-second-moment nonuniform Chen--Shao
theorem are optional strengthenings. They do not block the two frozen release targets. If completed,
review them under the same node-admission rule: associate them with an existing milestone when they
express the same mathematical result, and add a node only when they contribute an independently
recognizable dependency to the proof architecture.

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

The current release pins Lean and Mathlib at version 4.32.0. Toolchain upgrades are proposed by the
`Update Mathlib` workflow only after the matching Mathlib and Verso Blueprint revisions and caches
are available. Every upgrade advances the package patch version and must pass the complete
production and Blueprint validation before automatic merge.

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
- The Bentkus replacement proof is divided by mathematical stage under `Bentkus/Induction/`.
  Cross-stage helpers live in the narrow `ProbabilityTheory.BentkusInduction` implementation
  namespace; keep helpers used by only one stage module-private.
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
outside statement blocks. Bibliographic metadata is defined once in `references.bib`; do not
duplicate it in Lean declarations. `BibTeX.lean` must parse the file and generate the registered
Verso declarations, while theorem notes use `Citations.citet` and `Citations.citep` with precise
section, theorem, lemma, equation, and printed-page locators where the source permits them. These
roles render linked author--year text in HTML and PDF. `References.lean` automatically renders all
registered entries at the end of the document. Do not repeat full authors, titles, venues, and years
in theorem notes or reintroduce citation marginalia and PDF footnotes.

Formalization status is derived from real compiled declaration associations. Associate a node only
with exact production declarations after their narrow build and fidelity review; never use a
placeholder declaration, project-defined analytic axiom, or unrelated weaker theorem to manufacture
status. The strict completed baseline is 65 statements, 345 unique declaration associations,
97 reviewed dependency edges, and zero open nodes. It is validated by
`scripts/validate_manifest.py`; update the style and manifest validators in the same change whenever
a node, association, or reviewed edge changes. Do not maintain a parallel status ledger, and never
invent an edge between the scalar and multivariate routes to make the graph connected.

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
lake --wfail build ProbabilityApproximation
./.github/scripts/forbidden_tokens.sh
./.github/scripts/audit_axioms.sh
cd blueprint-verso
./scripts/site.sh build
```

During Blueprint editing, build the statement module before rendering the site:

```bash
cd blueprint-verso
lake build +ProbabilityApproximationBlueprint.NonuniformBerryEsseen
lake build +ProbabilityApproximationBlueprint.ConvexSetApproximation
lake build +ProbabilityApproximationBlueprint.References
```

`site.sh build` runs the statement-style check, Blueprint library build, HTML render, strict
manifest validator, `vbp check`, and PDF render. It installs the PDF into the HTML publication at
the stable `berry-esseen-bounds.pdf` path. Inspect generated HTML through `site.sh serve`, not
`file://`, and inspect the rendered book whenever mathematical prose or displayed formula layout
changes materially. `site.sh pdf` remains available for a PDF-only rebuild.

## Release and dependency maintenance

- The package follows pre-1.0 semantic versioning and begins its public release line at `v0.9.0`.
- Release tags and their GitHub assets are immutable. A Lean or Mathlib upgrade always creates a new
  package version.
- Downstream projects must pin an exact release tag rather than track `main`.
- `release.yml` validates the tag against `lakefile.toml`, rebuilds and audits the production
  library, and publishes Lake release archives for Linux x86-64 and macOS arm64.
- `update-mathlib.yml` checks the latest stable Mathlib release daily, waits until both the Mathlib
  and Blueprint dependency caches are usable, updates all pins and manifests, and opens a
  `dependencies` pull request.
- A failed upgrade is labeled `needs-fix` without naming or assuming a repair agent. Any repaired
  upgrade is merged automatically when the complete `CI` workflow succeeds.
- `merge-dependency-update.yml` restricts automatic merge, version tagging, and release dispatch to
  open `automation/mathlib-v*` pull requests carrying the `dependencies` label.

## Version-control boundaries

- Never commit source PDFs, `.lake/`, temporary proof files, `.DS_Store`, browser QA output, or
  generated Blueprint `_out/` artifacts.
- Track production and Verso sources, toolchain files, Lake configuration and manifests, CI,
  validation scripts, README, AGENTS, `.agents/SPEC.md`, and LICENSE.
- Do not stage, commit, push, add a remote, or rewrite history unless the user explicitly requests
  it.
- Before a release commit, inspect the full staged file list and verify that theorem status agrees
  across production Lean, Blueprint, manifest expectations, README, and AGENTS.
