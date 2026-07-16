# ProbabilityApproximation: Quantitative Limit Theorems in Lean

ProbabilityApproximation is a Lean 4 and Mathlib formalization of quantitative normal
approximation for sums of independent random variables and random vectors. Its release surface is
organized around two general theorems intended for reuse by Mathlib and by downstream projects
such as [FABL](https://github.com/Polarnova/FABL).

## Status

The repository contains a proved scalar Berry--Esseen foundation and the supporting Stein and
concentration infrastructure. The finite-third-moment release theorem follows Chen--Shao (2005),
Section 6; its Bennett--Hoeffding, one-sided truncation, residual, large-jump, and atom-safe
reflection layers are kernel-checked. The Bentkus release proof remains open:

On the multivariate route, the parallel-set geometry, metric projection and distance calculus,
smooth cutoff, setwise smoothing inequality, Gaussian companions, and canonical product-space
transport, together with the low-order rotation cancellation, are kernel-checked. The Gaussian
density derivative chain and its dimension-free cubic-contraction bound are also kernel-checked,
as are covariance additivity and the identity-total-covariance leave-one-out formula. Gaussian
companions now have exact second-moment matching, a dimension-free fourth-moment estimate, an
explicit third-moment comparison with constant `27`, and the mixed moment bound used in Bentkus's
Taylor remainders. The covariance-square-root whitening identity, Gaussian pushforward,
identity-covariance contract, and one-set convex-event transport are kernel-checked.
Bentkus's Lipschitz--Schwartz integration-by-parts lemma and the small-cardinality and
large-individual-moment trivial induction branches are kernel-checked as well. In the complementary
small-second-moment branch, the leave-one-out covariance is positive definite, its inverse square
root expands norms by at most `2`, and transformed third moments grow by at most `8`.
The first- and two-shift Taylor remainders, Gaussian-density integration by parts, the exact
support of the pulled-back cutoff derivative, and its closed-shell `D²ρ` bound are kernel-checked.

For the Gaussian shell route, signed distance, its almost-everywhere eikonal identity, the
positive/zero/negative level-frontier identifications, and the exact outer/inner slab identities are
kernel-checked. The standard Gaussian density/volume bridge, normalized affine codimension-one
slicing, and Gaussian surface integral of a hyperplane are also kernel-checked. Ball's supporting
normal existence, projection Jacobian and inverse graph charts, rotation-invariant spherical
second/absolute-first moments, and exact radial Gamma peak bound are proved. The full
dimension-at-least-two Ball convex-body projection/area composition and global nonlinear
signed-distance coarea identity remain open, as does the nontrivial standardized replacement
induction. These are the remaining blockers for the Bentkus flagship.

| Flagship | Scope | Blueprint status |
|---|---|---|
| Nonuniform Berry--Esseen | Independent centered real summands with finite third moments | Proved |
| Bentkus convex-set theorem | Independent finite-dimensional summands and measurable convex sets | Open |

The Blueprint presents a curated proof DAG: it includes the two flagships and the mathematically
meaningful scalar and convex-geometry milestones, while omitting proof-local integrability,
measurability, coercion, and algebraic bookkeeping.

## Using the library

The repository pins Lean and Mathlib at version 4.32.0. After cloning, obtain the Mathlib cache and
build the production library:

```bash
lake exe cache get
lake build ProbabilityApproximation
```

Import the verified production surface with:

```lean
import ProbabilityApproximation
```

## Blueprint

The [Verso Blueprint](https://github.com/leanprover/verso-blueprint) presents the curated theorem
graph, precise paper citations, and honest formalization status. Build and serve it locally with:

```bash
cd blueprint-verso
lake exe cache get
./scripts/site.sh serve
```

Then open [http://localhost:8000/](http://localhost:8000/). Generated HTML, manifests, and graph
data live under `blueprint-verso/_out/` and are not committed. Build the print-oriented book with
`./scripts/site.sh pdf`; its output is `blueprint-verso/_out/site/pdf/main.pdf`.

## Contributing

Read [`AGENTS.md`](AGENTS.md) for the theorem-fidelity, Mathlib-reuse, Blueprint, proof, and
verification contracts. [`SPEC.md`](SPEC.md) fixes the release theorem signatures and the research
sources for the remaining proofs.

## References

- Louis H. Y. Chen and Qi-Man Shao,
  [*A non-uniform Berry--Esseen bound via Stein's method*](https://doi.org/10.1007/PL00008782),
  *Probability Theory and Related Fields* 120 (2001), 236--254.
- Louis H. Y. Chen and Qi-Man Shao,
  [*Stein's method for normal approximation*](https://blog.nus.edu.sg/louischen/files/2019/01/IMS4-pp-1-59-2hma1np.pdf),
  in *An Introduction to Stein's Method* (2005), 1--59.
- Vidmantas Bentkus,
  [*A Lyapunov-type bound in R^d*](https://www.mathnet.ru/eng/tvp230),
  *Theory of Probability and its Applications* 49 (2005), 311--323; Russian original 2004.
- Keith Ball, *The reverse isoperimetric problem for Gaussian measure*,
  *Discrete & Computational Geometry* 10 (1993), 411--420.
- Martin Raič,
  [*A multivariate Berry--Esseen theorem with explicit constants*](https://doi.org/10.3150/18-BEJ1072),
  *Bernoulli* 25 (2019), 2824--2853.
- [Mathlib](https://github.com/leanprover-community/mathlib4), the mathematical foundation used by
  the project.
- [FABL](https://github.com/Polarnova/FABL), the initial downstream consumer of the scalar theorem.

## License

ProbabilityApproximation is released under the Apache License 2.0. See [`LICENSE`](LICENSE).
