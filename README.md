# ProbabilityApproximation: Berry–Esseen Bounds for Independent Sums

[![CI](https://github.com/Polarnova/ProbabilityApproximation/actions/workflows/ci.yml/badge.svg)](https://github.com/Polarnova/ProbabilityApproximation/actions/workflows/ci.yml)
[![Release](https://img.shields.io/github/v/release/Polarnova/ProbabilityApproximation)](https://github.com/Polarnova/ProbabilityApproximation/releases)
[![Lean 4](https://img.shields.io/badge/Lean-4.32.0-blue)](https://lean-lang.org/)
[![Blueprint](https://img.shields.io/badge/Verso-Blueprint-5b4b8a)](https://probability.polarnova.site)
[![License](https://img.shields.io/github/license/Polarnova/ProbabilityApproximation)](LICENSE)

ProbabilityApproximation is a Lean 4 and Mathlib library for the Berry–Esseen theorem, quantitative
normal approximation, and the multivariate central limit theorem. It formalizes the nonuniform
scalar bound of Chen and Shao via Stein's method and Bentkus's dimension-dependent Gaussian
approximation over convex sets.

Read the [interactive Blueprint](https://probability.polarnova.site), or download the
[complete mathematical text as a PDF](https://probability.polarnova.site/berry-esseen-bounds.pdf).

## Main results

### Nonuniform Berry–Esseen bound

Let $X_1,\ldots,X_n$ be independent real-valued random variables satisfying
$\mathbb E X_i=0$, $\sum_{i=1}^n\mathrm{Var}(X_i)=1$, and
$\beta_3:=\sum_{i=1}^n\mathbb E|X_i|^3<\infty$. For
$W:=\sum_{i=1}^n X_i$, there is a universal constant $C>0$ such that

$$
\left|\Pr(W\le x)-\Phi(x)\right|
\le \frac{C\beta_3}{1+|x|^3},
\qquad x\in\mathbb R.
$$

Here $\Phi$ denotes the standard normal distribution function.

### Bentkus's multivariate convex-set bound

Let $X_1,\ldots,X_n$ be independent centered random vectors in $\mathbb R^d$, set
$W:=\sum_{i=1}^n X_i$, and suppose that
$\Sigma:=\mathrm{Cov}(W)$ is positive definite. If
$Z\sim\mathcal N_d(0,\Sigma)$ and
$\beta:=\sum_{i=1}^n\mathbb E\lVert\Sigma^{-1/2}X_i\rVert_2^3<\infty$, then there is a universal
constant $C>0$ such that

$$
\sup_{A\in\mathcal C_d}
\left|\Pr(W\in A)-\Pr(Z\in A)\right|
\le C d^{1/4}\beta,
$$

where $\mathcal C_d$ is the class of Borel convex subsets of $\mathbb R^d$.

## Mathematical infrastructure

The library also develops reusable foundations for probability, analysis, and convex geometry:

- **Stein's method and scalar probability:** the half-line Stein equation, derivative estimates,
  leave-one-out concentration, Bennett--Hoeffding bounds, one-sided truncation, residual
  decompositions, large-jump estimates, and reflection of distribution functions.
- **Gaussian analysis:** independent Gaussian companions, covariance algebra, multivariate
  Gaussian pushforwards, whitening, Gaussian-density derivatives, integration by parts, and
  second-order Taylor remainder estimates.
- **Convex and geometric measure theory:** convex parallel sets, metric projection, signed
  distance, smooth approximations of convex indicators, Hausdorff and spherical measure,
  coarea formulas, Ball's Gaussian perimeter theorem, and Gaussian shell bounds.
- **Multivariate normal approximation:** smoothing inequalities, rotation and Fubini arguments,
  small- and large-angle estimates, Gaussian replacement induction, and transport from identity
  covariance to arbitrary positive-definite covariance.

## Using the library

The current release is `v0.9.6`, built with Lean and Mathlib `v4.32.0`. Add the tagged package to a
downstream `lakefile.toml`:

```toml
[[require]]
name = "ProbabilityApproximation"
git = "https://github.com/Polarnova/ProbabilityApproximation.git"
rev = "v0.9.6"
```

Then update and build:

```bash
lake update
lake exe cache get
lake build @ProbabilityApproximation:release
```

The explicit release target downloads the matching precompiled ProbabilityApproximation archive on
Linux x86-64 and macOS arm64 and fails if that verified platform asset is unavailable; it does not
silently replace the download with a local source build.

Import all public declarations with:

```lean
import ProbabilityApproximation
```

The principal declarations are:

```lean
#check ProbabilityTheory.nonuniformBerryEsseen
#check ProbabilityTheory.exists_bentkus_convex_set_constant
```

Full repository, Blueprint, and PDF builds run in GitHub Actions. For local proof development,
fetch Mathlib's cache and build only the affected production module, for example:

```bash
git clone https://github.com/Polarnova/ProbabilityApproximation.git
cd ProbabilityApproximation
lake exe cache get
lake build ProbabilityApproximation.BerryEsseen
```

## Blueprint

The [Verso Blueprint](https://github.com/leanprover/verso-blueprint) presents both proofs as a
mathematical text with complete statements, source citations, Lean declarations, and dependency
graphs. The same text is available as a
[downloadable PDF](https://probability.polarnova.site/berry-esseen-bounds.pdf).

After the root production artifacts are current, `./scripts/site.sh serve dev` inside
`blueprint-verso` retains fidelity metadata for optional local review. The Blueprint workspace
shares the root dependencies and refuses to rebuild a missing or stale production library. Public
builds run in GitHub Actions with the default `release` profile and omit fidelity tags from the
reading view.

## Contributing

Read [`AGENTS.md`](AGENTS.md) for the source-fidelity, Mathlib-reuse, proof, and Blueprint
conventions.

## Citation

If you use the Lean formalization, cite the specific software release through GitHub's
**Cite this repository** menu or [`CITATION.cff`](CITATION.cff). Cite the original mathematical
source as well: Bikelis (1966) for the classical finite-third-moment nonuniform bound,
Chen--Shao (2001) for the stronger truncated-moment theorem, Chen--Shao (2005) for the proof
presentation used here, or Bentkus (2004) for the multivariate convex-set theorem. Work using the
auxiliary geometric or explicit-constant results should additionally cite the corresponding source
listed below.

## Authors

Asher Yan with ChatGPT 5.6.

## References

- A. Bikelis,
  [*On estimates of the remainder term in the central limit theorem*](https://doi.org/10.15388/LMJ.1966.19732),
  *Lithuanian Mathematical Journal* 6(3) (1966), 323--346.
- Herbert Federer,
  [*Geometric Measure Theory*](https://doi.org/10.1007/978-3-642-62010-2),
  Springer, Grundlehren der mathematischen Wissenschaften 153 (1969).
- Keith Ball,
  [*The reverse isoperimetric problem for Gaussian measure*](https://doi.org/10.1007/BF02573986),
  *Discrete and Computational Geometry* 10(4) (1993), 411--420.
- Louis H. Y. Chen and Qi-Man Shao,
  [*A non-uniform Berry--Esseen bound via Stein's method*](https://doi.org/10.1007/PL00008782),
  *Probability Theory and Related Fields* 120(2) (2001), 236--254.
- Louis H. Y. Chen and Qi-Man Shao,
  [*Stein's method for normal approximation*](https://blog.nus.edu.sg/louischen/files/2019/01/IMS4-pp-1-59-2hma1np.pdf),
  in *An Introduction to Stein's Method*, Lecture Notes Series 4, Institute for Mathematical
  Sciences, National University of Singapore (2005), 1--59.
- Vidmantas Bentkus,
  [*On the dependence of the Berry--Esseen bound on dimension*](https://doi.org/10.1016/S0378-3758(02)00094-0),
  *Journal of Statistical Planning and Inference* 113(2) (2003), 385--402.
- Vidmantas Bentkus,
  [*A Lyapunov-type bound in R^d*](https://www.mathnet.ru/eng/tvp230),
  *Teoriya Veroyatnostei i ee Primeneniya* 49(2) (2004), 400--410.
- Martin Raič,
  [*A multivariate Berry--Esseen theorem with explicit constants*](https://doi.org/10.3150/18-BEJ1072),
  *Bernoulli* 25(4A) (2019), 2824--2853.

The Blueprint bibliography is generated from
[`references.bib`](blueprint-verso/ProbabilityApproximationBlueprint/references.bib).

## Related projects

[Mathlib](https://github.com/leanprover-community/mathlib4) supplies the mathematical foundation.
[FABL](https://github.com/Polarnova/FABL) is the initial downstream consumer of the scalar theorem.

## License

ProbabilityApproximation is released under the Apache License 2.0. See [`LICENSE`](LICENSE).
