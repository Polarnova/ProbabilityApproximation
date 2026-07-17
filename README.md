# ProbabilityApproximation: Berry–Esseen Bounds for Independent Sums

ProbabilityApproximation is a Lean 4 and Mathlib library for the Berry–Esseen theorem, quantitative
normal approximation, and the multivariate central limit theorem. It formalizes the nonuniform
scalar bound of Chen and Shao via Stein's method and Bentkus's dimension-dependent Gaussian
approximation over convex sets.

## Main results

For centered independent real summands of unit total variance, the nonuniform Berry–Esseen theorem
gives an absolute constant $C$ such that

$$
\left|\mathbb P\!\left[\sum_i X_i\le x\right]-\Phi(x)\right|
\le \frac{C\sum_i\mathbb E|X_i|^3}{1+|x|^3}.
$$

For centered independent random vectors in $\mathbb R^d$ with positive-definite total covariance
$S$, Bentkus's theorem gives an absolute constant $C$ such that every measurable convex set
$A\subseteq\mathbb R^d$ satisfies

$$
\left|\mathbb P\!\left[\sum_i X_i\in A\right]-\mathcal N(0,S)(A)\right|
\le C\ d^{1/4}\sum_i\mathbb E\left\|S^{-1/2}X_i\right\|_2^3.
$$

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

The repository pins Lean and Mathlib at version 4.32.0. After cloning, obtain the Mathlib cache and
build the production library:

```bash
lake exe cache get
lake build ProbabilityApproximation
```

Import the library with:

```lean
import ProbabilityApproximation
```

## Blueprint

The [Verso Blueprint](https://github.com/leanprover/verso-blueprint) presents both proofs as a
mathematical text with complete statements, source citations, Lean declarations, and dependency
graphs:

```bash
cd blueprint-verso
lake exe cache get
./scripts/site.sh serve
```

Then open [http://localhost:8000/](http://localhost:8000/). Run `./scripts/site.sh pdf` to generate
the printable book.

## Contributing

Read [`AGENTS.md`](AGENTS.md) for the source-fidelity, Mathlib-reuse, proof, and Blueprint
conventions.

## Authors

Asher Yan with ChatGPT 5.6.

## References

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
