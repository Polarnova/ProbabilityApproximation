/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.ConvexGeometry.BallRadialGammaBound
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Ball's radial projection majorant

This module formalizes the one-dimensional analytic construction in Keith Ball,
*The reverse isoperimetric problem for Gaussian measure*, Discrete & Computational Geometry
**10** (1993), 411--420, printed pp. 417--419.

For a dimension `n >= 2`, Ball defines a signed radial function `h` by differentiating the
Abel-type integral in his equation (5), and takes its positive part `f = h+`.  The scaled function
`exp (t^2 / 2) h(t)` is decreasing, `f` is therefore nonincreasing, and the spherical projection
transform of `f` dominates the `n`-dimensional standard Gaussian density.  Finally, the total
mass of the radial density on `R^(n-1)` is at most `2 * n^(1/4)`.

The definitions below use Ball's displayed formula (6).  Keeping this analytic construction in a
separate module prevents the subsequent convex-boundary area argument from depending on the
details of trigonometric integration and the Gamma estimate.
-/

open MeasureTheory Set
open scoped Real

noncomputable section

namespace ProbabilityTheory

/-- The normalization of the `n`-dimensional standard Gaussian density. -/
def ballGaussianNormalization (n : ℕ) : ℝ :=
  (√(2 * Real.pi))⁻¹ ^ n

/-- The integrand in Ball's formula (6) for the signed radial function `h`. -/
def ballRadialAuxIntegrand (n : ℕ) (t θ : ℝ) : ℝ :=
  (((n - 1 : ℕ) : ℝ) - t ^ 2 * Real.sin θ ^ 2) *
    Real.sin θ ^ (n - 2) * Real.exp (-(t ^ 2 * Real.sin θ ^ 2) / 2)

/-- Ball's signed radial density `h`, equation (6) on printed p. 417. -/
def ballRadialAux (n : ℕ) (t : ℝ) : ℝ :=
  ballGaussianNormalization n *
    ∫ θ in (0 : ℝ)..Real.pi / 2, ballRadialAuxIntegrand n t θ

/-- The exponentially rescaled auxiliary function used to prove monotonicity. -/
def ballRadialScaledAux (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (t ^ 2 / 2) * ballRadialAux n t

/-- The integrand obtained after pulling `exp (t² / 2)` into Ball's formula (6). -/
def ballRadialScaledIntegrand (n : ℕ) (t θ : ℝ) : ℝ :=
  (((n - 1 : ℕ) : ℝ) - t ^ 2 * Real.sin θ ^ 2) *
    Real.sin θ ^ (n - 2) * Real.exp (t ^ 2 * Real.cos θ ^ 2 / 2)

/-- The positive kernel that is the negative derivative of the scaled auxiliary integral. -/
def ballRadialDecreaseKernel (n : ℕ) (t θ : ℝ) : ℝ :=
  t * Real.sin θ ^ n * Real.exp (t ^ 2 * Real.cos θ ^ 2 / 2)

/-- The derivative with respect to the radial parameter of the scaled integrand. -/
def ballRadialScaledParameterDerivative (n : ℕ) (t θ : ℝ) : ℝ :=
  t *
    (((((n - 1 : ℕ) : ℝ) - t ^ 2 * Real.sin θ ^ 2) * Real.cos θ ^ 2 -
        2 * Real.sin θ ^ 2) * Real.sin θ ^ (n - 2) *
      Real.exp (t ^ 2 * Real.cos θ ^ 2 / 2))

/-- A trigonometric primitive used to integrate the parameter derivative by parts. -/
def ballRadialBoundaryPrimitive (n : ℕ) (t θ : ℝ) : ℝ :=
  Real.cos θ * Real.sin θ ^ (n - 1) *
    Real.exp (t ^ 2 * Real.cos θ ^ 2 / 2)

/-- Ball's nonnegative radial projection majorant `f = h+`. -/
def ballRadialMajorant (n : ℕ) (t : ℝ) : ℝ :=
  max (ballRadialAux n t) 0

/-- The half-sphere sine moment occurring throughout Ball's radial calculation. -/
def ballSineMoment (k : ℕ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi / 2, Real.sin θ ^ k

lemma ballGaussianNormalization_pos (n : ℕ) : 0 < ballGaussianNormalization n := by
  unfold ballGaussianNormalization
  positivity

lemma ballGaussianNormalization_nonneg (n : ℕ) : 0 ≤ ballGaussianNormalization n :=
  (ballGaussianNormalization_pos n).le

lemma continuous_ballRadialAuxIntegrand (n : ℕ) :
    Continuous (fun p : ℝ × ℝ ↦ ballRadialAuxIntegrand n p.1 p.2) := by
  unfold ballRadialAuxIntegrand
  fun_prop

lemma continuous_ballRadialScaledIntegrand (n : ℕ) :
    Continuous (fun p : ℝ × ℝ ↦ ballRadialScaledIntegrand n p.1 p.2) := by
  unfold ballRadialScaledIntegrand
  fun_prop

lemma continuous_ballRadialDecreaseKernel (n : ℕ) :
    Continuous (fun p : ℝ × ℝ ↦ ballRadialDecreaseKernel n p.1 p.2) := by
  unfold ballRadialDecreaseKernel
  fun_prop

lemma continuous_ballRadialScaledParameterDerivative (n : ℕ) :
    Continuous (fun p : ℝ × ℝ ↦ ballRadialScaledParameterDerivative n p.1 p.2) := by
  unfold ballRadialScaledParameterDerivative
  fun_prop

lemma continuous_ballRadialAux (n : ℕ) : Continuous (ballRadialAux n) := by
  unfold ballRadialAux
  apply Continuous.const_mul
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun t θ ↦ ballRadialAuxIntegrand n t θ)
    (by
      change Continuous (fun p : ℝ × ℝ ↦ ballRadialAuxIntegrand n p.1 p.2)
      exact continuous_ballRadialAuxIntegrand n) 0 (Real.pi / 2)

lemma continuous_ballRadialScaledAux (n : ℕ) : Continuous (ballRadialScaledAux n) := by
  unfold ballRadialScaledAux
  exact (Real.continuous_exp.comp ((continuous_id.pow 2).div_const 2)).mul
    (continuous_ballRadialAux n)

/-- Pulling the exponential rescaling inside the integral changes `sin²` in the exponent to
`cos²`. -/
theorem ballRadialScaledAux_eq_integral (n : ℕ) (t : ℝ) :
    ballRadialScaledAux n t = ballGaussianNormalization n *
      ∫ θ in (0 : ℝ)..Real.pi / 2, ballRadialScaledIntegrand n t θ := by
  rw [ballRadialScaledAux, ballRadialAux]
  calc
    Real.exp (t ^ 2 / 2) *
        (ballGaussianNormalization n *
          ∫ θ in (0 : ℝ)..Real.pi / 2, ballRadialAuxIntegrand n t θ) =
        ballGaussianNormalization n *
          (Real.exp (t ^ 2 / 2) *
            ∫ θ in (0 : ℝ)..Real.pi / 2, ballRadialAuxIntegrand n t θ) := by ring
    _ = ballGaussianNormalization n *
        ∫ θ in (0 : ℝ)..Real.pi / 2,
          Real.exp (t ^ 2 / 2) * ballRadialAuxIntegrand n t θ := by
      rw [intervalIntegral.integral_const_mul]
    _ = ballGaussianNormalization n *
        ∫ θ in (0 : ℝ)..Real.pi / 2, ballRadialScaledIntegrand n t θ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro θ _hθ
      unfold ballRadialAuxIntegrand ballRadialScaledIntegrand
      change Real.exp (t ^ 2 / 2) *
          (((((n - 1 : ℕ) : ℝ) - t ^ 2 * Real.sin θ ^ 2) *
            Real.sin θ ^ (n - 2)) * Real.exp (-(t ^ 2 * Real.sin θ ^ 2) / 2)) = _
      rw [show
        Real.exp (t ^ 2 / 2) *
            ((((n - 1 : ℕ) : ℝ) - t ^ 2 * Real.sin θ ^ 2) *
              Real.sin θ ^ (n - 2) *
                Real.exp (-(t ^ 2 * Real.sin θ ^ 2) / 2)) =
          ((((n - 1 : ℕ) : ℝ) - t ^ 2 * Real.sin θ ^ 2) *
              Real.sin θ ^ (n - 2)) *
            (Real.exp (t ^ 2 / 2) *
              Real.exp (-(t ^ 2 * Real.sin θ ^ 2) / 2)) by ring]
      rw [← Real.exp_add]
      have hexponent :
          t ^ 2 / 2 + -(t ^ 2 * Real.sin θ ^ 2) / 2 =
            t ^ 2 * Real.cos θ ^ 2 / 2 := by
        nlinarith [Real.sin_sq_add_cos_sq θ]
      rw [hexponent]

lemma continuous_ballRadialMajorant (n : ℕ) : Continuous (ballRadialMajorant n) := by
  unfold ballRadialMajorant
  exact (continuous_ballRadialAux n).max continuous_const

lemma ballRadialMajorant_nonneg (n : ℕ) (t : ℝ) : 0 ≤ ballRadialMajorant n t := by
  simp [ballRadialMajorant]

lemma ballRadialAux_le_ballRadialMajorant (n : ℕ) (t : ℝ) :
    ballRadialAux n t ≤ ballRadialMajorant n t := by
  simp [ballRadialMajorant]

lemma ballRadialMajorant_eq_ballRadialAux_of_nonneg {n : ℕ} {t : ℝ}
    (h : 0 ≤ ballRadialAux n t) :
    ballRadialMajorant n t = ballRadialAux n t := by
  simp [ballRadialMajorant, h]

lemma ballRadialMajorant_eq_zero_of_nonpos {n : ℕ} {t : ℝ}
    (h : ballRadialAux n t ≤ 0) :
    ballRadialMajorant n t = 0 := by
  simp [ballRadialMajorant, h]

lemma ballSineMoment_pos (k : ℕ) : 0 < ballSineMoment k := by
  unfold ballSineMoment
  apply intervalIntegral.integral_pos (by positivity)
  · fun_prop
  · intro θ hθ
    exact pow_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le (hθ.2.trans (by linarith [Real.pi_pos]))) _
  · refine ⟨Real.pi / 4, ⟨by positivity, by linarith [Real.pi_pos]⟩, ?_⟩
    exact pow_pos (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])) _

lemma ballSineMoment_nonneg (k : ℕ) : 0 ≤ ballSineMoment k :=
  (ballSineMoment_pos k).le

lemma ballSineMoment_le_pi_div_two (k : ℕ) :
    ballSineMoment k ≤ Real.pi / 2 := by
  unfold ballSineMoment
  calc
    (∫ θ in (0 : ℝ)..Real.pi / 2, Real.sin θ ^ k) ≤
        ∫ _θ in (0 : ℝ)..Real.pi / 2, (1 : ℝ) := by
      apply intervalIntegral.integral_mono_on (by positivity)
      · exact (by fun_prop : Continuous fun θ : ℝ ↦ Real.sin θ ^ k)
          |>.intervalIntegrable _ _
      · exact continuous_const.intervalIntegrable _ _
      · intro θ hθ
        have hsin : 0 ≤ Real.sin θ :=
          Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
            (hθ.2.trans (by linarith [Real.pi_pos]))
        exact pow_le_one₀ hsin (Real.sin_le_one θ)
    _ = Real.pi / 2 := by simp

/-- The exact adjacent-moment recurrence on `[0, π/2]`. -/
lemma mul_ballSineMoment_eq {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) * ballSineMoment n =
      ((n - 1 : ℕ) : ℝ) * ballSineMoment (n - 2) := by
  have h := @_root_.integral_sin_pow (0 : ℝ) (Real.pi / 2) (n - 2)
  have hsub : n - 2 + 2 = n := by omega
  have hsub1 : n - 2 + 1 = n - 1 := by omega
  rw [hsub, hsub1] at h
  simp only [Real.sin_zero, Real.cos_zero, Real.sin_pi_div_two, Real.cos_pi_div_two,
    zero_pow (by omega : n - 1 ≠ 0), one_pow, mul_one, mul_zero, zero_sub] at h
  have hncast : (((n - 2 : ℕ) : ℝ) + 2) = n := by exact_mod_cast hsub
  have hncast1 : (((n - 2 : ℕ) : ℝ) + 1) = (n - 1 : ℕ) := by
    exact_mod_cast hsub1
  rw [hncast, hncast1] at h
  rw [ballSineMoment, ballSineMoment, h]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

@[simp] lemma ballSineMoment_zero : ballSineMoment 0 = Real.pi / 2 := by
  simp [ballSineMoment]

@[simp] lemma ballSineMoment_one : ballSineMoment 1 = 1 := by
  simp [ballSineMoment, integral_sin]

/-- The pair of adjacent half-sphere moments has a dimension-independent normalized product. -/
theorem succ_mul_ballSineMoment_mul_succ (m : ℕ) :
    ((m + 1 : ℕ) : ℝ) * ballSineMoment m * ballSineMoment (m + 1) =
      Real.pi / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hrec := mul_ballSineMoment_eq (n := m + 2) (by omega)
      rw [show m + 2 - 2 = m by omega, show m + 2 - 1 = m + 1 by omega] at hrec
      calc
        (((m + 1 + 1 : ℕ) : ℝ) * ballSineMoment (m + 1) *
            ballSineMoment (m + 1 + 1)) =
            ballSineMoment (m + 1) *
              (((m + 2 : ℕ) : ℝ) * ballSineMoment (m + 2)) := by ring
        _ = ballSineMoment (m + 1) *
            (((m + 1 : ℕ) : ℝ) * ballSineMoment m) := by rw [hrec]
        _ = ((m + 1 : ℕ) : ℝ) * ballSineMoment m *
            ballSineMoment (m + 1) := by ring
        _ = Real.pi / 2 := ih

/-- Ball's integrand is pointwise nonnegative below `sqrt (n - 1)`. -/
lemma ballRadialAuxIntegrand_nonneg {n : ℕ} (_hn : 2 ≤ n) {t θ : ℝ}
    (ht : 0 ≤ t) (htop : t ≤ √((n - 1 : ℕ) : ℝ))
    (hθ : θ ∈ Set.uIcc (0 : ℝ) (Real.pi / 2)) :
    0 ≤ ballRadialAuxIntegrand n t θ := by
  have hsin : 0 ≤ Real.sin θ := by
    rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hθ
    exact Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (hθ.2.trans (by linarith [Real.pi_pos]))
  have hsin_le : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hn1 : 0 ≤ ((n - 1 : ℕ) : ℝ) := by positivity
  have ht_sq : t ^ 2 ≤ ((n - 1 : ℕ) : ℝ) := by
    calc
      t ^ 2 ≤ (√((n - 1 : ℕ) : ℝ)) ^ 2 :=
        pow_le_pow_left₀ ht htop 2
      _ = ((n - 1 : ℕ) : ℝ) := Real.sq_sqrt hn1
  have hfactor : 0 ≤ ((n - 1 : ℕ) : ℝ) - t ^ 2 * Real.sin θ ^ 2 := by
    have hsin_sq : Real.sin θ ^ 2 ≤ 1 := by nlinarith
    have hmul : t ^ 2 * Real.sin θ ^ 2 ≤ t ^ 2 := by
      nlinarith [sq_nonneg t]
    linarith
  unfold ballRadialAuxIntegrand
  exact mul_nonneg (mul_nonneg hfactor (pow_nonneg hsin _)) (Real.exp_nonneg _)

/-- The signed auxiliary density is nonnegative up to `sqrt (n - 1)`, Ball (7). -/
theorem ballRadialAux_nonneg_of_le_sqrt {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht : 0 ≤ t) (htop : t ≤ √((n - 1 : ℕ) : ℝ)) :
    0 ≤ ballRadialAux n t := by
  unfold ballRadialAux
  apply mul_nonneg (ballGaussianNormalization_nonneg n)
  exact intervalIntegral.integral_nonneg
    (by positivity : (0 : ℝ) ≤ Real.pi / 2)
    (fun θ hθ ↦ ballRadialAuxIntegrand_nonneg hn ht htop
      (by simpa [uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hθ))

private lemma pow_eq_sq_mul_pow_sub_two {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    x ^ n = x ^ 2 * x ^ (n - 2) := by
  rw [← pow_add]
  congr 1
  omega

private lemma mul_pow_pred_eq_sq_mul_pow_sub_two {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    x * x ^ (n - 1) = x ^ 2 * x ^ (n - 2) := by
  rw [← pow_succ']
  rw [show n - 1 + 1 = n by omega]
  exact pow_eq_sq_mul_pow_sub_two hn x

private theorem hasDerivAt_ballRadialBoundaryPrimitive {n : ℕ} (hn : 2 ≤ n)
    (t θ : ℝ) :
    HasDerivAt (ballRadialBoundaryPrimitive n t)
      (((((n - 1 : ℕ) : ℝ) * Real.cos θ ^ 2 - Real.sin θ ^ 2 -
          t ^ 2 * Real.cos θ ^ 2 * Real.sin θ ^ 2) *
        Real.sin θ ^ (n - 2)) * Real.exp (t ^ 2 * Real.cos θ ^ 2 / 2)) θ := by
  unfold ballRadialBoundaryPrimitive
  have hpow := (Real.hasDerivAt_sin θ).pow (n - 1)
  have hq := ((Real.hasDerivAt_cos θ).pow 2).const_mul (t ^ 2) |>.div_const 2
  have hexp := (Real.hasDerivAt_exp (t ^ 2 * Real.cos θ ^ 2 / 2)).comp θ hq
  have h := ((Real.hasDerivAt_cos θ).mul hpow).mul hexp
  change HasDerivAt
    (Real.cos * Real.sin ^ (n - 1) *
      (Real.exp ∘ fun x ↦ t ^ 2 * Real.cos x ^ 2 / 2)) _ θ
  apply h.congr_deriv
  rw [show n - 1 - 1 = n - 2 by omega]
  simp only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply]
  push_cast
  ring_nf
  rw [mul_pow_pred_eq_sq_mul_pow_sub_two hn]

private theorem integral_ballRadialScaled_parameterDerivative {n : ℕ} (hn : 2 ≤ n)
    (t : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi / 2,
        t *
          (((((n - 1 : ℕ) : ℝ) - t ^ 2 * Real.sin θ ^ 2) * Real.cos θ ^ 2 -
              2 * Real.sin θ ^ 2) * Real.sin θ ^ (n - 2) *
            Real.exp (t ^ 2 * Real.cos θ ^ 2 / 2))) =
      -∫ θ in (0 : ℝ)..Real.pi / 2, ballRadialDecreaseKernel n t θ := by
  let D : ℝ → ℝ := fun θ ↦
    ((((n - 1 : ℕ) : ℝ) * Real.cos θ ^ 2 - Real.sin θ ^ 2 -
        t ^ 2 * Real.cos θ ^ 2 * Real.sin θ ^ 2) *
      Real.sin θ ^ (n - 2)) * Real.exp (t ^ 2 * Real.cos θ ^ 2 / 2)
  have hDcont : Continuous D := by
    dsimp only [D]
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := Real.pi / 2)
    (f := ballRadialBoundaryPrimitive n t)
    (f' := D)
    (fun θ _hθ ↦ hasDerivAt_ballRadialBoundaryPrimitive hn t θ)
    (hDcont.intervalIntegrable 0 (Real.pi / 2))
  have hn1 : n - 1 ≠ 0 := by omega
  simp only [D, ballRadialBoundaryPrimitive, Real.sin_zero, zero_pow hn1, mul_zero,
    Real.cos_pi_div_two, zero_mul, sub_zero] at hftc
  have hKcont : Continuous (ballRadialDecreaseKernel n t) := by
    exact (continuous_ballRadialDecreaseKernel n).comp
      (continuous_const.prodMk continuous_id)
  calc
    (∫ θ in (0 : ℝ)..Real.pi / 2,
        t *
          (((((n - 1 : ℕ) : ℝ) - t ^ 2 * Real.sin θ ^ 2) * Real.cos θ ^ 2 -
              2 * Real.sin θ ^ 2) * Real.sin θ ^ (n - 2) *
            Real.exp (t ^ 2 * Real.cos θ ^ 2 / 2))) =
        ∫ θ in (0 : ℝ)..Real.pi / 2,
          (t * D θ - ballRadialDecreaseKernel n t θ) := by
      apply intervalIntegral.integral_congr
      intro θ _hθ
      dsimp only [D]
      unfold ballRadialDecreaseKernel
      rw [pow_eq_sq_mul_pow_sub_two hn]
      ring
    _ = t * (∫ θ in (0 : ℝ)..Real.pi / 2, D θ) -
        ∫ θ in (0 : ℝ)..Real.pi / 2, ballRadialDecreaseKernel n t θ := by
      rw [intervalIntegral.integral_sub
        ((hDcont.const_mul t).intervalIntegrable _ _)
        (hKcont.intervalIntegrable _ _), intervalIntegral.integral_const_mul]
    _ = -∫ θ in (0 : ℝ)..Real.pi / 2, ballRadialDecreaseKernel n t θ := by
      rw [hftc]
      ring

private theorem hasDerivAt_ballRadialScaledIntegrand (n : ℕ) (t θ : ℝ) :
    HasDerivAt (fun u ↦ ballRadialScaledIntegrand n u θ)
      (t *
        (((((n - 1 : ℕ) : ℝ) - t ^ 2 * Real.sin θ ^ 2) * Real.cos θ ^ 2 -
            2 * Real.sin θ ^ 2) * Real.sin θ ^ (n - 2) *
          Real.exp (t ^ 2 * Real.cos θ ^ 2 / 2))) t := by
  unfold ballRadialScaledIntegrand
  let N : ℝ := ((n - 1 : ℕ) : ℝ)
  let S : ℝ := Real.sin θ ^ (n - 2)
  let a : ℝ := Real.sin θ ^ 2
  let b : ℝ := Real.cos θ ^ 2
  have hleft₀ := (hasDerivAt_const t N).sub (((hasDerivAt_id t).pow 2).mul_const a)
  have hq₀ := (((hasDerivAt_id t).pow 2).mul_const b).div_const 2
  have hexp₀ := (Real.hasDerivAt_exp ((id ^ 2) t * b / 2)).comp t hq₀
  have h₀ := (hleft₀.mul_const S).mul hexp₀
  let F : ℝ → ℝ := fun u ↦ (N - u ^ 2 * a) * S * Real.exp (u ^ 2 * b / 2)
  have heq : F =ᶠ[nhds t]
      ((fun y ↦ (((fun x : ℝ ↦ N) - fun z ↦ (id ^ 2) z * a) y) * S) *
        (Real.exp ∘ fun x ↦ (id ^ 2) x * b / 2)) := by
    filter_upwards with u
    simp [F, id]
  have hF := h₀.congr_of_eventuallyEq heq
  change HasDerivAt F _ t
  apply hF.congr_deriv
  dsimp only [N, S, a, b]
  simp only [Function.comp_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
  push_cast
  ring

private theorem hasDerivAt_integral_ballRadialScaledIntegrand (n : ℕ) (t : ℝ) :
    HasDerivAt
      (fun u ↦ ∫ θ in (0 : ℝ)..Real.pi / 2, ballRadialScaledIntegrand n u θ)
      (∫ θ in (0 : ℝ)..Real.pi / 2, ballRadialScaledParameterDerivative n t θ) t := by
  let K : Set (ℝ × ℝ) :=
    Metric.closedBall t 1 ×ˢ Set.uIcc (0 : ℝ) (Real.pi / 2)
  let G : ℝ × ℝ → ℝ := fun p ↦ ‖ballRadialScaledParameterDerivative n p.1 p.2‖
  have hK : IsCompact K :=
    (isCompact_closedBall t 1).prod isCompact_uIcc
  have hG : Continuous G := by
    dsimp only [G]
    exact (continuous_ballRadialScaledParameterDerivative n).norm
  obtain ⟨B, hB⟩ := bddAbove_def.mp (hK.bddAbove_image hG.continuousOn)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume)
    (F := fun u θ ↦ ballRadialScaledIntegrand n u θ)
    (F' := fun u θ ↦ ballRadialScaledParameterDerivative n u θ)
    (x₀ := t) (s := Metric.closedBall t 1) (bound := fun _ ↦ B)
    (a := (0 : ℝ)) (b := Real.pi / 2)
    (Metric.closedBall_mem_nhds t zero_lt_one)
    (by
      filter_upwards with u
      exact ((continuous_ballRadialScaledIntegrand n).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (((continuous_ballRadialScaledIntegrand n).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
    (((continuous_ballRadialScaledParameterDerivative n).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (by
      filter_upwards with θ
      intro hθ u hu
      exact hB (G (u, θ)) (mem_image_of_mem G (show (u, θ) ∈ K by
        exact ⟨hu, uIoc_subset_uIcc hθ⟩)))
    (continuous_const.intervalIntegrable _ _)
    (by
      filter_upwards with θ
      intro _hθ u _hu
      exact hasDerivAt_ballRadialScaledIntegrand n u θ)
  exact h.2

/-- The scaled auxiliary function has a manifestly nonpositive derivative on the nonnegative
half-line.  This is Ball's monotonicity argument on printed p. 417, expressed by integration by
parts rather than by the paper's power-series coefficient calculation. -/
theorem hasDerivAt_ballRadialScaledAux {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    HasDerivAt (ballRadialScaledAux n)
      (-(ballGaussianNormalization n *
        ∫ θ in (0 : ℝ)..Real.pi / 2, ballRadialDecreaseKernel n t θ)) t := by
  have hparam := hasDerivAt_integral_ballRadialScaledIntegrand n t
  have hparameterIntegral :
      (∫ θ in (0 : ℝ)..Real.pi / 2, ballRadialScaledParameterDerivative n t θ) =
        -∫ θ in (0 : ℝ)..Real.pi / 2, ballRadialDecreaseKernel n t θ := by
    simpa only [ballRadialScaledParameterDerivative] using
      integral_ballRadialScaled_parameterDerivative hn t
  rw [hparameterIntegral] at hparam
  have hmul := hparam.const_mul (ballGaussianNormalization n)
  apply (hmul.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u ↦
    ballRadialScaledAux_eq_integral n u)).congr_deriv
  ring

lemma integral_ballRadialDecreaseKernel_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ∫ θ in (0 : ℝ)..Real.pi / 2, ballRadialDecreaseKernel n t θ := by
  apply intervalIntegral.integral_nonneg (by positivity)
  intro θ hθ
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (hθ.2.trans (by linarith [Real.pi_pos]))
  unfold ballRadialDecreaseKernel
  exact mul_nonneg (mul_nonneg ht (pow_nonneg hsin _)) (Real.exp_nonneg _)

/-- The scaled signed density is antitone on the nonnegative half-line. -/
theorem antitoneOn_ballRadialScaledAux {n : ℕ} (hn : 2 ≤ n) :
    AntitoneOn (ballRadialScaledAux n) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (continuous_ballRadialScaledAux n).continuousOn
  · intro t _ht
    exact (hasDerivAt_ballRadialScaledAux hn t).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hasDerivAt_ballRadialScaledAux hn t).deriv]
    apply neg_nonpos.mpr
    have htpos : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    exact mul_nonneg (ballGaussianNormalization_nonneg n)
      (integral_ballRadialDecreaseKernel_nonneg n htpos.le)

lemma ballRadialScaledAux_zero (n : ℕ) :
    ballRadialScaledAux n 0 = ballGaussianNormalization n *
      (((n - 1 : ℕ) : ℝ) * ballSineMoment (n - 2)) := by
  rw [ballRadialScaledAux_eq_integral]
  congr 1
  unfold ballSineMoment
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _hθ
  simp [ballRadialScaledIntegrand]

lemma mul_ballSineMoment_le_integral_decreaseKernel (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t * ballSineMoment n ≤
      ∫ θ in (0 : ℝ)..Real.pi / 2, ballRadialDecreaseKernel n t θ := by
  unfold ballSineMoment
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by positivity)
  · exact (by fun_prop : Continuous (fun θ : ℝ ↦ t * Real.sin θ ^ n))
      |>.intervalIntegrable _ _
  · exact ((continuous_ballRadialDecreaseKernel n).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · intro θ hθ
    unfold ballRadialDecreaseKernel
    have hsin : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (hθ.2.trans (by linarith [Real.pi_pos]))
    have hbase : 0 ≤ t * Real.sin θ ^ n :=
      mul_nonneg ht (pow_nonneg hsin _)
    calc
      t * Real.sin θ ^ n = (t * Real.sin θ ^ n) * 1 := (mul_one _).symm
      _ ≤ (t * Real.sin θ ^ n) * Real.exp (t ^ 2 * Real.cos θ ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left
          (Real.one_le_exp (by positivity : 0 ≤ t ^ 2 * Real.cos θ ^ 2 / 2)) hbase

private def ballRadialScaledAuxDerivative (n : ℕ) (t : ℝ) : ℝ :=
  -(ballGaussianNormalization n *
    ∫ θ in (0 : ℝ)..Real.pi / 2, ballRadialDecreaseKernel n t θ)

private lemma continuous_ballRadialScaledAuxDerivative (n : ℕ) :
    Continuous (ballRadialScaledAuxDerivative n) := by
  unfold ballRadialScaledAuxDerivative
  apply Continuous.neg
  apply Continuous.const_mul
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun t θ ↦ ballRadialDecreaseKernel n t θ)
    (by
      change Continuous (fun p : ℝ × ℝ ↦ ballRadialDecreaseKernel n p.1 p.2)
      exact continuous_ballRadialDecreaseKernel n) 0 (Real.pi / 2)

private lemma ballRadialScaledAuxDerivative_le {n : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    ballRadialScaledAuxDerivative n t ≤
      -(ballGaussianNormalization n * (t * ballSineMoment n)) := by
  unfold ballRadialScaledAuxDerivative
  exact neg_le_neg (mul_le_mul_of_nonneg_left
    (mul_ballSineMoment_le_integral_decreaseKernel n ht)
    (ballGaussianNormalization_nonneg n))

/-- A quadratic upper bound for the scaled auxiliary function.  Combined with the adjacent sine
moment recurrence, it forces a zero no later than `sqrt (2n)`, as on Ball's printed p. 418. -/
theorem ballRadialScaledAux_le_quadratic {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    ballRadialScaledAux n t ≤ ballGaussianNormalization n *
      (((n - 1 : ℕ) : ℝ) * ballSineMoment (n - 2) -
        t ^ 2 / 2 * ballSineMoment n) := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t) (f := ballRadialScaledAux n)
    (f' := ballRadialScaledAuxDerivative n)
    (fun u _hu ↦ by simpa [ballRadialScaledAuxDerivative] using
      hasDerivAt_ballRadialScaledAux hn u)
    ((continuous_ballRadialScaledAuxDerivative n).intervalIntegrable _ _)
  have hmono :
      (∫ u in (0 : ℝ)..t, ballRadialScaledAuxDerivative n u) ≤
        ∫ u in (0 : ℝ)..t,
          -(ballGaussianNormalization n * (u * ballSineMoment n)) := by
    apply intervalIntegral.integral_mono_on ht
    · exact (continuous_ballRadialScaledAuxDerivative n).intervalIntegrable _ _
    · exact (by fun_prop : Continuous
        (fun u : ℝ ↦ -(ballGaussianNormalization n * (u * ballSineMoment n))))
        |>.intervalIntegrable _ _
    · intro u hu
      exact ballRadialScaledAuxDerivative_le hu.1
  have hright :
      (∫ u in (0 : ℝ)..t,
          -(ballGaussianNormalization n * (u * ballSineMoment n))) =
        -(ballGaussianNormalization n * (t ^ 2 / 2 * ballSineMoment n)) := by
    rw [show (fun u : ℝ ↦ -(ballGaussianNormalization n * (u * ballSineMoment n))) =
        fun u ↦ (-(ballGaussianNormalization n * ballSineMoment n)) * u by
      funext u; ring]
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  rw [hright] at hmono
  rw [hftc, ballRadialScaledAux_zero] at hmono
  linarith

/-- The scaled auxiliary function is nonpositive at `sqrt (2n)`. -/
theorem ballRadialScaledAux_nonpos_sqrt_two_mul {n : ℕ} (hn : 2 ≤ n) :
    ballRadialScaledAux n (√(2 * n)) ≤ 0 := by
  have ht : 0 ≤ √(2 * (n : ℝ)) := Real.sqrt_nonneg _
  have hbound := ballRadialScaledAux_le_quadratic hn ht
  have hsq : (√(2 * (n : ℝ))) ^ 2 = 2 * n := by
    rw [Real.sq_sqrt]
    positivity
  rw [hsq, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
    mul_ballSineMoment_eq hn] at hbound
  simpa using hbound

lemma ballRadialAux_eq_exp_neg_mul_scaledAux (n : ℕ) (t : ℝ) :
    ballRadialAux n t = Real.exp (-(t ^ 2) / 2) * ballRadialScaledAux n t := by
  unfold ballRadialScaledAux
  rw [show Real.exp (-(t ^ 2) / 2) *
      (Real.exp (t ^ 2 / 2) * ballRadialAux n t) =
      (Real.exp (-(t ^ 2) / 2) * Real.exp (t ^ 2 / 2)) * ballRadialAux n t by ring,
    ← Real.exp_add]
  have hz : -(t ^ 2) / 2 + t ^ 2 / 2 = 0 := by ring
  rw [hz, Real.exp_zero, one_mul]

/-- The signed auxiliary function is nonpositive beyond `sqrt (2n)`. -/
theorem ballRadialAux_nonpos_of_sqrt_two_mul_le {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht : √(2 * n) ≤ t) :
    ballRadialAux n t ≤ 0 := by
  have hsqrt : 0 ≤ √(2 * (n : ℝ)) := Real.sqrt_nonneg _
  have hscaled : ballRadialScaledAux n t ≤ ballRadialScaledAux n (√(2 * n)) :=
    antitoneOn_ballRadialScaledAux hn hsqrt (hsqrt.trans ht) ht
  have hnonpos := hscaled.trans (ballRadialScaledAux_nonpos_sqrt_two_mul hn)
  rw [ballRadialAux_eq_exp_neg_mul_scaledAux]
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) hnonpos

/-- Ball's nonnegative radial majorant vanishes beyond `sqrt (2n)`. -/
theorem ballRadialMajorant_eq_zero_of_sqrt_two_mul_le {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht : √(2 * n) ≤ t) :
    ballRadialMajorant n t = 0 :=
  ballRadialMajorant_eq_zero_of_nonpos (ballRadialAux_nonpos_of_sqrt_two_mul_le hn ht)

/-- The positive part `f = h+` is nonincreasing on `[0, ∞)`, as required in Ball's
rearrangement step between equations (3) and (4). -/
theorem antitoneOn_ballRadialMajorant {n : ℕ} (hn : 2 ≤ n) :
    AntitoneOn (ballRadialMajorant n) (Set.Ici 0) := by
  intro a ha b hb hab
  by_cases hbaux : ballRadialAux n b ≤ 0
  · rw [ballRadialMajorant_eq_zero_of_nonpos hbaux]
    exact ballRadialMajorant_nonneg n a
  · have hbauxpos : 0 < ballRadialAux n b := lt_of_not_ge hbaux
    have hbscaledpos : 0 < ballRadialScaledAux n b := by
      unfold ballRadialScaledAux
      positivity
    have hscaled : ballRadialScaledAux n b ≤ ballRadialScaledAux n a :=
      antitoneOn_ballRadialScaledAux hn ha hb hab
    have hexp : Real.exp (-(b ^ 2) / 2) ≤ Real.exp (-(a ^ 2) / 2) := by
      apply Real.exp_le_exp.mpr
      have habsq : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha hab 2
      linarith
    have haux : ballRadialAux n b ≤ ballRadialAux n a := by
      rw [ballRadialAux_eq_exp_neg_mul_scaledAux,
        ballRadialAux_eq_exp_neg_mul_scaledAux]
      exact mul_le_mul hexp hscaled hbscaledpos.le (Real.exp_nonneg _)
    rw [ballRadialMajorant_eq_ballRadialAux_of_nonneg hbauxpos.le,
      ballRadialMajorant_eq_ballRadialAux_of_nonneg (hbauxpos.le.trans haux)]
    exact haux

private lemma intervalIntegral_tsum_of_summable_integral_norm
    (F : ℕ → ℝ → ℝ)
    (hFint : ∀ k, IntervalIntegrable (F k) volume (0 : ℝ) (Real.pi / 2))
    (hFsum : Summable fun k ↦ ∫ θ in (0 : ℝ)..Real.pi / 2, ‖F k θ‖) :
    (∫ θ in (0 : ℝ)..Real.pi / 2, ∑' k, F k θ) =
      ∑' k, ∫ θ in (0 : ℝ)..Real.pi / 2, F k θ := by
  rw [intervalIntegral.integral_of_le (by positivity)]
  simp_rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  have hFsum' : Summable fun k ↦
      ∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 2), ‖F k θ‖ := by
    simpa only [intervalIntegral.integral_of_le
      (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hFsum
  exact (MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc 0 (Real.pi / 2)))
    (fun k ↦ (hFint k).1) hFsum').symm

private def ballExpSineSeriesTerm (t : ℝ) (k : ℕ) (θ : ℝ) : ℝ :=
  (-(t ^ 2 * Real.sin θ ^ 2) / 2) ^ k / k.factorial

private lemma tsum_ballExpSineSeriesTerm (t θ : ℝ) :
    (∑' k, ballExpSineSeriesTerm t k θ) =
      Real.exp (-(t ^ 2 * Real.sin θ ^ 2) / 2) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rfl

private def ballRadialAuxSeriesIntegrand (n : ℕ) (t : ℝ) (k : ℕ) (θ : ℝ) : ℝ :=
  ((((n - 1 : ℕ) : ℝ) - t ^ 2 * Real.sin θ ^ 2) *
    Real.sin θ ^ (n - 2)) * ballExpSineSeriesTerm t k θ

private lemma continuous_ballRadialAuxSeriesIntegrand (n : ℕ) (t : ℝ) (k : ℕ) :
    Continuous (ballRadialAuxSeriesIntegrand n t k) := by
  unfold ballRadialAuxSeriesIntegrand ballExpSineSeriesTerm
  fun_prop

private lemma norm_ballRadialAuxSeriesIntegrand_le (n : ℕ) (t : ℝ) (k : ℕ)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    ‖ballRadialAuxSeriesIntegrand n t k θ‖ ≤
      ((((n - 1 : ℕ) : ℝ) + t ^ 2) * (t ^ 2 / 2) ^ k / k.factorial) := by
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (hθ.2.trans (by linarith [Real.pi_pos]))
  have hsinle : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hsinpow (m : ℕ) : Real.sin θ ^ m ≤ 1 := pow_le_one₀ hsin hsinle
  have hfactor :
      abs (((n - 1 : ℕ) : ℝ) - t ^ 2 * Real.sin θ ^ 2) ≤
        ((n - 1 : ℕ) : ℝ) + t ^ 2 := by
    calc
      abs (((n - 1 : ℕ) : ℝ) - t ^ 2 * Real.sin θ ^ 2) ≤
          |((n - 1 : ℕ) : ℝ)| + |t ^ 2 * Real.sin θ ^ 2| := abs_sub _ _
      _ = ((n - 1 : ℕ) : ℝ) + t ^ 2 * Real.sin θ ^ 2 := by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg _))]
      _ ≤ ((n - 1 : ℕ) : ℝ) + t ^ 2 := by
        gcongr
        nlinarith [sq_nonneg t, hsinpow 2]
  have hzpow :
      |(-(t ^ 2 * Real.sin θ ^ 2) / 2) ^ k| ≤ (t ^ 2 / 2) ^ k := by
    rw [abs_pow, abs_div, abs_neg, abs_mul, abs_pow, abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
      sq_abs, abs_of_nonneg hsin]
    apply pow_le_pow_left₀ (by positivity)
    gcongr
    nlinarith [sq_nonneg t, hsinpow 2]
  unfold ballRadialAuxSeriesIntegrand ballExpSineSeriesTerm
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div,
    abs_pow, abs_of_nonneg hsin]
  have hfacabs : |(k.factorial : ℝ)| = (k.factorial : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg k.factorial)
  rw [hfacabs]
  have hAB :
      abs (((n - 1 : ℕ) : ℝ) - t ^ 2 * Real.sin θ ^ 2) *
          Real.sin θ ^ (n - 2) ≤ ((n - 1 : ℕ) : ℝ) + t ^ 2 := by
    calc
      abs (((n - 1 : ℕ) : ℝ) - t ^ 2 * Real.sin θ ^ 2) *
          Real.sin θ ^ (n - 2) ≤
          (((n - 1 : ℕ) : ℝ) + t ^ 2) * Real.sin θ ^ (n - 2) :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ ≤ (((n - 1 : ℕ) : ℝ) + t ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left (hsinpow (n - 2)) (by positivity)
      _ = ((n - 1 : ℕ) : ℝ) + t ^ 2 := mul_one _
  have hnum :
      abs (((n - 1 : ℕ) : ℝ) - t ^ 2 * Real.sin θ ^ 2) *
          Real.sin θ ^ (n - 2) *
            abs (-(t ^ 2 * Real.sin θ ^ 2) / 2) ^ k ≤
        (((n - 1 : ℕ) : ℝ) + t ^ 2) * (t ^ 2 / 2) ^ k := by
    exact mul_le_mul hAB (by simpa only [abs_pow] using hzpow)
      (pow_nonneg (abs_nonneg _) _) (by positivity)
  rw [abs_pow]
  calc
    abs (((n - 1 : ℕ) : ℝ) - t ^ 2 * Real.sin θ ^ 2) *
          Real.sin θ ^ (n - 2) *
            (abs (-(t ^ 2 * Real.sin θ ^ 2) / 2) ^ k / (k.factorial : ℝ)) =
        (abs (((n - 1 : ℕ) : ℝ) - t ^ 2 * Real.sin θ ^ 2) *
          Real.sin θ ^ (n - 2) *
            abs (-(t ^ 2 * Real.sin θ ^ 2) / 2) ^ k) / (k.factorial : ℝ) := by ring
    _ ≤ ((((n - 1 : ℕ) : ℝ) + t ^ 2) * (t ^ 2 / 2) ^ k) /
        (k.factorial : ℝ) := div_le_div_of_nonneg_right hnum (by positivity)
    _ = (((n - 1 : ℕ) : ℝ) + t ^ 2) * (t ^ 2 / 2) ^ k /
        (k.factorial : ℝ) := rfl

private lemma summable_integral_norm_ballRadialAuxSeriesIntegrand
    (n : ℕ) (t : ℝ) :
    Summable fun k ↦ ∫ θ in (0 : ℝ)..Real.pi / 2,
      ‖ballRadialAuxSeriesIntegrand n t k θ‖ := by
  let q : ℝ := t ^ 2 / 2
  let A : ℝ := (((n - 1 : ℕ) : ℝ) + t ^ 2) * (Real.pi / 2)
  have hseries : Summable fun k : ℕ ↦ q ^ k / (k.factorial : ℝ) :=
    Real.summable_pow_div_factorial q
  have hmajor : Summable fun k : ℕ ↦ A * (q ^ k / (k.factorial : ℝ)) :=
    hseries.mul_left A
  apply Summable.of_nonneg_of_le
  · intro k
    apply intervalIntegral.integral_nonneg (by positivity)
    intro θ _hθ
    exact norm_nonneg _
  · intro k
    have hcont : Continuous fun θ : ℝ ↦
        ‖ballRadialAuxSeriesIntegrand n t k θ‖ :=
      (continuous_ballRadialAuxSeriesIntegrand n t k).norm
    have hconst : Continuous fun _θ : ℝ ↦
        (((n - 1 : ℕ) : ℝ) + t ^ 2) * q ^ k / (k.factorial : ℝ) :=
      continuous_const
    calc
      (∫ θ in (0 : ℝ)..Real.pi / 2,
          ‖ballRadialAuxSeriesIntegrand n t k θ‖) ≤
          ∫ _θ in (0 : ℝ)..Real.pi / 2,
            (((n - 1 : ℕ) : ℝ) + t ^ 2) * q ^ k /
              (k.factorial : ℝ) := by
        apply intervalIntegral.integral_mono_on (by positivity)
          (hcont.intervalIntegrable _ _) (hconst.intervalIntegrable _ _)
        intro θ hθ
        simpa only [q] using norm_ballRadialAuxSeriesIntegrand_le n t k
          hθ
      _ = A * (q ^ k / (k.factorial : ℝ)) := by
        rw [intervalIntegral.integral_const]
        dsimp only [A]
        dsimp only [q]
        simp only [sub_zero, smul_eq_mul]
        ring
  · exact hmajor

private lemma tsum_ballRadialAuxSeriesIntegrand (n : ℕ) (t θ : ℝ) :
    (∑' k, ballRadialAuxSeriesIntegrand n t k θ) =
      ballRadialAuxIntegrand n t θ := by
  unfold ballRadialAuxSeriesIntegrand ballRadialAuxIntegrand
  rw [tsum_mul_left, tsum_ballExpSineSeriesTerm]

private theorem ballRadialAux_eq_tsum_integrals (n : ℕ) (t : ℝ) :
    ballRadialAux n t = ballGaussianNormalization n *
      ∑' k, ∫ θ in (0 : ℝ)..Real.pi / 2,
        ballRadialAuxSeriesIntegrand n t k θ := by
  rw [ballRadialAux]
  congr 1
  rw [← intervalIntegral_tsum_of_summable_integral_norm]
  · apply intervalIntegral.integral_congr
    intro θ _hθ
    exact (tsum_ballRadialAuxSeriesIntegrand n t θ).symm
  · intro k
    exact (continuous_ballRadialAuxSeriesIntegrand n t k).intervalIntegrable _ _
  · exact summable_integral_norm_ballRadialAuxSeriesIntegrand n t

private def ballRadialAuxIntegralSeriesTerm (n : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  ((-(t ^ 2) / 2) ^ k / (k.factorial : ℝ)) *
    (((n - 1 : ℕ) : ℝ) * ballSineMoment (n - 2 + 2 * k) -
      t ^ 2 * ballSineMoment (n + 2 * k))

private lemma integral_ballRadialAuxSeriesIntegrand {n : ℕ} (hn : 2 ≤ n)
    (t : ℝ) (k : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi / 2,
      ballRadialAuxSeriesIntegrand n t k θ) =
      ballRadialAuxIntegralSeriesTerm n t k := by
  let c : ℝ := (-(t ^ 2) / 2) ^ k / (k.factorial : ℝ)
  have hpoint (θ : ℝ) :
      ballRadialAuxSeriesIntegrand n t k θ =
        c * ((((n - 1 : ℕ) : ℝ) * Real.sin θ ^ (n - 2 + 2 * k)) -
          t ^ 2 * Real.sin θ ^ (n + 2 * k)) := by
    have hseriesPower :
        (-(t ^ 2 * Real.sin θ ^ 2) / 2) ^ k =
          (-(t ^ 2) / 2) ^ k * Real.sin θ ^ (2 * k) := by
      rw [show -(t ^ 2 * Real.sin θ ^ 2) / 2 =
          (-(t ^ 2) / 2) * Real.sin θ ^ 2 by ring, mul_pow, ← pow_mul]
    have hpow1 :
        Real.sin θ ^ (n - 2) * Real.sin θ ^ (2 * k) =
          Real.sin θ ^ (n - 2 + 2 * k) := (pow_add _ _ _).symm
    have hpow2 :
        Real.sin θ ^ 2 * Real.sin θ ^ (n - 2) * Real.sin θ ^ (2 * k) =
          Real.sin θ ^ (n + 2 * k) := by
      rw [← pow_add, show 2 + (n - 2) = n by omega, ← pow_add]
    unfold ballRadialAuxSeriesIntegrand ballExpSineSeriesTerm
    rw [hseriesPower]
    calc
      ((((n - 1 : ℕ) : ℝ) - t ^ 2 * Real.sin θ ^ 2) *
          Real.sin θ ^ (n - 2)) *
          (((-(t ^ 2) / 2) ^ k * Real.sin θ ^ (2 * k)) /
            (k.factorial : ℝ)) =
          c * ((((n - 1 : ℕ) : ℝ) *
              (Real.sin θ ^ (n - 2) * Real.sin θ ^ (2 * k))) -
            t ^ 2 *
              (Real.sin θ ^ 2 * Real.sin θ ^ (n - 2) *
                Real.sin θ ^ (2 * k))) := by
        dsimp only [c]
        ring
      _ = c * ((((n - 1 : ℕ) : ℝ) * Real.sin θ ^ (n - 2 + 2 * k)) -
          t ^ 2 * Real.sin θ ^ (n + 2 * k)) := by rw [hpow1, hpow2]
  calc
    (∫ θ in (0 : ℝ)..Real.pi / 2,
        ballRadialAuxSeriesIntegrand n t k θ) =
        ∫ θ in (0 : ℝ)..Real.pi / 2,
          c * ((((n - 1 : ℕ) : ℝ) * Real.sin θ ^ (n - 2 + 2 * k)) -
            t ^ 2 * Real.sin θ ^ (n + 2 * k)) := by
      apply intervalIntegral.integral_congr
      intro θ _hθ
      exact hpoint θ
    _ = c * (∫ θ in (0 : ℝ)..Real.pi / 2,
          ((((n - 1 : ℕ) : ℝ) * Real.sin θ ^ (n - 2 + 2 * k)) -
            t ^ 2 * Real.sin θ ^ (n + 2 * k))) :=
      intervalIntegral.integral_const_mul _ _
    _ = c * ((((n - 1 : ℕ) : ℝ) * ballSineMoment (n - 2 + 2 * k)) -
          t ^ 2 * ballSineMoment (n + 2 * k)) := by
      rw [intervalIntegral.integral_sub]
      · rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
        rfl
      · exact (by fun_prop : Continuous (fun θ : ℝ ↦
          ((n - 1 : ℕ) : ℝ) * Real.sin θ ^ (n - 2 + 2 * k)))
          |>.intervalIntegrable _ _
      · exact (by fun_prop : Continuous (fun θ : ℝ ↦
          t ^ 2 * Real.sin θ ^ (n + 2 * k)))
          |>.intervalIntegrable _ _
    _ = ballRadialAuxIntegralSeriesTerm n t k := rfl

private theorem ballRadialAux_eq_tsum_raw {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    ballRadialAux n t = ballGaussianNormalization n *
      ∑' k, ballRadialAuxIntegralSeriesTerm n t k := by
  rw [ballRadialAux_eq_tsum_integrals]
  congr 1
  apply tsum_congr
  intro k
  exact integral_ballRadialAuxSeriesIntegrand hn t k

private lemma summable_nat_mul_pow_div_factorial (q : ℝ) :
    Summable fun k : ℕ ↦ (k : ℝ) * q ^ k / (k.factorial : ℝ) := by
  rw [← summable_nat_add_iff 1]
  have h := (Real.summable_pow_div_factorial q).mul_left q
  refine h.congr ?_
  intro k
  rw [show k + 1 = k.succ by omega, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_succ, pow_succ]
  field_simp

private def ballRadialAuxShiftSeriesTerm (n : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  ((-(t ^ 2) / 2) ^ k / (k.factorial : ℝ)) *
    ((2 * k : ℕ) : ℝ) * ballSineMoment (n - 2 + 2 * k)

private lemma summable_ballRadialAuxShiftSeriesTerm (n : ℕ) (t : ℝ) :
    Summable (ballRadialAuxShiftSeriesTerm n t) := by
  let q : ℝ := t ^ 2 / 2
  have hmajor : Summable fun k : ℕ ↦
      Real.pi * ((k : ℝ) * q ^ k / (k.factorial : ℝ)) :=
    (summable_nat_mul_pow_div_factorial q).mul_left Real.pi
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le
    (f := fun k : ℕ ↦ Real.pi * ((k : ℝ) * q ^ k / (k.factorial : ℝ)))
    ?_ ?_ hmajor
  · intro k
    exact norm_nonneg _
  · intro k
    unfold ballRadialAuxShiftSeriesTerm
    have hbaseabs : |-(t ^ 2) / 2| = t ^ 2 / 2 := by
      rw [abs_div, abs_neg, abs_of_nonneg (sq_nonneg t),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2)]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_pow, hbaseabs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k.factorial : ℝ)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 * k : ℕ) : ℝ)),
      abs_of_nonneg (ballSineMoment_nonneg _)]
    dsimp only [q]
    have hm := ballSineMoment_le_pi_div_two (n - 2 + 2 * k)
    have hkq : 0 ≤ (k : ℝ) * (t ^ 2 / 2) ^ k / (k.factorial : ℝ) := by positivity
    calc
      ((t ^ 2 / 2) ^ k / (k.factorial : ℝ)) * ((2 * k : ℕ) : ℝ) *
          ballSineMoment (n - 2 + 2 * k) ≤
          ((t ^ 2 / 2) ^ k / (k.factorial : ℝ)) * ((2 * k : ℕ) : ℝ) *
            (Real.pi / 2) := mul_le_mul_of_nonneg_left hm (by positivity)
      _ = Real.pi * ((k : ℝ) * (t ^ 2 / 2) ^ k /
          (k.factorial : ℝ)) := by push_cast; ring

private lemma summable_ballRadialAuxIntegralSeriesTerm {n : ℕ} (hn : 2 ≤ n)
    (t : ℝ) : Summable (ballRadialAuxIntegralSeriesTerm n t) := by
  have hnorm : Summable fun k ↦
      ‖∫ θ in (0 : ℝ)..Real.pi / 2,
        ballRadialAuxSeriesIntegrand n t k θ‖ := by
    refine Summable.of_nonneg_of_le
      (f := fun k ↦ ∫ θ in (0 : ℝ)..Real.pi / 2,
        ‖ballRadialAuxSeriesIntegrand n t k θ‖) ?_ ?_
      (summable_integral_norm_ballRadialAuxSeriesIntegrand n t)
    · intro k
      exact norm_nonneg _
    · intro k
      exact intervalIntegral.norm_integral_le_integral_norm (by positivity)
  have hintegrals : Summable fun k ↦
      ∫ θ in (0 : ℝ)..Real.pi / 2,
        ballRadialAuxSeriesIntegrand n t k θ := hnorm.of_norm
  exact hintegrals.congr fun k ↦ integral_ballRadialAuxSeriesIntegrand hn t k

private def ballRadialAuxBaseSeriesTerm (n : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  ((-(t ^ 2) / 2) ^ k / (k.factorial : ℝ)) *
    (((n - 1 : ℕ) : ℝ) * ballSineMoment (n - 2 + 2 * k))

private def ballRadialAuxCanonicalSeriesTerm (n : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  ((-(t ^ 2) / 2) ^ k / (k.factorial : ℝ)) *
    ((((n - 1 : ℕ) : ℝ) + ((2 * k : ℕ) : ℝ)) *
      ballSineMoment (n - 2 + 2 * k))

private lemma ballRadialAuxIntegralSeriesTerm_eq_base_add_shift_succ
    {n : ℕ} (hn : 2 ≤ n) (t : ℝ) (k : ℕ) :
    ballRadialAuxIntegralSeriesTerm n t k =
      ballRadialAuxBaseSeriesTerm n t k +
        ballRadialAuxShiftSeriesTerm n t (k + 1) := by
  unfold ballRadialAuxIntegralSeriesTerm ballRadialAuxBaseSeriesTerm
    ballRadialAuxShiftSeriesTerm
  rw [show n - 2 + 2 * (k + 1) = n + 2 * k by omega,
    Nat.factorial_succ]
  push_cast
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

private lemma ballRadialAuxCanonicalSeriesTerm_eq_base_add_shift
    (n : ℕ) (t : ℝ) (k : ℕ) :
    ballRadialAuxCanonicalSeriesTerm n t k =
      ballRadialAuxBaseSeriesTerm n t k +
        ballRadialAuxShiftSeriesTerm n t k := by
  unfold ballRadialAuxCanonicalSeriesTerm ballRadialAuxBaseSeriesTerm
    ballRadialAuxShiftSeriesTerm
  ring

private lemma summable_ballRadialAuxBaseSeriesTerm {n : ℕ} (hn : 2 ≤ n)
    (t : ℝ) : Summable (ballRadialAuxBaseSeriesTerm n t) := by
  have hraw := summable_ballRadialAuxIntegralSeriesTerm hn t
  have hshiftTail : Summable fun k ↦ ballRadialAuxShiftSeriesTerm n t (k + 1) :=
    (summable_nat_add_iff 1).mpr (summable_ballRadialAuxShiftSeriesTerm n t)
  have hdiff := hraw.sub hshiftTail
  exact hdiff.congr fun k ↦ by
    rw [ballRadialAuxIntegralSeriesTerm_eq_base_add_shift_succ hn]
    ring

private lemma summable_ballRadialAuxCanonicalSeriesTerm {n : ℕ} (hn : 2 ≤ n)
    (t : ℝ) : Summable (ballRadialAuxCanonicalSeriesTerm n t) := by
  have h := (summable_ballRadialAuxBaseSeriesTerm hn t).add
    (summable_ballRadialAuxShiftSeriesTerm n t)
  exact h.congr fun k ↦ (ballRadialAuxCanonicalSeriesTerm_eq_base_add_shift n t k).symm

private theorem tsum_ballRadialAuxIntegralSeriesTerm_eq_canonical {n : ℕ}
    (hn : 2 ≤ n) (t : ℝ) :
    (∑' k, ballRadialAuxIntegralSeriesTerm n t k) =
      ∑' k, ballRadialAuxCanonicalSeriesTerm n t k := by
  have hbase := summable_ballRadialAuxBaseSeriesTerm hn t
  have hshift := summable_ballRadialAuxShiftSeriesTerm n t
  have hshiftTail : Summable fun k ↦ ballRadialAuxShiftSeriesTerm n t (k + 1) :=
    (summable_nat_add_iff 1).mpr hshift
  have hrawDecomp :
      (∑' k, ballRadialAuxIntegralSeriesTerm n t k) =
        ∑' k, (ballRadialAuxBaseSeriesTerm n t k +
          ballRadialAuxShiftSeriesTerm n t (k + 1)) := by
    apply tsum_congr
    intro k
    exact ballRadialAuxIntegralSeriesTerm_eq_base_add_shift_succ hn t k
  have hcanonicalDecomp :
      (∑' k, ballRadialAuxCanonicalSeriesTerm n t k) =
        ∑' k, (ballRadialAuxBaseSeriesTerm n t k +
          ballRadialAuxShiftSeriesTerm n t k) := by
    apply tsum_congr
    intro k
    exact ballRadialAuxCanonicalSeriesTerm_eq_base_add_shift n t k
  have htail :
      (∑' k, ballRadialAuxShiftSeriesTerm n t (k + 1)) =
        ∑' k, ballRadialAuxShiftSeriesTerm n t k := by
    have hhead := hshift.tsum_eq_zero_add
    have hzero : ballRadialAuxShiftSeriesTerm n t 0 = 0 := by
      simp [ballRadialAuxShiftSeriesTerm]
    rw [hzero, zero_add] at hhead
    exact hhead.symm
  rw [hrawDecomp, hcanonicalDecomp, hbase.tsum_add hshiftTail,
    hbase.tsum_add hshift, htail]

private theorem ballRadialAux_eq_tsum_canonical {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    ballRadialAux n t = ballGaussianNormalization n *
      ∑' k, ballRadialAuxCanonicalSeriesTerm n t k := by
  rw [ballRadialAux_eq_tsum_raw hn, tsum_ballRadialAuxIntegralSeriesTerm_eq_canonical hn]

/-- Ball's spherical projection transform for a radial density in dimension `n - 1`. -/
def ballRadialProjectionTransform (n : ℕ) (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  (2 / Real.pi) *
    ∫ θ in (0 : ℝ)..Real.pi / 2, f (r * Real.sin θ) * Real.sin θ ^ (n - 1)

private def ballRadialProjectionSeriesIntegrand
    (n : ℕ) (r : ℝ) (k : ℕ) (θ : ℝ) : ℝ :=
  ballRadialAuxCanonicalSeriesTerm n (r * Real.sin θ) k *
    Real.sin θ ^ (n - 1)

private lemma continuous_ballRadialProjectionSeriesIntegrand
    (n : ℕ) (r : ℝ) (k : ℕ) :
    Continuous (ballRadialProjectionSeriesIntegrand n r k) := by
  unfold ballRadialProjectionSeriesIntegrand ballRadialAuxCanonicalSeriesTerm
  fun_prop

private lemma norm_ballRadialProjectionSeriesIntegrand_le
    (n : ℕ) (r : ℝ) (k : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    ‖ballRadialProjectionSeriesIntegrand n r k θ‖ ≤
      ((((n - 1 : ℕ) : ℝ) + ((2 * k : ℕ) : ℝ)) * (Real.pi / 2) *
        (r ^ 2 / 2) ^ k / (k.factorial : ℝ)) := by
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
      (hθ.2.trans (by linarith [Real.pi_pos]))
  have hsinle : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hsinpow (m : ℕ) : Real.sin θ ^ m ≤ 1 := pow_le_one₀ hsin hsinle
  have hbase :
      abs (-((r * Real.sin θ) ^ 2) / 2) ^ k ≤ (r ^ 2 / 2) ^ k := by
    have hbase₀ : abs (-((r * Real.sin θ) ^ 2) / 2) ≤ r ^ 2 / 2 := by
      rw [abs_div, abs_neg, abs_pow, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2), mul_pow, sq_abs,
        abs_of_nonneg hsin]
      nlinarith [sq_nonneg r, hsinpow 2]
    exact pow_le_pow_left₀ (abs_nonneg _) hbase₀ k
  unfold ballRadialProjectionSeriesIntegrand ballRadialAuxCanonicalSeriesTerm
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k.factorial : ℝ)),
    abs_mul,
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) + ((2 * k : ℕ) : ℝ)),
    abs_of_nonneg (ballSineMoment_nonneg _),
    abs_pow, abs_of_nonneg hsin]
  have hA :
      abs (-((r * Real.sin θ) ^ 2) / 2) ^ k / (k.factorial : ℝ) ≤
        (r ^ 2 / 2) ^ k / (k.factorial : ℝ) :=
    div_le_div_of_nonneg_right hbase (by positivity)
  have hBC :
      (((n - 1 : ℕ) : ℝ) + ((2 * k : ℕ) : ℝ)) *
          ballSineMoment (n - 2 + 2 * k) ≤
        (((n - 1 : ℕ) : ℝ) + ((2 * k : ℕ) : ℝ)) * (Real.pi / 2) :=
    mul_le_mul_of_nonneg_left (ballSineMoment_le_pi_div_two _) (by positivity)
  have hABC :
      (abs (-((r * Real.sin θ) ^ 2) / 2) ^ k / (k.factorial : ℝ)) *
          ((((n - 1 : ℕ) : ℝ) + ((2 * k : ℕ) : ℝ)) *
            ballSineMoment (n - 2 + 2 * k)) ≤
        ((r ^ 2 / 2) ^ k / (k.factorial : ℝ)) *
          ((((n - 1 : ℕ) : ℝ) + ((2 * k : ℕ) : ℝ)) *
            (Real.pi / 2)) := by
    exact mul_le_mul hA hBC
      (mul_nonneg (by positivity) (ballSineMoment_nonneg _)) (by positivity)
  calc
    abs (-((r * Real.sin θ) ^ 2) / 2) ^ k / (k.factorial : ℝ) *
          ((((n - 1 : ℕ) : ℝ) + ((2 * k : ℕ) : ℝ)) *
            ballSineMoment (n - 2 + 2 * k)) *
          Real.sin θ ^ (n - 1) ≤
          ((r ^ 2 / 2) ^ k / (k.factorial : ℝ)) *
          ((((n - 1 : ℕ) : ℝ) + ((2 * k : ℕ) : ℝ)) *
            (Real.pi / 2)) * 1 := by
      calc
        _ ≤ ((r ^ 2 / 2) ^ k / (k.factorial : ℝ)) *
            ((((n - 1 : ℕ) : ℝ) + ((2 * k : ℕ) : ℝ)) *
              (Real.pi / 2)) * Real.sin θ ^ (n - 1) :=
          mul_le_mul_of_nonneg_right hABC (by positivity)
        _ ≤ ((r ^ 2 / 2) ^ k / (k.factorial : ℝ)) *
            ((((n - 1 : ℕ) : ℝ) + ((2 * k : ℕ) : ℝ)) *
              (Real.pi / 2)) * 1 :=
          mul_le_mul_of_nonneg_left (hsinpow (n - 1)) (by positivity)
    _ = (((n - 1 : ℕ) : ℝ) + ((2 * k : ℕ) : ℝ)) * (Real.pi / 2) *
        (r ^ 2 / 2) ^ k / (k.factorial : ℝ) := by ring

private lemma summable_integral_norm_ballRadialProjectionSeriesIntegrand
    (n : ℕ) (r : ℝ) :
    Summable fun k ↦ ∫ θ in (0 : ℝ)..Real.pi / 2,
      ‖ballRadialProjectionSeriesIntegrand n r k θ‖ := by
  let q : ℝ := r ^ 2 / 2
  let A : ℝ := (Real.pi / 2) ^ 2 * ((n - 1 : ℕ) : ℝ)
  let B : ℝ := 2 * (Real.pi / 2) ^ 2
  have hmajor₀ : Summable fun k : ℕ ↦
      A * (q ^ k / (k.factorial : ℝ)) +
        B * ((k : ℝ) * q ^ k / (k.factorial : ℝ)) :=
    ((Real.summable_pow_div_factorial q).mul_left A).add
      ((summable_nat_mul_pow_div_factorial q).mul_left B)
  have hmajor : Summable fun k : ℕ ↦
      ((((n - 1 : ℕ) : ℝ) + ((2 * k : ℕ) : ℝ)) * (Real.pi / 2) *
        q ^ k / (k.factorial : ℝ)) * (Real.pi / 2) := by
    refine hmajor₀.congr ?_
    intro k
    dsimp only [A, B]
    push_cast
    ring
  refine Summable.of_nonneg_of_le
    (f := fun k : ℕ ↦
      ((((n - 1 : ℕ) : ℝ) + ((2 * k : ℕ) : ℝ)) * (Real.pi / 2) *
        q ^ k / (k.factorial : ℝ)) * (Real.pi / 2)) ?_ ?_ hmajor
  · intro k
    apply intervalIntegral.integral_nonneg (by positivity)
    intro θ _hθ
    exact norm_nonneg _
  · intro k
    have hcont := (continuous_ballRadialProjectionSeriesIntegrand n r k).norm
    calc
      (∫ θ in (0 : ℝ)..Real.pi / 2,
          ‖ballRadialProjectionSeriesIntegrand n r k θ‖) ≤
          ∫ _θ in (0 : ℝ)..Real.pi / 2,
            ((((n - 1 : ℕ) : ℝ) + ((2 * k : ℕ) : ℝ)) * (Real.pi / 2) *
              q ^ k / (k.factorial : ℝ)) := by
        apply intervalIntegral.integral_mono_on (by positivity)
          (hcont.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
        intro θ hθ
        simpa only [q] using norm_ballRadialProjectionSeriesIntegrand_le n r k hθ
      _ = ((((n - 1 : ℕ) : ℝ) + ((2 * k : ℕ) : ℝ)) * (Real.pi / 2) *
          q ^ k / (k.factorial : ℝ)) * (Real.pi / 2) := by
        rw [intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        ring

private lemma tsum_ballRadialProjectionSeriesIntegrand
    (n : ℕ) (r θ : ℝ) :
    (∑' k, ballRadialProjectionSeriesIntegrand n r k θ) =
      (∑' k, ballRadialAuxCanonicalSeriesTerm n (r * Real.sin θ) k) *
        Real.sin θ ^ (n - 1) := by
  unfold ballRadialProjectionSeriesIntegrand
  rw [tsum_mul_right]

private lemma integral_ballRadialProjectionSeriesIntegrand
    {n : ℕ} (_hn : 2 ≤ n) (r : ℝ) (k : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi / 2,
      ballRadialProjectionSeriesIntegrand n r k θ) =
      ((-(r ^ 2) / 2) ^ k / (k.factorial : ℝ)) *
        (((((n - 1 : ℕ) : ℝ) + ((2 * k : ℕ) : ℝ)) *
          ballSineMoment (n - 2 + 2 * k)) *
            ballSineMoment (n - 1 + 2 * k)) := by
  let c : ℝ := (-(r ^ 2) / 2) ^ k / (k.factorial : ℝ)
  let M : ℝ := (((n - 1 : ℕ) : ℝ) + ((2 * k : ℕ) : ℝ)) *
    ballSineMoment (n - 2 + 2 * k)
  have hpoint (θ : ℝ) :
      ballRadialProjectionSeriesIntegrand n r k θ =
        (c * M) * Real.sin θ ^ (n - 1 + 2 * k) := by
    have hseriesPower :
        (-((r * Real.sin θ) ^ 2) / 2) ^ k =
          (-(r ^ 2) / 2) ^ k * Real.sin θ ^ (2 * k) := by
      rw [show -((r * Real.sin θ) ^ 2) / 2 =
          (-(r ^ 2) / 2) * Real.sin θ ^ 2 by ring, mul_pow, ← pow_mul]
    unfold ballRadialProjectionSeriesIntegrand ballRadialAuxCanonicalSeriesTerm
    rw [hseriesPower]
    have hpow : Real.sin θ ^ (2 * k) * Real.sin θ ^ (n - 1) =
        Real.sin θ ^ (n - 1 + 2 * k) := by
      rw [mul_comm, ← pow_add]
    calc
      ((((-(r ^ 2) / 2) ^ k * Real.sin θ ^ (2 * k)) /
          (k.factorial : ℝ)) * M) * Real.sin θ ^ (n - 1) =
          c * M * (Real.sin θ ^ (2 * k) * Real.sin θ ^ (n - 1)) := by
        dsimp only [c]
        ring
      _ = (c * M) * Real.sin θ ^ (n - 1 + 2 * k) := by rw [hpow]
  calc
    (∫ θ in (0 : ℝ)..Real.pi / 2,
        ballRadialProjectionSeriesIntegrand n r k θ) =
        ∫ θ in (0 : ℝ)..Real.pi / 2,
          (c * M) * Real.sin θ ^ (n - 1 + 2 * k) := by
      apply intervalIntegral.integral_congr
      intro θ _hθ
      exact hpoint θ
    _ = (c * M) * ballSineMoment (n - 1 + 2 * k) := by
      rw [intervalIntegral.integral_const_mul]
      rfl
    _ = ((-(r ^ 2) / 2) ^ k / (k.factorial : ℝ)) *
        (((((n - 1 : ℕ) : ℝ) + ((2 * k : ℕ) : ℝ)) *
          ballSineMoment (n - 2 + 2 * k)) *
            ballSineMoment (n - 1 + 2 * k)) := by
      dsimp only [c, M]
      ring

private lemma two_div_pi_mul_integral_ballRadialProjectionSeriesIntegrand
    {n : ℕ} (hn : 2 ≤ n) (r : ℝ) (k : ℕ) :
    (2 / Real.pi) *
      (∫ θ in (0 : ℝ)..Real.pi / 2,
        ballRadialProjectionSeriesIntegrand n r k θ) =
      (-(r ^ 2) / 2) ^ k / (k.factorial : ℝ) := by
  rw [integral_ballRadialProjectionSeriesIntegrand hn]
  have hindex : n - 1 + 2 * k = (n - 2 + 2 * k) + 1 := by omega
  rw [hindex]
  have hcast :
      (((n - 1 : ℕ) : ℝ) + ((2 * k : ℕ) : ℝ)) =
        (((n - 2 + 2 * k + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show (n - 1) + 2 * k = n - 2 + 2 * k + 1 by omega)
  rw [hcast, succ_mul_ballSineMoment_mul_succ]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp

private theorem ballRadialProjectionTransform_aux_eq_tsum
    {n : ℕ} (hn : 2 ≤ n) (r : ℝ) :
    ballRadialProjectionTransform n (ballRadialAux n) r =
      ballGaussianNormalization n *
        ∑' k, (2 / Real.pi) *
          ∫ θ in (0 : ℝ)..Real.pi / 2,
            ballRadialProjectionSeriesIntegrand n r k θ := by
  unfold ballRadialProjectionTransform
  calc
    (2 / Real.pi) *
        (∫ θ in (0 : ℝ)..Real.pi / 2,
          ballRadialAux n (r * Real.sin θ) * Real.sin θ ^ (n - 1)) =
        (2 / Real.pi) *
          (∫ θ in (0 : ℝ)..Real.pi / 2,
            ballGaussianNormalization n *
              ((∑' k, ballRadialAuxCanonicalSeriesTerm n
                  (r * Real.sin θ) k) * Real.sin θ ^ (n - 1))) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro θ _hθ
      dsimp only
      rw [ballRadialAux_eq_tsum_canonical hn]
      ring
    _ = ballGaussianNormalization n *
        ((2 / Real.pi) *
          (∫ θ in (0 : ℝ)..Real.pi / 2,
            ∑' k, ballRadialProjectionSeriesIntegrand n r k θ)) := by
      rw [show (fun θ : ℝ ↦ ballGaussianNormalization n *
          ((∑' k, ballRadialAuxCanonicalSeriesTerm n (r * Real.sin θ) k) *
            Real.sin θ ^ (n - 1))) =
          fun θ ↦ ballGaussianNormalization n *
            (∑' k, ballRadialProjectionSeriesIntegrand n r k θ) by
        funext θ
        rw [tsum_ballRadialProjectionSeriesIntegrand]]
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = ballGaussianNormalization n *
        ((2 / Real.pi) *
          (∑' k, ∫ θ in (0 : ℝ)..Real.pi / 2,
            ballRadialProjectionSeriesIntegrand n r k θ)) := by
      rw [intervalIntegral_tsum_of_summable_integral_norm]
      · intro k
        exact (continuous_ballRadialProjectionSeriesIntegrand n r k)
          |>.intervalIntegrable _ _
      · exact summable_integral_norm_ballRadialProjectionSeriesIntegrand n r
    _ = ballGaussianNormalization n *
        ∑' k, (2 / Real.pi) *
          ∫ θ in (0 : ℝ)..Real.pi / 2,
            ballRadialProjectionSeriesIntegrand n r k θ := by
      rw [tsum_mul_left]

/-- Ball's signed radial density projects exactly to the standard Gaussian radial density. -/
theorem ballRadialAux_projection_eq_standardGaussian
    {n : ℕ} (hn : 2 ≤ n) (r : ℝ) :
    ballRadialProjectionTransform n (ballRadialAux n) r =
      ballGaussianNormalization n * Real.exp (-(r ^ 2) / 2) := by
  rw [ballRadialProjectionTransform_aux_eq_tsum hn]
  congr 1
  calc
    (∑' k, (2 / Real.pi) *
        ∫ θ in (0 : ℝ)..Real.pi / 2,
          ballRadialProjectionSeriesIntegrand n r k θ) =
        ∑' k, (-(r ^ 2) / 2) ^ k / (k.factorial : ℝ) := by
      apply tsum_congr
      intro k
      exact two_div_pi_mul_integral_ballRadialProjectionSeriesIntegrand hn r k
    _ = Real.exp (-(r ^ 2) / 2) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- The positive part of Ball's signed density has spherical projection at least the standard
Gaussian radial density. -/
theorem standardGaussianDensityReal_le_ballRadialMajorant_projection
    {n : ℕ} (hn : 2 ≤ n) (r : ℝ) :
    ballGaussianNormalization n * Real.exp (-(r ^ 2) / 2) ≤
      ballRadialProjectionTransform n (ballRadialMajorant n) r := by
  rw [← ballRadialAux_projection_eq_standardGaussian hn r]
  unfold ballRadialProjectionTransform
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono_on (by positivity)
  · exact ((continuous_ballRadialAux n).comp
      (continuous_const.mul Real.continuous_sin) |>.mul
        (Real.continuous_sin.pow (n - 1))).intervalIntegrable _ _
  · exact ((continuous_ballRadialMajorant n).comp
      (continuous_const.mul Real.continuous_sin) |>.mul
        (Real.continuous_sin.pow (n - 1))).intervalIntegrable _ _
  · intro θ hθ
    have hsin : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
        (hθ.2.trans (by linarith [Real.pi_pos]))
    exact mul_le_mul_of_nonneg_right
      (ballRadialAux_le_ballRadialMajorant n (r * Real.sin θ))
      (pow_nonneg hsin _)


end ProbabilityTheory
