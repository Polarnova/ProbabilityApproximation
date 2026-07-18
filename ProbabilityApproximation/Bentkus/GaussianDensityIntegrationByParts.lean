/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.ConvexGeometry.GaussianShell
import ProbabilityApproximation.Bentkus.GaussianIntegrationByParts

/-!
# Gaussian-density specialization of Bentkus's Lipschitz integration by parts

This file proves the instance of Bentkus (2004), Lemma 2.3 used in equation (3.32).  For a
Lipschitz function `f`, the rapidly decreasing factor is the first directional derivative of the
standard Gaussian density, and its derivative is the corresponding second contraction:

`|∫ f(x) D²φ(x)[w,h] dx| ≤ Lip(f) ‖h‖ ∫_{tsupport f} |Dφ(x)[w]| dx`.

The proof follows Bentkus's difference-quotient argument, using Rademacher's theorem for the
Lipschitz factor and an integrable Gaussian majorant for bounded translates.  Gaussian polynomial
moments are transferred from `stdGaussian` to Euclidean volume by the standard Gaussian density
identity.
-/

open Filter MeasureTheory Measure Module Topology Set
open scoped NNReal ENNReal Topology LineDeriv RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

private lemma integrable_norm_pow_mul_standardGaussianDensityReal
    {d k : ℕ} :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) ↦
      ‖x‖ ^ k * standardGaussianDensityReal x) := by
  have hmoment : Integrable
      (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ k)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    simpa only [id_eq] using
      (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin d)))
        (k : ℝ≥0∞) (by simp)).integrable_norm_pow'
  rw [stdGaussian_eq_withDensity_standardGaussianDensityReal] at hmoment
  have h := (integrable_withDensity_iff_integrable_smul'
    measurable_standardGaussianDensityReal.ennreal_ofReal (by simp)).mp hmoment
  simp_rw [ENNReal.toReal_ofReal (standardGaussianDensityReal_nonneg _), smul_eq_mul] at h
  simpa only [mul_comm] using h

private lemma standardGaussianDensityNormalization_nonneg
    {d : ℕ} : 0 ≤ standardGaussianDensityNormalization (EuclideanSpace ℝ (Fin d)) := by
  unfold standardGaussianDensityNormalization
  positivity

private lemma standardGaussianDensity_nonneg
    {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤ standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x := by
  unfold standardGaussianDensity
  exact mul_nonneg standardGaussianDensityNormalization_nonneg (Real.exp_nonneg _)

private lemma norm_fderiv_standardGaussianDensityD1_le
    {d : ℕ} (x w : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ (fun y ↦ standardGaussianDensityD1 y w) x‖ ≤
      ‖w‖ * (‖x‖ ^ 2 + 1) * standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact mul_nonneg
      (mul_nonneg (norm_nonneg w) (by positivity))
      (standardGaussianDensity_nonneg x)
  intro h
  rw [fderiv_standardGaussianDensityD1_apply]
  rw [Real.norm_eq_abs]
  unfold standardGaussianDensityD2
  rw [abs_mul, abs_of_nonneg (standardGaussianDensity_nonneg x)]
  have hxw := abs_real_inner_le_norm x w
  have hxh := abs_real_inner_le_norm x h
  have hwh := abs_real_inner_le_norm w h
  calc
    |inner ℝ x w * inner ℝ x h - inner ℝ w h| *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x ≤
      (|inner ℝ x w| * |inner ℝ x h| + |inner ℝ w h|) *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x := by
          apply mul_le_mul_of_nonneg_right _ (standardGaussianDensity_nonneg x)
          simpa only [abs_mul] using
            abs_sub (inner ℝ x w * inner ℝ x h) (inner ℝ w h)
    _ ≤ (‖x‖ * ‖w‖ * (‖x‖ * ‖h‖) + ‖w‖ * ‖h‖) *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x := by
          apply mul_le_mul_of_nonneg_right _ (standardGaussianDensity_nonneg x)
          apply add_le_add
          · exact mul_le_mul hxw hxh (abs_nonneg _) (mul_nonneg (norm_nonneg x) (norm_nonneg w))
          · exact hwh
    _ = (‖w‖ * (‖x‖ ^ 2 + 1) *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x) * ‖h‖ := by ring

private lemma standardGaussianDensity_le_exp_quarter_of_dist_le
    {d : ℕ} {x z : EuclideanSpace ℝ (Fin d)} {R : ℝ}
    (hR : 0 ≤ R) (hzx : dist z x ≤ R) :
    standardGaussianDensity (EuclideanSpace ℝ (Fin d)) z ≤
      standardGaussianDensityNormalization (EuclideanSpace ℝ (Fin d)) *
        Real.exp (R ^ 2 / 2) * Real.exp (-‖x‖ ^ 2 / 4) := by
  have hnorm : ‖x‖ ≤ ‖z‖ + R := by
    calc
      ‖x‖ = ‖z + (x - z)‖ := by congr 1; abel
      _ ≤ ‖z‖ + ‖x - z‖ := norm_add_le _ _
      _ = ‖z‖ + dist z x := by rw [dist_eq_norm, norm_sub_rev]
      _ ≤ ‖z‖ + R := by gcongr
  have hsquare1 : ‖x‖ ^ 2 ≤ (‖z‖ + R) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg x) (add_nonneg (norm_nonneg z) hR)).2 hnorm
  have hsquare2 : (‖z‖ + R) ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * R ^ 2 := by
    nlinarith [sq_nonneg (‖z‖ - R)]
  have hexponent : -‖z‖ ^ 2 / 2 ≤ R ^ 2 / 2 + -‖x‖ ^ 2 / 4 := by
    nlinarith [hsquare1.trans hsquare2]
  unfold standardGaussianDensity
  calc
    standardGaussianDensityNormalization (EuclideanSpace ℝ (Fin d)) *
        Real.exp (-‖z‖ ^ 2 / 2) ≤
      standardGaussianDensityNormalization (EuclideanSpace ℝ (Fin d)) *
        Real.exp (R ^ 2 / 2 + -‖x‖ ^ 2 / 4) := by
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
            standardGaussianDensityNormalization_nonneg
    _ = standardGaussianDensityNormalization (EuclideanSpace ℝ (Fin d)) *
        Real.exp (R ^ 2 / 2) * Real.exp (-‖x‖ ^ 2 / 4) := by
          rw [Real.exp_add]
          ring

private lemma norm_fderiv_standardGaussianDensityD1_le_exp_quarter_of_dist_le
    {d : ℕ} {x z w : EuclideanSpace ℝ (Fin d)} {R : ℝ}
    (hR : 0 ≤ R) (hzx : dist z x ≤ R) :
    ‖fderiv ℝ (fun y ↦ standardGaussianDensityD1 y w) z‖ ≤
      (‖w‖ * ((1 + R) ^ 2 + 1) *
        standardGaussianDensityNormalization (EuclideanSpace ℝ (Fin d)) *
          Real.exp (R ^ 2 / 2)) *
        (1 + ‖x‖) ^ 2 * Real.exp (-‖x‖ ^ 2 / 4) := by
  have hznorm : ‖z‖ ≤ ‖x‖ + R := by
    calc
      ‖z‖ = ‖x + (z - x)‖ := by congr 1; abel
      _ ≤ ‖x‖ + ‖z - x‖ := norm_add_le _ _
      _ = ‖x‖ + dist z x := by rw [dist_eq_norm]
      _ ≤ ‖x‖ + R := by gcongr
  have hlinear : ‖z‖ ≤ (1 + R) * (1 + ‖x‖) := by
    calc
      ‖z‖ ≤ ‖x‖ + R := hznorm
      _ ≤ (1 + R) * (1 + ‖x‖) := by
        nlinarith [norm_nonneg x]
  have hfactor : 0 ≤ (1 + R) * (1 + ‖x‖) :=
    mul_nonneg (by linarith) (by positivity)
  have hsquare : ‖z‖ ^ 2 ≤ ((1 + R) * (1 + ‖x‖)) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg z) hfactor).2 hlinear
  have hone : 1 ≤ (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
  have hpoly : ‖z‖ ^ 2 + 1 ≤ ((1 + R) ^ 2 + 1) * (1 + ‖x‖) ^ 2 := by
    nlinarith
  calc
    ‖fderiv ℝ (fun y ↦ standardGaussianDensityD1 y w) z‖ ≤
        ‖w‖ * (‖z‖ ^ 2 + 1) *
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) z :=
      norm_fderiv_standardGaussianDensityD1_le z w
    _ ≤ ‖w‖ * (((1 + R) ^ 2 + 1) * (1 + ‖x‖) ^ 2) *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) z := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpoly (norm_nonneg w))
        (standardGaussianDensity_nonneg z)
    _ ≤ ‖w‖ * (((1 + R) ^ 2 + 1) * (1 + ‖x‖) ^ 2) *
        (standardGaussianDensityNormalization (EuclideanSpace ℝ (Fin d)) *
          Real.exp (R ^ 2 / 2) * Real.exp (-‖x‖ ^ 2 / 4)) := by
      apply mul_le_mul_of_nonneg_left
      · exact standardGaussianDensity_le_exp_quarter_of_dist_le hR hzx
      · exact mul_nonneg (norm_nonneg w) (mul_nonneg (by positivity) (by positivity))
    _ = _ := by ring

private lemma standardGaussianDensityRealNormalization_pos
    {d : ℕ} : 0 < (√(2 * Real.pi))⁻¹ ^ d := by
  positivity

private lemma integrable_norm_pow_mul_gaussianExponentHalf
    {d k : ℕ} :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) ↦
      ‖x‖ ^ k * Real.exp (-‖x‖ ^ 2 / 2)) := by
  let c : ℝ := (√(2 * Real.pi))⁻¹ ^ d
  have hc : c ≠ 0 := ne_of_gt standardGaussianDensityRealNormalization_pos
  have h := (integrable_norm_pow_mul_standardGaussianDensityReal (d := d) (k := k)).const_mul c⁻¹
  convert h using 1
  funext x
  unfold standardGaussianDensityReal c
  field_simp

private lemma integrable_norm_pow_mul_gaussianExponentQuarter
    {d k : ℕ} :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) ↦
      ‖x‖ ^ k * Real.exp (-‖x‖ ^ 2 / 4)) := by
  let R : ℝ := (√2)⁻¹
  have hR : R ≠ 0 := by
    dsimp [R]
    positivity
  have hsqrt : (√2) ^ 2 = (2 : ℝ) := by norm_num
  have h := (integrable_norm_pow_mul_gaussianExponentHalf (d := d) (k := k)).comp_smul hR
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hRpow : R ^ k ≠ 0 := pow_ne_zero _ hR
  have h' := h.const_mul (R ^ k)⁻¹
  convert h' using 1
  funext x
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hRpos, mul_pow]
  have hRsq : R ^ 2 = (1 / 2 : ℝ) := by
    dsimp [R]
    rw [inv_pow, hsqrt]
    norm_num
  rw [hRsq]
  field_simp
  norm_num

private lemma integrable_one_add_norm_cube_mul_gaussianExponentQuarter
    {d : ℕ} :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) ↦
      (1 + ‖x‖) ^ 3 * Real.exp (-‖x‖ ^ 2 / 4)) := by
  have h0 := integrable_norm_pow_mul_gaussianExponentQuarter (d := d) (k := 0)
  have h1 := integrable_norm_pow_mul_gaussianExponentQuarter (d := d) (k := 1)
  have h2 := integrable_norm_pow_mul_gaussianExponentQuarter (d := d) (k := 2)
  have h3 := integrable_norm_pow_mul_gaussianExponentQuarter (d := d) (k := 3)
  apply (((h3.add (h2.const_mul 3)).add (h1.const_mul 3)).add h0).congr
  filter_upwards with x
  simp only [Pi.add_apply]
  ring

private lemma abs_lipschitz_le_one_add_norm'
    {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (x : EuclideanSpace ℝ (Fin d)) :
    |f x| ≤ (|f 0| + (C : ℝ)) * (1 + ‖x‖) := by
  calc
    |f x| = ‖f x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖f x - f 0‖ + ‖f 0‖ := by
      simpa only [sub_add_cancel] using norm_add_le (f x - f 0) (f 0)
    _ ≤ (C : ℝ) * ‖x - 0‖ + ‖f 0‖ := by
      gcongr
      exact hf.norm_sub_le x 0
    _ ≤ (|f 0| + (C : ℝ)) * (1 + ‖x‖) := by
      rw [sub_zero, Real.norm_eq_abs]
      nlinarith [norm_nonneg x, C.coe_nonneg, abs_nonneg (f 0)]

lemma integrable_standardGaussianDensityD1_volume
    {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x ↦ standardGaussianDensityD1 x w) := by
  let N := standardGaussianDensityNormalization (EuclideanSpace ℝ (Fin d))
  have hmajor := (integrable_norm_pow_mul_gaussianExponentHalf (d := d) (k := 1)).const_mul
    (N * ‖w‖)
  apply hmajor.mono' (continuous_standardGaussianDensityD1 w).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs]
  unfold standardGaussianDensityD1 standardGaussianDensity
  dsimp only [N]
  rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg standardGaussianDensityNormalization_nonneg,
    abs_of_pos (Real.exp_pos _)]
  have hi := abs_real_inner_le_norm x w
  calc
    |inner ℝ x w| *
        (standardGaussianDensityNormalization (EuclideanSpace ℝ (Fin d)) *
          Real.exp (-‖x‖ ^ 2 / 2)) ≤
      (‖x‖ * ‖w‖) *
        (standardGaussianDensityNormalization (EuclideanSpace ℝ (Fin d)) *
          Real.exp (-‖x‖ ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_right hi (mul_nonneg standardGaussianDensityNormalization_nonneg
        (Real.exp_nonneg _))
    _ = standardGaussianDensityNormalization (EuclideanSpace ℝ (Fin d)) * ‖w‖ *
        (‖x‖ ^ 1 * Real.exp (-‖x‖ ^ 2 / 2)) := by ring

private lemma integrable_lipschitz_mul_standardGaussianDensityD1
    {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (w : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x ↦ f x * standardGaussianDensityD1 x w) := by
  let A : ℝ := |f 0| + (C : ℝ)
  let N := standardGaussianDensityNormalization (EuclideanSpace ℝ (Fin d))
  have h1 := integrable_norm_pow_mul_gaussianExponentHalf (d := d) (k := 1)
  have h2 := integrable_norm_pow_mul_gaussianExponentHalf (d := d) (k := 2)
  have hmajor := (h1.add h2).const_mul (A * N * ‖w‖)
  apply hmajor.mono'
    (hf.continuous.mul (continuous_standardGaussianDensityD1 w)).aestronglyMeasurable
  filter_upwards with x
  simp only [Pi.add_apply, Pi.mul_apply, pow_one]
  rw [Real.norm_eq_abs, abs_mul]
  have hfbound := abs_lipschitz_le_one_add_norm' hf x
  have hi := abs_real_inner_le_norm x w
  unfold standardGaussianDensityD1 standardGaussianDensity
  dsimp only [A, N]
  rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg standardGaussianDensityNormalization_nonneg,
    abs_of_pos (Real.exp_pos _)]
  have hA : 0 ≤ |f 0| + (C : ℝ) := by positivity
  have hN := standardGaussianDensityNormalization_nonneg (d := d)
  have hexp := Real.exp_pos (-‖x‖ ^ 2 / 2)
  calc
    |f x| * (|inner ℝ x w| *
        (standardGaussianDensityNormalization (EuclideanSpace ℝ (Fin d)) *
          Real.exp (-‖x‖ ^ 2 / 2))) ≤
      ((|f 0| + (C : ℝ)) * (1 + ‖x‖)) *
        ((‖x‖ * ‖w‖) *
          (standardGaussianDensityNormalization (EuclideanSpace ℝ (Fin d)) *
            Real.exp (-‖x‖ ^ 2 / 2))) := by gcongr
    _ = (|f 0| + (C : ℝ)) *
        standardGaussianDensityNormalization (EuclideanSpace ℝ (Fin d)) * ‖w‖ *
          (‖x‖ * Real.exp (-‖x‖ ^ 2 / 2) +
            ‖x‖ ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)) := by ring

private lemma integrable_lipschitz_mul_standardGaussianDensity
    {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) :
    Integrable (fun x ↦
      f x * standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x) := by
  let A : ℝ := |f 0| + (C : ℝ)
  have h0 : Integrable (fun x : EuclideanSpace ℝ (Fin d) ↦
      standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x) := by
    simpa only [pow_zero, one_mul, standardGaussianDensityReal_eq_standardGaussianDensity] using
      (integrable_norm_pow_mul_standardGaussianDensityReal (d := d) (k := 0))
  have h1 : Integrable (fun x : EuclideanSpace ℝ (Fin d) ↦
      ‖x‖ * standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x) := by
    simpa only [pow_one, standardGaussianDensityReal_eq_standardGaussianDensity] using
      (integrable_norm_pow_mul_standardGaussianDensityReal (d := d) (k := 1))
  have hmajor := (h0.add h1).const_mul A
  apply hmajor.mono'
    (hf.continuous.mul continuous_standardGaussianDensity).aestronglyMeasurable
  filter_upwards with x
  simp only [Pi.add_apply, Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (standardGaussianDensity_nonneg x)]
  have hfbound := abs_lipschitz_le_one_add_norm' hf x
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hdensity := standardGaussianDensity_nonneg x
  calc
    |f x| * standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x ≤
        (A * (1 + ‖x‖)) *
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x := by gcongr
    _ = A * (standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x +
        ‖x‖ * standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x) := by ring

private lemma norm_standardGaussianDensityD1_slope_mul_lipschitz_le
    {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (w h : EuclideanSpace ℝ (Fin d))
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (x : EuclideanSpace ℝ (Fin d)) :
    ‖(t⁻¹ • (standardGaussianDensityD1 (x + t • (-h)) w -
        standardGaussianDensityD1 x w)) * f x‖ ≤
      ((‖w‖ * ((1 + ‖h‖) ^ 2 + 1) *
          standardGaussianDensityNormalization (EuclideanSpace ℝ (Fin d)) *
            Real.exp (‖h‖ ^ 2 / 2)) * ‖h‖ * (|f 0| + (C : ℝ))) *
        (1 + ‖x‖) ^ 3 * Real.exp (-‖x‖ ^ 2 / 4) := by
  let K := ‖w‖ * ((1 + ‖h‖) ^ 2 + 1) *
    standardGaussianDensityNormalization (EuclideanSpace ℝ (Fin d)) *
      Real.exp (‖h‖ ^ 2 / 2)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (norm_nonneg w) (by positivity))
        standardGaussianDensityNormalization_nonneg)
      (Real.exp_nonneg _)
  let y := x + t • (-h)
  have hy : y ∈ Metric.closedBall x ‖h‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    dsimp [y]
    rw [add_sub_cancel_left, norm_smul, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg ht.1.le]
    exact mul_le_of_le_one_left (norm_nonneg h) ht.2
  have hx : x ∈ Metric.closedBall x ‖h‖ :=
    Metric.mem_closedBall_self (norm_nonneg h)
  have hderiv : ∀ z ∈ Metric.closedBall x ‖h‖,
      DifferentiableAt ℝ (fun y ↦ standardGaussianDensityD1 y w) z := by
    intro z _hz
    unfold standardGaussianDensityD1
    have hi : DifferentiableAt ℝ (fun y ↦ inner ℝ y w) z := by
      have heq : (fun y ↦ inner ℝ y w) = innerSL ℝ w := by
        funext y
        exact (real_inner_comm y w).symm
      rw [heq]
      exact (innerSL ℝ w).differentiableAt
    exact hi.neg.mul (hasFDerivAt_standardGaussianDensity z).differentiableAt
  have hbound : ∀ z ∈ Metric.closedBall x ‖h‖,
      ‖fderiv ℝ (fun y ↦ standardGaussianDensityD1 y w) z‖ ≤
        K * (1 + ‖x‖) ^ 2 * Real.exp (-‖x‖ ^ 2 / 4) := by
    intro z hz
    exact norm_fderiv_standardGaussianDensityD1_le_exp_quarter_of_dist_le
      (norm_nonneg h) hz
  have hmv : ‖standardGaussianDensityD1 y w - standardGaussianDensityD1 x w‖ ≤
      (K * (1 + ‖x‖) ^ 2 * Real.exp (-‖x‖ ^ 2 / 4)) * ‖y - x‖ :=
    (convex_closedBall x ‖h‖).norm_image_sub_le_of_norm_fderiv_le
      hderiv hbound hx hy
  have hyx : ‖y - x‖ = t * ‖h‖ := by
    dsimp [y]
    rw [add_sub_cancel_left, norm_smul, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg ht.1.le]
  have hfbound := abs_lipschitz_le_one_add_norm' hf x
  have htinv : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.1.le
  have hdiff : |standardGaussianDensityD1 y w - standardGaussianDensityD1 x w| ≤
      (K * (1 + ‖x‖) ^ 2 * Real.exp (-‖x‖ ^ 2 / 4)) * (t * ‖h‖) := by
    simpa only [Real.norm_eq_abs, hyx] using hmv
  have hmiddle : 0 ≤
      (K * (1 + ‖x‖) ^ 2 * Real.exp (-‖x‖ ^ 2 / 4)) * (t * ‖h‖) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hK (sq_nonneg _)) (Real.exp_nonneg _))
      (mul_nonneg ht.1.le (norm_nonneg h))
  rw [norm_mul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg ht.1.le,
    Real.norm_eq_abs]
  calc
    t⁻¹ * |standardGaussianDensityD1 y w - standardGaussianDensityD1 x w| * |f x| ≤
      t⁻¹ * ((K * (1 + ‖x‖) ^ 2 * Real.exp (-‖x‖ ^ 2 / 4)) *
        (t * ‖h‖)) * ((|f 0| + (C : ℝ)) * (1 + ‖x‖)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hdiff htinv
      · exact hfbound
      · exact abs_nonneg _
      · exact mul_nonneg htinv hmiddle
    _ = (K * ‖h‖ * (|f 0| + (C : ℝ))) *
        (1 + ‖x‖) ^ 3 * Real.exp (-‖x‖ ^ 2 / 4) := by
      have htne : t ≠ 0 := ht.1.ne'
      field_simp
    _ = _ := rfl

private lemma integral_standardGaussianDensityD1_slope_mul_lipschitz_tendsto
    {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (w h : EuclideanSpace ℝ (Fin d)) :
    Tendsto
      (fun t : ℝ ↦ ∫ x,
        (t⁻¹ • (standardGaussianDensityD1 (x + t • (-h)) w -
          standardGaussianDensityD1 x w)) * f x)
      (nhdsWithin 0 (Ioi 0))
      (nhds (∫ x, f x * standardGaussianDensityD2 x w (-h))) := by
  let D := (‖w‖ * ((1 + ‖h‖) ^ 2 + 1) *
      standardGaussianDensityNormalization (EuclideanSpace ℝ (Fin d)) *
        Real.exp (‖h‖ ^ 2 / 2)) * ‖h‖ * (|f 0| + (C : ℝ))
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x : EuclideanSpace ℝ (Fin d) ↦
      D * ((1 + ‖x‖) ^ 3 * Real.exp (-‖x‖ ^ 2 / 4)))
  · filter_upwards with t
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · have hsub : Continuous (fun a : EuclideanSpace ℝ (Fin d) ↦
          standardGaussianDensityD1 (a + t • (-h)) w -
            standardGaussianDensityD1 a w) := by
        apply Continuous.sub
        · exact (continuous_standardGaussianDensityD1 w).comp (by fun_prop)
        · exact continuous_standardGaussianDensityD1 w
      exact hsub.const_smul t⁻¹
    · exact hf.continuous
  · filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    filter_upwards with x
    simpa only [D, mul_assoc] using
      norm_standardGaussianDensityD1_slope_mul_lipschitz_le hf w h ht x
  · exact (integrable_one_add_norm_cube_mul_gaussianExponentQuarter
      (d := d)).const_mul D
  · filter_upwards with x
    have hi : DifferentiableAt ℝ (fun y ↦ inner ℝ y w) x := by
      have heq : (fun y ↦ inner ℝ y w) = innerSL ℝ w := by
        funext y
        exact (real_inner_comm y w).symm
      rw [heq]
      exact (innerSL ℝ w).differentiableAt
    have hpDiff : DifferentiableAt ℝ (fun y ↦ standardGaussianDensityD1 y w) x := by
      unfold standardGaussianDensityD1
      exact hi.neg.mul (hasFDerivAt_standardGaussianDensity x).differentiableAt
    have hp := hpDiff.hasFDerivAt.hasLineDerivAt (-h)
    have hlim := hp.tendsto_slope_zero_right.mul_const (f x)
    rw [fderiv_standardGaussianDensityD1_apply] at hlim
    simpa only [smul_eq_mul, mul_comm] using hlim

private lemma lipschitzWith_comp_add_const'
    {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (a : EuclideanSpace ℝ (Fin d)) :
    LipschitzWith C (fun x ↦ f (x + a)) := by
  have htrans : LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin d) ↦ x + a) := by
    simpa using LipschitzWith.id.add (LipschitzWith.const a)
  simpa only [Function.comp_def, mul_one] using hf.comp htrans

private lemma integrable_lipschitz_mul_standardGaussianDensityD1_translate
    {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (w a : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x ↦ f x * standardGaussianDensityD1 (x + a) w) := by
  let g : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun x ↦ f x * standardGaussianDensityD1 (x + a) w
  have hbase : Integrable
      (fun x ↦ f (x + (-a)) * standardGaussianDensityD1 x w) :=
    integrable_lipschitz_mul_standardGaussianDensityD1
      (lipschitzWith_comp_add_const' hf (-a)) w
  have hgcont : Continuous g := by
    apply Continuous.mul
    · exact hf.continuous
    · exact (continuous_standardGaussianDensityD1 w).comp (by fun_prop)
  have hiff := (measurePreserving_add_right volume (-a)).integrable_comp
    hgcont.aestronglyMeasurable
  apply hiff.mp
  convert hbase using 1
  funext x
  dsimp only [g, Function.comp_apply]
  congr 2
  abel

private lemma integral_slope_lipschitz_standardGaussianDensityD1_eq
    {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (w h : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    ∫ x, (t⁻¹ • (f (x + t • h) - f x)) * standardGaussianDensityD1 x w =
      ∫ x, (t⁻¹ • (standardGaussianDensityD1 (x + t • (-h)) w -
        standardGaussianDensityD1 x w)) * f x := by
  suffices hraw :
      ∫ x, (f (x + t • h) - f x) * standardGaussianDensityD1 x w =
        ∫ x, f x * (standardGaussianDensityD1 (x + t • (-h)) w -
          standardGaussianDensityD1 x w) by
    simp only [smul_eq_mul, mul_assoc, integral_const_mul, hraw,
      mul_comm (f _)]
  have hshift :
      ∫ x, f (x + t • h) * standardGaussianDensityD1 x w =
        ∫ x, f x * standardGaussianDensityD1 (x + t • (-h)) w := by
    rw [← integral_add_right_eq_self _ (t • (-h))]
    simp
  simp_rw [_root_.sub_mul, _root_.mul_sub]
  rw [integral_sub, integral_sub, hshift]
  · exact integrable_lipschitz_mul_standardGaussianDensityD1_translate hf w (t • (-h))
  · exact integrable_lipschitz_mul_standardGaussianDensityD1 hf w
  · exact integrable_lipschitz_mul_standardGaussianDensityD1
      (lipschitzWith_comp_add_const' hf (t • h)) w
  · exact integrable_lipschitz_mul_standardGaussianDensityD1 hf w

private lemma integral_lineDeriv_mul_standardGaussianDensityD1_eq
    {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (w h : EuclideanSpace ℝ (Fin d)) :
    ∫ x, lineDeriv ℝ f x h * standardGaussianDensityD1 x w =
      ∫ x, f x * standardGaussianDensityD2 x w (-h) := by
  have hleft :
      Tendsto
        (fun t : ℝ ↦ ∫ x, (t⁻¹ • (f (x + t • h) - f x)) *
          standardGaussianDensityD1 x w)
        (nhdsWithin 0 (Ioi 0))
        (nhds (∫ x, lineDeriv ℝ f x h * standardGaussianDensityD1 x w)) :=
    hf.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul
      (integrable_standardGaussianDensityD1_volume w) h
  have hright := integral_standardGaussianDensityD1_slope_mul_lipschitz_tendsto hf w h
  have heq : ∀ t : ℝ,
      ∫ x, (t⁻¹ • (f (x + t • h) - f x)) * standardGaussianDensityD1 x w =
        ∫ x, (t⁻¹ • (standardGaussianDensityD1 (x + t • (-h)) w -
          standardGaussianDensityD1 x w)) * f x :=
    integral_slope_lipschitz_standardGaussianDensityD1_eq hf w h
  simp only [heq] at hleft
  exact tendsto_nhds_unique hleft hright

private lemma integral_lipschitz_mul_standardGaussianDensityD2_eq_neg
    {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (w h : EuclideanSpace ℝ (Fin d)) :
    ∫ x, f x * standardGaussianDensityD2 x w h =
      -∫ x, lineDeriv ℝ f x h * standardGaussianDensityD1 x w := by
  have hibp := integral_lineDeriv_mul_standardGaussianDensityD1_eq hf w h
  have hneg : ∀ x, standardGaussianDensityD2 x w (-h) =
      -standardGaussianDensityD2 x w h := by
    intro x
    unfold standardGaussianDensityD2
    simp only [inner_neg_right]
    ring
  rw [show (fun x ↦ f x * standardGaussianDensityD2 x w (-h)) =
      fun x ↦ -(f x * standardGaussianDensityD2 x w h) by
    funext x
    rw [hneg]
    ring, integral_neg] at hibp
  linarith

/-- First-order integration by parts for standard Gaussian density against a globally Lipschitz
`C¹` function.  This is the density identity used before the Taylor expansion in Bentkus (2004),
equation (3.32), p. 407. -/
theorem integral_fderiv_mul_standardGaussianDensity_eq_neg
    {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (hfdiff : Differentiable ℝ f)
    (h : EuclideanSpace ℝ (Fin d)) :
    ∫ x, (fderiv ℝ f x) h *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x ∂volume =
      -∫ x, f x * standardGaussianDensityD1 x h ∂volume := by
  have hdensity : Integrable (fun x : EuclideanSpace ℝ (Fin d) ↦
      standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x) := by
    simpa only [pow_zero, one_mul, standardGaussianDensityReal_eq_standardGaussianDensity] using
      (integrable_norm_pow_mul_standardGaussianDensityReal (d := d) (k := 0))
  have hfderivDensity : Integrable (fun x ↦ (fderiv ℝ f x) h *
      standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x) := by
    have hline : Integrable (fun x ↦ lineDeriv ℝ f x h *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x) :=
      (hf.memLp_lineDeriv h).integrable_mul
        (memLp_one_iff_integrable.mpr hdensity)
    apply hline.congr
    filter_upwards with x
    rw [(hfdiff x).lineDeriv_eq_fderiv]
  have hfDensityD1 : Integrable (fun x ↦
      f x * standardGaussianDensityD1 x h) :=
    integrable_lipschitz_mul_standardGaussianDensityD1 hf h
  have hfDensity : Integrable (fun x ↦
      f x * standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x) :=
    integrable_lipschitz_mul_standardGaussianDensity hf
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := f) (g := standardGaussianDensity (EuclideanSpace ℝ (Fin d))) (v := h)
    hfderivDensity (by
      simpa only [fderiv_standardGaussianDensity_apply] using hfDensityD1)
    hfDensity (fun x _ ↦ hfdiff x)
    (fun x _ ↦ (hasFDerivAt_standardGaussianDensity x).differentiableAt)
  simp_rw [fderiv_standardGaussianDensity_apply] at hibp
  linarith

/-- Bentkus (2004), Lemma 2.3, specialized to the first derivative of the standard Gaussian
density.  This is the exact rapid-decay integration-by-parts estimate used in equation (3.32). -/
theorem bentkus_lipschitz_standardGaussianDensityD1_integral_D2_bound
    {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (w h : EuclideanSpace ℝ (Fin d)) :
    |∫ x, f x * standardGaussianDensityD2 x w h| ≤
      (C : ℝ) * ‖h‖ * ∫ x in tsupport f, |standardGaussianDensityD1 x w| := by
  have hibp := integral_lipschitz_mul_standardGaussianDensityD2_eq_neg hf w h
  rw [hibp, abs_neg]
  have hp : Integrable (fun x ↦ |standardGaussianDensityD1 x w|) :=
    (integrable_standardGaussianDensityD1_volume w).abs
  have hprod : Integrable
      (fun x ↦ lineDeriv ℝ f x h * standardGaussianDensityD1 x w) :=
    (hf.memLp_lineDeriv h).integrable_mul
      (memLp_one_iff_integrable.mpr (integrable_standardGaussianDensityD1_volume w))
  calc
    |∫ x, lineDeriv ℝ f x h * standardGaussianDensityD1 x w| ≤
        ∫ x, |lineDeriv ℝ f x h * standardGaussianDensityD1 x w| :=
      abs_integral_le_integral_abs
    _ = ∫ x in tsupport f,
        |lineDeriv ℝ f x h * standardGaussianDensityD1 x w| := by
      have hsf : MeasurableSet (tsupport f) := isClosed_closure.measurableSet
      rw [← integral_indicator hsf]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ tsupport f
      · simp [hx]
      · have hd := HasFDerivAt.of_notMem_tsupport ℝ hx
        have hlinezero : lineDeriv ℝ f x h = 0 := by
          rw [hd.differentiableAt.lineDeriv_eq_fderiv, hd.fderiv]
          simp
        simp [hx, hlinezero]
    _ ≤ ∫ x in tsupport f,
        ((C : ℝ) * ‖h‖) * |standardGaussianDensityD1 x w| := by
      have hsf : MeasurableSet (tsupport f) := isClosed_closure.measurableSet
      apply setIntegral_mono_on hprod.abs.integrableOn
        (hp.const_mul ((C : ℝ) * ‖h‖)).integrableOn hsf
      intro x hx
      rw [abs_mul]
      gcongr
      exact norm_lineDeriv_le_of_lipschitz ℝ hf
    _ = (C : ℝ) * ‖h‖ *
        ∫ x in tsupport f, |standardGaussianDensityD1 x w| := by
      rw [integral_const_mul]

end ProbabilityTheory
