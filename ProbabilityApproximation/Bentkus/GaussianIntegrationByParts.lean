/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.Bentkus.GaussianDensityDerivatives
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Bentkus's Lipschitz--Schwartz integration-by-parts bound

This file formalizes V. Bentkus, *A Lyapunov type bound in `ℝ^d`*, Lemma 2.3 on original
printed page 402, equations (2.3)--(2.4).  The paper assumes that `p` is smooth and that it and all
its derivatives decay faster than every inverse power.  Mathlib's `SchwartzMap` is exactly this
hypothesis.  For a `C`-Lipschitz function `f`, the theorem proves

`|∫ f(y) Dp(y)[v] dy| ≤ C ‖v‖ ∫_{tsupport f} |p(y)| dy`.

The proof follows the paper's difference-quotient argument.  It uses Mathlib's Rademacher theorem
for the Lipschitz factor, proves a common integrable majorant for bounded translates of the
Schwartz derivative, changes variables using Haar invariance at each positive step size, and then
passes to the limit.  In particular, no differentiability assumption is imposed on `f`.
-/

open Filter MeasureTheory Measure Module Topology
open scoped NNReal ENNReal Topology SchwartzMap LineDeriv

noncomputable section

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

private lemma one_add_pow_inv_transport {x z R : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z)
    (hR : 0 ≤ R) (h : x ≤ z + R) (m : ℕ) :
    (1 + z) ^ (-(m : ℝ)) ≤ (1 + R) ^ m * (1 + x) ^ (-(m : ℝ)) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast,
    Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [show (1 + R) ^ m * ((1 + x) ^ m)⁻¹ =
    (1 + R) ^ m / (1 + x) ^ m by simp [div_eq_mul_inv]]
  rw [show ((1 + z) ^ m)⁻¹ = 1 / (1 + z) ^ m by simp]
  apply (le_div_iff₀ (by positivity)).2
  calc
    1 / (1 + z) ^ m * (1 + x) ^ m =
        (1 + x) ^ m / (1 + z) ^ m := by simp [div_eq_mul_inv, mul_comm]
    _ ≤ (1 + R) ^ m := by
      apply (div_le_iff₀ (by positivity)).2
      rw [← mul_pow]
      gcongr
      calc
        1 + x ≤ 1 + (z + R) := by linarith
        _ ≤ (1 + R) * (1 + z) := by nlinarith

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
private lemma norm_fderiv_schwartz_le_of_dist_le (p : 𝓢(E, ℝ)) (m : ℕ)
    {x z : E} {R : ℝ} (hR : 0 ≤ R) (hzx : dist z x ≤ R) :
    ‖fderiv ℝ p z‖ ≤
      (2 ^ m * (SchwartzMap.seminorm ℝ 0 1 p + SchwartzMap.seminorm ℝ m 1 p) *
        (1 + R) ^ m) * (1 + ‖x‖) ^ (-(m : ℝ)) := by
  have hzero : ‖fderiv ℝ p z‖ ≤ SchwartzMap.seminorm ℝ 0 1 p := by
    simpa using SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ p 1 z
  have hm : ‖z‖ ^ m * ‖fderiv ℝ p z‖ ≤ SchwartzMap.seminorm ℝ m 1 p := by
    simpa using SchwartzMap.le_seminorm ℝ m 1 p z
  have hm' : ‖z‖ ^ (0 + m) * ‖fderiv ℝ p z‖ ≤
      SchwartzMap.seminorm ℝ m 1 p := by simpa using hm
  have hdecay : ‖fderiv ℝ p z‖ ≤
      2 ^ m * (SchwartzMap.seminorm ℝ 0 1 p + SchwartzMap.seminorm ℝ m 1 p) *
        (1 + ‖z‖) ^ (-(m : ℝ)) := by
    simpa using pow_mul_le_of_le_of_pow_mul_le (k := 0) (l := m)
      (norm_nonneg z) (norm_nonneg (fderiv ℝ p z)) hzero hm'
  have hnorm : ‖x‖ ≤ ‖z‖ + R := by
    calc
      ‖x‖ ≤ ‖z‖ + ‖x - z‖ := by
        simpa [sub_eq_add_neg, add_comm] using norm_add_le z (x - z)
      _ = ‖z‖ + dist z x := by rw [dist_eq_norm, norm_sub_rev]
      _ ≤ ‖z‖ + R := by gcongr
  have hweight := one_add_pow_inv_transport (norm_nonneg x) (norm_nonneg z) hR hnorm m
  calc
    ‖fderiv ℝ p z‖ ≤
        2 ^ m * (SchwartzMap.seminorm ℝ 0 1 p + SchwartzMap.seminorm ℝ m 1 p) *
          (1 + ‖z‖) ^ (-(m : ℝ)) := hdecay
    _ ≤ 2 ^ m * (SchwartzMap.seminorm ℝ 0 1 p + SchwartzMap.seminorm ℝ m 1 p) *
          ((1 + R) ^ m * (1 + ‖x‖) ^ (-(m : ℝ))) := by
      gcongr
    _ = _ := by ring

private def schwartzFDerivTranslateConstant (p : 𝓢(E, ℝ)) (m : ℕ) (R : ℝ) : ℝ :=
  2 ^ m * (SchwartzMap.seminorm ℝ 0 1 p + SchwartzMap.seminorm ℝ m 1 p) *
    (1 + R) ^ m

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
private lemma schwartzFDerivTranslateConstant_nonneg (p : 𝓢(E, ℝ)) (m : ℕ)
    {R : ℝ} (hR : 0 ≤ R) : 0 ≤ schwartzFDerivTranslateConstant p m R := by
  simp only [schwartzFDerivTranslateConstant]
  positivity

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
private lemma abs_lipschitz_le_one_add_norm {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (x : E) :
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

private lemma rpow_one_mul_rpow_neg_succ (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    (1 + x) * (1 + x) ^ (-((m + 1 : ℕ) : ℝ)) =
      (1 + x) ^ (-(m : ℝ)) := by
  calc
    (1 + x) * (1 + x) ^ (-((m + 1 : ℕ) : ℝ)) =
        (1 + x) ^ (1 : ℝ) * (1 + x) ^ (-((m + 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_one]
    _ = (1 + x) ^ ((1 : ℝ) + (-((m + 1 : ℕ) : ℝ))) := by
      rw [Real.rpow_add (by positivity)]
    _ = (1 + x) ^ (-(m : ℝ)) := by
      congr 1
      norm_num

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
private lemma norm_schwartz_slope_mul_lipschitz_le
    (p : 𝓢(E, ℝ)) {f : E → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    (v : E) (m : ℕ) {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) (x : E) :
    ‖(t⁻¹ • (p (x + t • (-v)) - p x)) * f x‖ ≤
      (schwartzFDerivTranslateConstant p (m + 1) ‖v‖ * ‖v‖ *
        (|f 0| + (C : ℝ))) * (1 + ‖x‖) ^ (-(m : ℝ)) := by
  let K := schwartzFDerivTranslateConstant p (m + 1) ‖v‖
  have hK : 0 ≤ K := schwartzFDerivTranslateConstant_nonneg p (m + 1) (norm_nonneg v)
  let y := x + t • (-v)
  have hy : y ∈ Metric.closedBall x ‖v‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    dsimp [y]
    rw [add_sub_cancel_left, norm_smul, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg ht.1.le]
    exact mul_le_of_le_one_left (norm_nonneg v) ht.2
  have hx : x ∈ Metric.closedBall x ‖v‖ := Metric.mem_closedBall_self (norm_nonneg v)
  have hderiv : ∀ z ∈ Metric.closedBall x ‖v‖, DifferentiableAt ℝ (p : E → ℝ) z :=
    fun z _ ↦ p.differentiableAt
  have hbound : ∀ z ∈ Metric.closedBall x ‖v‖,
      ‖fderiv ℝ p z‖ ≤ K * (1 + ‖x‖) ^ (-((m + 1 : ℕ) : ℝ)) := by
    intro z hz
    exact norm_fderiv_schwartz_le_of_dist_le p (m + 1) (norm_nonneg v) hz
  have hmv : ‖p y - p x‖ ≤
      (K * (1 + ‖x‖) ^ (-((m + 1 : ℕ) : ℝ))) * ‖y - x‖ :=
    (convex_closedBall x ‖v‖).norm_image_sub_le_of_norm_fderiv_le
      hderiv hbound hx hy
  have hyx : ‖y - x‖ = t * ‖v‖ := by
    dsimp [y]
    rw [add_sub_cancel_left, norm_smul, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg ht.1.le]
  have hfbound := abs_lipschitz_le_one_add_norm hf x
  have htinv : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.1.le
  have hdiff : |p y - p x| ≤
      K * (1 + ‖x‖) ^ (-((m + 1 : ℕ) : ℝ)) * (t * ‖v‖) := by
    simpa only [Real.norm_eq_abs, hyx] using hmv
  have hmiddle : 0 ≤
      K * (1 + ‖x‖) ^ (-((m + 1 : ℕ) : ℝ)) * (t * ‖v‖) := by
    exact mul_nonneg (mul_nonneg hK (Real.rpow_nonneg (by positivity) _))
      (mul_nonneg ht.1.le (norm_nonneg v))
  rw [norm_mul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg ht.1.le,
    Real.norm_eq_abs]
  calc
    t⁻¹ * |p y - p x| * |f x| ≤
        t⁻¹ * ((K * (1 + ‖x‖) ^ (-((m + 1 : ℕ) : ℝ))) * (t * ‖v‖)) *
          ((|f 0| + (C : ℝ)) * (1 + ‖x‖)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hdiff htinv
      · exact hfbound
      · exact abs_nonneg _
      · exact mul_nonneg htinv hmiddle
    _ = (K * ‖v‖ * (|f 0| + (C : ℝ))) *
        (1 + ‖x‖) ^ (-(m : ℝ)) := by
      have htne : t ≠ 0 := ht.1.ne'
      field_simp
      rw [mul_assoc K (1 + ‖x‖),
        rpow_one_mul_rpow_neg_succ ‖x‖ (norm_nonneg x) m]
      ring
    _ = _ := rfl

private lemma integral_schwartz_slope_mul_lipschitz_tendsto
    (μ : Measure E) [IsAddHaarMeasure μ]
    (p : 𝓢(E, ℝ)) {f : E → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) (v : E) :
    Tendsto
      (fun t : ℝ ↦ ∫ x,
        (t⁻¹ • (p (x + t • (-v)) - p x)) * f x ∂μ)
      (𝓝[>] 0)
      (𝓝 (∫ x, f x * fderiv ℝ p x (-v) ∂μ)) := by
  let m := μ.integrablePower
  let D := schwartzFDerivTranslateConstant p (m + 1) ‖v‖ * ‖v‖ *
    (|f 0| + (C : ℝ))
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x : E ↦ D * (1 + ‖x‖) ^ (-(m : ℝ)))
  · filter_upwards with t
    exact ((((p.continuous.comp (continuous_id.add
      (continuous_const.smul continuous_const))).sub p.continuous).const_smul t⁻¹).mul
        hf.continuous).aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    filter_upwards with x
    exact norm_schwartz_slope_mul_lipschitz_le p hf v m ht x
  · exact (Measure.integrable_pow_neg_integrablePower μ).const_mul D
  · filter_upwards with x
    have hp := (p.hasFDerivAt x).hasLineDerivAt (-v)
    have hlim := hp.tendsto_slope_zero_right.mul_const (f x)
    simpa only [smul_eq_mul, mul_comm] using hlim

private lemma integrable_lipschitz_mul_schwartz
    (μ : Measure E) [IsAddHaarMeasure μ]
    {f : E → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) (p : 𝓢(E, ℝ)) :
    Integrable (fun x ↦ f x * p x) μ := by
  let A : ℝ := |f 0| + (C : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hp0 : Integrable (fun x : E ↦ |p x|) μ := p.integrable.abs
  have hp1 : Integrable (fun x : E ↦ ‖x‖ * |p x|) μ := by
    simpa only [pow_one, Real.norm_eq_abs] using p.integrable_pow_mul μ 1
  have hmajor : Integrable (fun x : E ↦ A * (|p x| + ‖x‖ * |p x|)) μ :=
    (hp0.add hp1).const_mul A
  apply hmajor.mono' (hf.continuous.mul p.continuous).aestronglyMeasurable
  filter_upwards with x
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
  calc
    |f x| * |p x| ≤ (A * (1 + ‖x‖)) * |p x| := by
      gcongr
      exact abs_lipschitz_le_one_add_norm hf x
    _ = A * (|p x| + ‖x‖ * |p x|) := by ring

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
private lemma lipschitzWith_comp_add_const {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (a : E) : LipschitzWith C (fun x ↦ f (x + a)) := by
  have htrans : LipschitzWith 1 (fun x : E ↦ x + a) := by
    simpa using LipschitzWith.id.add (LipschitzWith.const a)
  simpa only [Function.comp_def, mul_one] using hf.comp htrans

private lemma integral_slope_lipschitz_schwartz_eq
    (μ : Measure E) [IsAddHaarMeasure μ]
    {f : E → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) (p : 𝓢(E, ℝ))
    (v : E) (t : ℝ) :
    ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * p x ∂μ =
      ∫ x, (t⁻¹ • (p (x + t • (-v)) - p x)) * f x ∂μ := by
  suffices hraw :
      ∫ x, (f (x + t • v) - f x) * p x ∂μ =
        ∫ x, f x * (p (x + t • (-v)) - p x) ∂μ by
    simp only [smul_eq_mul, mul_assoc, integral_const_mul, hraw, mul_comm (f _)]
  have hshift :
      ∫ x, f (x + t • v) * p x ∂μ =
        ∫ x, f x * p (x + t • (-v)) ∂μ := by
    rw [← integral_add_right_eq_self _ (t • (-v))]
    simp
  simp_rw [_root_.sub_mul, _root_.mul_sub]
  rw [integral_sub, integral_sub, hshift]
  · let q : 𝓢(E, ℝ) := p.compSubConstCLM ℝ (t • v)
    have hq : (fun x ↦ p (x + t • (-v))) = q := by
      funext x
      simp only [q, SchwartzMap.compSubConstCLM_apply]
      congr 1
      module
    convert integrable_lipschitz_mul_schwartz μ hf q using 1
    funext x
    rw [← hq]
  · exact integrable_lipschitz_mul_schwartz μ hf p
  · have hft := lipschitzWith_comp_add_const hf (t • v)
    exact integrable_lipschitz_mul_schwartz μ hft p
  · exact integrable_lipschitz_mul_schwartz μ hf p

private lemma integral_lineDeriv_mul_schwartz_eq
    (μ : Measure E) [IsAddHaarMeasure μ]
    {f : E → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) (p : 𝓢(E, ℝ)) (v : E) :
    ∫ x, lineDeriv ℝ f x v * p x ∂μ =
      ∫ x, f x * fderiv ℝ p x (-v) ∂μ := by
  have hleft :
      Tendsto
        (fun t : ℝ ↦ ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * p x ∂μ)
        (𝓝[>] 0)
        (𝓝 (∫ x, lineDeriv ℝ f x v * p x ∂μ)) :=
    hf.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul p.integrable v
  have hright := integral_schwartz_slope_mul_lipschitz_tendsto μ p hf v
  have heq : ∀ t : ℝ,
      ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * p x ∂μ =
        ∫ x, (t⁻¹ • (p (x + t • (-v)) - p x)) * f x ∂μ :=
    integral_slope_lipschitz_schwartz_eq μ hf p v
  simp only [heq] at hleft
  exact tendsto_nhds_unique hleft hright

private lemma integral_lipschitz_mul_fderiv_schwartz_eq_neg
    (μ : Measure E) [IsAddHaarMeasure μ]
    {f : E → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) (p : 𝓢(E, ℝ)) (v : E) :
    ∫ x, f x * fderiv ℝ p x v ∂μ =
      -∫ x, lineDeriv ℝ f x v * p x ∂μ := by
  have h := integral_lineDeriv_mul_schwartz_eq μ hf p v
  have hpneg : ∀ x, fderiv ℝ p x (-v) = -(fderiv ℝ p x v) := by
    intro x
    exact map_neg (fderiv ℝ p x) v
  rw [show (fun x ↦ f x * fderiv ℝ p x (-v)) =
      fun x ↦ -(f x * fderiv ℝ p x v) by
    funext x
    rw [hpneg]
    ring, integral_neg] at h
  linarith

/-- Bentkus's Lemma 2.3: a directional derivative may be transferred from a rapidly decaying
smooth function to a merely Lipschitz factor at the cost of restricting the absolute-value
integral to the topological support of that factor.

The Haar measure represents Lebesgue measure on the finite-dimensional real space.  The statement
is invariant under its arbitrary positive normalization. -/
theorem bentkus_lipschitz_schwartz_integral_fderiv_bound
    (μ : Measure E) [IsAddHaarMeasure μ]
    {f : E → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) (p : 𝓢(E, ℝ)) (v : E)
    :
    |∫ x, f x * fderiv ℝ p x v ∂μ| ≤
      (C : ℝ) * ‖v‖ * ∫ x in tsupport f, |p x| ∂μ := by
  have hibp := integral_lipschitz_mul_fderiv_schwartz_eq_neg μ hf p v
  rw [hibp, abs_neg]
  have hp : Integrable (fun x : E ↦ |p x|) μ := p.integrable.abs
  have hline : AEStronglyMeasurable (fun x ↦ lineDeriv ℝ f x v) μ :=
    aestronglyMeasurable_lineDeriv hf.continuous μ
  have hprod : Integrable (fun x ↦ lineDeriv ℝ f x v * p x) μ :=
    (hf.memLp_lineDeriv v).integrable_mul (p.memLp 1 μ)
  calc
    |∫ x, lineDeriv ℝ f x v * p x ∂μ| ≤
        ∫ x, |lineDeriv ℝ f x v * p x| ∂μ := abs_integral_le_integral_abs
    _ = ∫ x in tsupport f, |lineDeriv ℝ f x v * p x| ∂μ := by
      have hsf : MeasurableSet (tsupport f) := isClosed_closure.measurableSet
      rw [← integral_indicator hsf]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ tsupport f
      · simp [hx]
      · have hd := HasFDerivAt.of_notMem_tsupport ℝ hx
        have hlinezero : lineDeriv ℝ f x v = 0 := by
          rw [hd.differentiableAt.lineDeriv_eq_fderiv, hd.fderiv]
          simp
        simp [hx, hlinezero]
    _ ≤ ∫ x in tsupport f, ((C : ℝ) * ‖v‖) * |p x| ∂μ := by
      have hsf : MeasurableSet (tsupport f) := isClosed_closure.measurableSet
      apply setIntegral_mono_on hprod.abs.integrableOn
        (hp.const_mul ((C : ℝ) * ‖v‖)).integrableOn hsf
      intro x hx
      rw [abs_mul]
      gcongr
      exact norm_lineDeriv_le_of_lipschitz ℝ hf
    _ = (C : ℝ) * ‖v‖ * ∫ x in tsupport f, |p x| ∂μ := by
      rw [integral_const_mul]

end ProbabilityTheory
