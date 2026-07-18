/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.Bentkus.Induction.GaussianDensityComparison

/-!
# Large-angle estimates in Bentkus's replacement rotation

This module formalizes Bentkus (3.37)--(3.40) and the Gaussian-reference contribution: mixed-moment
bounds, centered and covariance-matched cancellation, actual-minus-reference remainders, and the
conditioned cubic Gaussian-density estimate.
-/

open MeasureTheory InnerProductSpace Matrix Set
open scoped ENNReal MatrixOrder Pointwise RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

universe u

local instance largeAngleEstimateConvexSpace {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

local instance largeAngleEstimateIsModuleConvexSpace {d : ℕ} :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.ofModule

namespace BentkusInduction

set_option maxHeartbeats 2000000

/-- The two mixed moments in Bentkus (3.39)--(3.40), after leave-one-out whitening.  The constants
are deliberately inherited from the already proved rotation-moment estimate. -/
private theorem bentkus_whitened_coordinate_twoShift_moments_le
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (r : ℝ) (hr : 0 ≤ r) :
    let ρ := bentkusReplacementMeasure μ X
    let B := bentkusWhiteningCLM (bentkusLeaveOneOutCovarianceMatrix μ X k)
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    (∫ ω, ‖B (O ω)‖ ^ 2 * (‖B (G ω)‖ + r * ‖B (O ω)‖) ∂ρ) ≤
        (896 + 8 * r) * ∫ ω, ‖O ω‖ ^ 3 ∂ρ ∧
      (∫ ω, ‖B (G ω)‖ ^ 2 * (r * ‖B (O ω)‖ + ‖B (G ω)‖) ∂ρ) ≤
        (896 * r + 216) * ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
  let ρ := bentkusReplacementMeasure μ X
  let B := bentkusWhiteningCLM (bentkusLeaveOneOutCovarianceMatrix μ X k)
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hO3 : MemLp O 3 ρ := memLp_replacementOriginal hXm hX3 k
  have hG3 : MemLp G 3 ρ := memLp_three_replacementGaussian hXm k
  have hBO3 : MemLp (fun ω ↦ B (O ω)) 3 ρ :=
    memLp_bentkusWhiteningCLM_comp _ hO3
  have hBG3 : MemLp (fun ω ↦ B (G ω)) 3 ρ :=
    memLp_bentkusWhiteningCLM_comp _ hG3
  have hBO3int : Integrable (fun ω ↦ ‖B (O ω)‖ ^ 3) ρ :=
    hBO3.integrable_norm_pow (by norm_num)
  have hBG3int : Integrable (fun ω ↦ ‖B (G ω)‖ ^ 3) ρ :=
    hBG3.integrable_norm_pow (by norm_num)
  have hcubic (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 * b ≤ a ^ 3 + b ^ 3 := by
    by_cases hab : b ≤ a
    · calc
        a ^ 2 * b ≤ a ^ 2 * a := mul_le_mul_of_nonneg_left hab (sq_nonneg a)
        _ ≤ a ^ 3 + b ^ 3 := by
          rw [show a ^ 2 * a = a ^ 3 by ring]
          exact le_add_of_nonneg_right (pow_nonneg hb 3)
    · have hab' : a ≤ b := le_of_not_ge hab
      calc
        a ^ 2 * b ≤ b ^ 2 * b := by gcongr
        _ ≤ a ^ 3 + b ^ 3 := by
          rw [show b ^ 2 * b = b ^ 3 by ring]
          exact le_add_of_nonneg_left (pow_nonneg ha 3)
  have hOGint : Integrable (fun ω ↦ ‖B (O ω)‖ ^ 2 * ‖B (G ω)‖) ρ := by
    apply (hBO3int.add hBG3int).mono'
      ((hBO3.aestronglyMeasurable.norm.pow 2).mul hBG3.aestronglyMeasurable.norm)
    filter_upwards with ω
    change |‖B (O ω)‖ ^ 2 * ‖B (G ω)‖| ≤
      ‖B (O ω)‖ ^ 3 + ‖B (G ω)‖ ^ 3
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _))]
    exact hcubic _ _ (norm_nonneg _) (norm_nonneg _)
  have hGOint : Integrable (fun ω ↦ ‖B (G ω)‖ ^ 2 * ‖B (O ω)‖) ρ := by
    apply (hBG3int.add hBO3int).mono'
      ((hBG3.aestronglyMeasurable.norm.pow 2).mul hBO3.aestronglyMeasurable.norm)
    filter_upwards with ω
    change |‖B (G ω)‖ ^ 2 * ‖B (O ω)‖| ≤
      ‖B (G ω)‖ ^ 3 + ‖B (O ω)‖ ^ 3
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _))]
    exact hcubic _ _ (norm_nonneg _) (norm_nonneg _)
  have hOG : (∫ ω, ‖B (O ω)‖ ^ 2 * ‖B (G ω)‖ ∂ρ) ≤
      896 * ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
    simpa only [ρ, B, O, G, bentkusRotated, bentkusRotatedDeriv,
      Real.cos_zero, Real.sin_zero, one_smul, zero_smul, zero_add, add_zero, neg_zero,
      map_add, map_zero] using
      (integral_norm_whitened_replacementRotated_sq_mul_norm_whitened_replacementRotatedDeriv_le
        hXm hX3 h_indep hX0 hidentity k hk 0)
  have hGO : (∫ ω, ‖B (G ω)‖ ^ 2 * ‖B (O ω)‖ ∂ρ) ≤
      896 * ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
    simpa only [ρ, B, O, G, bentkusRotated, bentkusRotatedDeriv,
      Real.cos_pi_div_two, Real.sin_pi_div_two, one_smul, zero_smul, add_zero,
      zero_add, neg_one_smul, norm_neg, map_add, map_zero, map_neg] using
      (integral_norm_whitened_replacementRotated_sq_mul_norm_whitened_replacementRotatedDeriv_le
        hXm hX3 h_indep hX0 hidentity k hk (Real.pi / 2))
  have hBO : (∫ ω, ‖B (O ω)‖ ^ 3 ∂ρ) ≤
      8 * ∫ ω, ‖O ω‖ ^ 3 ∂ρ :=
    integral_norm_bentkusWhiteningCLM_leaveOneOut_pow_three_le
      hX3 h_indep hX0 hidentity k hk hO3
  have hBGbase : (∫ ω, ‖B (G ω)‖ ^ 3 ∂ρ) ≤
      8 * ∫ ω, ‖G ω‖ ^ 3 ∂ρ :=
    integral_norm_bentkusWhiteningCLM_leaveOneOut_pow_three_le
      hX3 h_indep hX0 hidentity k hk hG3
  have hGcomp := integral_norm_pow_three_replacementGaussian_le hXm hX3 hX0 k
  have hBG : (∫ ω, ‖B (G ω)‖ ^ 3 ∂ρ) ≤
      216 * ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
    calc
      _ ≤ 8 * ∫ ω, ‖G ω‖ ^ 3 ∂ρ := hBGbase
      _ ≤ 8 * (gaussianCompanionThirdMomentConstant *
          ∫ ω, ‖O ω‖ ^ 3 ∂ρ) := by gcongr
      _ = 216 * ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
        norm_num [gaussianCompanionThirdMomentConstant]
        ring
  constructor
  · calc
      (∫ ω, ‖B (O ω)‖ ^ 2 * (‖B (G ω)‖ + r * ‖B (O ω)‖) ∂ρ) =
          (∫ ω, ‖B (O ω)‖ ^ 2 * ‖B (G ω)‖ ∂ρ) +
            r * ∫ ω, ‖B (O ω)‖ ^ 3 ∂ρ := by
        rw [← integral_const_mul, ← integral_add hOGint (hBO3int.const_mul r)]
        apply integral_congr_ae
        filter_upwards with ω
        ring
      _ ≤ 896 * (∫ ω, ‖O ω‖ ^ 3 ∂ρ) +
          r * (8 * ∫ ω, ‖O ω‖ ^ 3 ∂ρ) :=
        add_le_add hOG (mul_le_mul_of_nonneg_left hBO hr)
      _ = (896 + 8 * r) * ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by ring
  · calc
      (∫ ω, ‖B (G ω)‖ ^ 2 * (r * ‖B (O ω)‖ + ‖B (G ω)‖) ∂ρ) =
          r * (∫ ω, ‖B (G ω)‖ ^ 2 * ‖B (O ω)‖ ∂ρ) +
            ∫ ω, ‖B (G ω)‖ ^ 3 ∂ρ := by
        rw [← integral_const_mul, ← integral_add (hGOint.const_mul r) hBG3int]
        apply integral_congr_ae
        filter_upwards with ω
        ring
      _ ≤ r * (896 * ∫ ω, ‖O ω‖ ^ 3 ∂ρ) +
          216 * ∫ ω, ‖O ω‖ ^ 3 ∂ρ :=
        add_le_add (mul_le_mul_of_nonneg_left hGO hr) hBG
      _ = (896 * r + 216) * ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by ring

/-- Analytic remainder budget in Bentkus (3.37)--(3.40), at one angle.  The statement preserves
the decisive `cos α / (sin α)²` dependence. -/
private theorem bentkus_largeAngle_twoShiftDensityRemainders_le
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφm : Measurable φ)
    {D : ℝ} (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ D)
    (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    let ρ := bentkusReplacementMeasure μ X
    let B := bentkusWhiteningCLM (bentkusLeaveOneOutCovarianceMatrix μ X k)
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let r := p / q
    |∫ ω, (∫ x, φ x *
        (standardGaussianDensityD1 (x + (-(B (G ω))) + (-r) • B (O ω)) (B (O ω)) -
          standardGaussianDensityD1 (x + (-(B (G ω)))) (B (O ω)) -
          standardGaussianDensityD2 x (B (O ω)) ((-r) • B (O ω)))
        ∂volume) ∂ρ| +
      r * |∫ ω, (∫ x, φ x *
        (standardGaussianDensityD1 (x + ((-r) • B (O ω)) + (-1 : ℝ) • B (G ω))
            (B (G ω)) -
          standardGaussianDensityD1 (x + ((-r) • B (O ω))) (B (G ω)) -
          standardGaussianDensityD2 x (B (G ω)) ((-1 : ℝ) • B (G ω)))
        ∂volume) ∂ρ| ≤
      2016 * D * (3 + Real.sqrt standardGaussianFourthMoment) *
        (p / q ^ 2) * ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
  let ρ := bentkusReplacementMeasure μ X
  let B := bentkusWhiteningCLM (bentkusLeaveOneOutCovarianceMatrix μ X k)
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let r := p / q
  let K : ℝ := 3 + Real.sqrt standardGaussianFourthMoment
  let βk : ℝ := ∫ ω, ‖O ω‖ ^ 3 ∂ρ
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hr : 0 ≤ r := div_nonneg hp0 hq0.le
  have hrAbs : |r| = r := abs_of_nonneg hr
  have hO3 : MemLp O 3 ρ := memLp_replacementOriginal hXm hX3 k
  have hG3 : MemLp G 3 ρ := memLp_three_replacementGaussian hXm k
  have hBO3 : MemLp (fun ω ↦ B (O ω)) 3 ρ :=
    memLp_bentkusWhiteningCLM_comp _ hO3
  have hBG3 : MemLp (fun ω ↦ B (G ω)) 3 ρ :=
    memLp_bentkusWhiteningCLM_comp _ hG3
  have hOm : Measurable O := by
    exact (measurable_pi_apply k).comp measurable_fst
  have hGm : Measurable G := by
    exact (measurable_pi_apply k).comp measurable_snd
  have hBOm : Measurable (fun ω ↦ B (O ω)) := B.continuous.measurable.comp hOm
  have hBGm : Measurable (fun ω ↦ B (G ω)) := B.continuous.measurable.comp hGm
  have hcubic (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 * b ≤ a ^ 3 + b ^ 3 := by
    by_cases hab : b ≤ a
    · calc
        a ^ 2 * b ≤ a ^ 2 * a := mul_le_mul_of_nonneg_left hab (sq_nonneg a)
        _ ≤ a ^ 3 + b ^ 3 := by
          rw [show a ^ 2 * a = a ^ 3 by ring]
          exact le_add_of_nonneg_right (pow_nonneg hb 3)
    · have hab' : a ≤ b := le_of_not_ge hab
      calc
        a ^ 2 * b ≤ b ^ 2 * b := by gcongr
        _ ≤ a ^ 3 + b ^ 3 := by
          rw [show b ^ 2 * b = b ^ 3 by ring]
          exact le_add_of_nonneg_left (pow_nonneg ha 3)
  have hBO3int : Integrable (fun ω ↦ ‖B (O ω)‖ ^ 3) ρ :=
    hBO3.integrable_norm_pow (by norm_num)
  have hBG3int : Integrable (fun ω ↦ ‖B (G ω)‖ ^ 3) ρ :=
    hBG3.integrable_norm_pow (by norm_num)
  have hfirstInt : Integrable
      (fun ω ↦ ‖B (O ω)‖ ^ 2 * (‖-(B (G ω))‖ + |-r| * ‖B (O ω)‖)) ρ := by
    have hmajor : Integrable (fun ω ↦
        (1 + r) * ‖B (O ω)‖ ^ 3 + ‖B (G ω)‖ ^ 3) ρ :=
      (hBO3int.const_mul (1 + r)).add hBG3int
    have hm : AEStronglyMeasurable
        (fun ω ↦ ‖B (O ω)‖ ^ 2 * (‖-(B (G ω))‖ + |-r| * ‖B (O ω)‖)) ρ := by
      exact (hBO3.aestronglyMeasurable.norm.pow 2).mul
        (hBG3.aestronglyMeasurable.neg.norm.add
          (hBO3.aestronglyMeasurable.norm.const_mul |-r|))
    apply hmajor.mono' hm
    filter_upwards with ω
    simp only [norm_neg, abs_neg, hrAbs]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hmixed := hcubic ‖B (O ω)‖ ‖B (G ω)‖ (norm_nonneg _) (norm_nonneg _)
    nlinarith [mul_nonneg hr (pow_nonneg (norm_nonneg (B (O ω))) 3)]
  have hsecondInt : Integrable
      (fun ω ↦ ‖B (G ω)‖ ^ 2 *
        (‖(-r) • B (O ω)‖ + |(-1 : ℝ)| * ‖B (G ω)‖)) ρ := by
    have hmajor : Integrable (fun ω ↦
        r * ‖B (O ω)‖ ^ 3 + (r + 1) * ‖B (G ω)‖ ^ 3) ρ :=
      (hBO3int.const_mul r).add (hBG3int.const_mul (r + 1))
    have hm : AEStronglyMeasurable (fun ω ↦ ‖B (G ω)‖ ^ 2 *
        (‖(-r) • B (O ω)‖ + |(-1 : ℝ)| * ‖B (G ω)‖)) ρ := by
      exact (hBG3.aestronglyMeasurable.norm.pow 2).mul
        ((hBO3.aestronglyMeasurable.const_smul (-r)).norm.add
          (hBG3.aestronglyMeasurable.norm.const_mul |(-1 : ℝ)|))
    apply hmajor.mono' hm
    filter_upwards with ω
    simp only [norm_smul, Real.norm_eq_abs, abs_neg, hrAbs, abs_one, one_mul]
    rw [abs_of_nonneg (by positivity)]
    have hmixed := hcubic ‖B (G ω)‖ ‖B (O ω)‖ (norm_nonneg _) (norm_nonneg _)
    nlinarith [mul_nonneg hr (pow_nonneg (norm_nonneg (B (O ω))) 3),
      mul_nonneg hr (pow_nonneg (norm_nonneg (B (G ω))) 3)]
  have hfirst :=
    bentkus_integral_standardGaussianDensityD1_twoShift_integral_bound_of_bounded
      hφm hD hφ (v := fun ω ↦ -(B (G ω))) (g := fun ω ↦ B (O ω))
      hBGm.neg hBOm (-r) hfirstInt
  have hsecond :=
    bentkus_integral_standardGaussianDensityD1_twoShift_integral_bound_of_bounded
      hφm hD hφ (v := fun ω ↦ (-r) • B (O ω)) (g := fun ω ↦ B (G ω))
      (by
        change Measurable ((-r) • (fun ω ↦ B (O ω)))
        exact hBOm.const_smul (-r))
      hBGm (-1) hsecondInt
  have hmom := bentkus_whitened_coordinate_twoShift_moments_le
    hXm hX3 h_indep hX0 hidentity k hk r hr
  have hfirst' :
      |∫ ω, (∫ x, φ x *
        (standardGaussianDensityD1 (x + (-(B (G ω))) + (-r) • B (O ω)) (B (O ω)) -
          standardGaussianDensityD1 (x + (-(B (G ω)))) (B (O ω)) -
          standardGaussianDensityD2 x (B (O ω)) ((-r) • B (O ω))) ∂volume) ∂ρ| ≤
        D * r * K * ((896 + 8 * r) * βk) := by
    calc
      _ ≤ D * r * K *
          ∫ ω, ‖B (O ω)‖ ^ 2 * (‖B (G ω)‖ + r * ‖B (O ω)‖) ∂ρ := by
        simpa only [abs_neg, hrAbs, norm_neg, K, mul_assoc] using hfirst
      _ ≤ D * r * K * ((896 + 8 * r) * βk) := by
        gcongr
        simpa only [βk, ρ, B, O, G] using hmom.1
  have hsecond' :
      |∫ ω, (∫ x, φ x *
        (standardGaussianDensityD1 (x + ((-r) • B (O ω)) + (-1 : ℝ) • B (G ω))
            (B (G ω)) -
          standardGaussianDensityD1 (x + ((-r) • B (O ω))) (B (G ω)) -
          standardGaussianDensityD2 x (B (G ω)) ((-1 : ℝ) • B (G ω))) ∂volume) ∂ρ| ≤
        D * K * ((896 * r + 216) * βk) := by
    calc
      _ ≤ D * K *
          ∫ ω, ‖B (G ω)‖ ^ 2 * (r * ‖B (O ω)‖ + ‖B (G ω)‖) ∂ρ := by
        simpa only [abs_neg, hrAbs, abs_one, norm_smul, Real.norm_eq_abs,
          one_mul, K, mul_assoc] using hsecond
      _ ≤ D * K * ((896 * r + 216) * βk) := by
        gcongr
        simpa only [βk, ρ, B, O, G] using hmom.2
  have hβk : 0 ≤ βk := integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg _) 3
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hrle : r ≤ 1 / q := by
    dsimp only [r]
    exact (div_le_div_iff_of_pos_right hq0).2 hp1
  have hcoef : r * (1112 + 904 * r) ≤ 2016 * (p / q ^ 2) := by
    have h1112 : (1112 : ℝ) ≤ 1112 / q := by
      apply (le_div_iff₀ hq0).2
      nlinarith
    have h904 : 904 * r ≤ 904 / q := by
      calc
        904 * r ≤ 904 * (1 / q) := by gcongr
        _ = 904 / q := by ring
    calc
      r * (1112 + 904 * r) ≤ r * (2016 / q) := by
        gcongr
        calc
          1112 + 904 * r ≤ 1112 / q + 904 / q := add_le_add h1112 h904
          _ = 2016 / q := by ring
      _ = 2016 * (p / q ^ 2) := by
        dsimp only [r]
        field_simp
  calc
    |∫ ω, (∫ x, φ x *
        (standardGaussianDensityD1 (x + (-(B (G ω))) + (-r) • B (O ω)) (B (O ω)) -
          standardGaussianDensityD1 (x + (-(B (G ω)))) (B (O ω)) -
          standardGaussianDensityD2 x (B (O ω)) ((-r) • B (O ω))) ∂volume) ∂ρ| +
      r * |∫ ω, (∫ x, φ x *
        (standardGaussianDensityD1 (x + ((-r) • B (O ω)) + (-1 : ℝ) • B (G ω))
            (B (G ω)) -
          standardGaussianDensityD1 (x + ((-r) • B (O ω))) (B (G ω)) -
          standardGaussianDensityD2 x (B (G ω)) ((-1 : ℝ) • B (G ω))) ∂volume) ∂ρ| ≤
        D * r * K * ((896 + 8 * r) * βk) +
          r * (D * K * ((896 * r + 216) * βk)) :=
      add_le_add hfirst' (mul_le_mul_of_nonneg_left hsecond' hr)
    _ = D * K * (r * (1112 + 904 * r)) * βk := by ring
    _ ≤ D * K * (2016 * (p / q ^ 2)) * βk := by gcongr
    _ = 2016 * D * (3 + Real.sqrt standardGaussianFourthMoment) *
        (p / q ^ 2) * ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
      dsimp only [K, βk]
      ring

/-- Integrability of the centered Gaussian score after a measurable translation. -/
private lemma integrable_neg_standardGaussianDensity_smul_sub_comp
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ] {ν : Measure Θ}
    [IsFiniteMeasure ν]
    {h : Θ → EuclideanSpace ℝ (Fin d)}
    (hhm : Measurable h) (hh : Integrable h ν)
    (x : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun z ↦
      (-standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (x - h z)) •
        (x - h z)) ν := by
  let c := standardGaussianDensityNormalization (EuclideanSpace ℝ (Fin d))
  have hc : 0 ≤ c := by
    dsimp only [c, standardGaussianDensityNormalization]
    positivity
  have hdensity (y : EuclideanSpace ℝ (Fin d)) :
      |standardGaussianDensity (EuclideanSpace ℝ (Fin d)) y| ≤ c := by
    rw [abs_of_nonneg]
    · unfold standardGaussianDensity
      exact mul_le_of_le_one_right hc
        (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖y‖]))
    · unfold standardGaussianDensity
      positivity
  have hmajor : Integrable (fun z ↦ c * (‖x‖ + ‖h z‖)) ν :=
    ((integrable_const ‖x‖).add hh.norm).const_mul c
  apply hmajor.mono'
  · exact (((continuous_standardGaussianDensity.measurable.comp
        (measurable_const.sub hhm)).neg.smul (measurable_const.sub hhm)
      ).aestronglyMeasurable)
  · filter_upwards with z
    rw [norm_smul, Real.norm_eq_abs, abs_neg]
    calc
      |standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (x - h z)| *
          ‖x - h z‖ ≤ c * ‖x - h z‖ :=
        mul_le_mul_of_nonneg_right (hdensity _) (norm_nonneg _)
      _ ≤ c * (‖x‖ + ‖h z‖) := by
        gcongr
        exact norm_sub_le x (h z)

/-- A translated first-density contraction has zero mean when its direction is a centered
random vector independent of the translating vector. -/
private lemma integral_standardGaussianDensityD1_sub_independent_centered_eq_zero
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ] {ν : Measure Θ}
    [IsFiniteMeasure ν]
    {O G : Θ → EuclideanSpace ℝ (Fin d)}
    (hOG : O ⟂ᵢ[ν] G) (hGm : Measurable G)
    (hOint : Integrable O ν) (hGint : Integrable G ν)
    (hOzero : ∫ z, O z ∂ν = 0)
    (BH BK : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun z ↦
        standardGaussianDensityD1 (x - BH (G z)) (BK (O z))) ν ∧
      ∫ z, standardGaussianDensityD1 (x - BH (G z)) (BK (O z)) ∂ν = 0 := by
  let F : Θ → EuclideanSpace ℝ (Fin d) := fun z ↦
    (-standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (x - BH (G z))) •
      (x - BH (G z))
  let BO : Θ → EuclideanSpace ℝ (Fin d) := fun z ↦ BK (O z)
  have hBGm : Measurable (fun z ↦ BH (G z)) := BH.continuous.measurable.comp hGm
  have hBGint : Integrable (fun z ↦ BH (G z)) ν := BH.integrable_comp hGint
  have hFint : Integrable F ν := by
    simpa only [F] using
      integrable_neg_standardGaussianDensity_smul_sub_comp hBGm hBGint x
  have hBOint : Integrable BO ν := by
    simpa only [BO] using BK.integrable_comp hOint
  have hBOzero : ∫ z, BO z ∂ν = 0 := by
    dsimp only [BO]
    rw [BK.integral_comp_comm hOint, hOzero, map_zero]
  have hFindepBO : F ⟂ᵢ[ν] BO := by
    have hFbase : Measurable (fun y : EuclideanSpace ℝ (Fin d) ↦
        (-standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (x - BH y)) •
          (x - BH y)) := by
      exact (((continuous_standardGaussianDensity.measurable.comp
        (measurable_const.sub BH.continuous.measurable)).neg.smul
          (measurable_const.sub BH.continuous.measurable)))
    have hcomp := hOG.symm.comp hFbase BK.continuous.measurable
    convert hcomp using 1 <;> funext z <;> rfl
  have hfactor := hFindepBO.integral_bilin hFint hBOint (innerSL ℝ)
  rw [hBOzero, map_zero] at hfactor
  have hfun (z : Θ) :
      standardGaussianDensityD1 (x - BH (G z)) (BK (O z)) =
        (innerSL ℝ) (F z) (BO z) := by
    dsimp only [F, BO]
    rw [innerSL_apply_apply, inner_smul_left]
    simp only [conj_trivial]
    unfold standardGaussianDensityD1
    ring
  constructor
  · apply (hFindepBO.integrable_bilin hFint hBOint (innerSL ℝ)).congr
    filter_upwards with z
    exact (hfun z).symm
  · calc
      (∫ z, standardGaussianDensityD1 (x - BH (G z)) (BK (O z)) ∂ν) =
          ∫ z, (innerSL ℝ) (F z) (BO z) ∂ν := by
        apply integral_congr_ae
        filter_upwards with z
        exact hfun z
      _ = 0 := hfactor

/-- Matched covariance makes the two self-contracted second-density terms equal. -/
private lemma integral_standardGaussianDensityD2_self_eq_of_covarianceBilin_eq
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ] {ν : Measure Θ}
    [IsProbabilityMeasure ν]
    {O G : Θ → EuclideanSpace ℝ (Fin d)}
    (hO2 : MemLp O 2 ν) (hG2 : MemLp G 2 ν)
    (hOzero : ∫ z, O z ∂ν = 0) (hGzero : ∫ z, G z ∂ν = 0)
    (hcov : ∀ u v,
      covarianceBilin (ν.map O) u v = covarianceBilin (ν.map G) u v)
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) :
    (Integrable (fun z ↦ standardGaussianDensityD2 x (B (O z)) (B (O z))) ν ∧
      Integrable (fun z ↦ standardGaussianDensityD2 x (B (G z)) (B (G z))) ν) ∧
      (∫ z, standardGaussianDensityD2 x (B (O z)) (B (O z)) ∂ν) =
        ∫ z, standardGaussianDensityD2 x (B (G z)) (B (G z)) ∂ν := by
  let l : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := (innerSL ℝ x).comp B
  let Bprod : EuclideanSpace ℝ (Fin d) →L[ℝ]
      EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    (ContinuousLinearMap.mul ℝ ℝ).bilinearComp l l
  let Binner : EuclideanSpace ℝ (Fin d) →L[ℝ]
      EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp B B
  let Q : EuclideanSpace ℝ (Fin d) →L[ℝ]
      EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x • (Bprod - Binner)
  have hmatch := integral_bilin_self_eq_of_covarianceBilin_eq
    hO2 hG2 hOzero hGzero hcov Q
  have hfunO :
      (fun z ↦ standardGaussianDensityD2 x (B (O z)) (B (O z))) =
        fun z ↦ Q (O z) (O z) := by
    funext z
    dsimp only [Q, Bprod, Binner, l]
    simp only [_root_.smul_apply, _root_.sub_apply,
      ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply]
    unfold standardGaussianDensityD2
    rw [show ((ContinuousLinearMap.mul ℝ ℝ)
      (inner ℝ x (B (O z)))) (inner ℝ x (B (O z))) =
        inner ℝ x (B (O z)) * inner ℝ x (B (O z)) by rfl]
    simp only [smul_eq_mul]
    ring
  have hfunG :
      (fun z ↦ standardGaussianDensityD2 x (B (G z)) (B (G z))) =
        fun z ↦ Q (G z) (G z) := by
    funext z
    dsimp only [Q, Bprod, Binner, l]
    simp only [_root_.smul_apply, _root_.sub_apply,
      ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply]
    unfold standardGaussianDensityD2
    rw [show ((ContinuousLinearMap.mul ℝ ℝ)
      (inner ℝ x (B (G z)))) (inner ℝ x (B (G z))) =
        inner ℝ x (B (G z)) * inner ℝ x (B (G z)) by rfl]
    simp only [smul_eq_mul]
    ring
  constructor
  · constructor
    · rw [hfunO]
      exact integrable_bilin_self_of_memLp_two hO2 Q
    · rw [hfunG]
      exact integrable_bilin_self_of_memLp_two hG2 Q
  · rw [hfunO, hfunG]
    exact hmatch

/-- The centered linear terms and the matched-covariance quadratic pair left by the
large-angle two-shift expansion have zero joint integral. -/
private theorem bentkus_largeAngle_densityCancellation
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (k : Fin (n + 1))
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (r : ℝ) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφm : Measurable φ) (hφ : ∀ x, |φ x| ≤ 1) :
    let ρ := bentkusReplacementMeasure μ X
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let cancel :
        (((Fin (n + 1) → EuclideanSpace ℝ (Fin d)) ×
            (Fin (n + 1) → EuclideanSpace ℝ (Fin d))) ×
          EuclideanSpace ℝ (Fin d)) → ℝ := fun p ↦
      φ p.2 * (standardGaussianDensityD1 (p.2 - B (G p.1)) (B (O p.1)) -
        r * standardGaussianDensityD1 (p.2 - r • B (O p.1)) (B (G p.1)) +
        standardGaussianDensityD2 p.2 (B (O p.1)) ((-r) • B (O p.1)) -
        r * standardGaussianDensityD2 p.2 (B (G p.1)) ((-1 : ℝ) • B (G p.1)))
    Integrable cancel (ρ.prod volume) ∧
      (∫ z, (∫ x, cancel (z, x) ∂volume) ∂ρ) = 0 := by
  let ρ := bentkusReplacementMeasure μ X
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let BO := fun z ↦ B (O z)
  let BG := fun z ↦ B (G z)
  let cancel := fun p :
      (((Fin (n + 1) → EuclideanSpace ℝ (Fin d)) ×
          (Fin (n + 1) → EuclideanSpace ℝ (Fin d))) ×
        EuclideanSpace ℝ (Fin d)) ↦
    φ p.2 * (standardGaussianDensityD1 (p.2 - BG p.1) (BO p.1) -
      r * standardGaussianDensityD1 (p.2 - r • BO p.1) (BG p.1) +
      standardGaussianDensityD2 p.2 (BO p.1) ((-r) • BO p.1) -
      r * standardGaussianDensityD2 p.2 (BG p.1) ((-1 : ℝ) • BG p.1))
  let linearO := fun p :
      (((Fin (n + 1) → EuclideanSpace ℝ (Fin d)) ×
          (Fin (n + 1) → EuclideanSpace ℝ (Fin d))) ×
        EuclideanSpace ℝ (Fin d)) ↦
    φ p.2 * standardGaussianDensityD1 (p.2 - BG p.1) (BO p.1)
  let linearG := fun p :
      (((Fin (n + 1) → EuclideanSpace ℝ (Fin d)) ×
          (Fin (n + 1) → EuclideanSpace ℝ (Fin d))) ×
        EuclideanSpace ℝ (Fin d)) ↦
    φ p.2 * standardGaussianDensityD1 (p.2 - r • BO p.1) (BG p.1)
  let quadraticO := fun p :
      (((Fin (n + 1) → EuclideanSpace ℝ (Fin d)) ×
          (Fin (n + 1) → EuclideanSpace ℝ (Fin d))) ×
        EuclideanSpace ℝ (Fin d)) ↦
    φ p.2 * standardGaussianDensityD2 p.2 (BO p.1) (BO p.1)
  let quadraticG := fun p :
      (((Fin (n + 1) → EuclideanSpace ℝ (Fin d)) ×
          (Fin (n + 1) → EuclideanSpace ℝ (Fin d))) ×
        EuclideanSpace ℝ (Fin d)) ↦
    φ p.2 * standardGaussianDensityD2 p.2 (BG p.1) (BG p.1)
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hOm : Measurable O := by
    exact (measurable_pi_apply k).comp measurable_fst
  have hGm : Measurable G := by
    exact (measurable_pi_apply k).comp measurable_snd
  have hBOm : Measurable BO := B.continuous.measurable.comp hOm
  have hBGm : Measurable BG := B.continuous.measurable.comp hGm
  have hO3 : MemLp O 3 ρ := memLp_replacementOriginal hXm hX3 k
  have hG3 : MemLp G 3 ρ := memLp_three_replacementGaussian hXm k
  have hO2 : MemLp O 2 ρ := hO3.mono_exponent (by norm_num)
  have hG2 : MemLp G 2 ρ := hG3.mono_exponent (by norm_num)
  have hOint : Integrable O ρ := hO3.integrable (by norm_num)
  have hGint : Integrable G ρ := hG3.integrable (by norm_num)
  have hBO2 : MemLp BO 2 ρ := by
    simpa only [BO] using hO2.continuousLinearMap_comp B
  have hBG2 : MemLp BG 2 ρ := by
    simpa only [BG] using hG2.continuousLinearMap_comp B
  have hBOint : Integrable BO ρ := hBO2.integrable (by norm_num)
  have hBGint : Integrable BG ρ := hBG2.integrable (by norm_num)
  have hOzero : ∫ z, O z ∂ρ = 0 := by
    simpa only [O, ρ] using (integral_replacementOriginal_eq hXm k).trans (hX0 k)
  have hGzero : ∫ z, G z ∂ρ = 0 := by
    simpa only [G, ρ] using integral_replacementGaussian_eq_zero hXm k
  have hOG : O ⟂ᵢ[ρ] G := by
    simpa only [O, G, ρ] using
      indepFun_replacementOriginal_replacementGaussian hXm k k
  have hcov : ∀ u v,
      covarianceBilin (ρ.map O) u v = covarianceBilin (ρ.map G) u v := by
    intro u v
    simpa only [O, G, ρ] using
      (covarianceBilin_replacementGaussian_eq_replacementOriginal hXm k u v).symm
  have hlinearO : Integrable linearO (ρ.prod volume) := by
    simpa only [linearO, BO, BG] using
      integrable_prod_bounded_mul_standardGaussianDensityD1_sub
        hφm hφ hBGm hBOm hBOint
  have hlinearG : Integrable linearG (ρ.prod volume) := by
    have hshift : Measurable (fun z ↦ r • BO z) := hBOm.const_smul r
    simpa only [linearG] using
      integrable_prod_bounded_mul_standardGaussianDensityD1_sub
        hφm hφ hshift hBGm hBGint
  have hBOsq : Integrable (fun z ↦ ‖BO z‖ ^ 2) ρ :=
    hBO2.integrable_norm_pow (by norm_num)
  have hBGsq : Integrable (fun z ↦ ‖BG z‖ ^ 2) ρ :=
    hBG2.integrable_norm_pow (by norm_num)
  have hBOmajor : Integrable (fun z ↦
      (‖BO z‖ ^ 2 + ‖BO z‖ ^ 2) / 2 + ‖BO z‖ * ‖BO z‖) ρ := by
    apply (hBOsq.const_mul 2).congr
    filter_upwards with z
    ring
  have hBGmajor : Integrable (fun z ↦
      (‖BG z‖ ^ 2 + ‖BG z‖ ^ 2) / 2 + ‖BG z‖ * ‖BG z‖) ρ := by
    apply (hBGsq.const_mul 2).congr
    filter_upwards with z
    ring
  have hquadraticO : Integrable quadraticO (ρ.prod volume) := by
    simpa only [quadraticO] using
      integrable_prod_bounded_mul_standardGaussianDensityD2
        hφm hφ hBOm hBOm hBOmajor
  have hquadraticG : Integrable quadraticG (ρ.prod volume) := by
    simpa only [quadraticG] using
      integrable_prod_bounded_mul_standardGaussianDensityD2
        hφm hφ hBGm hBGm hBGmajor
  have hcancel : Integrable cancel (ρ.prod volume) := by
    have hbase :=
      ((hlinearO.sub (hlinearG.const_mul r)).sub (hquadraticO.const_mul r)).add
        (hquadraticG.const_mul r)
    apply hbase.congr
    filter_upwards with p
    change linearO p - r * linearG p - r * quadraticO p + r * quadraticG p = cancel p
    dsimp only [cancel, linearO, linearG, quadraticO, quadraticG]
    unfold standardGaussianDensityD2
    simp only [inner_smul_right, neg_mul, one_mul]
    ring_nf
  constructor
  · simpa only [cancel, BO, BG, O, G, ρ] using hcancel
  · have hzero (x : EuclideanSpace ℝ (Fin d)) :
        ∫ z, cancel (z, x) ∂ρ = 0 := by
      have hlinO :=
        integral_standardGaussianDensityD1_sub_independent_centered_eq_zero
          hOG hGm hOint hGint hOzero B B x
      have hlinG :=
        integral_standardGaussianDensityD1_sub_independent_centered_eq_zero
          hOG.symm hOm hGint hOint hGzero (r • B) B x
      have hquad :=
        integral_standardGaussianDensityD2_self_eq_of_covarianceBilin_eq
          hO2 hG2 hOzero hGzero hcov B x
      have hlinOφ :
          (∫ z, φ x * standardGaussianDensityD1 (x - BG z) (BO z) ∂ρ) = 0 := by
        rw [integral_const_mul]
        simpa only [BO, BG, mul_zero] using congrArg (fun t ↦ φ x * t) hlinO.2
      have hlinGφ :
          (∫ z, φ x * standardGaussianDensityD1 (x - r • BO z) (BG z) ∂ρ) = 0 := by
        rw [integral_const_mul]
        simpa only [BO, BG, _root_.smul_apply, mul_zero] using
          congrArg (fun t ↦ φ x * t) hlinG.2
      have hquadOφ : Integrable
          (fun z ↦ φ x * standardGaussianDensityD2 x (BO z) (BO z)) ρ := by
        exact hquad.1.1.const_mul (φ x)
      have hquadGφ : Integrable
          (fun z ↦ φ x * standardGaussianDensityD2 x (BG z) (BG z)) ρ := by
        exact hquad.1.2.const_mul (φ x)
      have hquadφ :
          (∫ z, φ x * standardGaussianDensityD2 x (BO z) (BO z) ∂ρ) =
            ∫ z, φ x * standardGaussianDensityD2 x (BG z) (BG z) ∂ρ := by
        rw [integral_const_mul, integral_const_mul]
        simpa only [BO, BG] using congrArg (fun t ↦ φ x * t) hquad.2
      have hlinOint : Integrable
          (fun z ↦ φ x * standardGaussianDensityD1 (x - BG z) (BO z)) ρ := by
        exact (by simpa only [BO, BG] using hlinO.1.const_mul (φ x))
      have hlinGint : Integrable
          (fun z ↦ φ x * standardGaussianDensityD1 (x - r • BO z) (BG z)) ρ := by
        exact (by simpa only [BO, BG, _root_.smul_apply] using hlinG.1.const_mul (φ x))
      calc
        (∫ z, cancel (z, x) ∂ρ) =
            ∫ z,
              ((φ x * standardGaussianDensityD1 (x - BG z) (BO z) -
                  r * (φ x * standardGaussianDensityD1
                    (x - r • BO z) (BG z))) -
                r * (φ x * standardGaussianDensityD2 x (BO z) (BO z))) +
              r * (φ x * standardGaussianDensityD2 x (BG z) (BG z)) ∂ρ := by
          apply integral_congr_ae
          filter_upwards with z
          dsimp only [cancel]
          unfold standardGaussianDensityD2
          simp only [inner_smul_right, neg_mul, one_mul]
          ring_nf
        _ =
            (∫ z, φ x * standardGaussianDensityD1 (x - BG z) (BO z) ∂ρ) -
              r * (∫ z,
                φ x * standardGaussianDensityD1 (x - r • BO z) (BG z) ∂ρ) -
              r * (∫ z,
                φ x * standardGaussianDensityD2 x (BO z) (BO z) ∂ρ) +
              r * (∫ z,
                φ x * standardGaussianDensityD2 x (BG z) (BG z) ∂ρ) := by
          have hAB :
              (∫ z,
                φ x * standardGaussianDensityD1 (x - BG z) (BO z) -
                  r * (φ x * standardGaussianDensityD1
                    (x - r • BO z) (BG z)) ∂ρ) =
                (∫ z, φ x * standardGaussianDensityD1 (x - BG z) (BO z) ∂ρ) -
                  ∫ z, r * (φ x * standardGaussianDensityD1
                    (x - r • BO z) (BG z)) ∂ρ := by
            exact integral_sub hlinOint (hlinGint.const_mul r)
          have hABC :
              (∫ z,
                (φ x * standardGaussianDensityD1 (x - BG z) (BO z) -
                    r * (φ x * standardGaussianDensityD1
                      (x - r • BO z) (BG z))) -
                  r * (φ x * standardGaussianDensityD2 x (BO z) (BO z)) ∂ρ) =
                (∫ z,
                  φ x * standardGaussianDensityD1 (x - BG z) (BO z) -
                    r * (φ x * standardGaussianDensityD1
                      (x - r • BO z) (BG z)) ∂ρ) -
                  ∫ z, r * (φ x *
                    standardGaussianDensityD2 x (BO z) (BO z)) ∂ρ := by
            exact integral_sub
              (hlinOint.sub (hlinGint.const_mul r)) (hquadOφ.const_mul r)
          have hABCD :
              (∫ z,
                ((φ x * standardGaussianDensityD1 (x - BG z) (BO z) -
                    r * (φ x * standardGaussianDensityD1
                      (x - r • BO z) (BG z))) -
                  r * (φ x * standardGaussianDensityD2 x (BO z) (BO z))) +
                r * (φ x * standardGaussianDensityD2 x (BG z) (BG z)) ∂ρ) =
                (∫ z,
                  (φ x * standardGaussianDensityD1 (x - BG z) (BO z) -
                      r * (φ x * standardGaussianDensityD1
                        (x - r • BO z) (BG z))) -
                    r * (φ x * standardGaussianDensityD2 x (BO z) (BO z)) ∂ρ) +
                  ∫ z, r * (φ x *
                    standardGaussianDensityD2 x (BG z) (BG z)) ∂ρ := by
            exact integral_add
              ((hlinOint.sub (hlinGint.const_mul r)).sub (hquadOφ.const_mul r))
              (hquadGφ.const_mul r)
          have hscaleB :
              (∫ z, r * (φ x * standardGaussianDensityD1
                (x - r • BO z) (BG z)) ∂ρ) =
                r * ∫ z, φ x * standardGaussianDensityD1
                  (x - r • BO z) (BG z) ∂ρ := by
            exact integral_const_mul r
              (fun z ↦ φ x * standardGaussianDensityD1
                (x - r • BO z) (BG z))
          have hscaleO :
              (∫ z, r * (φ x *
                standardGaussianDensityD2 x (BO z) (BO z)) ∂ρ) =
                r * ∫ z, φ x *
                  standardGaussianDensityD2 x (BO z) (BO z) ∂ρ := by
            exact integral_const_mul r
              (fun z ↦ φ x * standardGaussianDensityD2 x (BO z) (BO z))
          have hscaleG :
              (∫ z, r * (φ x *
                standardGaussianDensityD2 x (BG z) (BG z)) ∂ρ) =
                r * ∫ z, φ x *
                  standardGaussianDensityD2 x (BG z) (BG z) ∂ρ := by
            exact integral_const_mul r
              (fun z ↦ φ x * standardGaussianDensityD2 x (BG z) (BG z))
          calc
            _ = (∫ z,
                  (φ x * standardGaussianDensityD1 (x - BG z) (BO z) -
                      r * (φ x * standardGaussianDensityD1
                        (x - r • BO z) (BG z))) -
                    r * (φ x * standardGaussianDensityD2 x (BO z) (BO z)) ∂ρ) +
                  ∫ z, r * (φ x *
                    standardGaussianDensityD2 x (BG z) (BG z)) ∂ρ := hABCD
            _ = _ := by
              rw [hABC, hAB, hscaleB, hscaleO, hscaleG]
        _ = 0 := by rw [hlinOφ, hlinGφ, hquadφ]; ring
    simpa only [cancel, BO, BG, O, G, ρ] using
      integral_integral_eq_zero_of_integral_eq_zero hcancel hzero

/-- The algebraic remainder decomposition in Bentkus (3.37)--(3.40).  Once the two
centered linear terms and the matched-covariance quadratic pair have zero integral,
the full large-angle density contraction is exactly the difference of the two
two-shift Taylor remainders. -/
private theorem
    bentkus_largeAngle_densityContraction_eq_twoShiftRemainders_of_cancellation
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ] {ν : Measure Θ} [SFinite ν]
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    {O G : Θ → EuclideanSpace ℝ (Fin d)}
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (r : ℝ) :
    let full : Θ × EuclideanSpace ℝ (Fin d) → ℝ := fun p ↦
      φ p.2 * (standardGaussianDensityD1
          (p.2 - B (G p.1) - r • B (O p.1)) (B (O p.1)) -
        r * standardGaussianDensityD1
          (p.2 - B (G p.1) - r • B (O p.1)) (B (G p.1)))
    let first : Θ × EuclideanSpace ℝ (Fin d) → ℝ := fun p ↦
      φ p.2 * (standardGaussianDensityD1
          (p.2 - B (G p.1) - r • B (O p.1)) (B (O p.1)) -
        standardGaussianDensityD1 (p.2 - B (G p.1)) (B (O p.1)) -
        standardGaussianDensityD2 p.2 (B (O p.1)) ((-r) • B (O p.1)))
    let second : Θ × EuclideanSpace ℝ (Fin d) → ℝ := fun p ↦
      φ p.2 * (standardGaussianDensityD1
          (p.2 - B (G p.1) - r • B (O p.1)) (B (G p.1)) -
        standardGaussianDensityD1 (p.2 - r • B (O p.1)) (B (G p.1)) -
        standardGaussianDensityD2 p.2 (B (G p.1)) ((-1 : ℝ) • B (G p.1)))
    let cancel : Θ × EuclideanSpace ℝ (Fin d) → ℝ := fun p ↦
      φ p.2 * (standardGaussianDensityD1 (p.2 - B (G p.1)) (B (O p.1)) -
        r * standardGaussianDensityD1 (p.2 - r • B (O p.1)) (B (G p.1)) +
        standardGaussianDensityD2 p.2 (B (O p.1)) ((-r) • B (O p.1)) -
        r * standardGaussianDensityD2 p.2 (B (G p.1)) ((-1 : ℝ) • B (G p.1)))
    Integrable first (ν.prod volume) →
    Integrable second (ν.prod volume) →
    Integrable cancel (ν.prod volume) →
    (∫ z, (∫ x, cancel (z, x) ∂volume) ∂ν) = 0 →
    (∫ z, (∫ x, full (z, x) ∂volume) ∂ν) =
      (∫ z, (∫ x, first (z, x) ∂volume) ∂ν) -
        r * ∫ z, (∫ x, second (z, x) ∂volume) ∂ν := by
  dsimp only
  intro hfirst hsecond hcancel hcancelZero
  let full : Θ × EuclideanSpace ℝ (Fin d) → ℝ := fun p ↦
    φ p.2 * (standardGaussianDensityD1
        (p.2 - B (G p.1) - r • B (O p.1)) (B (O p.1)) -
      r * standardGaussianDensityD1
        (p.2 - B (G p.1) - r • B (O p.1)) (B (G p.1)))
  let first : Θ × EuclideanSpace ℝ (Fin d) → ℝ := fun p ↦
    φ p.2 * (standardGaussianDensityD1
        (p.2 - B (G p.1) - r • B (O p.1)) (B (O p.1)) -
      standardGaussianDensityD1 (p.2 - B (G p.1)) (B (O p.1)) -
      standardGaussianDensityD2 p.2 (B (O p.1)) ((-r) • B (O p.1)))
  let second : Θ × EuclideanSpace ℝ (Fin d) → ℝ := fun p ↦
    φ p.2 * (standardGaussianDensityD1
        (p.2 - B (G p.1) - r • B (O p.1)) (B (G p.1)) -
      standardGaussianDensityD1 (p.2 - r • B (O p.1)) (B (G p.1)) -
      standardGaussianDensityD2 p.2 (B (G p.1)) ((-1 : ℝ) • B (G p.1)))
  let cancel : Θ × EuclideanSpace ℝ (Fin d) → ℝ := fun p ↦
    φ p.2 * (standardGaussianDensityD1 (p.2 - B (G p.1)) (B (O p.1)) -
      r * standardGaussianDensityD1 (p.2 - r • B (O p.1)) (B (G p.1)) +
      standardGaussianDensityD2 p.2 (B (O p.1)) ((-r) • B (O p.1)) -
      r * standardGaussianDensityD2 p.2 (B (G p.1)) ((-1 : ℝ) • B (G p.1)))
  have hpoint (p : Θ × EuclideanSpace ℝ (Fin d)) :
      full p = first p - r * second p + cancel p := by
    dsimp only [full, first, second, cancel]
    ring
  have hfull : Integrable full (ν.prod volume) := by
    apply ((hfirst.sub (hsecond.const_mul r)).add hcancel).congr
    filter_upwards with p
    exact (hpoint p).symm
  have hfull' :
      Integrable (Function.uncurry fun z x ↦ full (z, x)) (ν.prod volume) := by
    apply hfull.congr
    filter_upwards with p
    rcases p with ⟨z, x⟩
    rfl
  have hfirst' :
      Integrable (Function.uncurry fun z x ↦ first (z, x)) (ν.prod volume) := by
    apply hfirst.congr
    filter_upwards with p
    rcases p with ⟨z, x⟩
    rfl
  have hsecond' :
      Integrable (Function.uncurry fun z x ↦ second (z, x)) (ν.prod volume) := by
    apply hsecond.congr
    filter_upwards with p
    rcases p with ⟨z, x⟩
    rfl
  have hcancel' :
      Integrable (Function.uncurry fun z x ↦ cancel (z, x)) (ν.prod volume) := by
    apply hcancel.congr
    filter_upwards with p
    rcases p with ⟨z, x⟩
    rfl
  have hcancelProd : (∫ p, cancel p ∂(ν.prod volume)) = 0 := by
    calc
      (∫ p, cancel p ∂(ν.prod volume)) =
          ∫ z, (∫ x, cancel (z, x) ∂volume) ∂ν := by
        simpa only using (integral_integral hcancel').symm
      _ = 0 := hcancelZero
  calc
    (∫ z, (∫ x, full (z, x) ∂volume) ∂ν) =
        ∫ p, full p ∂(ν.prod volume) := by
      simpa only using integral_integral hfull'
    _ = ∫ p, (first p - r * second p) + cancel p ∂(ν.prod volume) := by
      apply integral_congr_ae
      filter_upwards with p
      rw [hpoint]
    _ = (∫ p, first p - r * second p ∂(ν.prod volume)) +
        ∫ p, cancel p ∂(ν.prod volume) :=
      integral_add (hfirst.sub (hsecond.const_mul r)) hcancel
    _ = (∫ p, first p ∂(ν.prod volume)) -
        r * ∫ p, second p ∂(ν.prod volume) := by
      rw [integral_sub hfirst (hsecond.const_mul r), integral_const_mul, hcancelProd,
        add_zero]
    _ = (∫ z, (∫ x, first (z, x) ∂volume) ∂ν) -
        r * ∫ z, (∫ x, second (z, x) ∂volume) ∂ν := by
      rw [show (∫ p, first p ∂(ν.prod volume)) =
          ∫ z, (∫ x, first (z, x) ∂volume) ∂ν by
            simpa only using (integral_integral hfirst').symm,
        show (∫ p, second p ∂(ν.prod volume)) =
          ∫ z, (∫ x, second (z, x) ∂volume) ∂ν by
            simpa only using (integral_integral hsecond').symm]

/-- Product-integrability of a translated first-density two-shift remainder. -/
private theorem
    integrable_prod_bounded_mul_standardGaussianDensityD1_twoShiftRemainder
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ] {ν : Measure Θ} [SFinite ν]
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφm : Measurable φ) (hφ : ∀ x, |φ x| ≤ 1)
    {h v g : Θ → EuclideanSpace ℝ (Fin d)}
    (hhm : Measurable h) (hvm : Measurable v) (hgm : Measurable g)
    (hg : Integrable g ν)
    (hmajor : Integrable (fun z ↦
      (‖g z‖ ^ 2 + ‖v z‖ ^ 2) / 2 + ‖g z‖ * ‖v z‖) ν) :
    Integrable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦
      φ p.2 * (standardGaussianDensityD1
          (p.2 - h p.1 + v p.1) (g p.1) -
        standardGaussianDensityD1 (p.2 - h p.1) (g p.1) -
        standardGaussianDensityD2 p.2 (g p.1) (v p.1))) (ν.prod volume) := by
  have hshift : Measurable (fun z ↦ h z - v z) := hhm.sub hvm
  have hfull := integrable_prod_bounded_mul_standardGaussianDensityD1_sub
    hφm hφ hshift hgm hg
  have hbase := integrable_prod_bounded_mul_standardGaussianDensityD1_sub
    hφm hφ hhm hgm hg
  have hquad := integrable_prod_bounded_mul_standardGaussianDensityD2
    hφm hφ hgm hvm hmajor
  apply ((hfull.sub hbase).sub hquad).congr
  filter_upwards with p
  change
    (φ p.2 * standardGaussianDensityD1
        (p.2 - (h p.1 - v p.1)) (g p.1) -
      φ p.2 * standardGaussianDensityD1
        (p.2 - h p.1) (g p.1)) -
        φ p.2 * standardGaussianDensityD2 p.2 (g p.1) (v p.1) = _
  rw [show p.2 - (h p.1 - v p.1) = p.2 - h p.1 + v p.1 by abel]
  ring

/-- A third moment supplies the linear and self/negative-self quadratic majorants used by the
Gaussian-coordinate remainder. -/
private theorem integrable_and_selfNeg_D2Major_of_memLp_three
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ] {ν : Measure Θ} [IsFiniteMeasure ν]
    {g : Θ → EuclideanSpace ℝ (Fin d)} (hg3 : MemLp g 3 ν) :
    Integrable g ν ∧
      Integrable (fun z ↦
        (‖g z‖ ^ 2 + ‖(-1 : ℝ) • g z‖ ^ 2) / 2 +
          ‖g z‖ * ‖(-1 : ℝ) • g z‖) ν := by
  have hg2 : MemLp g 2 ν := hg3.mono_exponent (by norm_num)
  have hgsq : Integrable (fun z ↦ ‖g z‖ ^ 2) ν :=
    hg2.integrable_norm_pow (by norm_num)
  constructor
  · exact hg3.integrable (by norm_num)
  · apply (hgsq.const_mul 2).congr
    filter_upwards with z
    simp
    ring

/-- Product-integrability of the original-coordinate cubic remainder in the large-angle
density expansion. -/
private theorem bentkus_largeAngle_firstShiftRemainder_integrable
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ)
    (k : Fin (n + 1))
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (r : ℝ) (hr : 0 ≤ r)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφm : Measurable φ) (hφ : ∀ x, |φ x| ≤ 1) :
    let ρ := bentkusReplacementMeasure μ X
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let first : _ × EuclideanSpace ℝ (Fin d) → ℝ := fun z ↦
      φ z.2 * (standardGaussianDensityD1
          (z.2 - B (G z.1) - r • B (O z.1)) (B (O z.1)) -
        standardGaussianDensityD1 (z.2 - B (G z.1)) (B (O z.1)) -
        standardGaussianDensityD2 z.2 (B (O z.1)) ((-r) • B (O z.1)))
    Integrable first (ρ.prod volume) := by
  let ρ := bentkusReplacementMeasure μ X
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let BO := fun z ↦ B (O z)
  let BG := fun z ↦ B (G z)
  let first :
      (((Fin (n + 1) → EuclideanSpace ℝ (Fin d)) ×
          (Fin (n + 1) → EuclideanSpace ℝ (Fin d))) ×
        EuclideanSpace ℝ (Fin d)) → ℝ := fun z ↦
    φ z.2 * (standardGaussianDensityD1
        (z.2 - BG z.1 - r • BO z.1) (BO z.1) -
      standardGaussianDensityD1 (z.2 - BG z.1) (BO z.1) -
      standardGaussianDensityD2 z.2 (BO z.1) ((-r) • BO z.1))
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hOm : Measurable O := by
    exact (measurable_pi_apply k).comp measurable_fst
  have hGm : Measurable G := by
    exact (measurable_pi_apply k).comp measurable_snd
  have hBOm : Measurable BO := B.continuous.measurable.comp hOm
  have hBGm : Measurable BG := B.continuous.measurable.comp hGm
  have hO3 : MemLp O 3 ρ := memLp_replacementOriginal hXm hX3 k
  have hBO3 : MemLp BO 3 ρ := by
    simpa only [BO] using hO3.continuousLinearMap_comp B
  have hBO2 : MemLp BO 2 ρ := hBO3.mono_exponent (by norm_num)
  have hBOint : Integrable BO ρ := hBO3.integrable (by norm_num)
  have hBOsq : Integrable (fun z ↦ ‖BO z‖ ^ 2) ρ :=
    hBO2.integrable_norm_pow (by norm_num)
  have hfirstMajor : Integrable (fun z ↦
      (‖BO z‖ ^ 2 + ‖(-r) • BO z‖ ^ 2) / 2 +
        ‖BO z‖ * ‖(-r) • BO z‖) ρ := by
    apply (hBOsq.const_mul ((1 + r ^ 2) / 2 + r)).congr
    filter_upwards with z
    simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hr]
    ring
  have hrem :=
    integrable_prod_bounded_mul_standardGaussianDensityD1_twoShiftRemainder
      (ν := ρ) (φ := φ) (h := BG)
      (v := fun z ↦ (-r) • BO z) (g := BO)
      hφm hφ hBGm (hBOm.const_smul (-r)) hBOm hBOint hfirstMajor
  apply hrem.congr
  filter_upwards with z
  change
    φ z.2 * (standardGaussianDensityD1
        (z.2 - BG z.1 + (-r) • BO z.1) (BO z.1) -
      standardGaussianDensityD1 (z.2 - BG z.1) (BO z.1) -
      standardGaussianDensityD2 z.2 (BO z.1) ((-r) • BO z.1)) =
      first z
  dsimp only [first]
  rw [show z.2 - BG z.1 + (-r) • BO z.1 =
    z.2 - BG z.1 - r • BO z.1 by module]

/-- Product-integrability of the Gaussian-coordinate cubic remainder in the large-angle
density expansion. -/
private theorem bentkus_largeAngle_secondShiftRemainder_integrable
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ν : Measure Θ} [SFinite ν] [IsFiniteMeasure ν]
    {BO BG : Θ → EuclideanSpace ℝ (Fin d)}
    (hBOm : Measurable BO) (hBGm : Measurable BG)
    (hBG3 : MemLp BG 3 ν)
    (r : ℝ)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφm : Measurable φ) (hφ : ∀ x, |φ x| ≤ 1) :
    Integrable (fun z : Θ × EuclideanSpace ℝ (Fin d) ↦
    φ z.2 * (standardGaussianDensityD1
        (z.2 - BG z.1 - r • BO z.1) (BG z.1) -
      standardGaussianDensityD1 (z.2 - r • BO z.1) (BG z.1) -
      standardGaussianDensityD2 z.2 (BG z.1) ((-1 : ℝ) • BG z.1)))
      (ν.prod volume) := by
  have hmom := integrable_and_selfNeg_D2Major_of_memLp_three hBG3
  have hrBOm : Measurable (fun z ↦ r • BO z) := by
    fun_prop
  have hnegBGm : Measurable (fun z ↦ (-1 : ℝ) • BG z) := by
    fun_prop
  have hrem :=
    integrable_prod_bounded_mul_standardGaussianDensityD1_twoShiftRemainder
      (ν := ν) (φ := φ)
      (h := fun z ↦ r • BO z) (v := fun z ↦ (-1 : ℝ) • BG z) (g := BG)
      hφm hφ hrBOm hnegBGm hBGm hmom.1 hmom.2
  apply hrem.congr
  filter_upwards with z
  simp only [neg_one_smul]
  rw [show z.2 - r • BO z.1 + -BG z.1 =
    z.2 - BG z.1 - r • BO z.1 by abel]

/-- Bentkus (3.14) after Gaussian integration by parts: the centered and covariance-matched
terms cancel, so the full density contraction is controlled by the two cubic remainders. -/
private theorem bentkus_largeAngle_densityContraction_le
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφm : Measurable φ) (hφ : ∀ x, |φ x| ≤ 1)
    {D : ℝ} (hD : 0 ≤ D) (hφD : ∀ x, |φ x| ≤ D)
    (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    let ρ := bentkusReplacementMeasure μ X
    let B := bentkusWhiteningCLM (bentkusLeaveOneOutCovarianceMatrix μ X k)
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let r := p / q
    |∫ z, ∫ x, φ x *
        (standardGaussianDensityD1
            (x - B (G z) - r • B (O z)) (B (O z)) -
          r * standardGaussianDensityD1
            (x - B (G z) - r • B (O z)) (B (G z))) ∂volume ∂ρ| ≤
      2016 * D * (3 + Real.sqrt standardGaussianFourthMoment) *
        (p / q ^ 2) * ∫ z, ‖O z‖ ^ 3 ∂ρ := by
  let ρ := bentkusReplacementMeasure μ X
  let B := bentkusWhiteningCLM (bentkusLeaveOneOutCovarianceMatrix μ X k)
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let BO := fun z ↦ B (O z)
  let BG := fun z ↦ B (G z)
  let r := p / q
  let first :
      (((Fin (n + 1) → EuclideanSpace ℝ (Fin d)) ×
          (Fin (n + 1) → EuclideanSpace ℝ (Fin d))) ×
        EuclideanSpace ℝ (Fin d)) → ℝ := fun z ↦
    φ z.2 * (standardGaussianDensityD1
        (z.2 - BG z.1 - r • BO z.1) (BO z.1) -
      standardGaussianDensityD1 (z.2 - BG z.1) (BO z.1) -
      standardGaussianDensityD2 z.2 (BO z.1) ((-r) • BO z.1))
  let second :
      (((Fin (n + 1) → EuclideanSpace ℝ (Fin d)) ×
          (Fin (n + 1) → EuclideanSpace ℝ (Fin d))) ×
        EuclideanSpace ℝ (Fin d)) → ℝ := fun z ↦
    φ z.2 * (standardGaussianDensityD1
        (z.2 - BG z.1 - r • BO z.1) (BG z.1) -
      standardGaussianDensityD1 (z.2 - r • BO z.1) (BG z.1) -
      standardGaussianDensityD2 z.2 (BG z.1) ((-1 : ℝ) • BG z.1))
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hr : 0 ≤ r := div_nonneg hp0 hq0.le
  have hfirstRaw := bentkus_largeAngle_firstShiftRemainder_integrable
    hXm hX3 k B r hr hφm hφ
  have hfirst : Integrable first (ρ.prod volume) := by
    simpa only [first, BO, BG, ρ, O, G] using hfirstRaw
  have hOm : Measurable O := by
    exact (measurable_pi_apply k).comp measurable_fst
  have hGm : Measurable G := by
    exact (measurable_pi_apply k).comp measurable_snd
  have hBOm : Measurable BO := B.continuous.measurable.comp hOm
  have hBGm : Measurable BG := B.continuous.measurable.comp hGm
  have hG3 : MemLp G 3 ρ := memLp_three_replacementGaussian hXm k
  have hBG3 : MemLp BG 3 ρ := by
    simpa only [BG] using hG3.continuousLinearMap_comp B
  have hsecondRaw := bentkus_largeAngle_secondShiftRemainder_integrable
    hBOm hBGm hBG3 r hφm hφ
  have hsecond : Integrable second (ρ.prod volume) := by
    simpa only [second] using hsecondRaw
  have hcancel := bentkus_largeAngle_densityCancellation
    hXm hX3 hX0 k B r hφm hφ
  have hdecomp :=
    bentkus_largeAngle_densityContraction_eq_twoShiftRemainders_of_cancellation
      (ν := ρ) (φ := φ) (O := O) (G := G) B r hfirst hsecond hcancel.1 hcancel.2
  have hrem := bentkus_largeAngle_twoShiftDensityRemainders_le
    hXm hX3 h_indep hX0 hidentity k hk hφm (D := D) hD hφD
      p q hp0 hp1 hq0 hq1
  let A := ∫ z, ∫ x, first (z, x) ∂volume ∂ρ
  let C := ∫ z, ∫ x, second (z, x) ∂volume ∂ρ
  have hfirstEq :
      A = ∫ z, (∫ x, φ x *
        (standardGaussianDensityD1 (x + (-(B (G z))) + (-r) • B (O z)) (B (O z)) -
          standardGaussianDensityD1 (x + (-(B (G z)))) (B (O z)) -
          standardGaussianDensityD2 x (B (O z)) ((-r) • B (O z)))
        ∂volume) ∂ρ := by
    apply integral_congr_ae
    filter_upwards with z
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [A, first, BO, BG]
    rw [show x - B (G z) - r • B (O z) =
        x + (-(B (G z))) + (-r) • B (O z) by module,
      show x - B (G z) = x + (-(B (G z))) by module]
  have hsecondEq :
      C = ∫ z, (∫ x, φ x *
        (standardGaussianDensityD1 (x + ((-r) • B (O z)) + (-1 : ℝ) • B (G z))
            (B (G z)) -
          standardGaussianDensityD1 (x + ((-r) • B (O z))) (B (G z)) -
          standardGaussianDensityD2 x (B (G z)) ((-1 : ℝ) • B (G z)))
        ∂volume) ∂ρ := by
    apply integral_congr_ae
    filter_upwards with z
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [C, second, BO, BG]
    rw [show x - B (G z) - r • B (O z) =
        x + ((-r) • B (O z)) + (-1 : ℝ) • B (G z) by module,
      show x - r • B (O z) = x + ((-r) • B (O z)) by module]
  have hrem' :
      |A| + r * |C| ≤
        2016 * D * (3 + Real.sqrt standardGaussianFourthMoment) *
          (p / q ^ 2) * ∫ z, ‖O z‖ ^ 3 ∂ρ := by
    rw [hfirstEq, hsecondEq]
    simpa only [r, ρ, B, O, G] using hrem
  change
    |∫ z, ∫ x, φ x *
        (standardGaussianDensityD1
            (x - B (G z) - r • B (O z)) (B (O z)) -
          r * standardGaussianDensityD1
            (x - B (G z) - r • B (O z)) (B (G z))) ∂volume ∂ρ| ≤
      2016 * D * (3 + Real.sqrt standardGaussianFourthMoment) *
        (p / q ^ 2) * ∫ z, ‖O z‖ ^ 3 ∂ρ
  have hdecomp' :
      (∫ z, ∫ x, φ x *
        (standardGaussianDensityD1
            (x - B (G z) - r • B (O z)) (B (O z)) -
          r * standardGaussianDensityD1
            (x - B (G z) - r • B (O z)) (B (G z))) ∂volume ∂ρ) =
        A - r * C := by
    simpa only [A, C, first, second, BO, BG] using hdecomp
  rw [hdecomp']
  calc
    |A - r * C| ≤ |A| + |r * C| := abs_sub A (r * C)
    _ = |A| + r * |C| := by rw [abs_mul, abs_of_nonneg hr]
    _ ≤ _ := hrem'

/-- Bentkus (3.14) at one large angle: the actual-minus-reference coordinate derivative has
the exact `cos α / (sin α)²` envelope required for angle integration. -/
private theorem bentkus_largeAngle_rotationCoordinate_sub_reference_le
    {C : ℝ} (hC : 0 ≤ C) {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hIH : bentkusIdentityCovarianceBoundAt.{u} C n)
    (hd : 0 < d) (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (α : ℝ)
    (hp0 : 0 ≤ Real.cos α) (hp1 : Real.cos α ≤ 1)
    (hq0 : 0 < Real.sin α) (hq1 : Real.sin α ≤ 1)
    (s : Set (EuclideanSpace ℝ (Fin d)))
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε) :
    let ρ := bentkusReplacementMeasure μ X
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let UO := bentkusLeaveOneOut
      (fun i ↦ replacementOriginal (d := d) i) k
    let VG := bentkusLeaveOneOut
      (fun i ↦ replacementGaussian (d := d) i) k
    let β := ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
    let βk := ∫ ω, ‖O ω‖ ^ 3 ∂ρ
    |((∫ ω, (fderiv ℝ (convexSetCutoff s ε)
        ((Real.cos α • UO ω + Real.sin α • VG ω) +
          (Real.cos α • O ω + Real.sin α • G ω)))
        ((-(Real.sin α)) • O ω + Real.cos α • G ω) ∂ρ) -
      ∫ ω, (fderiv ℝ (convexSetCutoff s ε)
        (VG ω + (Real.cos α • O ω + Real.sin α • G ω)))
        ((-(Real.sin α)) • O ω + Real.cos α • G ω) ∂ρ)| ≤
      2016 * (8 * C * (d : ℝ) ^ (1 / 4 : ℝ) * β) *
        (3 + Real.sqrt standardGaussianFourthMoment) *
        (Real.cos α / (Real.sin α) ^ 2) * βk := by
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let P := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  let B₀ := bentkusWhiteningCLM S
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let UO := bentkusLeaveOneOut
    (fun i ↦ replacementOriginal (d := d) i) k
  let VG := bentkusLeaveOneOut
    (fun i ↦ replacementGaussian (d := d) i) k
  let U := bentkusLeaveOneOut X k
  let ν := μ.map (fun ω ↦ B (U ω))
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let ψ := fun x ↦ ∫ u, convexSetCutoff s ε
    (P (Real.sin α • x + Real.cos α • u)) ∂ν
  let ψγ := fun x ↦ ∫ u, convexSetCutoff s ε
    (P (Real.sin α • x + Real.cos α • u)) ∂γ
  let φ := fun x ↦ ψ x - ψγ x
  let D := 8 * C * (d : ℝ) ^ (1 / 4 : ℝ) *
    ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
  have hrepr :=
    bentkus_largeAngle_rotationCoordinate_sub_reference_eq_densityContraction
      hXm hX3 h_indep hX0 hidentity k hk α hq0.ne' s hs hε
  have hbounds :=
    bentkus_largeAngle_conditionalCutoff_sub_bounds
      hC hIH hd hXm hX3 h_indep hX0 hidentity k hk
        (Real.cos α) (Real.sin α) s hs hε
  have hφm : Measurable φ := by
    simpa only [S, hS, e, P, B, U, ν, γ, ψ, ψγ, φ] using hbounds.1
  have hφ : ∀ x, |φ x| ≤ 1 := by
    simpa only [S, hS, e, P, B, U, ν, γ, ψ, ψγ, φ] using hbounds.2.1
  have hφD : ∀ x, |φ x| ≤ D := by
    simpa only [S, hS, e, P, B, U, ν, γ, ψ, ψγ, φ, D] using hbounds.2.2
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hcontract :=
    bentkus_largeAngle_densityContraction_le
      hXm hX3 h_indep hX0 hidentity k hk hφm hφ hD hφD
        (Real.cos α) (Real.sin α) hp0 hp1 hq0 hq1
  have hB : B = B₀ := by
    apply ContinuousLinearMap.ext
    intro x
    exact bentkusWhiteningEquiv_apply S hS x
  change
    |((∫ ω, (fderiv ℝ (convexSetCutoff s ε)
        ((Real.cos α • UO ω + Real.sin α • VG ω) +
          (Real.cos α • O ω + Real.sin α • G ω)))
        ((-(Real.sin α)) • O ω + Real.cos α • G ω) ∂ρ) -
      ∫ ω, (fderiv ℝ (convexSetCutoff s ε)
        (VG ω + (Real.cos α • O ω + Real.sin α • G ω)))
        ((-(Real.sin α)) • O ω + Real.cos α • G ω) ∂ρ)| ≤ _
  rw [show
      (∫ ω, (fderiv ℝ (convexSetCutoff s ε)
          ((Real.cos α • UO ω + Real.sin α • VG ω) +
            (Real.cos α • O ω + Real.sin α • G ω)))
          ((-(Real.sin α)) • O ω + Real.cos α • G ω) ∂ρ) -
        ∫ ω, (fderiv ℝ (convexSetCutoff s ε)
          (VG ω + (Real.cos α • O ω + Real.sin α • G ω)))
          ((-(Real.sin α)) • O ω + Real.cos α • G ω) ∂ρ =
        ∫ z, ∫ x, φ x *
          (standardGaussianDensityD1
              (x - B (G z) -
                (Real.cos α / Real.sin α) • B (O z)) (B (O z)) -
            (Real.cos α / Real.sin α) * standardGaussianDensityD1
              (x - B (G z) -
                (Real.cos α / Real.sin α) • B (O z)) (B (G z)))
            ∂volume ∂ρ by
      simpa only [ρ, S, hS, e, P, B, O, G, UO, VG, U, ν, γ, ψ, ψγ, φ]
        using hrepr]
  simpa only [ρ, S, B₀, O, G, φ, D, hB] using hcontract

/-- Integrating the one-angle large-angle replacement bound from `arcsin ε` to `π / 2`
costs exactly one reciprocal smoothing parameter. -/
theorem bentkus_largeAngle_interval_rotationCoordinate_sub_reference_le
    {C : ℝ} (hC : 0 ≤ C) {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hIH : bentkusIdentityCovarianceBoundAt.{u} C n)
    (hd : 0 < d) (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (s : Set (EuclideanSpace ℝ (Fin d)))
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let ρ := bentkusReplacementMeasure μ X
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let UO := bentkusLeaveOneOut
      (fun i ↦ replacementOriginal (d := d) i) k
    let VG := bentkusLeaveOneOut
      (fun i ↦ replacementGaussian (d := d) i) k
    let F := fun α ↦
      (∫ ω, (fderiv ℝ (convexSetCutoff s ε)
        ((Real.cos α • UO ω + Real.sin α • VG ω) +
          (Real.cos α • O ω + Real.sin α • G ω)))
        ((-(Real.sin α)) • O ω + Real.cos α • G ω) ∂ρ) -
      ∫ ω, (fderiv ℝ (convexSetCutoff s ε)
        (VG ω + (Real.cos α • O ω + Real.sin α • G ω)))
        ((-(Real.sin α)) • O ω + Real.cos α • G ω) ∂ρ
    let β := ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
    let βk := ∫ ω, ‖O ω‖ ^ 3 ∂ρ
    |∫ α in Real.arcsin ε..Real.pi / 2, F α| ≤
      (2016 * (8 * C * (d : ℝ) ^ (1 / 4 : ℝ) * β) *
        (3 + Real.sqrt standardGaussianFourthMoment) * βk) / ε := by
  let ρ := bentkusReplacementMeasure μ X
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let UO := bentkusLeaveOneOut
    (fun i ↦ replacementOriginal (d := d) i) k
  let VG := bentkusLeaveOneOut
    (fun i ↦ replacementGaussian (d := d) i) k
  let F := fun α ↦
    (∫ ω, (fderiv ℝ (convexSetCutoff s ε)
      ((Real.cos α • UO ω + Real.sin α • VG ω) +
        (Real.cos α • O ω + Real.sin α • G ω)))
      ((-(Real.sin α)) • O ω + Real.cos α • G ω) ∂ρ) -
    ∫ ω, (fderiv ℝ (convexSetCutoff s ε)
      (VG ω + (Real.cos α • O ω + Real.sin α • G ω)))
      ((-(Real.sin α)) • O ω + Real.cos α • G ω) ∂ρ
  let β := ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
  let βk := ∫ ω, ‖O ω‖ ^ 3 ∂ρ
  let K := 2016 * (8 * C * (d : ℝ) ^ (1 / 4 : ℝ) * β) *
    (3 + Real.sqrt standardGaussianFourthMoment) * βk
  have hβ : 0 ≤ β := by
    dsimp only [β]
    positivity
  have hβk : 0 ≤ βk := by
    dsimp only [βk]
    positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hhalfpi_lt_pi : Real.pi / 2 < Real.pi := by
    linarith [Real.pi_pos]
  have hF : ∀ α ∈ Set.Ioc (Real.arcsin ε) (Real.pi / 2),
      |F α| ≤ K * (Real.cos α / Real.sin α ^ 2) := by
    intro α hα
    have hαpos : 0 < α :=
      (Real.arcsin_pos.mpr hε).trans hα.1
    have hαpi : α < Real.pi := hα.2.trans_lt hhalfpi_lt_pi
    have hp0 : 0 ≤ Real.cos α :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hα.2⟩
    have hp1 : Real.cos α ≤ 1 := Real.cos_le_one α
    have hq0 : 0 < Real.sin α :=
      Real.sin_pos_of_pos_of_lt_pi hαpos hαpi
    have hq1 : Real.sin α ≤ 1 := Real.sin_le_one α
    have hpoint :=
      bentkus_largeAngle_rotationCoordinate_sub_reference_le
        hC hIH hd hXm hX3 h_indep hX0 hidentity k hk α
          hp0 hp1 hq0 hq1 s hs hε
    simpa only [F, K, ρ, O, G, UO, VG, β, βk,
      mul_assoc, mul_left_comm, mul_comm] using hpoint
  simpa only [F, K, ρ, O, G, UO, VG, β, βk] using
    bentkus_largeAngle_integral_le_of_cos_div_sin_sq_envelope
      hε hε1 hK hF



/-- The pointwise Gaussian-density remainder estimate remains valid after conditioning on an
arbitrary measurable parameter.  This is the Fubini step used for the omitted pair
`(X_k,Y_k)` in Bentkus (3.15). -/
private theorem
    bentkus_integral_standardGaussianDensityD1_secondOrderRemainder_le
    {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφm : Measurable φ) (hφ : ∀ x, |φ x| ≤ 1)
    {h g : Ξ → EuclideanSpace ℝ (Fin d)}
    (hh : Measurable h) (hg : Measurable g)
    (hhg : Integrable (fun z ↦ ‖h z‖ ^ 2 * ‖g z‖) ν) :
    |∫ z, (∫ x, φ x *
        (standardGaussianDensityD1 (x - h z) (g z) -
          standardGaussianDensityD1 x (g z) +
          standardGaussianDensityD2 x (h z) (g z)) ∂volume) ∂ν| ≤
      (3 + Real.sqrt standardGaussianFourthMoment) / 2 *
        ∫ z, ‖h z‖ ^ 2 * ‖g z‖ ∂ν := by
  let c : ℝ := (3 + Real.sqrt standardGaussianFourthMoment) / 2
  let R : Ξ → EuclideanSpace ℝ (Fin d) → ℝ := fun z x ↦ φ x *
    (standardGaussianDensityD1 (x - h z) (g z) -
      standardGaussianDensityD1 x (g z) +
      standardGaussianDensityD2 x (h z) (g z))
  have hRm : Measurable (Function.uncurry R) := by
    change Measurable (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ φ p.2 *
      (standardGaussianDensityD1 (p.2 - h p.1) (g p.1) -
        standardGaussianDensityD1 p.2 (g p.1) +
        standardGaussianDensityD2 p.2 (h p.1) (g p.1)))
    unfold standardGaussianDensityD1 standardGaussianDensityD2
    have hx : Measurable (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ p.2) := measurable_snd
    have hh' : Measurable (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ h p.1) :=
      hh.comp measurable_fst
    have hg' : Measurable (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ g p.1) :=
      hg.comp measurable_fst
    have hshift : Measurable
        (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ p.2 - h p.1) := hx.sub hh'
    have hinnerShift : Measurable
        (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ inner ℝ (p.2 - h p.1) (g p.1)) :=
      by
        change Measurable
          ((fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
              inner ℝ q.1 q.2) ∘
            fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ (p.2 - h p.1, g p.1))
        exact continuous_inner.measurable.comp (hshift.prodMk hg')
    have hinnerXG : Measurable
        (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ inner ℝ p.2 (g p.1)) :=
      by
        change Measurable
          ((fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
              inner ℝ q.1 q.2) ∘
            fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ (p.2, g p.1))
        exact continuous_inner.measurable.comp (hx.prodMk hg')
    have hinnerXH : Measurable
        (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ inner ℝ p.2 (h p.1)) :=
      by
        change Measurable
          ((fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
              inner ℝ q.1 q.2) ∘
            fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ (p.2, h p.1))
        exact continuous_inner.measurable.comp (hx.prodMk hh')
    have hinnerHG : Measurable
        (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ inner ℝ (h p.1) (g p.1)) :=
      by
        change Measurable
          ((fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
              inner ℝ q.1 q.2) ∘
            fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ (h p.1, g p.1))
        exact continuous_inner.measurable.comp (hh'.prodMk hg')
    have hdensityShift : Measurable
        (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (p.2 - h p.1)) :=
      continuous_standardGaussianDensity.measurable.comp hshift
    have hdensityX : Measurable
        (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) p.2) :=
      continuous_standardGaussianDensity.measurable.comp hx
    exact (hφm.comp hx).mul
      (((hinnerShift.neg.mul hdensityShift).sub (hinnerXG.neg.mul hdensityX)).add
        (((hinnerXH.mul hinnerXG).sub hinnerHG).mul hdensityX))
  have hinnerMeas : AEStronglyMeasurable (fun z ↦ ∫ x, R z x ∂volume) ν :=
    hRm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
  have hc : 0 ≤ c := by
    dsimp only [c]
    positivity
  have hmajorant : Integrable (fun z ↦ c * (‖h z‖ ^ 2 * ‖g z‖)) ν :=
    hhg.const_mul c
  have hpoint (z : Ξ) : |∫ x, R z x ∂volume| ≤
      c * (‖h z‖ ^ 2 * ‖g z‖) := by
    simpa only [R, c, mul_assoc] using
      bentkus_standardGaussianDensityD1_secondOrderRemainder_integral_bound
        hφm hφ (h z) (g z)
  have hinnerInt : Integrable (fun z ↦ ∫ x, R z x ∂volume) ν := by
    apply hmajorant.mono' hinnerMeas
    filter_upwards with z
    rw [Real.norm_eq_abs]
    exact hpoint z
  calc
    |∫ z, (∫ x, φ x *
        (standardGaussianDensityD1 (x - h z) (g z) -
          standardGaussianDensityD1 x (g z) +
          standardGaussianDensityD2 x (h z) (g z)) ∂volume) ∂ν| =
        |∫ z, ∫ x, R z x ∂volume ∂ν| := rfl
    _ ≤ ∫ z, |∫ x, R z x ∂volume| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ z, c * (‖h z‖ ^ 2 * ‖g z‖) ∂ν := by
      exact integral_mono hinnerInt.abs hmajorant hpoint
    _ = (3 + Real.sqrt standardGaussianFourthMoment) / 2 *
        ∫ z, ‖h z‖ ^ 2 * ‖g z‖ ∂ν := by
      rw [integral_const_mul]

/-- Bentkus (3.15), at a fixed coordinate and angle, after the constant, linear, and quadratic
terms have been removed.  The remaining Gaussian-density contribution is bounded by the third
moment of the original omitted summand. -/
private theorem bentkus_replacementRotated_D1_secondOrderRemainder_le
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (α : ℝ) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφm : Measurable φ) (hφ : ∀ x, |φ x| ≤ 1) :
    let ρ := bentkusReplacementMeasure μ X
    let B := bentkusWhiteningCLM (bentkusLeaveOneOutCovarianceMatrix μ X k)
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let H := fun ω ↦ B (bentkusRotated α O G ω)
    let K := fun ω ↦ B (bentkusRotatedDeriv α O G ω)
    |∫ ω, (∫ x, φ x *
        (standardGaussianDensityD1 (x - H ω) (K ω) -
          standardGaussianDensityD1 x (K ω) +
          standardGaussianDensityD2 x (H ω) (K ω)) ∂volume) ∂ρ| ≤
      448 * (3 + Real.sqrt standardGaussianFourthMoment) *
        ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  let B := bentkusWhiteningCLM S
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let R := bentkusRotated α O G
  let R' := bentkusRotatedDeriv α O G
  let H := fun ω ↦ B (R ω)
  let K := fun ω ↦ B (R' ω)
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hO3 : MemLp O 3 ρ := memLp_replacementOriginal hXm hX3 k
  have hG3 : MemLp G 3 ρ := memLp_three_replacementGaussian hXm k
  have hR3 : MemLp R 3 ρ := by
    change MemLp ((Real.cos α) • O + (Real.sin α) • G) 3 ρ
    exact (hO3.const_smul (Real.cos α)).add (hG3.const_smul (Real.sin α))
  have hR'3 : MemLp R' 3 ρ := by
    change MemLp ((-(Real.sin α)) • O + (Real.cos α) • G) 3 ρ
    exact (hO3.const_smul (-(Real.sin α))).add (hG3.const_smul (Real.cos α))
  have hH3 : MemLp H 3 ρ := by
    simpa only [H, B, S] using memLp_bentkusWhiteningCLM_comp S hR3
  have hK3 : MemLp K 3 ρ := by
    simpa only [K, B, S] using memLp_bentkusWhiteningCLM_comp S hR'3
  letI : ENNReal.HolderTriple 3 3 (3 / 2) := by
    constructor
    have hdiv : (3 / 2 : ℝ≥0∞) ≠ 0 :=
      ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩
    have hinvdiv : (3 / 2 : ℝ≥0∞)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hdiv
    rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) hinvdiv,
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    norm_num
  have hHsq : MemLp (fun ω ↦ ‖H ω‖ * ‖H ω‖) (3 / 2 : ℝ≥0∞) ρ := by
    exact hH3.norm.mul hH3.norm
  letI : ENNReal.HolderTriple (3 / 2) 3 1 := by
    constructor
    have hdiv : (3 / 2 : ℝ≥0∞) ≠ 0 :=
      ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩
    have hinvdiv : (3 / 2 : ℝ≥0∞)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hdiv
    rw [← ENNReal.toReal_eq_toReal_iff'
        (ENNReal.add_ne_top.mpr ⟨hinvdiv, by finiteness⟩) (by norm_num),
      ENNReal.toReal_add hinvdiv (by finiteness)]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_ofNat,
      ENNReal.toReal_one]
    norm_num
  have hmix : Integrable (fun ω ↦ ‖H ω‖ ^ 2 * ‖K ω‖) ρ := by
    have hprod := hHsq.integrable_mul hK3.norm
    refine hprod.congr ?_
    filter_upwards with ω
    simp only [Pi.mul_apply, pow_two]
  have hHmeas : Measurable H := by
    dsimp only [H, R, O, G, B, bentkusRotated,
      replacementOriginal, replacementGaussian]
    fun_prop
  have hKmeas : Measurable K := by
    dsimp only [K, R', O, G, B, bentkusRotatedDeriv,
      replacementOriginal, replacementGaussian]
    fun_prop
  have hrem := bentkus_integral_standardGaussianDensityD1_secondOrderRemainder_le
    (d := d) (ν := ρ) hφm hφ hHmeas hKmeas hmix
  have hmixed :=
    integral_norm_whitened_replacementRotated_sq_mul_norm_whitened_replacementRotatedDeriv_le
      hXm hX3 h_indep hX0 hidentity k hk α
  have hc : 0 ≤ (3 + Real.sqrt standardGaussianFourthMoment) / 2 := by positivity
  calc
    |∫ ω, (∫ x, φ x *
        (standardGaussianDensityD1 (x - H ω) (K ω) -
          standardGaussianDensityD1 x (K ω) +
          standardGaussianDensityD2 x (H ω) (K ω)) ∂volume) ∂ρ| ≤
        (3 + Real.sqrt standardGaussianFourthMoment) / 2 *
          ∫ ω, ‖H ω‖ ^ 2 * ‖K ω‖ ∂ρ := hrem
    _ ≤ (3 + Real.sqrt standardGaussianFourthMoment) / 2 *
        (896 * ∫ ω, ‖O ω‖ ^ 3 ∂ρ) :=
      mul_le_mul_of_nonneg_left (by simpa only [H, K, R, R', B, S, O, G, ρ] using hmixed) hc
    _ = 448 * (3 + Real.sqrt standardGaussianFourthMoment) *
        ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by ring

/-- Bentkus (3.15) at a fixed coordinate and angle.  Gaussian integration by parts, translation,
and equality of the first two moments reduce the full rotation derivative to the cubic density
remainder. -/
private theorem bentkus_gaussianLeaveOneOut_rotationDerivative_le
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (α : ℝ) {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε) :
    let ρ := bentkusReplacementMeasure μ X
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let V := bentkusLeaveOneOut
      (fun i ↦ replacementGaussian (d := d) i) k
    let R := bentkusRotated α O G
    let R' := bentkusRotatedDeriv α O G
    |∫ ω, (fderiv ℝ (convexSetCutoff s ε) (V ω + R ω)) (R' ω) ∂ρ| ≤
      448 * (3 + Real.sqrt standardGaussianFourthMoment) *
        ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let P := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let V := bentkusLeaveOneOut (fun i ↦ replacementGaussian (d := d) i) k
  let R := bentkusRotated α O G
  let R' := bentkusRotatedDeriv α O G
  let H := fun ω ↦ B (R ω)
  let K := fun ω ↦ B (R' ω)
  let φ := fun x ↦ convexSetCutoff s ε (P x)
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hφm : Measurable φ :=
    (measurable_convexSetCutoff s ε).comp P.continuous.measurable
  have hφ : ∀ x, |φ x| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (convexSetCutoff_nonneg s ε (P x))]
    exact convexSetCutoff_le_one s ε (P x)
  have hO3 : MemLp O 3 ρ := memLp_replacementOriginal hXm hX3 k
  have hG3 : MemLp G 3 ρ := memLp_three_replacementGaussian hXm k
  have hR3 : MemLp R 3 ρ := by
    change MemLp ((Real.cos α) • O + (Real.sin α) • G) 3 ρ
    exact (hO3.const_smul (Real.cos α)).add (hG3.const_smul (Real.sin α))
  have hR'3 : MemLp R' 3 ρ := by
    change MemLp ((-(Real.sin α)) • O + (Real.cos α) • G) 3 ρ
    exact (hO3.const_smul (-(Real.sin α))).add (hG3.const_smul (Real.cos α))
  have hH3 : MemLp H 3 ρ := by
    simpa only [H] using hR3.continuousLinearMap_comp B
  have hK3 : MemLp K 3 ρ := by
    simpa only [K] using hR'3.continuousLinearMap_comp B
  have hHm : Measurable H := by
    dsimp only [H, R, O, G, bentkusRotated, replacementOriginal, replacementGaussian]
    fun_prop
  have hKm : Measurable K := by
    dsimp only [K, R', O, G, bentkusRotatedDeriv, replacementOriginal, replacementGaussian]
    fun_prop
  have hKint : Integrable K ρ := hK3.integrable (by norm_num)
  have hshift : Integrable (fun p : _ × EuclideanSpace ℝ (Fin d) ↦
      φ p.2 * standardGaussianDensityD1 (p.2 - H p.1) (K p.1))
      (ρ.prod volume) :=
    integrable_prod_bounded_mul_standardGaussianDensityD1_sub
      hφm hφ hHm hKm hKint
  have hlinear : Integrable (fun p : _ × EuclideanSpace ℝ (Fin d) ↦
      φ p.2 * standardGaussianDensityD1 p.2 (K p.1)) (ρ.prod volume) :=
    integrable_prod_bounded_mul_standardGaussianDensityD1 hφm hφ hKm hKint
  have hH2 := hH3.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 3)
  have hK2 := hK3.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 3)
  have hHsq : Integrable (fun ω ↦ ‖H ω‖ ^ 2) ρ :=
    hH2.integrable_norm_pow (by norm_num)
  have hKsq : Integrable (fun ω ↦ ‖K ω‖ ^ 2) ρ :=
    hK2.integrable_norm_pow (by norm_num)
  have hHK : Integrable (fun ω ↦ ‖H ω‖ * ‖K ω‖) ρ :=
    hH2.norm.integrable_mul hK2.norm
  have hquadMajor : Integrable (fun ω ↦
      (‖H ω‖ ^ 2 + ‖K ω‖ ^ 2) / 2 + ‖H ω‖ * ‖K ω‖) ρ :=
    ((hHsq.add hKsq).div_const 2).add hHK
  have hquadratic : Integrable (fun p : _ × EuclideanSpace ℝ (Fin d) ↦
      φ p.2 * standardGaussianDensityD2 p.2 (H p.1) (K p.1))
      (ρ.prod volume) :=
    integrable_prod_bounded_mul_standardGaussianDensityD2
      hφm hφ hHm hKm hquadMajor
  have hremainder : Integrable (fun p : _ × EuclideanSpace ℝ (Fin d) ↦
      φ p.2 *
        (standardGaussianDensityD1 (p.2 - H p.1) (K p.1) -
          standardGaussianDensityD1 p.2 (K p.1) +
          standardGaussianDensityD2 p.2 (H p.1) (K p.1)))
      (ρ.prod volume) := by
    apply ((hshift.sub hlinear).add hquadratic).congr
    filter_upwards with p
    change (φ p.2 * standardGaussianDensityD1 (p.2 - H p.1) (K p.1) -
        φ p.2 * standardGaussianDensityD1 p.2 (K p.1)) +
        φ p.2 * standardGaussianDensityD2 p.2 (H p.1) (K p.1) = _
    ring
  let Ishift := ∫ ω, ∫ x, φ x *
    standardGaussianDensityD1 (x - H ω) (K ω) ∂volume ∂ρ
  let Ilinear := ∫ ω, ∫ x, φ x *
    standardGaussianDensityD1 x (K ω) ∂volume ∂ρ
  let Iquadratic := ∫ ω, ∫ x, φ x *
    standardGaussianDensityD2 x (H ω) (K ω) ∂volume ∂ρ
  let Iremainder := ∫ ω, ∫ x, φ x *
    (standardGaussianDensityD1 (x - H ω) (K ω) -
      standardGaussianDensityD1 x (K ω) +
      standardGaussianDensityD2 x (H ω) (K ω)) ∂volume ∂ρ
  have hshiftProd : Ishift = ∫ p, φ p.2 *
      standardGaussianDensityD1 (p.2 - H p.1) (K p.1) ∂(ρ.prod volume) := by
    simpa only [Ishift] using integral_integral hshift
  have hlinearProd : Ilinear = ∫ p, φ p.2 *
      standardGaussianDensityD1 p.2 (K p.1) ∂(ρ.prod volume) := by
    simpa only [Ilinear] using integral_integral hlinear
  have hquadraticProd : Iquadratic = ∫ p, φ p.2 *
      standardGaussianDensityD2 p.2 (H p.1) (K p.1) ∂(ρ.prod volume) := by
    simpa only [Iquadratic] using integral_integral hquadratic
  have hdecomp : Iremainder = Ishift - Ilinear + Iquadratic := by
    calc
      Iremainder = ∫ p, φ p.2 *
          (standardGaussianDensityD1 (p.2 - H p.1) (K p.1) -
            standardGaussianDensityD1 p.2 (K p.1) +
            standardGaussianDensityD2 p.2 (H p.1) (K p.1))
          ∂(ρ.prod volume) := integral_integral hremainder
      _ = ∫ p, (φ p.2 * standardGaussianDensityD1 (p.2 - H p.1) (K p.1) -
            φ p.2 * standardGaussianDensityD1 p.2 (K p.1)) +
            φ p.2 * standardGaussianDensityD2 p.2 (H p.1) (K p.1)
          ∂(ρ.prod volume) := by
        apply integral_congr_ae
        filter_upwards with p
        ring
      _ = (∫ p, φ p.2 * standardGaussianDensityD1 (p.2 - H p.1) (K p.1)
            ∂(ρ.prod volume) -
          ∫ p, φ p.2 * standardGaussianDensityD1 p.2 (K p.1)
            ∂(ρ.prod volume)) +
          ∫ p, φ p.2 * standardGaussianDensityD2 p.2 (H p.1) (K p.1)
            ∂(ρ.prod volume) := by
        calc
          _ = (∫ p, φ p.2 * standardGaussianDensityD1 (p.2 - H p.1) (K p.1) -
                φ p.2 * standardGaussianDensityD1 p.2 (K p.1) ∂(ρ.prod volume)) +
              ∫ p, φ p.2 * standardGaussianDensityD2 p.2 (H p.1) (K p.1)
                ∂(ρ.prod volume) :=
            integral_add (hshift.sub hlinear) hquadratic
          _ = _ := by rw [integral_sub hshift hlinear]
      _ = Ishift - Ilinear + Iquadratic := by
        rw [← hshiftProd, ← hlinearProd, ← hquadraticProd]
  have hlow := bentkus_integral_integral_lowOrderDensity_eq_zero
    hXm hX3 hX0 B k α hφm hφ
  have hlinear0 : Ilinear = 0 := by
    simpa only [Ilinear, K, R', O, G, ρ] using hlow.1
  have hquadratic0 : Iquadratic = 0 := by
    simpa only [Iquadratic, H, K, R, R', O, G, ρ] using hlow.2
  have hIeq : Ishift = Iremainder := by
    rw [hdecomp, hlinear0, hquadratic0]
    ring
  have hrem := bentkus_replacementRotated_D1_secondOrderRemainder_le
    hXm hX3 h_indep hX0 hidentity k hk α hφm hφ
  have hB : B = bentkusWhiteningCLM S := by
    apply ContinuousLinearMap.ext
    intro x
    exact bentkusWhiteningEquiv_apply S hS x
  have hrem' : |Iremainder| ≤
      448 * (3 + Real.sqrt standardGaussianFourthMoment) *
        ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
    simpa only [Iremainder, H, K, R, R', hB, S, O, G, ρ] using hrem
  have hderiv :=
    integral_fderiv_convexSetCutoff_gaussianLeaveOneOut_eq_neg_translated_D1
      hXm hX3 h_indep hX0 hidentity k hk α hs hε
  have hderiv' :
      (∫ ω, (fderiv ℝ (convexSetCutoff s ε) (V ω + R ω)) (R' ω) ∂ρ) =
        -Ishift := by
    simpa only [Ishift, φ, H, K, ρ, S, e, P, B, O, G, V, R, R'] using hderiv
  change
    |∫ ω, (fderiv ℝ (convexSetCutoff s ε) (V ω + R ω)) (R' ω) ∂ρ| ≤
      448 * (3 + Real.sqrt standardGaussianFourthMoment) *
        ∫ ω, ‖O ω‖ ^ 3 ∂ρ
  rw [hderiv', abs_neg, hIeq]
  exact hrem'

/-- The Gaussian-reference term in Bentkus (3.12)--(3.15), integrated over an arbitrary ordered
angle interval. -/
theorem bentkus_intervalIntegral_gaussianLeaveOneOut_rotationDerivative_le
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    {a b : ℝ} (hab : a ≤ b) {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε) :
    let ρ := bentkusReplacementMeasure μ X
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let V := bentkusLeaveOneOut
      (fun i ↦ replacementGaussian (d := d) i) k
    |∫ α in a..b, ∫ ω,
        (fderiv ℝ (convexSetCutoff s ε)
          (V ω + bentkusRotated α O G ω))
          (bentkusRotatedDeriv α O G ω) ∂ρ| ≤
      (b - a) * (448 * (3 + Real.sqrt standardGaussianFourthMoment)) *
        ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
  let ρ := bentkusReplacementMeasure μ X
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let V := bentkusLeaveOneOut (fun i ↦ replacementGaussian (d := d) i) k
  let M := (448 * (3 + Real.sqrt standardGaussianFourthMoment)) *
    ∫ ω, ‖O ω‖ ^ 3 ∂ρ
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity
  have hpoint (α : ℝ) :
      ‖∫ ω, (fderiv ℝ (convexSetCutoff s ε)
          (V ω + bentkusRotated α O G ω))
          (bentkusRotatedDeriv α O G ω) ∂ρ‖ ≤ M := by
    rw [Real.norm_eq_abs]
    simpa only [M, ρ, O, G, V, mul_assoc] using
      bentkus_gaussianLeaveOneOut_rotationDerivative_le
        hXm hX3 h_indep hX0 hidentity k hk α hs hε
  change
    |∫ α in a..b, ∫ ω,
        (fderiv ℝ (convexSetCutoff s ε)
          (V ω + bentkusRotated α O G ω))
          (bentkusRotatedDeriv α O G ω) ∂ρ| ≤
      (b - a) * (448 * (3 + Real.sqrt standardGaussianFourthMoment)) *
        ∫ ω, ‖O ω‖ ^ 3 ∂ρ
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ α in a..b, ∫ ω,
        (fderiv ℝ (convexSetCutoff s ε)
          (V ω + bentkusRotated α O G ω))
          (bentkusRotatedDeriv α O G ω) ∂ρ‖ ≤ M * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun α _ ↦ hpoint α
    _ = (b - a) * M := by
      rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      ring
    _ = (b - a) * (448 * (3 + Real.sqrt standardGaussianFourthMoment)) *
        ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
      dsimp only [M]
      ring

end BentkusInduction

end ProbabilityTheory
