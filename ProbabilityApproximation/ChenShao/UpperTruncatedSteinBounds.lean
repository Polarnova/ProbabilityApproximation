/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.ChenShao.UpperTruncatedResidual
import Mathlib.Tactic

/-!
# Exponential Stein bounds for one-sided truncated sums

This module proves the exponentially decaying Stein-solution estimates used for `R₁` and `R₃` in
Chen--Shao (2005), equations (6.17)--(6.18).  Numerical constants are deliberately coarse.
-/

open MeasureTheory ProbabilityTheory Real Set Filter

noncomputable section

namespace ProbabilityTheory

/-- A coarse standard-Gaussian upper-tail estimate in the range used by the nonuniform proof. -/
lemma one_sub_cdf_gaussian_le_exp_neg_half {z : ℝ} (hz : 2 ≤ z) :
    1 - cdf (gaussianReal 0 1) z ≤ exp (-z / 2) := by
  have hz0 : 0 < z := by linarith
  have hmills := one_sub_cdf_gaussian_le_pdf_div hz0
  have hpdf : gaussianPDFReal 0 1 z =
      (√(2 * π))⁻¹ * exp (-z ^ 2 / 2) := by
    simp [gaussianPDFReal, NNReal.coe_one]
  rw [hpdf] at hmills
  have hsqrt : (1 : ℝ) ≤ √(2 * π) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith [Real.two_le_pi]
  have hinvSqrt : (√(2 * π))⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).2 hsqrt
  have hinvZ : z⁻¹ ≤ 1 := (inv_le_one₀ hz0).2 (by linarith)
  have hexp : exp (-z ^ 2 / 2) ≤ exp (-z / 2) := by
    apply exp_le_exp.mpr
    nlinarith [sq_nonneg z]
  calc
    1 - cdf (gaussianReal 0 1) z ≤
        ((√(2 * π))⁻¹ * exp (-z ^ 2 / 2)) / z := hmills
    _ = (√(2 * π))⁻¹ * exp (-z ^ 2 / 2) * z⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ 1 * exp (-z / 2) * 1 := by gcongr
    _ = exp (-z / 2) := by ring

/-- The lower-half pointwise majorant for `|f'_z|` decays exponentially in `z`. -/
lemma steinDeriv_half_region_majorant_le_two_exp {z : ℝ} (hz : 2 ≤ z) :
    (1 - cdf (gaussianReal 0 1) z) *
        (1 + √(2 * π) * (z / 2) * exp (z ^ 2 / 8)) ≤
      2 * exp (-z / 2) := by
  have hz0 : 0 < z := by linarith
  have hmills := one_sub_cdf_gaussian_le_pdf_div hz0
  have hpdf : gaussianPDFReal 0 1 z =
      (√(2 * π))⁻¹ * exp (-z ^ 2 / 2) := by
    simp [gaussianPDFReal, NNReal.coe_one]
  have hmills' : 1 - cdf (gaussianReal 0 1) z ≤
      ((√(2 * π))⁻¹ * exp (-z ^ 2 / 2)) / z := by
    rwa [hpdf] at hmills
  have hsqrtNe : (√(2 * π) : ℝ) ≠ 0 := sqrt_ne_zero'.2 (by positivity)
  have hexpMul : exp (-z ^ 2 / 2) * exp (z ^ 2 / 8) =
      exp (-(3 : ℝ) * z ^ 2 / 8) := by
    rw [← exp_add]
    congr 1
    ring
  have hexpand :
      (((√(2 * π))⁻¹ * exp (-z ^ 2 / 2)) / z) *
          (1 + √(2 * π) * (z / 2) * exp (z ^ 2 / 8)) =
        ((√(2 * π))⁻¹ * exp (-z ^ 2 / 2)) / z +
          (1 / 2) * exp (-(3 : ℝ) * z ^ 2 / 8) := by
    have hst:
        ((√(2 * π))⁻¹ * exp (-z ^ 2 / 2) / z) *
            (√(2 * π) * (z / 2) * exp (z ^ 2 / 8)) =
          (1 / 2) * (exp (-z ^ 2 / 2) * exp (z ^ 2 / 8)) := by
      have hsqrtInv : (√(2 * π))⁻¹ * √(2 * π) = 1 := inv_mul_cancel₀ hsqrtNe
      have hzdiv : (z / 2) / z = (1 : ℝ) / 2 := by field_simp [hz0.ne']
      calc
        ((√(2 * π))⁻¹ * exp (-z ^ 2 / 2) / z) *
              (√(2 * π) * (z / 2) * exp (z ^ 2 / 8)) =
            ((√(2 * π))⁻¹ * √(2 * π)) *
              (exp (-z ^ 2 / 2) * exp (z ^ 2 / 8)) * ((z / 2) / z) := by ring
        _ = 1 * (exp (-z ^ 2 / 2) * exp (z ^ 2 / 8)) * (1 / 2) := by
          rw [hsqrtInv, hzdiv]
        _ = (1 / 2) * (exp (-z ^ 2 / 2) * exp (z ^ 2 / 8)) := by ring
    calc
      (((√(2 * π))⁻¹ * exp (-z ^ 2 / 2)) / z) *
            (1 + √(2 * π) * (z / 2) * exp (z ^ 2 / 8)) =
          ((√(2 * π))⁻¹ * exp (-z ^ 2 / 2)) / z +
            ((√(2 * π))⁻¹ * exp (-z ^ 2 / 2) / z) *
              (√(2 * π) * (z / 2) * exp (z ^ 2 / 8)) := by ring
      _ = ((√(2 * π))⁻¹ * exp (-z ^ 2 / 2)) / z +
            (1 / 2) * (exp (-z ^ 2 / 2) * exp (z ^ 2 / 8)) := by rw [hst]
      _ = ((√(2 * π))⁻¹ * exp (-z ^ 2 / 2)) / z +
            (1 / 2) * exp (-(3 : ℝ) * z ^ 2 / 8) := by rw [hexpMul]
  have htermOne : ((√(2 * π))⁻¹ * exp (-z ^ 2 / 2)) / z ≤
      exp (-z / 2) := by
    have hsqrt : (1 : ℝ) ≤ √(2 * π) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      linarith [Real.two_le_pi]
    have hinvSqrt : (√(2 * π))⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).2 hsqrt
    have hinvZ : z⁻¹ ≤ 1 := (inv_le_one₀ hz0).2 (by linarith)
    have hexp : exp (-z ^ 2 / 2) ≤ exp (-z / 2) := by
      apply exp_le_exp.mpr
      nlinarith [sq_nonneg z]
    rw [div_eq_mul_inv]
    calc
      (√(2 * π))⁻¹ * exp (-z ^ 2 / 2) * z⁻¹ ≤
          1 * exp (-z / 2) * 1 := by gcongr
      _ = exp (-z / 2) := by ring
  have htermTwo : (1 / 2 : ℝ) * exp (-(3 : ℝ) * z ^ 2 / 8) ≤
      exp (-z / 2) := by
    have hexp : exp (-(3 : ℝ) * z ^ 2 / 8) ≤ exp (-z / 2) := by
      apply exp_le_exp.mpr
      nlinarith [sq_nonneg z]
    calc
      (1 / 2 : ℝ) * exp (-(3 : ℝ) * z ^ 2 / 8) ≤
          1 * exp (-z / 2) := by gcongr <;> norm_num
      _ = exp (-z / 2) := one_mul _
  have hfactor : 0 ≤ 1 + √(2 * π) * (z / 2) * exp (z ^ 2 / 8) := by positivity
  have hprod := mul_le_mul_of_nonneg_right hmills' hfactor
  calc
    (1 - cdf (gaussianReal 0 1) z) *
          (1 + √(2 * π) * (z / 2) * exp (z ^ 2 / 8)) ≤
        (((√(2 * π))⁻¹ * exp (-z ^ 2 / 2)) / z) *
          (1 + √(2 * π) * (z / 2) * exp (z ^ 2 / 8)) := hprod
    _ = ((√(2 * π))⁻¹ * exp (-z ^ 2 / 2)) / z +
          (1 / 2) * exp (-(3 : ℝ) * z ^ 2 / 8) := hexpand
    _ ≤ exp (-z / 2) + exp (-z / 2) := add_le_add htermOne htermTwo
    _ = 2 * exp (-z / 2) := by ring

/-- On the lower half-space `w ≤ z/2`, the Stein derivative has exponential decay. -/
lemma abs_steinSolutionDeriv_le_two_exp_of_le_half
    {z w : ℝ} (hz : 2 ≤ z) (hw : w ≤ z / 2) :
    |steinSolutionDeriv z w| ≤ 2 * exp (-z / 2) := by
  have hz0 : 0 < z := by linarith
  rcases le_or_gt w 0 with hw0 | hw0
  · exact (abs_steinSolutionDeriv_le_two_mul_tail hz0 hw0).trans
      (mul_le_mul_of_nonneg_left (one_sub_cdf_gaussian_le_exp_neg_half hz) (by norm_num))
  · have habs : |w| ≤ z / 2 := by simpa [abs_of_nonneg hw0.le] using hw
    exact (abs_steinSolutionDeriv_le_majorant_of_abs_le_half hz habs).trans
      (steinDeriv_half_region_majorant_le_two_exp hz)

private lemma sqrt_two_pi_le_four : √(2 * π) ≤ (4 : ℝ) := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [pi_le_four]

/-- On the lower half-space `w ≤ z/2`, the nonnegative Stein solution has exponential decay. -/
lemma steinSolution_le_two_exp_of_le_half
    {z w : ℝ} (hz : 2 ≤ z) (hw : w ≤ z / 2) :
    steinSolution z w ≤ 2 * exp (-z / 2) := by
  have hz0 : 0 < z := by linarith
  have hwz : w ≤ z := by linarith
  rw [steinSolution_of_le z w hwz]
  rcases le_or_gt w 0 with hw0 | hw0
  · have hmirror := exp_mul_one_sub_Φ_le_half (w := -w) (neg_nonneg.mpr hw0)
    change exp ((-w) ^ 2 / 2) *
      (1 - cdf (gaussianReal 0 1) (-w)) ≤ 1 / 2 at hmirror
    have hexpPhi : exp (w ^ 2 / 2) * cdf (gaussianReal 0 1) w ≤ 1 / 2 := by
      rw [cdf_gaussian_neg w] at hmirror
      simpa [neg_sq] using hmirror
    have htail := one_sub_cdf_gaussian_le_exp_neg_half hz
    have hsqrt0 : 0 ≤ √(2 * π) := sqrt_nonneg _
    have htail0 : 0 ≤ 1 - cdf (gaussianReal 0 1) z :=
      sub_nonneg.mpr (cdf_le_one _ _)
    have hexpPhi0 : 0 ≤ exp (w ^ 2 / 2) * cdf (gaussianReal 0 1) w :=
      mul_nonneg (exp_nonneg _) (cdf_nonneg _ _)
    have hfirst :
        √(2 * π) * (exp (w ^ 2 / 2) * cdf (gaussianReal 0 1) w) ≤
          4 * (1 / 2) :=
      mul_le_mul sqrt_two_pi_le_four hexpPhi hexpPhi0 (by norm_num)
    calc
      √(2 * π) * exp (w ^ 2 / 2) *
            (1 - cdf (gaussianReal 0 1) z) * cdf (gaussianReal 0 1) w =
          √(2 * π) * (exp (w ^ 2 / 2) * cdf (gaussianReal 0 1) w) *
            (1 - cdf (gaussianReal 0 1) z) := by ring
      _ ≤ 4 * (1 / 2) * exp (-z / 2) :=
        mul_le_mul hfirst htail htail0 (by positivity)
      _ = 2 * exp (-z / 2) := by ring
  · have hw0' : 0 ≤ w := hw0.le
    have hwabs : |w| ≤ z / 2 := by simpa [abs_of_nonneg hw0'] using hw
    have hwSq : w ^ 2 ≤ (z / 2) ^ 2 := by
      calc
        w ^ 2 = |w| ^ 2 := (sq_abs w).symm
        _ ≤ (z / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hwabs 2
    have hwExp : exp (w ^ 2 / 2) ≤ exp (z ^ 2 / 8) := by
      apply exp_le_exp.mpr
      nlinarith
    have hΦ : cdf (gaussianReal 0 1) w ≤ 1 := cdf_le_one _ _
    have hmills := one_sub_cdf_gaussian_le_pdf_div hz0
    have hpdf : gaussianPDFReal 0 1 z =
        (√(2 * π))⁻¹ * exp (-z ^ 2 / 2) := by
      simp [gaussianPDFReal, NNReal.coe_one]
    rw [hpdf] at hmills
    have hsqrtNe : (√(2 * π) : ℝ) ≠ 0 := sqrt_ne_zero'.2 (by positivity)
    have hΦ0 : 0 ≤ cdf (gaussianReal 0 1) w := cdf_nonneg _ _
    have htail0 : 0 ≤ 1 - cdf (gaussianReal 0 1) z :=
      sub_nonneg.mpr (cdf_le_one _ _)
    have hmain :
        √(2 * π) * exp (w ^ 2 / 2) *
            (1 - cdf (gaussianReal 0 1) z) * cdf (gaussianReal 0 1) w ≤
          exp (-(3 : ℝ) * z ^ 2 / 8) / z := by
      calc
        √(2 * π) * exp (w ^ 2 / 2) *
              (1 - cdf (gaussianReal 0 1) z) * cdf (gaussianReal 0 1) w ≤
            √(2 * π) * exp (z ^ 2 / 8) *
              (((√(2 * π))⁻¹ * exp (-z ^ 2 / 2)) / z) * 1 := by
                gcongr
        _ = exp (-(3 : ℝ) * z ^ 2 / 8) / z := by
          have hsqrtMul : √(2 * π) * (√(2 * π))⁻¹ = 1 := mul_inv_cancel₀ hsqrtNe
          have hexpMul : exp (z ^ 2 / 8) * exp (-z ^ 2 / 2) =
              exp (-(3 : ℝ) * z ^ 2 / 8) := by
            rw [← exp_add]
            congr 1
            ring
          calc
            √(2 * π) * exp (z ^ 2 / 8) *
                  (((√(2 * π))⁻¹ * exp (-z ^ 2 / 2)) / z) * 1 =
                (√(2 * π) * (√(2 * π))⁻¹) *
                  (exp (z ^ 2 / 8) * exp (-z ^ 2 / 2)) / z := by ring
            _ = exp (-(3 : ℝ) * z ^ 2 / 8) / z := by rw [hsqrtMul, hexpMul, one_mul]
    have hexp : exp (-(3 : ℝ) * z ^ 2 / 8) ≤ exp (-z / 2) := by
      apply exp_le_exp.mpr
      nlinarith [sq_nonneg z]
    calc
      √(2 * π) * exp (w ^ 2 / 2) *
            (1 - cdf (gaussianReal 0 1) z) * cdf (gaussianReal 0 1) w ≤
          exp (-(3 : ℝ) * z ^ 2 / 8) / z := hmain
      _ ≤ exp (-z / 2) / z := div_le_div_of_nonneg_right hexp hz0.le
      _ ≤ exp (-z / 2) := (div_le_iff₀ hz0).2 (by
        have hz1 : 1 ≤ z := by linarith
        nlinarith [exp_pos (-z / 2)])
      _ ≤ 2 * exp (-z / 2) := by nlinarith [exp_pos (-z / 2)]

/-- Global pointwise majorant obtained by combining the lower-half estimate with an exponential
weight on the upper half-space. -/
lemma abs_steinSolutionDeriv_le_exp_majorant
    {z w : ℝ} (hz : 2 ≤ z) :
    |steinSolutionDeriv z w| ≤
      2 * exp (-z / 2) + 2 * exp (w - z / 2) := by
  by_cases hw : w ≤ z / 2
  · exact (abs_steinSolutionDeriv_le_two_exp_of_le_half hz hw).trans
      (le_add_of_nonneg_right (by positivity))
  · have hpos : 0 < w - z / 2 := sub_pos.mpr (lt_of_not_ge hw)
    have hexp : 1 ≤ exp (w - z / 2) := one_le_exp hpos.le
    calc
      |steinSolutionDeriv z w| ≤ 2 := abs_steinSolutionDeriv_le_two z w
      _ ≤ 2 * exp (w - z / 2) := by nlinarith
      _ ≤ 2 * exp (-z / 2) + 2 * exp (w - z / 2) :=
        le_add_of_nonneg_left (by positivity)

/-- The analogous global exponential majorant for the nonnegative Stein solution. -/
lemma steinSolution_le_exp_majorant {z w : ℝ} (hz : 2 ≤ z) :
    steinSolution z w ≤ 2 * exp (-z / 2) + 2 * exp (w - z / 2) := by
  by_cases hw : w ≤ z / 2
  · exact (steinSolution_le_two_exp_of_le_half hz hw).trans
      (le_add_of_nonneg_right (by positivity))
  · have hpos : 0 < w - z / 2 := sub_pos.mpr (lt_of_not_ge hw)
    have hexp : 1 ≤ exp (w - z / 2) := one_le_exp hpos.le
    have habs := abs_steinSolution_le_sqrt_two_pi_div_two z w
    have hfTwo : steinSolution z w ≤ 2 := by
      calc
        steinSolution z w ≤ |steinSolution z w| := le_abs_self _
        _ ≤ √(2 * π) / 2 := habs
        _ ≤ 2 := by linarith [sqrt_two_pi_le_four]
    calc
      steinSolution z w ≤ 2 := hfTwo
      _ ≤ 2 * exp (w - z / 2) := by nlinarith
      _ ≤ 2 * exp (-z / 2) + 2 * exp (w - z / 2) :=
        le_add_of_nonneg_left (by positivity)

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Any random variable with `E e^W ≤ 3` satisfies the exponential expectation bound for
`|f'_z(W)|`. -/
lemma integral_abs_steinSolutionDeriv_le_eight_exp_of_mgf
    {W : Ω → ℝ} (hWmeas : Measurable W)
    (hExp : Integrable (fun ω ↦ exp (W ω)) μ)
    (hmgf : mgf W μ 1 ≤ 3) {z : ℝ} (hz : 2 ≤ z) :
    ∫ ω, |steinSolutionDeriv z (W ω)| ∂μ ≤ 8 * exp (-z / 2) := by
  have hleft : Integrable (fun ω ↦ |steinSolutionDeriv z (W ω)|) μ :=
    Integrable.of_bound
      (((measurable_steinSolutionDeriv z).comp hWmeas).abs.aestronglyMeasurable)
      2 (Eventually.of_forall fun ω ↦ by
        simpa [Real.norm_eq_abs] using abs_steinSolutionDeriv_le_two z (W ω))
  have hshift : Integrable (fun ω ↦ exp (W ω - z / 2)) μ := by
    have heq : (fun ω ↦ exp (W ω - z / 2)) =
        fun ω ↦ exp (-z / 2) * exp (W ω) := by
      funext ω
      rw [← exp_add]
      congr 1
      ring
    rw [heq]
    exact hExp.const_mul _
  have hmajorant : Integrable
      (fun ω ↦ 2 * exp (-z / 2) + 2 * exp (W ω - z / 2)) μ :=
    (integrable_const _).add (hshift.const_mul 2)
  have hmono : ∫ ω, |steinSolutionDeriv z (W ω)| ∂μ ≤
      ∫ ω, (2 * exp (-z / 2) + 2 * exp (W ω - z / 2)) ∂μ :=
    integral_mono hleft hmajorant fun ω ↦ abs_steinSolutionDeriv_le_exp_majorant hz
  calc
    ∫ ω, |steinSolutionDeriv z (W ω)| ∂μ ≤
        ∫ ω, (2 * exp (-z / 2) + 2 * exp (W ω - z / 2)) ∂μ := hmono
    _ = 2 * exp (-z / 2) + 2 * exp (-z / 2) * mgf W μ 1 := by
      rw [integral_add (integrable_const _) (hshift.const_mul 2), integral_const]
      simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
      rw [show (fun ω ↦ 2 * exp (W ω - z / 2)) =
          fun ω ↦ (2 * exp (-z / 2)) * exp (1 * W ω) by
        funext ω
        rw [one_mul, show exp (W ω - z / 2) = exp (-z / 2) * exp (W ω) by
          rw [← exp_add]
          congr 1
          ring]
        ring]
      rw [integral_const_mul]
      rfl
    _ ≤ 2 * exp (-z / 2) + 2 * exp (-z / 2) * 3 := by
      gcongr
    _ = 8 * exp (-z / 2) := by ring

/-- The same MGF assumption bounds `E f_z(W)`. -/
lemma integral_steinSolution_le_eight_exp_of_mgf
    {W : Ω → ℝ} (hWmeas : Measurable W)
    (hExp : Integrable (fun ω ↦ exp (W ω)) μ)
    (hmgf : mgf W μ 1 ≤ 3) {z : ℝ} (hz : 2 ≤ z) :
    ∫ ω, steinSolution z (W ω) ∂μ ≤ 8 * exp (-z / 2) := by
  have hleft : Integrable (fun ω ↦ steinSolution z (W ω)) μ :=
    (integrable_const (μ := μ) (sqrt (2 * π) / 2)).mono'
      ((continuous_steinSolution z).comp_aestronglyMeasurable hWmeas.aestronglyMeasurable)
      (Eventually.of_forall fun ω ↦ by
        simpa [Real.norm_eq_abs, abs_of_nonneg (steinSolution_nonneg z (W ω))] using
          abs_steinSolution_le_sqrt_two_pi_div_two z (W ω))
  have hshift : Integrable (fun ω ↦ exp (W ω - z / 2)) μ := by
    have heq : (fun ω ↦ exp (W ω - z / 2)) =
        fun ω ↦ exp (-z / 2) * exp (W ω) := by
      funext ω
      rw [← exp_add]
      congr 1
      ring
    rw [heq]
    exact hExp.const_mul _
  have hmajorant : Integrable
      (fun ω ↦ 2 * exp (-z / 2) + 2 * exp (W ω - z / 2)) μ :=
    (integrable_const _).add (hshift.const_mul 2)
  have hmono : ∫ ω, steinSolution z (W ω) ∂μ ≤
      ∫ ω, (2 * exp (-z / 2) + 2 * exp (W ω - z / 2)) ∂μ :=
    integral_mono hleft hmajorant fun ω ↦ steinSolution_le_exp_majorant hz
  calc
    ∫ ω, steinSolution z (W ω) ∂μ ≤
        ∫ ω, (2 * exp (-z / 2) + 2 * exp (W ω - z / 2)) ∂μ := hmono
    _ = 2 * exp (-z / 2) + 2 * exp (-z / 2) * mgf W μ 1 := by
      rw [integral_add (integrable_const _) (hshift.const_mul 2), integral_const]
      simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
      rw [show (fun ω ↦ 2 * exp (W ω - z / 2)) =
          fun ω ↦ (2 * exp (-z / 2)) * exp (1 * W ω) by
        funext ω
        rw [one_mul, show exp (W ω - z / 2) = exp (-z / 2) * exp (W ω) by
          rw [← exp_add]
          congr 1
          ring]
        ring]
      rw [integral_const_mul]
      rfl
    _ ≤ 2 * exp (-z / 2) + 2 * exp (-z / 2) * 3 := by
      gcongr
    _ = 8 * exp (-z / 2) := by ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {X : ι → Ω → ℝ}

private lemma integrable_exp_upperTruncated_finsetSum
    (s : Finset ι) (hXmeas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ) :
    Integrable
      (fun ω ↦ exp ((∑ i ∈ s, upperTruncatedFamily X i) ω)) μ := by
  let Y := upperTruncatedFamily X
  have hYmeas : ∀ i, Measurable (Y i) := measurable_upperTruncatedFamily hXmeas
  have hYindep : iIndepFun Y μ := iIndepFun_upperTruncatedFamily h_indep
  have hYle : ∀ i, ∀ᵐ ω ∂μ, Y i ω ≤ 1 := fun i ↦
    ae_of_all μ fun ω ↦ upperTruncateOne_le_one (X i ω)
  have hcoord : ∀ i ∈ s, Integrable (fun ω ↦ exp (1 * Y i ω)) μ := by
    intro i hi
    refine Integrable.of_bound
      (by
        have hmeas : Measurable (fun ω ↦ exp (1 * Y i ω)) := by fun_prop
        exact hmeas.aestronglyMeasurable)
      (exp 1) ?_
    filter_upwards [hYle i] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    simpa only [one_mul] using exp_le_exp.mpr hω
  simpa only [one_mul, Y] using
    hYindep.integrable_exp_mul_sum hYmeas (t := (1 : ℝ)) hcoord

/-- The MGF of the full one-sided truncated sum is at most three at `t = 1`. -/
lemma mgf_upperTruncatedSum_one_le_three
    (hXmeas : ∀ i, Measurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (h_indep : iIndepFun X μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1) :
    mgf (upperTruncatedSum X) μ 1 ≤ 3 := by
  let Y := upperTruncatedFamily X
  have hYmeas : ∀ i, Measurable (Y i) := measurable_upperTruncatedFamily hXmeas
  have hYmem : ∀ i, MemLp (Y i) 2 μ := memLp_upperTruncatedFamily hXmeas hX2
  have hYindep : iIndepFun Y μ := iIndepFun_upperTruncatedFamily h_indep
  have hYmean : ∀ i, ∫ ω, Y i ω ∂μ ≤ 0 := fun i ↦ by
    simpa only [Y, upperTruncatedFamily, Function.comp_apply] using
      integral_upperTruncateOne_comp_nonpos (hXmeas i) (hX2 i) (h_mean i)
  have hYle : ∀ i, ∀ᵐ ω ∂μ, Y i ω ≤ 1 := fun i ↦
    ae_of_all μ fun ω ↦ upperTruncateOne_le_one (X i ω)
  have hsecond : ∑ i ∈ Finset.univ, ∫ ω, (Y i ω) ^ 2 ∂μ ≤ 1 := by
    simpa only [Finset.sum_filter, Finset.mem_univ, if_true] using
      sum_integral_sq_upperTruncatedFamily_le hXmeas hX2 h_mean hvar
  have hmgf := mgf_finsetSum_one_le_three (μ := μ) Finset.univ
    hYmeas hYindep hYmem hYmean hYle hsecond
  have hfun : sumX Y = ∑ i : ι, Y i := by
    funext ω
    simp only [sumX, Finset.sum_apply]
  change mgf (sumX Y) μ 1 ≤ 3
  rw [hfun]
  exact hmgf

lemma integrable_exp_upperTruncatedSum
    (hXmeas : ∀ i, Measurable (X i)) (h_indep : iIndepFun X μ) :
    Integrable (fun ω ↦ exp (upperTruncatedSum X ω)) μ := by
  have h := integrable_exp_upperTruncated_finsetSum (X := X) Finset.univ hXmeas h_indep
  simpa only [upperTruncatedSum, sumX, Finset.sum_apply, Finset.sum_filter,
    Finset.mem_univ, if_true] using h

/-- The leave-one-out truncated sum also has MGF at most three at `t = 1`. -/
lemma mgf_upperTruncated_leaveOneOut_one_le_three
    (hXmeas : ∀ i, Measurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (h_indep : iIndepFun X μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1) (i : ι) :
    mgf (leaveOneOut (upperTruncatedFamily X) i) μ 1 ≤ 3 := by
  let Y := upperTruncatedFamily X
  have hYmeas : ∀ j, Measurable (Y j) := measurable_upperTruncatedFamily hXmeas
  have hYmem : ∀ j, MemLp (Y j) 2 μ := memLp_upperTruncatedFamily hXmeas hX2
  have hYindep : iIndepFun Y μ := iIndepFun_upperTruncatedFamily h_indep
  have hYmean : ∀ j, ∫ ω, Y j ω ∂μ ≤ 0 := fun j ↦ by
    simpa only [Y, upperTruncatedFamily, Function.comp_apply] using
      integral_upperTruncateOne_comp_nonpos (hXmeas j) (hX2 j) (h_mean j)
  have hYle : ∀ j, ∀ᵐ ω ∂μ, Y j ω ≤ 1 := fun j ↦
    ae_of_all μ fun ω ↦ upperTruncateOne_le_one (X j ω)
  have hsecond : ∑ j ∈ Finset.univ.erase i, ∫ ω, (Y j ω) ^ 2 ∂μ ≤ 1 := by
    simpa only [Y, upperTruncatedFamily, Function.comp_apply] using
      sum_integral_sq_upperTruncateOne_erase_le_one hXmeas hX2 h_mean hvar i
  have hmgf := mgf_finsetSum_one_le_three (μ := μ) (Finset.univ.erase i)
    hYmeas hYindep hYmem hYmean hYle hsecond
  have hfun : leaveOneOut (upperTruncatedFamily X) i =
      ∑ j ∈ Finset.univ.erase i, Y j := by
    funext ω
    simp only [leaveOneOut, Finset.sum_apply, Y]
  rw [hfun]
  exact hmgf

lemma integrable_exp_upperTruncated_leaveOneOut
    (hXmeas : ∀ i, Measurable (X i)) (h_indep : iIndepFun X μ) (i : ι) :
    Integrable
      (fun ω ↦ exp (leaveOneOut (upperTruncatedFamily X) i ω)) μ := by
  have h := integrable_exp_upperTruncated_finsetSum (X := X) (Finset.univ.erase i)
    hXmeas h_indep
  simpa only [leaveOneOut, Finset.sum_apply] using h

/-- `E|f'_z(W̄)| ≤ 8 e^{-z/2}`. -/
lemma integral_abs_steinSolutionDeriv_upperTruncatedSum_le
    (hXmeas : ∀ i, Measurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (h_indep : iIndepFun X μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1)
    {z : ℝ} (hz : 2 ≤ z) :
    ∫ ω, |steinSolutionDeriv z (upperTruncatedSum X ω)| ∂μ ≤
      8 * exp (-z / 2) :=
  integral_abs_steinSolutionDeriv_le_eight_exp_of_mgf
    (by simpa only [upperTruncatedSum] using
      measurable_sumX (measurable_upperTruncatedFamily hXmeas))
    (integrable_exp_upperTruncatedSum hXmeas h_indep)
    (mgf_upperTruncatedSum_one_le_three hXmeas hX2 h_indep h_mean hvar) hz

/-- `E f_z(W̄⁽ⁱ⁾) ≤ 8 e^{-z/2}`. -/
lemma integral_steinSolution_upperTruncated_leaveOneOut_le
    (hXmeas : ∀ j, Measurable (X j))
    (hX2 : ∀ j, MemLp (X j) 2 μ)
    (h_indep : iIndepFun X μ)
    (h_mean : ∀ j, ∫ ω, X j ω ∂μ = 0)
    (hvar : ∑ j, variance (X j) μ = 1)
    (i : ι) {z : ℝ} (hz : 2 ≤ z) :
    ∫ ω, steinSolution z (leaveOneOut (upperTruncatedFamily X) i ω) ∂μ ≤
      8 * exp (-z / 2) :=
  integral_steinSolution_le_eight_exp_of_mgf
    (measurable_leaveOneOut (measurable_upperTruncatedFamily hXmeas) i)
    (integrable_exp_upperTruncated_leaveOneOut hXmeas h_indep i)
    (mgf_upperTruncated_leaveOneOut_one_le_three
      hXmeas hX2 h_indep h_mean hvar i) hz

/-- Chen--Shao (2005), (6.17), with explicit constant `8`. -/
lemma abs_upperTruncatedR1_le
    (hXmeas : ∀ i, Measurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (h_indep : iIndepFun X μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1)
    (h3 : ∀ i, Integrable (fun ω ↦ |X i ω| ^ 3) μ)
    {z : ℝ} (hz : 2 ≤ z) :
    |upperTruncatedR1 X μ z| ≤ 8 * exp (-z / 2) * thirdMomentSum X μ := by
  have hmissing0 := upperTruncatedMissingSecondMoment_nonneg hXmeas hX2 h_mean hvar
  have hmissing := upperTruncatedMissingSecondMoment_le_thirdMomentSum
    hXmeas hX2 h_mean hvar h3
  have hgamma0 := thirdMomentSum_nonneg h3
  have hinter := integral_abs_steinSolutionDeriv_upperTruncatedSum_le
    hXmeas hX2 h_indep h_mean hvar hz
  rw [upperTruncatedR1, abs_mul, abs_of_nonneg hmissing0]
  calc
    upperTruncatedMissingSecondMoment X μ *
          |∫ ω, steinSolutionDeriv z (upperTruncatedSum X ω) ∂μ| ≤
        upperTruncatedMissingSecondMoment X μ *
          ∫ ω, |steinSolutionDeriv z (upperTruncatedSum X ω)| ∂μ := by
            gcongr
            exact abs_integral_le_integral_abs
    _ ≤ thirdMomentSum X μ * (8 * exp (-z / 2)) := by
      gcongr
    _ = 8 * exp (-z / 2) * thirdMomentSum X μ := by ring

/-- The total magnitude of the negative means introduced by one-sided truncation is at most the
sum of absolute third moments. -/
lemma sum_neg_integral_upperTruncatedFamily_le_thirdMomentSum
    (hXmeas : ∀ i, Measurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (h3 : ∀ i, Integrable (fun ω ↦ |X i ω| ^ 3) μ) :
    ∑ i, -(∫ ω, upperTruncatedFamily X i ω ∂μ) ≤ thirdMomentSum X μ := by
  unfold thirdMomentSum
  exact Finset.sum_le_sum fun i _ ↦ by
    simpa only [upperTruncatedFamily, Function.comp_apply] using
      neg_integral_upperTruncateOne_comp_le_cube
        (hXmeas i) (hX2 i) (h_mean i) (h3 i)

/-- Chen--Shao (2005), (6.18), with explicit constant `8`. -/
lemma abs_upperTruncatedR3_le
    (hXmeas : ∀ i, Measurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (h_indep : iIndepFun X μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1)
    (h3 : ∀ i, Integrable (fun ω ↦ |X i ω| ^ 3) μ)
    {z : ℝ} (hz : 2 ≤ z) :
    |upperTruncatedR3 X μ z| ≤ 8 * exp (-z / 2) * thirdMomentSum X μ := by
  have hmeanNonpos (i : ι) : ∫ ω, upperTruncatedFamily X i ω ∂μ ≤ 0 := by
    simpa only [upperTruncatedFamily, Function.comp_apply] using
      integral_upperTruncateOne_comp_nonpos (hXmeas i) (hX2 i) (h_mean i)
  have hsteinNonneg (i : ι) : 0 ≤
      ∫ ω, steinSolution z (leaveOneOut (upperTruncatedFamily X) i ω) ∂μ :=
    integral_nonneg fun ω ↦ steinSolution_nonneg z _
  have hrewrite : upperTruncatedR3 X μ z =
      ∑ i, (-(∫ ω, upperTruncatedFamily X i ω ∂μ)) *
        ∫ ω, steinSolution z (leaveOneOut (upperTruncatedFamily X) i ω) ∂μ := by
    simp only [upperTruncatedR3, upperTruncatedMeanCorrection]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hrewrite, abs_of_nonneg (Finset.sum_nonneg fun i _ ↦
    mul_nonneg (neg_nonneg.mpr (hmeanNonpos i)) (hsteinNonneg i))]
  calc
    ∑ i, (-(∫ ω, upperTruncatedFamily X i ω ∂μ)) *
          ∫ ω, steinSolution z (leaveOneOut (upperTruncatedFamily X) i ω) ∂μ ≤
        ∑ i, (-(∫ ω, upperTruncatedFamily X i ω ∂μ)) *
          (8 * exp (-z / 2)) := by
            exact Finset.sum_le_sum fun i _ ↦
              mul_le_mul_of_nonneg_left
                (integral_steinSolution_upperTruncated_leaveOneOut_le
                  hXmeas hX2 h_indep h_mean hvar i hz)
                (neg_nonneg.mpr (hmeanNonpos i))
    _ = (8 * exp (-z / 2)) *
          ∑ i, -(∫ ω, upperTruncatedFamily X i ω ∂μ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ ≤ (8 * exp (-z / 2)) * thirdMomentSum X μ := by
      exact mul_le_mul_of_nonneg_left
        (sum_neg_integral_upperTruncatedFamily_le_thirdMomentSum
          hXmeas hX2 h_mean h3) (by positivity)

end ProbabilityTheory
