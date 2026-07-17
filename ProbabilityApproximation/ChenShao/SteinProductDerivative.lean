/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.ChenShao.NonuniformStein

/-!
# The derivative of the Stein product

This module isolates the pure real-analysis kernel used in Chen--Shao (2005), Lemma 6.5.
For the indicator Stein solution `f_z`, it studies

`g_z(w) = (w f_z(w))' = f_z(w) + w f_z'(w)`.

The product is continuous but has one possible derivative kink, at `w = z`.  The interval FTC
statement below crosses that kink, and the final two pointwise estimates give the partition used
before the probabilistic expectation argument.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped intervalIntegral

noncomputable section

namespace ProbabilityTheory

/-- The pointwise extension of `(w * f_z(w))'` across the unique possible kink `w = z`. -/
def steinProductDeriv (z w : ℝ) : ℝ :=
  steinSolution z w + w * steinSolutionDeriv z w

/-- Away from the indicator kink, `steinProductDeriv` is the classical derivative of `w f_z(w)`.
-/
lemma hasDerivAt_mul_steinSolution (z w : ℝ) (hw : w ≠ z) :
    HasDerivAt (fun u => u * steinSolution z u) (steinProductDeriv z w) w := by
  have h := (hasDerivAt_id w).mul (hasDerivAt_steinSolutionDeriv z w hw)
  exact h.congr_deriv (by simp [steinProductDeriv])

/-- Closed form of the product derivative on the lower side of the kink. -/
lemma steinProductDeriv_of_le {z w : ℝ} (hw : w ≤ z) :
    steinProductDeriv z w =
      (1 - cdf (gaussianReal 0 1) z) *
        (√(2 * π) * (1 + w ^ 2) * exp (w ^ 2 / 2) *
            cdf (gaussianReal 0 1) w + w) := by
  rw [steinProductDeriv, steinSolution_of_le z w hw, steinSolutionDeriv_of_le hw]
  ring

/-- Closed form of the product derivative on the upper side of the kink. -/
lemma steinProductDeriv_of_gt {z w : ℝ} (hw : z < w) :
    steinProductDeriv z w =
      cdf (gaussianReal 0 1) z *
        (√(2 * π) * (1 + w ^ 2) * exp (w ^ 2 / 2) *
            (1 - cdf (gaussianReal 0 1) w) - w) := by
  rw [steinProductDeriv, steinSolution_of_ge z w hw.le, steinSolutionDeriv_of_gt hw]
  ring

/-! ### Lower Mills inequality and positivity -/

private lemma integral_standardNormalPDF_Iic (x : ℝ) :
    ∫ t in Iic x, gaussianPDFReal 0 1 t = cdf (gaussianReal 0 1) x := by
  have hμ : (gaussianReal (0 : ℝ) 1) (Iic x) =
      ENNReal.ofReal (∫ t in Iic x, gaussianPDFReal 0 1 t) :=
    gaussianReal_apply_eq_integral 0 one_ne_zero (Iic x)
  have hcdf : cdf (gaussianReal 0 1) x = (gaussianReal 0 1).real (Iic x) :=
    cdf_eq_real (gaussianReal 0 1) x
  have hnonneg : 0 ≤ ∫ t in Iic x, gaussianPDFReal 0 1 t :=
    setIntegral_nonneg measurableSet_Iic fun _ _ => gaussianPDFReal_nonneg 0 1 _
  rw [hcdf, Measure.real, hμ, ENNReal.toReal_ofReal hnonneg]

private lemma hasDerivAt_standardNormalCDF (x : ℝ) :
    HasDerivAt (cdf (gaussianReal 0 1)) (gaussianPDFReal 0 1 x) x := by
  have hpdf : Integrable (gaussianPDFReal 0 1) := integrable_gaussianPDFReal 0 1
  have hcont : ContinuousAt (gaussianPDFReal 0 1) x := by
    unfold gaussianPDFReal
    fun_prop
  have hpoint (u : ℝ) :
      ∫ t in Iic u, gaussianPDFReal 0 1 t =
        (∫ t in Iic x, gaussianPDFReal 0 1 t) +
          ∫ t in x..u, gaussianPDFReal 0 1 t := by
    have hu := hpdf.integrableOn (s := Iic u)
    have hx := hpdf.integrableOn (s := Iic x)
    linarith [intervalIntegral.integral_Iic_sub_Iic hx hu]
  have hFTC : HasDerivAt (fun u => ∫ t in x..u, gaussianPDFReal 0 1 t)
      (gaussianPDFReal 0 1 x) x :=
    intervalIntegral.integral_hasDerivAt_right hpdf.intervalIntegrable
      hpdf.aestronglyMeasurable.stronglyMeasurableAtFilter hcont
  have hbase := (hasDerivAt_const x (∫ t in Iic x, gaussianPDFReal 0 1 t)).add hFTC
  have hsum : HasDerivAt (fun u => ∫ t in Iic u, gaussianPDFReal 0 1 t)
      (gaussianPDFReal 0 1 x) x :=
    (hbase.congr_of_eventuallyEq (Eventually.of_forall hpoint)).congr_deriv (by ring)
  exact hsum.congr_of_eventuallyEq
    (Eventually.of_forall fun u => (integral_standardNormalPDF_Iic u).symm)

private lemma hasDerivAt_standardNormalPDF (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hinner : HasDerivAt (fun u : ℝ => -u ^ 2 / 2) (-x) x := by
    have h := ((hasDerivAt_id x).mul (hasDerivAt_id x)).neg.div_const 2
    have h' : HasDerivAt (fun u : ℝ => -(u * u) / 2) (-x) x := by
      exact h.congr_of_eventuallyEq (Eventually.of_forall fun u => by rfl) |>.congr_deriv (by
        simp [id_eq])
    simpa only [pow_two] using h'
  have h := (hasDerivAt_const x (√(2 * π))⁻¹).mul hinner.exp
  have h' : HasDerivAt
      (fun u : ℝ => (√(2 * π))⁻¹ * exp (-u ^ 2 / 2))
      (-x * ((√(2 * π))⁻¹ * exp (-x ^ 2 / 2))) x := by
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun u => by rfl) |>.congr_deriv (by ring)
  rw [gaussianPDFReal_def]
  simpa only [NNReal.coe_one, mul_one, sub_zero] using h'

private def lowerMillsGap (x : ℝ) : ℝ :=
  1 - cdf (gaussianReal 0 1) x -
    x / (1 + x ^ 2) * gaussianPDFReal 0 1 x

private lemma hasDerivAt_lowerMillsGap (x : ℝ) :
    HasDerivAt lowerMillsGap
      (-2 * gaussianPDFReal 0 1 x / (1 + x ^ 2) ^ 2) x := by
  have hden : (1 + x ^ 2 : ℝ) ≠ 0 := by positivity
  have hratio : HasDerivAt (fun u : ℝ => u / (1 + u ^ 2))
      ((1 - x ^ 2) / (1 + x ^ 2) ^ 2) x := by
    have h := (hasDerivAt_id x).div
      ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_pow 2 x)) hden
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun u => by
      simp [Pi.add_apply]) |>.congr_deriv (by
      simp only [Pi.add_apply, id_eq, zero_add, one_mul, Nat.cast_ofNat, pow_succ,
        pow_zero]
      field_simp [hden]
      ring)
  have htail : HasDerivAt (fun u : ℝ => 1 - cdf (gaussianReal 0 1) u)
      (-gaussianPDFReal 0 1 x) x := by
    have h := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_standardNormalCDF x)
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun u => by rfl) |>.congr_deriv (by ring)
  have hprod := hratio.mul (hasDerivAt_standardNormalPDF x)
  have h := htail.sub hprod
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun u => by rfl) |>.congr_deriv (by
    field_simp [hden]
    ring)

private lemma tendsto_standardNormalPDF_atTop_zero :
    Tendsto (gaussianPDFReal 0 1) atTop (𝓝 0) := by
  have hsq : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := by
    simpa [pow_two] using (tendsto_mul_self_atTop (α := ℝ))
  have hhalf : Tendsto (fun x : ℝ => x ^ 2 / 2) atTop atTop :=
    hsq.atTop_div_const (by norm_num)
  have hbot : Tendsto (fun x : ℝ => -x ^ 2 / 2) atTop atBot := by
    refine (tendsto_neg_atTop_atBot.comp hhalf).congr ?_
    intro x
    simp
    ring
  have hexp : Tendsto (fun x : ℝ => exp (-x ^ 2 / 2)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp hbot
  have hconst : Tendsto (fun _ : ℝ => (√(2 * π))⁻¹) atTop (𝓝 (√(2 * π))⁻¹) :=
    tendsto_const_nhds
  have h := hconst.mul hexp
  have hzero : Tendsto
      (fun x : ℝ => (√(2 * π))⁻¹ * exp (-x ^ 2 / 2)) atTop (𝓝 0) := by
    simpa using h
  refine hzero.congr' ?_
  filter_upwards with x
  simp [gaussianPDFReal, NNReal.coe_one]

private lemma tendsto_lowerMillsGap_atTop_zero :
    Tendsto lowerMillsGap atTop (𝓝 0) := by
  have htail : Tendsto (fun x : ℝ => 1 - cdf (gaussianReal 0 1) x) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa using hconst.sub (tendsto_cdf_atTop (gaussianReal 0 1))
  have hprod : Tendsto
      (fun x : ℝ => x / (1 + x ^ 2) * gaussianPDFReal 0 1 x) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ tendsto_standardNormalPDF_atTop_zero
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      exact mul_nonneg (div_nonneg hx (by positivity)) (gaussianPDFReal_nonneg 0 1 x)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      have hratio : x / (1 + x ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith [sq_nonneg x]
      exact mul_le_of_le_one_left (gaussianPDFReal_nonneg 0 1 x) hratio
  change Tendsto
    (fun x : ℝ => 1 - cdf (gaussianReal 0 1) x -
      x / (1 + x ^ 2) * gaussianPDFReal 0 1 x) atTop (𝓝 0)
  simpa only [sub_zero] using htail.sub hprod

/-- Lower Mills inequality for the standard Gaussian, including the endpoint `x = 0`. -/
lemma gaussianPDF_mul_div_one_add_sq_le_one_sub_cdf {x : ℝ} (hx : 0 ≤ x) :
    x / (1 + x ^ 2) * gaussianPDFReal 0 1 x ≤
      1 - cdf (gaussianReal 0 1) x := by
  have hCDF : Continuous (cdf (gaussianReal 0 1)) :=
    continuous_iff_continuousAt.2 fun y => (hasDerivAt_standardNormalCDF y).continuousAt
  have hPDF : Continuous (gaussianPDFReal 0 1) :=
    continuous_iff_continuousAt.2 fun y => (hasDerivAt_standardNormalPDF y).continuousAt
  have hden : Continuous (fun y : ℝ => 1 + y ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hratio : Continuous (fun y : ℝ => y / (1 + y ^ 2)) :=
    continuous_id.div₀ hden fun y => by positivity
  have hcont : Continuous lowerMillsGap := by
    unfold lowerMillsGap
    exact (continuous_const.sub hCDF).sub (hratio.mul hPDF)
  have hanti : AntitoneOn lowerMillsGap (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont.continuousOn ?_ ?_
    · intro y hy
      exact (hasDerivAt_lowerMillsGap y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hasDerivAt_lowerMillsGap y).deriv]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (gaussianPDFReal_nonneg 0 1 y))
        (sq_nonneg _)
  have hgap : 0 ≤ lowerMillsGap x := by
    refine le_of_tendsto tendsto_lowerMillsGap_atTop_zero ?_
    filter_upwards [eventually_ge_atTop x] with y hxy
    exact hanti hx (le_trans hx hxy) hxy
  exact sub_nonneg.mp hgap

private lemma rightMillsBracket_nonneg (w : ℝ) :
    0 ≤ √(2 * π) * (1 + w ^ 2) * exp (w ^ 2 / 2) *
        (1 - cdf (gaussianReal 0 1) w) - w := by
  rcases le_or_gt w 0 with hw | hw
  · have hterm : 0 ≤ √(2 * π) * (1 + w ^ 2) * exp (w ^ 2 / 2) *
        (1 - cdf (gaussianReal 0 1) w) := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (sqrt_nonneg _) (by positivity)) (exp_nonneg _))
        (sub_nonneg.mpr (cdf_le_one _ _))
    linarith
  · have hlow := gaussianPDF_mul_div_one_add_sq_le_one_sub_cdf hw.le
    have hfac : 0 ≤ √(2 * π) * (1 + w ^ 2) * exp (w ^ 2 / 2) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlow hfac
    have hne : (√(2 * π) : ℝ) ≠ 0 := sqrt_ne_zero'.2 (by positivity)
    have hden : (1 + w ^ 2 : ℝ) ≠ 0 := by positivity
    have he : exp (w ^ 2 / 2) * exp (-w ^ 2 / 2) = (1 : ℝ) := by
      rw [← exp_add, show w ^ 2 / 2 + -w ^ 2 / 2 = 0 by ring, exp_zero]
    have hsimp :
        (√(2 * π) * (1 + w ^ 2) * exp (w ^ 2 / 2)) *
            (w / (1 + w ^ 2) * gaussianPDFReal 0 1 w) = w := by
      have hpdf : gaussianPDFReal 0 1 w =
          (√(2 * π))⁻¹ * exp (-w ^ 2 / 2) := by
        simp [gaussianPDFReal, NNReal.coe_one]
      rw [hpdf]
      calc
        (√(2 * π) * (1 + w ^ 2) * exp (w ^ 2 / 2)) *
              (w / (1 + w ^ 2) * ((√(2 * π))⁻¹ * exp (-w ^ 2 / 2))) =
            w * (√(2 * π) * (√(2 * π))⁻¹) *
              (exp (w ^ 2 / 2) * exp (-w ^ 2 / 2)) := by
                field_simp [hden]
        _ = w := by rw [mul_inv_cancel₀ hne, he]; ring
    rw [hsimp] at hmul
    exact sub_nonneg.mpr hmul

private lemma leftMillsBracket_nonneg (w : ℝ) :
    0 ≤ √(2 * π) * (1 + w ^ 2) * exp (w ^ 2 / 2) *
        cdf (gaussianReal 0 1) w + w := by
  rcases le_or_gt w 0 with hw | hw
  · have h := rightMillsBracket_nonneg (-w)
    rw [cdf_gaussian_neg w] at h
    simpa [neg_sq] using h
  · exact add_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (sqrt_nonneg _) (by positivity)) (exp_nonneg _))
        (cdf_nonneg _ _)) hw.le

/-- The Stein product derivative is nonnegative everywhere. -/
lemma steinProductDeriv_nonneg (z w : ℝ) : 0 ≤ steinProductDeriv z w := by
  rcases le_or_gt w z with hw | hw
  · rw [steinProductDeriv_of_le hw]
    exact mul_nonneg (sub_nonneg.mpr (cdf_le_one _ _)) (leftMillsBracket_nonneg w)
  · rw [steinProductDeriv_of_gt hw]
    exact mul_nonneg (cdf_nonneg _ _) (rightMillsBracket_nonneg w)

/-! ### Chen--Shao partition bounds -/

/-- An explicit absolute constant for the lower half-space estimate. -/
def steinProductLowConstant : ℝ :=
  2 * √(2 * π) * exp (1 / 2) + 9

lemma steinProductLowConstant_pos : 0 < steinProductLowConstant := by
  unfold steinProductLowConstant
  positivity

/-- The standard Gaussian tail is at most `e^{-z/2}` for `z ≥ 2`. -/
lemma one_sub_cdf_gaussian_le_exp_neg_half_linear {z : ℝ} (hz : 2 ≤ z) :
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
  have hinvSqrt : (√(2 * π))⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).2 hsqrt
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

private lemma rightMillsBracket_le_lowConstant (x : ℝ) (hx : 0 ≤ x) :
    √(2 * π) * (1 + x ^ 2) * exp (x ^ 2 / 2) *
        (1 - cdf (gaussianReal 0 1) x) - x ≤ steinProductLowConstant - 8 := by
  rcases le_or_gt x 1 with hx1 | hx1
  · have hsq : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
    have hfac : 0 ≤ √(2 * π) * (1 + x ^ 2) * exp (x ^ 2 / 2) := by positivity
    have htail : 1 - cdf (gaussianReal 0 1) x ≤ 1 :=
      sub_le_self 1 (cdf_nonneg _ _)
    have hone : 1 + x ^ 2 ≤ (2 : ℝ) := by linarith
    have hexp : exp (x ^ 2 / 2) ≤ exp (1 / 2) :=
      exp_le_exp.mpr (by linarith)
    have hterm :
        √(2 * π) * (1 + x ^ 2) * exp (x ^ 2 / 2) *
            (1 - cdf (gaussianReal 0 1) x) ≤
          2 * √(2 * π) * exp (1 / 2) := by
      calc
        √(2 * π) * (1 + x ^ 2) * exp (x ^ 2 / 2) *
              (1 - cdf (gaussianReal 0 1) x) ≤
            √(2 * π) * (1 + x ^ 2) * exp (x ^ 2 / 2) * 1 := by gcongr
        _ ≤ √(2 * π) * 2 * exp (x ^ 2 / 2) * 1 := by gcongr
        _ ≤ √(2 * π) * 2 * exp (1 / 2) * 1 := by gcongr
        _ = 2 * √(2 * π) * exp (1 / 2) := by ring
    unfold steinProductLowConstant
    linarith
  · have hx0 : 0 < x := lt_of_le_of_lt zero_le_one hx1
    have hmills := one_sub_cdf_gaussian_le_pdf_div hx0
    have hfac : 0 ≤ √(2 * π) * (1 + x ^ 2) * exp (x ^ 2 / 2) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hmills hfac
    have hne : (√(2 * π) : ℝ) ≠ 0 := sqrt_ne_zero'.2 (by positivity)
    have he : exp (x ^ 2 / 2) * exp (-x ^ 2 / 2) = (1 : ℝ) := by
      rw [← exp_add, show x ^ 2 / 2 + -x ^ 2 / 2 = 0 by ring, exp_zero]
    have hsimp :
        (√(2 * π) * (1 + x ^ 2) * exp (x ^ 2 / 2)) *
            (gaussianPDFReal 0 1 x / x) = (1 + x ^ 2) / x := by
      have hpdf : gaussianPDFReal 0 1 x =
          (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) := by
        simp [gaussianPDFReal, NNReal.coe_one]
      rw [hpdf]
      calc
        (√(2 * π) * (1 + x ^ 2) * exp (x ^ 2 / 2)) *
              (((√(2 * π))⁻¹ * exp (-x ^ 2 / 2)) / x) =
            (1 + x ^ 2) / x * (√(2 * π) * (√(2 * π))⁻¹) *
              (exp (x ^ 2 / 2) * exp (-x ^ 2 / 2)) := by ring
        _ = (1 + x ^ 2) / x := by rw [mul_inv_cancel₀ hne, he]; ring
    rw [hsimp] at hmul
    have hdiv : (1 + x ^ 2) / x - x = 1 / x := by field_simp [hx0.ne']; ring
    have hinv : 1 / x ≤ 1 := by
      exact (div_le_one hx0).2 hx1.le
    have hbracket :
        √(2 * π) * (1 + x ^ 2) * exp (x ^ 2 / 2) *
            (1 - cdf (gaussianReal 0 1) x) - x ≤ 1 := by
      calc
        √(2 * π) * (1 + x ^ 2) * exp (x ^ 2 / 2) *
              (1 - cdf (gaussianReal 0 1) x) - x ≤ (1 + x ^ 2) / x - x :=
          sub_le_sub_right hmul x
        _ = 1 / x := hdiv
        _ ≤ 1 := hinv
    have hnonneg : 0 ≤ 2 * √(2 * π) * exp (1 / 2) := by positivity
    unfold steinProductLowConstant
    linarith

private lemma steinProductDeriv_le_eight_exp_of_nonneg_le_half
    {z w : ℝ} (hz : 2 ≤ z) (hw0 : 0 ≤ w) (hw : w ≤ z / 2) :
    steinProductDeriv z w ≤ 8 * exp (-z / 2) := by
  have hz0 : 0 < z := by linarith
  have hwz : w ≤ z := by linarith
  have hsq : w ^ 2 ≤ (z / 2) ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self hw0 hw
  have hsqz : w ^ 2 ≤ z ^ 2 := by nlinarith [sq_nonneg z]
  have hexp : exp (w ^ 2 / 2) ≤ exp (z ^ 2 / 8) := by
    apply exp_le_exp.mpr
    nlinarith
  have hΦ : cdf (gaussianReal 0 1) w ≤ 1 := cdf_le_one _ _
  have hfacw : 0 ≤ √(2 * π) * (1 + w ^ 2) * exp (w ^ 2 / 2) := by positivity
  let B : ℝ := √(2 * π) * (1 + z ^ 2) * exp (z ^ 2 / 8)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hterm :
      √(2 * π) * (1 + w ^ 2) * exp (w ^ 2 / 2) *
          cdf (gaussianReal 0 1) w ≤ B := by
    calc
      √(2 * π) * (1 + w ^ 2) * exp (w ^ 2 / 2) *
            cdf (gaussianReal 0 1) w ≤
          √(2 * π) * (1 + w ^ 2) * exp (w ^ 2 / 2) * 1 := by gcongr
      _ ≤ √(2 * π) * (1 + z ^ 2) * exp (z ^ 2 / 8) * 1 := by gcongr
      _ = B := by simp [B]
  have hsqrt : (1 : ℝ) ≤ √(2 * π) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith [Real.two_le_pi]
  have honeexp : (1 : ℝ) ≤ exp (z ^ 2 / 8) := one_le_exp (by positivity)
  have hzpoly : z ≤ 1 + z ^ 2 := by nlinarith [sq_nonneg (z - 1)]
  have hzB : z ≤ B := by
    calc
      z ≤ 1 * (1 + z ^ 2) * 1 := by simpa using hzpoly
      _ ≤ √(2 * π) * (1 + z ^ 2) * exp (z ^ 2 / 8) := by gcongr
      _ = B := rfl
  have hbracket :
      √(2 * π) * (1 + w ^ 2) * exp (w ^ 2 / 2) *
          cdf (gaussianReal 0 1) w + w ≤ 2 * B := by
    linarith
  have htail0 : 0 ≤ 1 - cdf (gaussianReal 0 1) z :=
    sub_nonneg.mpr (cdf_le_one _ _)
  rw [steinProductDeriv_of_le hwz]
  have hfirst :
      (1 - cdf (gaussianReal 0 1) z) *
          (√(2 * π) * (1 + w ^ 2) * exp (w ^ 2 / 2) *
            cdf (gaussianReal 0 1) w + w) ≤
        (1 - cdf (gaussianReal 0 1) z) * (2 * B) :=
    mul_le_mul_of_nonneg_left hbracket htail0
  have hmills := one_sub_cdf_gaussian_le_pdf_div hz0
  have hsecond :
      (1 - cdf (gaussianReal 0 1) z) * (2 * B) ≤
        (gaussianPDFReal 0 1 z / z) * (2 * B) :=
    mul_le_mul_of_nonneg_right hmills (mul_nonneg (by norm_num) hB0)
  have hne : (√(2 * π) : ℝ) ≠ 0 := sqrt_ne_zero'.2 (by positivity)
  have he : exp (-z ^ 2 / 2) * exp (z ^ 2 / 8) =
      exp (-(3 : ℝ) * z ^ 2 / 8) := by
    rw [← exp_add]
    congr 1
    ring
  have hsimp :
      (gaussianPDFReal 0 1 z / z) * (2 * B) =
        2 * ((1 + z ^ 2) / z) * exp (-(3 : ℝ) * z ^ 2 / 8) := by
    have hpdf : gaussianPDFReal 0 1 z =
        (√(2 * π))⁻¹ * exp (-z ^ 2 / 2) := by
      simp [gaussianPDFReal, NNReal.coe_one]
    rw [hpdf]
    dsimp [B]
    calc
      (((√(2 * π))⁻¹ * exp (-z ^ 2 / 2)) / z) *
            (2 * (√(2 * π) * (1 + z ^ 2) * exp (z ^ 2 / 8))) =
          2 * ((1 + z ^ 2) / z) *
            ((√(2 * π))⁻¹ * √(2 * π)) *
            (exp (-z ^ 2 / 2) * exp (z ^ 2 / 8)) := by ring
      _ = 2 * ((1 + z ^ 2) / z) * exp (-(3 : ℝ) * z ^ 2 / 8) := by
        rw [inv_mul_cancel₀ hne, he]
        ring
  have hratio : (1 + z ^ 2) / z = z + 1 / z := by field_simp [hz0.ne']; ring
  have hinv : 1 / z ≤ 1 := (div_le_one hz0).2 (by linarith)
  have hratio_le : (1 + z ^ 2) / z ≤ z + 1 := by rw [hratio]; linarith
  have hsplit :
      exp (-(3 : ℝ) * z ^ 2 / 8) ≤ exp (-z / 2) * exp (-z / 4) := by
    rw [← exp_add]
    exact exp_le_exp.mpr (by nlinarith)
  have hpoly : (z + 1) * exp (-z / 4) ≤ 4 := by
    have hexplower := Real.add_one_le_exp (z / 4)
    have hlin : z + 1 ≤ 4 * exp (z / 4) := by
      have hpos := exp_pos (z / 4)
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hlin (exp_nonneg (-z / 4))
    have hecancel : exp (z / 4) * exp (-z / 4) = (1 : ℝ) := by
      rw [← exp_add, show z / 4 + -z / 4 = 0 by ring, exp_zero]
    calc
      (z + 1) * exp (-z / 4) ≤
          (4 * exp (z / 4)) * exp (-z / 4) := hmul
      _ = 4 := by rw [mul_assoc, hecancel, mul_one]
  calc
    (1 - cdf (gaussianReal 0 1) z) *
          (√(2 * π) * (1 + w ^ 2) * exp (w ^ 2 / 2) *
            cdf (gaussianReal 0 1) w + w) ≤
        (1 - cdf (gaussianReal 0 1) z) * (2 * B) := hfirst
    _ ≤ (gaussianPDFReal 0 1 z / z) * (2 * B) := hsecond
    _ = 2 * ((1 + z ^ 2) / z) * exp (-(3 : ℝ) * z ^ 2 / 8) := hsimp
    _ ≤ 2 * (z + 1) * (exp (-z / 2) * exp (-z / 4)) := by gcongr
    _ = 2 * ((z + 1) * exp (-z / 4)) * exp (-z / 2) := by ring
    _ ≤ 2 * 4 * exp (-z / 2) := by gcongr
    _ = 8 * exp (-z / 2) := by ring

/-- Lower partition estimate used in Chen--Shao Lemma 6.5.  Its constant is explicit and
absolute; the relevant feature is the `e^{-z/2}` decay, uniform over the whole half-line
`w ≤ z/2`. -/
lemma steinProductDeriv_le_low_exp {z w : ℝ} (hz : 2 ≤ z) (hw : w ≤ z / 2) :
    steinProductDeriv z w ≤ steinProductLowConstant * exp (-z / 2) := by
  rcases le_or_gt w 0 with hw0 | hw0
  · have hwz : w ≤ z := by linarith
    have hleft :
        √(2 * π) * (1 + w ^ 2) * exp (w ^ 2 / 2) *
            cdf (gaussianReal 0 1) w + w ≤ steinProductLowConstant - 8 := by
      have h := rightMillsBracket_le_lowConstant (-w) (neg_nonneg.mpr hw0)
      rw [cdf_gaussian_neg w] at h
      simpa [neg_sq] using h
    have htail0 : 0 ≤ 1 - cdf (gaussianReal 0 1) z :=
      sub_nonneg.mpr (cdf_le_one _ _)
    have hcoef0 : 0 ≤ steinProductLowConstant - 8 := by
      unfold steinProductLowConstant
      have hnonneg : 0 ≤ 2 * √(2 * π) * exp (1 / 2) := by positivity
      linarith
    have htail := one_sub_cdf_gaussian_le_exp_neg_half_linear hz
    rw [steinProductDeriv_of_le hwz]
    calc
      (1 - cdf (gaussianReal 0 1) z) *
            (√(2 * π) * (1 + w ^ 2) * exp (w ^ 2 / 2) *
              cdf (gaussianReal 0 1) w + w) ≤
          (1 - cdf (gaussianReal 0 1) z) * (steinProductLowConstant - 8) :=
        mul_le_mul_of_nonneg_left hleft htail0
      _ ≤ exp (-z / 2) * (steinProductLowConstant - 8) :=
        mul_le_mul_of_nonneg_right htail hcoef0
      _ ≤ steinProductLowConstant * exp (-z / 2) := by
        have hC : steinProductLowConstant - 8 ≤ steinProductLowConstant := by linarith
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hC (exp_nonneg _)
  · have h8 := steinProductDeriv_le_eight_exp_of_nonneg_le_half hz hw0.le hw
    have h8C : (8 : ℝ) ≤ steinProductLowConstant := by
      unfold steinProductLowConstant
      have hnonneg : 0 ≤ 2 * √(2 * π) * exp (1 / 2) := by positivity
      linarith
    exact h8.trans (mul_le_mul_of_nonneg_right h8C (exp_nonneg _))

/-- Upper partition estimate used in Chen--Shao Lemma 6.5.  The factor
`exp (2*w-z)` is designed to be integrated against an `E exp (2W)` bound. -/
lemma steinProductDeriv_le_upper_exp {z w : ℝ} (hz : 2 ≤ z) (hw : z / 2 < w) :
    steinProductDeriv z w ≤
      (√(2 * π) / 2 + 2) * (1 + z) * exp (2 * w - z) := by
  let A : ℝ := √(2 * π) / 2 + 2
  let u : ℝ := 2 * w - z
  have hw0 : 0 < w := by linarith
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have hz0 : 0 ≤ z := by linarith
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA1 : 1 ≤ A := by
    dsimp [A]
    have hs := sqrt_nonneg (2 * π)
    linarith
  have hAsqrt : √(2 * π) / 2 ≤ A := by dsimp [A]; linarith
  have hzu : 0 ≤ z + u := add_nonneg hz0 hu0
  have hpoly : 1 + z + u ≤ (1 + z) * (1 + u) := by
    have hzu0 : 0 ≤ z * u := mul_nonneg hz0 hu0
    nlinarith
  have hexp : 1 + u ≤ exp u := by simpa [add_comm] using Real.add_one_le_exp u
  have hcoarse :
      steinProductDeriv z w ≤ √(2 * π) / 2 + 2 * w := by
    calc
      steinProductDeriv z w ≤ |steinProductDeriv z w| := le_abs_self _
      _ = |steinSolution z w + w * steinSolutionDeriv z w| := by
        rw [steinProductDeriv]
      _ ≤ |steinSolution z w| + |w * steinSolutionDeriv z w| := abs_add_le _ _
      _ = |steinSolution z w| + |w| * |steinSolutionDeriv z w| := by rw [abs_mul]
      _ ≤ √(2 * π) / 2 + w * 2 := by
        rw [abs_of_pos hw0]
        gcongr
        · exact abs_steinSolution_le_sqrt_two_pi_div_two z w
        · exact abs_steinSolutionDeriv_le_two z w
      _ = √(2 * π) / 2 + 2 * w := by ring
  change steinProductDeriv z w ≤ A * (1 + z) * exp u
  calc
    steinProductDeriv z w ≤ √(2 * π) / 2 + 2 * w := hcoarse
    _ = √(2 * π) / 2 + z + u := by dsimp [u]; ring
    _ = √(2 * π) / 2 + (z + u) := by ring
    _ ≤ A + A * (z + u) := by
      have hmul : z + u ≤ A * (z + u) := by
        simpa using mul_le_mul_of_nonneg_right hA1 hzu
      exact add_le_add hAsqrt hmul
    _ = A * (1 + z + u) := by ring
    _ ≤ A * ((1 + z) * (1 + u)) := mul_le_mul_of_nonneg_left hpoly hA0
    _ = A * (1 + z) * (1 + u) := by ring
    _ ≤ A * (1 + z) * exp u := by gcongr

/-- MGF-factorized form of `steinProductDeriv_le_upper_exp`. -/
lemma steinProductDeriv_le_upper_mgf {z w : ℝ} (hz : 2 ≤ z) (hw : z / 2 < w) :
    steinProductDeriv z w ≤
      (√(2 * π) / 2 + 2) * (1 + z) * exp (-z) * exp (2 * w) := by
  have h := steinProductDeriv_le_upper_exp hz hw
  calc
    steinProductDeriv z w ≤
        (√(2 * π) / 2 + 2) * (1 + z) * exp (2 * w - z) := h
    _ = (√(2 * π) / 2 + 2) * (1 + z) * exp (-z) * exp (2 * w) := by
      rw [show 2 * w - z = -z + 2 * w by ring, exp_add]
      ring

lemma measurable_steinProductDeriv (z : ℝ) : Measurable (steinProductDeriv z) := by
  exact (continuous_steinSolution z).measurable.add
    (measurable_id.mul (measurable_steinSolutionDeriv z))

lemma intervalIntegrable_steinProductDeriv (z a b : ℝ) :
    IntervalIntegrable (steinProductDeriv z) volume a b := by
  let C : ℝ → ℝ := fun w => √(2 * π) / 2 + 2 * |w|
  have hC : IntervalIntegrable C volume a b := by
    exact (continuous_const.add (continuous_const.mul continuous_abs)).intervalIntegrable a b
  refine IntervalIntegrable.mono_fun (f := C) hC
    (measurable_steinProductDeriv z).aestronglyMeasurable.restrict ?_
  filter_upwards with w
  have hf := abs_steinSolution_le_sqrt_two_pi_div_two z w
  have hf' := abs_steinSolutionDeriv_le_two z w
  calc
    ‖steinProductDeriv z w‖ = |steinSolution z w + w * steinSolutionDeriv z w| := by
      rw [Real.norm_eq_abs, steinProductDeriv]
    _ ≤ |steinSolution z w| + |w * steinSolutionDeriv z w| := abs_add_le _ _
    _ = |steinSolution z w| + |w| * |steinSolutionDeriv z w| := by rw [abs_mul]
    _ ≤ √(2 * π) / 2 + |w| * 2 := by gcongr
    _ = ‖C w‖ := by
      have hCw : 0 ≤ C w := by
        dsimp [C]
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hCw]
      dsimp [C]
      ring

/-- FTC for `w f_z(w)`, valid even when the interval crosses the single kink `z`. -/
lemma mul_steinSolution_sub_eq_integral_steinProductDeriv (z a b : ℝ) :
    b * steinSolution z b - a * steinSolution z a =
      ∫ w in a..b, steinProductDeriv z w := by
  let F : ℝ → ℝ := fun w => w * steinSolution z w
  have hcont : Continuous F := continuous_id.mul (continuous_steinSolution z)
  wlog hab : a ≤ b generalizing a b
  · have h := this b a (le_of_not_ge hab)
    have hsym : ∫ w in a..b, steinProductDeriv z w =
        -∫ w in b..a, steinProductDeriv z w := intervalIntegral.integral_symm _ _
    dsimp [F] at hcont
    linarith
  rcases eq_or_lt_of_le hab with rfl | hablt
  · simp
  have htend (c : ℝ) :
      Tendsto F (𝓝[>] c) (𝓝 (F c)) ∧ Tendsto F (𝓝[<] c) (𝓝 (F c)) := by
    constructor <;> exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hFTC_open {c d : ℝ} (hcd : c < d) (havoid : ∀ x ∈ Ioo c d, x ≠ z) :
      F d - F c = ∫ w in c..d, steinProductDeriv z w := by
    have hderiv : ∀ x ∈ Ioo c d, HasDerivAt F (steinProductDeriv z x) x :=
      fun x hx => hasDerivAt_mul_steinSolution z x (havoid x hx)
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hcd hderiv
      (intervalIntegrable_steinProductDeriv z c d) (htend c).1 (htend d).2).symm
  change F b - F a = _
  by_cases hz : z ∈ Ioo a b
  · have h1 : F z - F a = ∫ w in a..z, steinProductDeriv z w :=
      hFTC_open hz.1 fun x hx => ne_of_lt hx.2
    have h2 : F b - F z = ∫ w in z..b, steinProductDeriv z w :=
      hFTC_open hz.2 fun x hx => ne_of_gt hx.1
    have hsum := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_steinProductDeriv z a z)
      (intervalIntegrable_steinProductDeriv z z b)
    linarith
  · exact hFTC_open hablt fun x hx hxz => hz (hxz ▸ hx)

end ProbabilityTheory
