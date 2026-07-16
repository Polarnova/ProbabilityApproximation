/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

/-!
# Indicator Stein solution (definitions, Stein equation, and bounds)

The solution `f_z` of Stein's equation for `1_{(−∞,z]}`, following Chen–Shao (2005):

* definition and integrability;
* vanishing of the weighted full-line integral of the Stein integrand;
* upper-tail representation;
* Stein equation pointwise for `w ≠ z`;
* Stein equation and the bound `|w f_z(w)| ≤ 1`.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped intervalIntegral

noncomputable section

namespace ProbabilityTheory

/-! ### Private normal density / cdf aliases -/

/-- Standard normal density (private; not a competing public API). -/
private def φ (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

private lemma φ_eq (x : ℝ) : φ x = (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) := by
  simp [φ, gaussianPDFReal, NNReal.coe_one]

private lemma φ_pos (x : ℝ) : 0 < φ x := gaussianPDFReal_pos 0 1 x one_ne_zero

private lemma φ_nonneg (x : ℝ) : 0 ≤ φ x := (φ_pos x).le

private lemma measurable_φ : Measurable φ := measurable_gaussianPDFReal 0 1

private lemma integrable_φ : Integrable φ := integrable_gaussianPDFReal 0 1

private abbrev Φ : ℝ → ℝ := cdf (gaussianReal 0 1)

private lemma Φ_nonneg (z : ℝ) : 0 ≤ Φ z := cdf_nonneg _ _

private lemma Φ_le_one (z : ℝ) : Φ z ≤ 1 := cdf_le_one _ _

/-! ### Stein integrand and solution -/

/-- Integrand of the Stein solution: `1_{w ≤ z} - Φ(z)`. -/
def steinIntegrand (z w : ℝ) : ℝ := (if w ≤ z then (1 : ℝ) else 0) - Φ z

lemma steinIntegrand_abs_le (z w : ℝ) : |steinIntegrand z w| ≤ 1 := by
  have h0 := Φ_nonneg z
  have h1 := Φ_le_one z
  simp only [steinIntegrand]
  split_ifs <;> simp [abs_le] <;> constructor <;> linarith

lemma measurable_steinIntegrand (z : ℝ) : Measurable (steinIntegrand z) := by
  refine Measurable.sub ?_ measurable_const
  exact Measurable.ite (measurableSet_le measurable_id measurable_const)
    measurable_const measurable_const

lemma integrable_exp_neg_half_sq : Integrable fun x : ℝ => exp (-x ^ 2 / 2) := by
  convert integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1 / 2) using 1
  ext x; ring_nf

lemma integrable_steinIntegrand_mul_exp (z : ℝ) :
    Integrable fun x : ℝ => steinIntegrand z x * exp (-x ^ 2 / 2) := by
  refine integrable_exp_neg_half_sq.mono' ?_ ?_
  · exact (measurable_steinIntegrand z).mul (by fun_prop) |>.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (exp_nonneg _)]
    exact mul_le_of_le_one_left (exp_nonneg _) (steinIntegrand_abs_le z x)

/--
Indicator Stein solution:
`f_z(w) = e^{w²/2} ∫_{-∞}^w (1_{x≤z} - Φ(z)) e^{-x²/2} dx`.
-/
def steinSolution (z w : ℝ) : ℝ :=
  exp (w ^ 2 / 2) * ∫ x in Iic w, steinIntegrand z x * exp (-x ^ 2 / 2)

lemma steinSolution_def (z w : ℝ) :
    steinSolution z w =
      exp (w ^ 2 / 2) * ∫ x in Iic w, steinIntegrand z x * exp (-x ^ 2 / 2) :=
  rfl

/-! ### Gaussian integral identities -/

lemma integral_exp_neg_half_sq_eq : ∫ x : ℝ, exp (-x ^ 2 / 2) = √(2 * π) := by
  have h := integral_gaussian (1 / 2 : ℝ)
  have h' : (fun x : ℝ => exp (-(1 / 2) * x ^ 2)) = fun x => exp (-x ^ 2 / 2) := by
    ext x; ring_nf
  rw [h'] at h
  rw [h]
  refine congrArg sqrt ?_
  field

private lemma integral_φ_Iic (z : ℝ) : ∫ x in Iic z, φ x = Φ z := by
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  have hμ : (gaussianReal (0 : ℝ) 1) (Iic z) =
      ENNReal.ofReal (∫ x in Iic z, gaussianPDFReal 0 1 x) :=
    gaussianReal_apply_eq_integral 0 hv (Iic z)
  have hcdf : Φ z = (gaussianReal 0 1).real (Iic z) := cdf_eq_real (gaussianReal 0 1) z
  have hnonneg : 0 ≤ ∫ x in Iic z, gaussianPDFReal 0 1 x :=
    setIntegral_nonneg measurableSet_Iic fun _ _ => gaussianPDFReal_nonneg 0 1 _
  rw [hcdf, Measure.real, hμ, ENNReal.toReal_ofReal hnonneg]
  rfl

private lemma integral_exp_neg_half_sq_Iic (z : ℝ) :
    ∫ x in Iic z, exp (-x ^ 2 / 2) = √(2 * π) * Φ z := by
  have hφ : ∫ x in Iic z, φ x = Φ z := integral_φ_Iic z
  have hrewrite :
      ∫ x in Iic z, φ x = (√(2 * π))⁻¹ * ∫ x in Iic z, exp (-x ^ 2 / 2) := by
    calc
      ∫ x in Iic z, φ x = ∫ x in Iic z, (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) := by
        refine setIntegral_congr_fun measurableSet_Iic fun x _ => φ_eq x
      _ = (√(2 * π))⁻¹ * ∫ x in Iic z, exp (-x ^ 2 / 2) := integral_const_mul _ _
  rw [hrewrite] at hφ
  have hne : (√(2 * π) : ℝ) ≠ 0 := sqrt_ne_zero'.2 (by positivity)
  apply_fun (fun t : ℝ => √(2 * π) * t) at hφ
  rwa [← mul_assoc, mul_inv_cancel₀ hne, one_mul] at hφ

/-- The weighted Stein integrand integrates to zero on `ℝ`. -/
lemma integral_steinIntegrand_mul_exp_eq_zero (z : ℝ) :
    ∫ x : ℝ, steinIntegrand z x * exp (-x ^ 2 / 2) = 0 := by
  have h_exp := integrable_exp_neg_half_sq
  have h_ind : Integrable fun x : ℝ => (if x ≤ z then (1 : ℝ) else 0) * exp (-x ^ 2 / 2) := by
    refine h_exp.mono' ?_ ?_
    · refine (Measurable.ite (measurableSet_le measurable_id measurable_const)
        measurable_const measurable_const).mul (by fun_prop) |>.aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (exp_nonneg _)]
      exact mul_le_of_le_one_left (exp_nonneg _) (by split_ifs <;> norm_num)
  have heq : ∀ x, steinIntegrand z x * exp (-x ^ 2 / 2) =
      (if x ≤ z then (1 : ℝ) else 0) * exp (-x ^ 2 / 2) - Φ z * exp (-x ^ 2 / 2) := by
    intro x
    simp only [steinIntegrand, sub_mul]
  simp_rw [heq]
  rw [integral_sub h_ind (h_exp.const_mul (Φ z))]
  have h1 :
      ∫ x : ℝ, (if x ≤ z then (1 : ℝ) else 0) * exp (-x ^ 2 / 2) =
        ∫ x in Iic z, exp (-x ^ 2 / 2) := by
    calc
      ∫ x : ℝ, (if x ≤ z then (1 : ℝ) else 0) * exp (-x ^ 2 / 2)
          = ∫ x : ℝ, (Iic z).indicator (fun x => exp (-x ^ 2 / 2)) x := by
            congr 1; ext x
            by_cases hx : x ≤ z
            · simp [hx, indicator_of_mem, mem_Iic]
            · simp [hx, indicator_of_notMem, mem_Iic]
      _ = ∫ x in Iic z, exp (-x ^ 2 / 2) := integral_indicator measurableSet_Iic
  have h2 : ∫ x : ℝ, Φ z * exp (-x ^ 2 / 2) = Φ z * √(2 * π) := by
    rw [integral_const_mul, integral_exp_neg_half_sq_eq]
  rw [h1, h2, integral_exp_neg_half_sq_Iic]
  ring

/-! ### Upper-tail representation -/

private lemma integrableOn_steinIntegrand_mul_exp_Iic (z w : ℝ) :
    IntegrableOn (fun x => steinIntegrand z x * exp (-x ^ 2 / 2)) (Iic w) :=
  (integrable_steinIntegrand_mul_exp z).integrableOn

private lemma integrableOn_steinIntegrand_mul_exp_Ioi (z w : ℝ) :
    IntegrableOn (fun x => steinIntegrand z x * exp (-x ^ 2 / 2)) (Ioi w) :=
  (integrable_steinIntegrand_mul_exp z).integrableOn

/--
Alternative upper-tail formula:
`f_z(w) = - e^{w²/2} ∫_w^∞ (1_{x≤z} - Φ(z)) e^{-x²/2} dx`.
-/
lemma steinSolution_Ioi (z w : ℝ) :
    steinSolution z w =
      -exp (w ^ 2 / 2) * ∫ x in Ioi w, steinIntegrand z x * exp (-x ^ 2 / 2) := by
  have hsum :=
    intervalIntegral.integral_Iic_add_Ioi
      (integrableOn_steinIntegrand_mul_exp_Iic z w)
      (integrableOn_steinIntegrand_mul_exp_Ioi z w)
  have h0 := integral_steinIntegrand_mul_exp_eq_zero z
  have hIic :
      ∫ x in Iic w, steinIntegrand z x * exp (-x ^ 2 / 2) =
        -∫ x in Ioi w, steinIntegrand z x * exp (-x ^ 2 / 2) := by
    linarith [hsum, h0]
  simp only [steinSolution, hIic, mul_neg, neg_mul]

/-! ### Continuity of the weighted integrand away from `z` -/

private def steinKernel (z x : ℝ) : ℝ := steinIntegrand z x * exp (-x ^ 2 / 2)

private lemma continuousAt_steinKernel (z w : ℝ) (hw : w ≠ z) :
    ContinuousAt (steinKernel z) w := by
  by_cases hlt : w < z
  · have hnhds : ∀ᶠ x in 𝓝 w, x ≤ z := eventually_le_nhds hlt
    have hEq : steinKernel z =ᶠ[𝓝 w] fun x => (1 - Φ z) * exp (-x ^ 2 / 2) := by
      filter_upwards [hnhds] with x hx
      simp [steinKernel, steinIntegrand, hx]
    exact ContinuousAt.congr (by fun_prop) hEq.symm
  · have hgt : z < w := lt_of_le_of_ne (le_of_not_gt hlt) hw.symm
    have hnhds : ∀ᶠ x in 𝓝 w, ¬x ≤ z := by
      filter_upwards [eventually_gt_nhds hgt] with x hx
      exact not_le.mpr hx
    have hEq : steinKernel z =ᶠ[𝓝 w] fun x => (0 - Φ z) * exp (-x ^ 2 / 2) := by
      filter_upwards [hnhds] with x hx
      simp [steinKernel, steinIntegrand, hx]
    exact ContinuousAt.congr (by fun_prop) hEq.symm

/-! ### Differentiability of the cumulative integral and the Stein equation -/

private lemma hasDerivAt_integral_Iic_steinKernel (z w : ℝ) (hw : w ≠ z) :
    HasDerivAt (fun u => ∫ x in Iic u, steinKernel z x) (steinKernel z w) w := by
  have hcont := continuousAt_steinKernel z w hw
  have hInt : Integrable (steinKernel z) := integrable_steinIntegrand_mul_exp z
  have hI : IntervalIntegrable (steinKernel z) volume w w := hInt.intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter (steinKernel z) (𝓝 w) volume :=
    hInt.aestronglyMeasurable.stronglyMeasurableAtFilter
  have hpoint (u : ℝ) :
      ∫ x in Iic u, steinKernel z x =
        (∫ x in Iic w, steinKernel z x) + ∫ x in w..u, steinKernel z x := by
    have hu : IntegrableOn (steinKernel z) (Iic u) := hInt.integrableOn
    have hw' : IntegrableOn (steinKernel z) (Iic w) := hInt.integrableOn
    have := intervalIntegral.integral_Iic_sub_Iic hw' hu
    linarith
  have hFTC : HasDerivAt (fun u => ∫ x in w..u, steinKernel z x) (steinKernel z w) w :=
    intervalIntegral.integral_hasDerivAt_right hI hmeas hcont
  have hconst :
      HasDerivAt (fun _ : ℝ => ∫ x in Iic w, steinKernel z x) 0 w := hasDerivAt_const _ _
  exact ((hconst.add hFTC).congr_of_eventuallyEq (Eventually.of_forall hpoint)).congr_deriv
    (by ring)

private lemma hasDerivAt_exp_half_sq (w : ℝ) :
    HasDerivAt (fun u : ℝ => exp (u ^ 2 / 2)) (w * exp (w ^ 2 / 2)) w := by
  have hsq : HasDerivAt (fun u : ℝ => u ^ 2) ((2 : ℝ) * w ^ (2 - 1)) w :=
    hasDerivAt_pow 2 w
  have hsq' : HasDerivAt (fun u : ℝ => u ^ 2) (2 * w) w := by
    convert hsq using 1
    norm_num
  have hhalf : HasDerivAt (fun u : ℝ => u ^ 2 / 2) ((2 * w) / 2) w :=
    hsq'.div_const 2
  have hhalf' : HasDerivAt (fun u : ℝ => u ^ 2 / 2) w w := by
    convert hhalf using 1
    ring
  have hexp : HasDerivAt (fun u : ℝ => exp (u ^ 2 / 2)) (exp (w ^ 2 / 2) * w) w :=
    hhalf'.exp
  convert hexp using 1
  ring

/-- Stein equation at points of continuity of the indicator: for `w ≠ z`,
`f_z'(w) - w f_z(w) = 1_{w ≤ z} - Φ(z)`. -/
lemma hasDerivAt_steinSolution (z w : ℝ) (hw : w ≠ z) :
    HasDerivAt (steinSolution z)
      (w * steinSolution z w + steinIntegrand z w) w := by
  let F : ℝ → ℝ := fun u => ∫ x in Iic u, steinKernel z x
  let a : ℝ → ℝ := fun u => exp (u ^ 2 / 2)
  have hF : HasDerivAt F (steinKernel z w) w := hasDerivAt_integral_Iic_steinKernel z w hw
  have ha : HasDerivAt a (w * exp (w ^ 2 / 2)) w := hasDerivAt_exp_half_sq w
  have hprod : HasDerivAt (fun u => a u * F u)
      ((w * exp (w ^ 2 / 2)) * F w + a w * steinKernel z w) w := ha.mul hF
  have hexp_cancel :
      exp (w ^ 2 / 2) * (steinIntegrand z w * exp (-w ^ 2 / 2)) = steinIntegrand z w := by
    calc
      exp (w ^ 2 / 2) * (steinIntegrand z w * exp (-w ^ 2 / 2))
          = steinIntegrand z w * (exp (w ^ 2 / 2) * exp (-w ^ 2 / 2)) := by ring
      _ = steinIntegrand z w * exp (w ^ 2 / 2 + (-w ^ 2 / 2)) := by rw [← exp_add]
      _ = steinIntegrand z w * exp 0 := by ring_nf
      _ = steinIntegrand z w := by simp
  have hval :
      (w * exp (w ^ 2 / 2)) * F w + a w * steinKernel z w =
        w * steinSolution z w + steinIntegrand z w := by
    simp only [steinSolution, steinKernel, F, a, hexp_cancel]
    ring
  -- `steinSolution z` is defeq to `fun u => a u * F u`
  exact hprod.congr_deriv hval

lemma stein_equation (z w : ℝ) (hw : w ≠ z) :
    deriv (steinSolution z) w - w * steinSolution z w = steinIntegrand z w := by
  have h := hasDerivAt_steinSolution z w hw
  rw [h.deriv]
  ring


/-! ### Closed forms and nonnegativity of the Stein solution -/

private lemma integral_φ_Ioi (w : ℝ) : ∫ t in Ioi w, φ t = 1 - Φ w := by
  have htot : ∫ t : ℝ, φ t = 1 := integral_gaussianPDFReal_eq_one 0 one_ne_zero
  have hIic : ∫ t in Iic w, φ t = Φ w := integral_φ_Iic w
  have hsum :=
    intervalIntegral.integral_Iic_add_Ioi
      (integrable_φ.integrableOn : IntegrableOn φ (Iic w))
      integrable_φ.integrableOn
  linarith

private lemma integral_exp_neg_half_sq_Ioi (w : ℝ) :
    ∫ t in Ioi w, exp (-t ^ 2 / 2) = √(2 * π) * (1 - Φ w) := by
  have hφIoi : ∫ t in Ioi w, φ t = 1 - Φ w := integral_φ_Ioi w
  have hrewrite :
      ∫ t in Ioi w, φ t = (√(2 * π))⁻¹ * ∫ t in Ioi w, exp (-t ^ 2 / 2) := by
    calc
      ∫ t in Ioi w, φ t = ∫ t in Ioi w, (√(2 * π))⁻¹ * exp (-t ^ 2 / 2) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => φ_eq t
      _ = (√(2 * π))⁻¹ * ∫ t in Ioi w, exp (-t ^ 2 / 2) := integral_const_mul _ _
  have hne : (√(2 * π) : ℝ) ≠ 0 := sqrt_ne_zero'.2 (by positivity)
  rw [hrewrite] at hφIoi
  apply_fun (fun t : ℝ => √(2 * π) * t) at hφIoi
  rwa [← mul_assoc, mul_inv_cancel₀ hne, one_mul] at hφIoi

/-- Closed form for `w ≥ z`: `f_z(w) = √(2π) e^{w²/2} Φ(z) (1 - Φ(w))`. -/
lemma steinSolution_of_ge (z w : ℝ) (hw : z ≤ w) :
    steinSolution z w = √(2 * π) * exp (w ^ 2 / 2) * Φ z * (1 - Φ w) := by
  have hcongr :
      (fun x => steinIntegrand z x * exp (-x ^ 2 / 2)) =ᵐ[volume.restrict (Ioi w)]
        fun x => (-Φ z) * exp (-x ^ 2 / 2) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    filter_upwards with x hx
    have : ¬ x ≤ z := not_le.mpr (lt_of_le_of_lt hw hx)
    simp [steinIntegrand, this]
  have hint :
      ∫ x in Ioi w, steinIntegrand z x * exp (-x ^ 2 / 2) =
        (-Φ z) * ∫ x in Ioi w, exp (-x ^ 2 / 2) := by
    rw [integral_congr_ae hcongr, integral_const_mul]
  rw [steinSolution_Ioi, hint, integral_exp_neg_half_sq_Ioi w]
  ring

/-- Closed form for `w ≤ z`: `f_z(w) = √(2π) e^{w²/2} (1 - Φ(z)) Φ(w)`. -/
lemma steinSolution_of_le (z w : ℝ) (hw : w ≤ z) :
    steinSolution z w = √(2 * π) * exp (w ^ 2 / 2) * (1 - Φ z) * Φ w := by
  have hcongr :
      (fun x => steinIntegrand z x * exp (-x ^ 2 / 2)) =ᵐ[volume.restrict (Iic w)]
        fun x => (1 - Φ z) * exp (-x ^ 2 / 2) := by
    refine (ae_restrict_iff' measurableSet_Iic).mpr ?_
    filter_upwards with x hx
    have : x ≤ z := le_trans hx hw
    simp [steinIntegrand, this]
  have hint :
      ∫ x in Iic w, steinIntegrand z x * exp (-x ^ 2 / 2) =
        (1 - Φ z) * ∫ x in Iic w, exp (-x ^ 2 / 2) := by
    rw [integral_congr_ae hcongr, integral_const_mul]
  rw [steinSolution, hint, integral_exp_neg_half_sq_Iic w]
  ring

/-- The indicator Stein solution is nonnegative. -/
lemma steinSolution_nonneg (z w : ℝ) : 0 ≤ steinSolution z w := by
  rcases le_or_gt w z with hw | hw
  · rw [steinSolution_of_le z w hw]
    exact mul_nonneg (mul_nonneg (mul_nonneg (sqrt_nonneg _) (exp_nonneg _))
      (sub_nonneg.mpr (Φ_le_one z))) (Φ_nonneg w)
  · rw [steinSolution_of_ge z w hw.le]
    exact mul_nonneg (mul_nonneg (mul_nonneg (sqrt_nonneg _) (exp_nonneg _))
      (Φ_nonneg z)) (sub_nonneg.mpr (Φ_le_one w))

/-- Pointwise extension of the Stein derivative (classical for `w ≠ z`). -/
def steinSolutionDeriv (z w : ℝ) : ℝ :=
  w * steinSolution z w + steinIntegrand z w

lemma hasDerivAt_steinSolutionDeriv (z w : ℝ) (hw : w ≠ z) :
    HasDerivAt (steinSolution z) (steinSolutionDeriv z w) w := by
  convert hasDerivAt_steinSolution z w hw using 1
  rfl

/-! ### Mills ratios and related Stein bounds -/

private lemma hasDerivAt_neg_exp_neg_half_sq (t : ℝ) :
    HasDerivAt (fun u : ℝ => -exp (-u ^ 2 / 2)) (t * exp (-t ^ 2 / 2)) t := by
  have hsq : HasDerivAt (fun u : ℝ => u ^ 2) ((2 : ℝ) * t ^ (2 - 1)) t :=
    hasDerivAt_pow 2 t
  have hsq' : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
    convert hsq using 1; norm_num
  have hhalf : HasDerivAt (fun u : ℝ => u ^ 2 / 2) ((2 * t) / 2) t :=
    hsq'.div_const 2
  have hhalf' : HasDerivAt (fun u : ℝ => u ^ 2 / 2) t t := by
    convert hhalf using 1; ring
  have hneg : HasDerivAt (fun u : ℝ => -u ^ 2 / 2) (-t) t := by
    refine hhalf'.neg.congr_of_eventuallyEq ?_
    filter_upwards with u
    simp; ring
  have hexp : HasDerivAt (fun u : ℝ => exp (-u ^ 2 / 2))
      (exp (-t ^ 2 / 2) * (-t)) t := hneg.exp
  refine hexp.neg.congr_deriv ?_
  ring

private lemma tendsto_exp_neg_half_sq_atTop :
    Tendsto (fun b : ℝ => exp (-b ^ 2 / 2)) atTop (𝓝 0) := by
  have hsq : Tendsto (fun b : ℝ => b ^ 2) atTop atTop := by
    simpa [pow_two] using (tendsto_mul_self_atTop (α := ℝ))
  have hhalf : Tendsto (fun b : ℝ => b ^ 2 / 2) atTop atTop :=
    hsq.atTop_div_const (by positivity : (0 : ℝ) < 2)
  have hbot : Tendsto (fun b : ℝ => -b ^ 2 / 2) atTop atBot := by
    refine (tendsto_neg_atTop_atBot.comp hhalf).congr ?_
    intro b; simp; ring
  exact tendsto_exp_atBot.comp hbot

/-- For `x ≥ 0`, `∫_{x}^∞ t e^{-t²/2} dt = e^{-x²/2}`. -/
lemma integral_t_mul_exp_neg_half_sq_Ioi {x : ℝ} (hx : 0 ≤ x) :
    ∫ t in Ioi x, t * exp (-t ^ 2 / 2) = exp (-x ^ 2 / 2) := by
  have hderiv : ∀ t ∈ Ici x,
      HasDerivAt (fun u : ℝ => -exp (-u ^ 2 / 2)) (t * exp (-t ^ 2 / 2)) t :=
    fun t _ => hasDerivAt_neg_exp_neg_half_sq t
  have hpos : ∀ t ∈ Ioi x, 0 ≤ t * exp (-t ^ 2 / 2) := fun t ht =>
    mul_nonneg (le_trans hx (le_of_lt ht)) (exp_nonneg _)
  have htend : Tendsto (fun b : ℝ => -exp (-b ^ 2 / 2)) atTop (𝓝 0) := by
    simpa using tendsto_exp_neg_half_sq_atTop.neg
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos htend
  linarith

/-- Upper Mills bound: for `x > 0`, `∫_{x}^∞ e^{-t²/2} dt ≤ e^{-x²/2}/x`. -/
lemma integral_exp_neg_half_sq_Ioi_le {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi x, exp (-t ^ 2 / 2) ≤ exp (-x ^ 2 / 2) / x := by
  have hx0 : 0 ≤ x := hx.le
  have hInt_exp : IntegrableOn (fun t : ℝ => exp (-t ^ 2 / 2)) (Ioi x) :=
    integrable_exp_neg_half_sq.integrableOn
  have hderiv : ∀ t ∈ Ici x,
      HasDerivAt (fun u : ℝ => -exp (-u ^ 2 / 2)) (t * exp (-t ^ 2 / 2)) t :=
    fun t _ => hasDerivAt_neg_exp_neg_half_sq t
  have hpos : ∀ t ∈ Ioi x, 0 ≤ t * exp (-t ^ 2 / 2) := fun t ht =>
    mul_nonneg (le_trans hx0 (le_of_lt ht)) (exp_nonneg _)
  have htend : Tendsto (fun b : ℝ => -exp (-b ^ 2 / 2)) atTop (𝓝 0) := by
    simpa using tendsto_exp_neg_half_sq_atTop.neg
  have hInt_t : IntegrableOn (fun t : ℝ => t * exp (-t ^ 2 / 2)) (Ioi x) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv hpos htend
  have hle_on : ∀ t ∈ Ioi x,
      exp (-t ^ 2 / 2) ≤ (1 / x) * (t * exp (-t ^ 2 / 2)) := by
    intro t ht
    have : exp (-t ^ 2 / 2) ≤ (t / x) * exp (-t ^ 2 / 2) :=
      le_mul_of_one_le_left (exp_nonneg _) ((one_le_div hx).mpr ht.le)
    convert this using 1
    field_simp
  have hmono :=
    setIntegral_mono_on hInt_exp (hInt_t.const_mul (1 / x)) measurableSet_Ioi hle_on
  have hrhs : ∫ t in Ioi x, (1 / x) * (t * exp (-t ^ 2 / 2)) =
      (1 / x) * exp (-x ^ 2 / 2) := by
    rw [integral_const_mul, integral_t_mul_exp_neg_half_sq_Ioi hx0]
  have : ∫ t in Ioi x, exp (-t ^ 2 / 2) ≤ (1 / x) * exp (-x ^ 2 / 2) := by
    rwa [hrhs] at hmono
  convert this using 1
  field_simp

/-- Upper Mills inequality: for `x > 0`, `1 - Φ(x) ≤ φ(x) / x`. -/
lemma one_sub_Φ_le_φ_div {x : ℝ} (hx : 0 < x) : 1 - Φ x ≤ φ x / x := by
  have hIoi := integral_φ_Ioi x
  have hrewrite :
      ∫ t in Ioi x, φ t = (√(2 * π))⁻¹ * ∫ t in Ioi x, exp (-t ^ 2 / 2) := by
    calc
      ∫ t in Ioi x, φ t = ∫ t in Ioi x, (√(2 * π))⁻¹ * exp (-t ^ 2 / 2) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => φ_eq t
      _ = (√(2 * π))⁻¹ * ∫ t in Ioi x, exp (-t ^ 2 / 2) := integral_const_mul _ _
  have hMills := integral_exp_neg_half_sq_Ioi_le hx
  have hφ : φ x / x = (√(2 * π))⁻¹ * (exp (-x ^ 2 / 2) / x) := by
    rw [φ_eq]; ring
  have hinv0 : 0 ≤ (√(2 * π))⁻¹ := inv_nonneg.mpr (sqrt_nonneg _)
  calc
    1 - Φ x = ∫ t in Ioi x, φ t := hIoi.symm
    _ = (√(2 * π))⁻¹ * ∫ t in Ioi x, exp (-t ^ 2 / 2) := hrewrite
    _ ≤ (√(2 * π))⁻¹ * (exp (-x ^ 2 / 2) / x) := by gcongr
    _ = φ x / x := hφ.symm

/-- For `w ≥ z` and `w > 0`, `|w f_z(w)| ≤ 1`. -/
lemma abs_mul_steinSolution_le_one_of_pos_ge {z w : ℝ} (hwz : z ≤ w) (hw : 0 < w) :
    |w * steinSolution z w| ≤ 1 := by
  have hnn : 0 ≤ w * steinSolution z w :=
    mul_nonneg hw.le (steinSolution_nonneg z w)
  rw [abs_of_nonneg hnn, steinSolution_of_ge z w hwz]
  have hMills := one_sub_Φ_le_φ_div hw
  have hφ : φ w = (√(2 * π))⁻¹ * exp (-w ^ 2 / 2) := φ_eq w
  have h1 : √(2 * π) * exp (w ^ 2 / 2) * (1 - Φ w) ≤ 1 / w := by
    have : 1 - Φ w ≤ ((√(2 * π))⁻¹ * exp (-w ^ 2 / 2)) / w := by
      rwa [hφ] at hMills
    have hle :
        √(2 * π) * exp (w ^ 2 / 2) * (1 - Φ w) ≤
          √(2 * π) * exp (w ^ 2 / 2) *
            (((√(2 * π))⁻¹ * exp (-w ^ 2 / 2)) / w) :=
      mul_le_mul_of_nonneg_left this
        (mul_nonneg (sqrt_nonneg _) (exp_nonneg _))
    refine hle.trans_eq ?_
    have hne : (√(2 * π) : ℝ) ≠ 0 := sqrt_ne_zero'.2 (by positivity)
    have he : exp (w ^ 2 / 2) * exp (-w ^ 2 / 2) = (1 : ℝ) := by
      rw [← exp_add, show (w ^ 2 / 2) + (-w ^ 2 / 2) = 0 by ring, exp_zero]
    calc
      √(2 * π) * exp (w ^ 2 / 2) * (((√(2 * π))⁻¹ * exp (-w ^ 2 / 2)) / w)
          = (√(2 * π) * (√(2 * π))⁻¹) * (exp (w ^ 2 / 2) * exp (-w ^ 2 / 2)) / w := by
            ring
      _ = 1 * 1 / w := by rw [mul_inv_cancel₀ hne, he]
      _ = 1 / w := by ring
  have hterm0 : 0 ≤ √(2 * π) * exp (w ^ 2 / 2) * (1 - Φ w) :=
    mul_nonneg (mul_nonneg (sqrt_nonneg _) (exp_nonneg _)) (sub_nonneg.mpr (Φ_le_one w))
  have hmid :
      Φ z * (w * (√(2 * π) * exp (w ^ 2 / 2) * (1 - Φ w))) ≤
        Φ z * (w * (1 / w)) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left h1 hw.le) (Φ_nonneg z)
  calc
    w * (√(2 * π) * exp (w ^ 2 / 2) * Φ z * (1 - Φ w))
        = Φ z * (w * (√(2 * π) * exp (w ^ 2 / 2) * (1 - Φ w))) := by ring
    _ ≤ Φ z * (w * (1 / w)) := hmid
    _ = Φ z := by field_simp [hw.ne']
    _ ≤ 1 := Φ_le_one z

/-! ### Symmetry of Φ, mills factor, and full `|w f_z(w)| ≤ 1` -/

private lemma φ_even (t : ℝ) : φ (-t) = φ t := by
  simp only [φ_eq]; ring_nf

private lemma integral_φ_singleton (a : ℝ) : ∫ t in ({a} : Set ℝ), φ t = 0 := by
  rw [integral_singleton]
  simp [Measure.real, φ]

private lemma Ioi_union_singleton_eq_Ici (a : ℝ) : Ioi a ∪ {a} = Ici a := by
  ext t
  simp only [mem_union, mem_Ioi, mem_singleton_iff, mem_Ici]
  exact ⟨fun h => h.elim le_of_lt (fun h => h ▸ le_rfl),
    fun h => (lt_or_eq_of_le h).elim Or.inl (fun he => Or.inr (he.symm))⟩

private lemma Iio_union_singleton_eq_Iic (a : ℝ) : Iio a ∪ {a} = Iic a := by
  ext t
  simp only [mem_union, mem_Iio, mem_singleton_iff, mem_Iic]
  exact ⟨fun h => h.elim le_of_lt (fun h => h ▸ le_rfl),
    fun h => (lt_or_eq_of_le h).elim Or.inl Or.inr⟩

/-- `Φ 0 = 1/2`. -/
lemma Φ_zero : Φ 0 = 1 / 2 := by
  have hmap : ∫ t in Iic (0 : ℝ), φ t = ∫ t in Ici (0 : ℝ), φ t := by
    have hpres := Measure.measurePreserving_neg (volume : Measure ℝ)
    have hset : (fun t : ℝ => -t) ⁻¹' Ici (0 : ℝ) = Iic 0 := by
      ext t; simp
    have hflip : ∫ t in Iic (0 : ℝ), φ (-t) = ∫ t in Ici (0 : ℝ), φ t := by
      simpa [hset] using
        (MeasurePreserving.setIntegral_preimage_emb hpres measurableEmbedding_neg
          φ (Ici (0 : ℝ)))
    have heven : ∫ t in Iic (0 : ℝ), φ (-t) = ∫ t in Iic (0 : ℝ), φ t :=
      setIntegral_congr_fun measurableSet_Iic fun t _ => φ_even t
    linarith [hflip, heven]
  have hIci : ∫ t in Ici (0 : ℝ), φ t = ∫ t in Ioi (0 : ℝ), φ t := by
    have hU := Ioi_union_singleton_eq_Ici (0 : ℝ)
    have hdisj : Disjoint (Ioi (0 : ℝ)) ({0} : Set ℝ) :=
      Set.disjoint_singleton_right.2 (by simp)
    have hsum :=
      setIntegral_union hdisj (by simp : MeasurableSet ({0} : Set ℝ))
        (integrable_φ.integrableOn : IntegrableOn φ (Ioi 0))
        (integrable_φ.integrableOn : IntegrableOn φ ({0}))
    have h0 := integral_φ_singleton 0
    rw [hU] at hsum
    linarith [hsum, h0]
  have hIicΦ : ∫ t in Iic (0 : ℝ), φ t = Φ 0 := integral_φ_Iic 0
  have hIoi : ∫ t in Ioi (0 : ℝ), φ t = 1 - Φ 0 := integral_φ_Ioi 0
  linarith [hmap, hIci, hIicΦ, hIoi]

/-- Symmetry of the standard normal CDF: `Φ(-x) = 1 - Φ(x)`. -/
lemma Φ_neg (x : ℝ) : Φ (-x) = 1 - Φ x := by
  have hflip : ∫ t in Iic (-x), φ t = ∫ t in Ici x, φ t := by
    have hpres := Measure.measurePreserving_neg (volume : Measure ℝ)
    have hset : (fun t : ℝ => -t) ⁻¹' Ici x = Iic (-x) := by
      ext t
      simp only [mem_preimage, mem_Ici, mem_Iic, le_neg]
    have h1 : ∫ t in Iic (-x), φ (-t) = ∫ t in Ici x, φ t := by
      simpa [hset] using
        (MeasurePreserving.setIntegral_preimage_emb hpres measurableEmbedding_neg φ (Ici x))
    have h2 : ∫ t in Iic (-x), φ (-t) = ∫ t in Iic (-x), φ t :=
      setIntegral_congr_fun measurableSet_Iic fun t _ => φ_even t
    linarith [h1, h2]
  have hIci : ∫ t in Ici x, φ t = 1 - ∫ t in Iio x, φ t := by
    have htot : ∫ t : ℝ, φ t = 1 := integral_gaussianPDFReal_eq_one 0 one_ne_zero
    have hdisj : Disjoint (Iio x) (Ici x) :=
      disjoint_left.2 fun t (ht1 : t ∈ Iio x) (ht2 : t ∈ Ici x) =>
        (not_le_of_gt (mem_Iio.mp ht1)) (mem_Ici.mp ht2)
    have hU : Iio x ∪ Ici x = univ := Iio_union_Ici
    have hsum :=
      setIntegral_union hdisj measurableSet_Ici
        integrable_φ.integrableOn integrable_φ.integrableOn
    rw [hU, setIntegral_univ] at hsum
    linarith [htot, hsum]
  have hIio : ∫ t in Iio x, φ t = ∫ t in Iic x, φ t := by
    have hU := Iio_union_singleton_eq_Iic x
    have hdisj : Disjoint (Iio x) ({x} : Set ℝ) :=
      Set.disjoint_singleton_right.2 (by simp)
    have hsum :=
      setIntegral_union hdisj (by simp : MeasurableSet ({x} : Set ℝ))
        integrable_φ.integrableOn integrable_φ.integrableOn
    have h0 := integral_φ_singleton x
    rw [hU] at hsum
    linarith [hsum, h0]
  have hΦneg : Φ (-x) = ∫ t in Iic (-x), φ t := (integral_φ_Iic (-x)).symm
  have hΦ : Φ x = ∫ t in Iic x, φ t := (integral_φ_Iic x).symm
  linarith [hΦneg, hΦ, hflip, hIci, hIio]

/-- Mills factor: for `w > 0`, `w * √(2π) * e^{w²/2} * (1 - Φ(w)) ≤ 1`. -/
lemma mills_factor_le_one {w : ℝ} (hw : 0 < w) :
    w * √(2 * π) * exp (w ^ 2 / 2) * (1 - Φ w) ≤ 1 := by
  have hMills := one_sub_Φ_le_φ_div hw
  have hφ : φ w = (√(2 * π))⁻¹ * exp (-w ^ 2 / 2) := φ_eq w
  have hle0 : 1 - Φ w ≤ ((√(2 * π))⁻¹ * exp (-w ^ 2 / 2)) / w := by
    rwa [hφ] at hMills
  have hne : (√(2 * π) : ℝ) ≠ 0 := sqrt_ne_zero'.2 (by positivity)
  have he : exp (w ^ 2 / 2) * exp (-w ^ 2 / 2) = (1 : ℝ) := by
    rw [← exp_add, show (w ^ 2 / 2) + (-w ^ 2 / 2) = 0 by ring, exp_zero]
  have hnn : 0 ≤ w * √(2 * π) * exp (w ^ 2 / 2) :=
    mul_nonneg (mul_nonneg hw.le (sqrt_nonneg _)) (exp_nonneg _)
  have hle := mul_le_mul_of_nonneg_left hle0 hnn
  refine hle.trans_eq ?_
  calc
    w * √(2 * π) * exp (w ^ 2 / 2) * (((√(2 * π))⁻¹ * exp (-w ^ 2 / 2)) / w)
        = (√(2 * π) * (√(2 * π))⁻¹) * (exp (w ^ 2 / 2) * exp (-w ^ 2 / 2)) *
            (w / w) := by ring
    _ = 1 * 1 * 1 := by rw [mul_inv_cancel₀ hne, he, div_self hw.ne']
    _ = 1 := by ring

private lemma abs_mul_stein_le_one_of_le_zero_le
    (z w : ℝ) (_hwz : w ≤ z) (hw0 : w ≤ 0) :
    |w * (√(2 * π) * exp (w ^ 2 / 2) * (1 - Φ z) * Φ w)| ≤ 1 := by
  have hΦw : Φ w = 1 - Φ (-w) := by
    simpa using Φ_neg (-w)
  have hnonpos :
      w * (√(2 * π) * exp (w ^ 2 / 2) * (1 - Φ z) * Φ w) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hw0
      (mul_nonneg (mul_nonneg (mul_nonneg (sqrt_nonneg _) (exp_nonneg _))
        (sub_nonneg.mpr (Φ_le_one z))) (Φ_nonneg w))
  rw [abs_of_nonpos hnonpos]
  -- |wf| = (-w) * positive form
  have habs :
      -(w * (√(2 * π) * exp (w ^ 2 / 2) * (1 - Φ z) * Φ w)) =
        (-w) * √(2 * π) * exp (w ^ 2 / 2) * (1 - Φ z) * (1 - Φ (-w)) := by
    rw [hΦw]; ring
  rw [habs]
  have hy0 : 0 ≤ -w := neg_nonneg.mpr hw0
  rcases eq_or_lt_of_le hy0 with hy00 | hypos
  · simp [← hy00]
  · have hm := mills_factor_le_one hypos
    have hexp : exp (w ^ 2 / 2) = exp ((-w) ^ 2 / 2) := by rw [neg_sq]
    calc
      (-w) * √(2 * π) * exp (w ^ 2 / 2) * (1 - Φ z) * (1 - Φ (-w))
          = (1 - Φ z) * ((-w) * √(2 * π) * exp ((-w) ^ 2 / 2) * (1 - Φ (-w))) := by
            rw [hexp]; ring
      _ ≤ 1 * 1 := by
            exact mul_le_mul (sub_le_self _ (Φ_nonneg z)) hm
              (mul_nonneg (mul_nonneg (mul_nonneg hy0 (sqrt_nonneg _)) (exp_nonneg _))
                (sub_nonneg.mpr (Φ_le_one (-w)))) zero_le_one
      _ = 1 := by ring

private lemma abs_mul_stein_le_one_of_pos_le
    (z w : ℝ) (hwz : w ≤ z) (hw0 : 0 < w) :
    |w * (√(2 * π) * exp (w ^ 2 / 2) * (1 - Φ z) * Φ w)| ≤ 1 := by
  have hnonneg :
      0 ≤ w * (√(2 * π) * exp (w ^ 2 / 2) * (1 - Φ z) * Φ w) :=
    mul_nonneg hw0.le
      (mul_nonneg (mul_nonneg (mul_nonneg (sqrt_nonneg _) (exp_nonneg _))
        (sub_nonneg.mpr (Φ_le_one z))) (Φ_nonneg w))
  rw [abs_of_nonneg hnonneg]
  have h1z : 1 - Φ z ≤ 1 - Φ w :=
    sub_le_sub_left (monotone_cdf (gaussianReal 0 1) hwz) 1
  have hm := mills_factor_le_one hw0
  calc
    w * (√(2 * π) * exp (w ^ 2 / 2) * (1 - Φ z) * Φ w)
        = Φ w * (w * √(2 * π) * exp (w ^ 2 / 2) * (1 - Φ z)) := by ring
    _ ≤ Φ w * (w * √(2 * π) * exp (w ^ 2 / 2) * (1 - Φ w)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Φ_nonneg w)
          exact mul_le_mul_of_nonneg_left h1z
            (mul_nonneg (mul_nonneg hw0.le (sqrt_nonneg _)) (exp_nonneg _))
    _ ≤ 1 * 1 := by
          exact mul_le_mul (Φ_le_one w) hm
            (mul_nonneg (mul_nonneg (mul_nonneg hw0.le (sqrt_nonneg _)) (exp_nonneg _))
              (sub_nonneg.mpr (Φ_le_one w))) zero_le_one
    _ = 1 := by ring

private lemma abs_mul_stein_le_one_of_le_zero_ge
    (z w : ℝ) (hwz : z ≤ w) (hw0 : w ≤ 0) :
    |w * (√(2 * π) * exp (w ^ 2 / 2) * Φ z * (1 - Φ w))| ≤ 1 := by
  have h1Φw : 1 - Φ w = Φ (-w) := (Φ_neg w).symm
  have hnonpos :
      w * (√(2 * π) * exp (w ^ 2 / 2) * Φ z * (1 - Φ w)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hw0
      (mul_nonneg (mul_nonneg (mul_nonneg (sqrt_nonneg _) (exp_nonneg _)) (Φ_nonneg z))
        (sub_nonneg.mpr (Φ_le_one w)))
  rw [abs_of_nonpos hnonpos]
  have habs :
      -(w * (√(2 * π) * exp (w ^ 2 / 2) * Φ z * (1 - Φ w))) =
        (-w) * √(2 * π) * exp (w ^ 2 / 2) * Φ z * Φ (-w) := by
    rw [h1Φw]; ring
  rw [habs]
  have hy0 : 0 ≤ -w := neg_nonneg.mpr hw0
  -- Key: Φ z ≤ Φ w = 1 - Φ (-w)
  have hΦz_le : Φ z ≤ 1 - Φ (-w) := by
    have hle : Φ z ≤ Φ w := monotone_cdf (gaussianReal 0 1) hwz
    have hΦw : Φ w = 1 - Φ (-w) := by simpa using Φ_neg (-w)
    rwa [hΦw] at hle
  rcases eq_or_lt_of_le hy0 with hy00 | hypos
  · simp [← hy00]
  · have hm := mills_factor_le_one hypos
    have hexp : exp (w ^ 2 / 2) = exp ((-w) ^ 2 / 2) := by rw [neg_sq]
    calc
      (-w) * √(2 * π) * exp (w ^ 2 / 2) * Φ z * Φ (-w)
          ≤ (-w) * √(2 * π) * exp (w ^ 2 / 2) * (1 - Φ (-w)) * Φ (-w) := by
            refine mul_le_mul_of_nonneg_right ?_ (Φ_nonneg (-w))
            exact mul_le_mul_of_nonneg_left hΦz_le
              (mul_nonneg (mul_nonneg hy0 (sqrt_nonneg _)) (exp_nonneg _))
      _ = Φ (-w) * ((-w) * √(2 * π) * exp ((-w) ^ 2 / 2) * (1 - Φ (-w))) := by
            rw [hexp]; ring
      _ ≤ 1 * 1 := by
            exact mul_le_mul (Φ_le_one (-w)) hm
              (mul_nonneg (mul_nonneg (mul_nonneg hy0 (sqrt_nonneg _)) (exp_nonneg _))
                (sub_nonneg.mpr (Φ_le_one (-w)))) zero_le_one
      _ = 1 := by ring

/-- Full bound `|w · f_z(w)| ≤ 1` for all real `w, z`. -/
lemma abs_mul_steinSolution_le_one (z w : ℝ) :
    |w * steinSolution z w| ≤ 1 := by
  rcases le_or_gt w z with hwz | hzw
  · rw [steinSolution_of_le z w hwz]
    rcases le_or_gt w 0 with hw0 | hw0
    · exact abs_mul_stein_le_one_of_le_zero_le z w hwz hw0
    · exact abs_mul_stein_le_one_of_pos_le z w hwz hw0
  · have hwz : z ≤ w := hzw.le
    rw [steinSolution_of_ge z w hwz]
    rcases le_or_gt w 0 with hw0 | hw0
    · exact abs_mul_stein_le_one_of_le_zero_ge z w hwz hw0
    · have h := abs_mul_steinSolution_le_one_of_pos_ge (z := z) (w := w) hwz hw0
      rwa [steinSolution_of_ge z w hwz] at h

/-- Bound `|steinSolutionDeriv z w| ≤ 2` (coarse; sharpens to 1 with lower mills). -/
lemma abs_steinSolutionDeriv_le_two (z w : ℝ) :
    |steinSolutionDeriv z w| ≤ 2 := by
  -- |wf + (1_{w≤z}-Φ)| ≤ |wf| + 1 ≤ 2
  unfold steinSolutionDeriv
  have h1 := abs_mul_steinSolution_le_one z w
  have h2 := steinIntegrand_abs_le z w
  calc
    |w * steinSolution z w + steinIntegrand z w|
        ≤ |w * steinSolution z w| + |steinIntegrand z w| := abs_add_le _ _
    _ ≤ 1 + 1 := add_le_add h1 h2
    _ = 2 := by norm_num

private lemma continuous_φ : Continuous φ := by
  unfold φ
  simp only [gaussianPDFReal, NNReal.coe_one]
  fun_prop

/-- The Gaussian CDF is differentiable with derivative `φ`. -/
lemma hasDerivAt_Φ (t : ℝ) : HasDerivAt Φ (φ t) t := by
  have hcont : ContinuousAt φ t := continuous_φ.continuousAt
  have hpoint (u : ℝ) :
      ∫ x in Iic u, φ x = (∫ x in Iic t, φ x) + ∫ x in t..u, φ x := by
    have hu : IntegrableOn φ (Iic u) := integrable_φ.integrableOn
    have ht : IntegrableOn φ (Iic t) := integrable_φ.integrableOn
    have := intervalIntegral.integral_Iic_sub_Iic ht hu
    linarith
  have hFTC : HasDerivAt (fun u => ∫ x in t..u, φ x) (φ t) t :=
    intervalIntegral.integral_hasDerivAt_right
      integrable_φ.intervalIntegrable
      integrable_φ.aestronglyMeasurable.stronglyMeasurableAtFilter hcont
  have hconst : HasDerivAt (fun _ : ℝ => ∫ x in Iic t, φ x) 0 t := hasDerivAt_const _ _
  have hsum : HasDerivAt (fun u => ∫ x in Iic u, φ x) (φ t) t :=
    ((hconst.add hFTC).congr_of_eventuallyEq (Eventually.of_forall hpoint)).congr_deriv
      (by ring)
  exact hsum.congr_of_eventuallyEq (Eventually.of_forall fun u => (integral_φ_Iic u).symm)

lemma continuous_Φ : Continuous Φ :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_Φ t).continuousAt

/-- Tail factor `e^{w²/2}(1-Φ(w)) ≤ 1/2` for `w ≥ 0`. -/
lemma exp_mul_one_sub_Φ_le_half {w : ℝ} (hw : 0 ≤ w) :
    exp (w ^ 2 / 2) * (1 - Φ w) ≤ 1 / 2 := by
  have hm0 : exp ((0 : ℝ) ^ 2 / 2) * (1 - Φ 0) = 1 / 2 := by
    rw [Φ_zero]; norm_num
  rcases eq_or_lt_of_le hw with rfl | _hwpos
  · exact hm0.le
  · have hderiv (t : ℝ) :
        HasDerivAt (fun u => exp (u ^ 2 / 2) * (1 - Φ u))
          (exp (t ^ 2 / 2) * (t * (1 - Φ t) - φ t)) t := by
      have hexp := hasDerivAt_exp_half_sq t
      have h1m : HasDerivAt (fun u : ℝ => 1 - Φ u) (-φ t) t := by
        have hneg : HasDerivAt (fun u => -Φ u) (-φ t) t := (hasDerivAt_Φ t).neg
        have hadd : HasDerivAt (fun u => -Φ u + 1) (-φ t + 0) t :=
          hneg.add (hasDerivAt_const t (1 : ℝ))
        convert hadd using 1
        · funext u; ring
        · ring
      have hmul := hexp.mul h1m
      exact hmul.congr_deriv (by ring)
    have hm'le (t : ℝ) (ht : 0 < t) :
        exp (t ^ 2 / 2) * (t * (1 - Φ t) - φ t) ≤ 0 := by
      have hMills := one_sub_Φ_le_φ_div ht
      have hle : t * (1 - Φ t) ≤ φ t := by
        have := mul_le_mul_of_nonneg_left hMills ht.le
        rwa [mul_div_cancel₀ _ ht.ne'] at this
      exact mul_nonpos_of_nonneg_of_nonpos (exp_nonneg _) (by linarith)
    have hcont : Continuous (fun u => exp (u ^ 2 / 2) * (1 - Φ u)) := by
      have := continuous_Φ; fun_prop
    have hcont' : Continuous
        (fun t => exp (t ^ 2 / 2) * (t * (1 - Φ t) - φ t)) := by
      have := continuous_Φ
      have := continuous_φ
      fun_prop
    have hint := hcont'.intervalIntegrable (μ := volume) 0 w
    have hFTC :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hw
        hcont.continuousOn (fun t _ => hderiv t) hint
    have hle_int :
        ∫ t in (0 : ℝ)..w, exp (t ^ 2 / 2) * (t * (1 - Φ t) - φ t) ≤ 0 := by
      rw [intervalIntegral.integral_of_le hw]
      exact integral_nonpos fun t => by
        by_cases ht : 0 < t
        · exact hm'le t ht
        · have ht0 : t ≤ 0 := le_of_not_gt ht
          have h1 : t * (1 - Φ t) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg ht0 (sub_nonneg.mpr (Φ_le_one t))
          exact mul_nonpos_of_nonneg_of_nonpos (exp_nonneg _) (by linarith [φ_nonneg t])
    have : exp (w ^ 2 / 2) * (1 - Φ w) - exp ((0 : ℝ) ^ 2 / 2) * (1 - Φ 0) ≤ 0 := by
      rwa [← hFTC]
    linarith [hm0]

/-- Bound `|f_z(w)| ≤ √(2π)/2`. -/
lemma abs_steinSolution_le_sqrt_two_pi_div_two (z w : ℝ) :
    |steinSolution z w| ≤ sqrt (2 * π) / 2 := by
  have hnn := steinSolution_nonneg z w
  have hsqrt : 0 ≤ sqrt (2 * π) := sqrt_nonneg _
  have hle : steinSolution z w ≤ sqrt (2 * π) / 2 := by
    rcases le_or_gt w z with hwz | hzw
    · rw [steinSolution_of_le z w hwz]
      rcases le_or_gt w 0 with hw0 | hw0
      · have hΦw : Φ w = 1 - Φ (-w) := by simpa using Φ_neg (-w)
        have hy0 : 0 ≤ -w := neg_nonneg.mpr hw0
        have hm := exp_mul_one_sub_Φ_le_half hy0
        have hexp : exp (w ^ 2 / 2) = exp ((-w) ^ 2 / 2) := by rw [neg_sq]
        have h1z : 1 - Φ z ≤ 1 := sub_le_self _ (Φ_nonneg z)
        calc
          sqrt (2 * π) * exp (w ^ 2 / 2) * (1 - Φ z) * Φ w
              = (1 - Φ z) * (sqrt (2 * π) * exp (w ^ 2 / 2) * Φ w) := by ring
          _ ≤ 1 * (sqrt (2 * π) * (exp ((-w) ^ 2 / 2) * (1 - Φ (-w)))) := by
                rw [hΦw, hexp, mul_assoc]
                refine mul_le_mul h1z le_rfl ?_ zero_le_one
                exact mul_nonneg hsqrt (mul_nonneg (exp_nonneg _)
                  (sub_nonneg.mpr (Φ_le_one (-w))))
          _ = sqrt (2 * π) * (exp ((-w) ^ 2 / 2) * (1 - Φ (-w))) := by ring
          _ ≤ sqrt (2 * π) * (1 / 2) := mul_le_mul_of_nonneg_left hm hsqrt
          _ = sqrt (2 * π) / 2 := by ring
      · have h1z : 1 - Φ z ≤ 1 - Φ w :=
          sub_le_sub_left (monotone_cdf (gaussianReal 0 1) hwz) 1
        have hm := exp_mul_one_sub_Φ_le_half hw0.le
        calc
          sqrt (2 * π) * exp (w ^ 2 / 2) * (1 - Φ z) * Φ w
              = Φ w * (sqrt (2 * π) * exp (w ^ 2 / 2) * (1 - Φ z)) := by ring
          _ ≤ 1 * (sqrt (2 * π) * exp (w ^ 2 / 2) * (1 - Φ w)) := by
                refine mul_le_mul (Φ_le_one w) ?_ ?_ zero_le_one
                · exact mul_le_mul_of_nonneg_left h1z (mul_nonneg hsqrt (exp_nonneg _))
                · exact mul_nonneg (mul_nonneg hsqrt (exp_nonneg _))
                    (sub_nonneg.mpr (Φ_le_one z))
          _ = sqrt (2 * π) * (exp (w ^ 2 / 2) * (1 - Φ w)) := by ring
          _ ≤ sqrt (2 * π) * (1 / 2) := mul_le_mul_of_nonneg_left hm hsqrt
          _ = sqrt (2 * π) / 2 := by ring
    · have hwz' : z ≤ w := hzw.le
      rw [steinSolution_of_ge z w hwz']
      rcases le_or_gt w 0 with hw0 | hw0
      · have hΦz : Φ z ≤ Φ w := monotone_cdf (gaussianReal 0 1) hwz'
        have hy0 : 0 ≤ -w := neg_nonneg.mpr hw0
        have hm := exp_mul_one_sub_Φ_le_half hy0
        have hexp : exp (w ^ 2 / 2) = exp ((-w) ^ 2 / 2) := by rw [neg_sq]
        have h1w : 1 - Φ w = Φ (-w) := (Φ_neg w).symm
        calc
          sqrt (2 * π) * exp (w ^ 2 / 2) * Φ z * (1 - Φ w)
              = Φ z * (sqrt (2 * π) * exp (w ^ 2 / 2) * (1 - Φ w)) := by ring
          _ ≤ Φ w * (sqrt (2 * π) * exp (w ^ 2 / 2) * (1 - Φ w)) := by
                refine mul_le_mul_of_nonneg_right hΦz ?_
                exact mul_nonneg (mul_nonneg hsqrt (exp_nonneg _))
                  (sub_nonneg.mpr (Φ_le_one w))
          _ = Φ w * (sqrt (2 * π) * exp ((-w) ^ 2 / 2) * Φ (-w)) := by
                rw [hexp, h1w]
          _ = (1 - Φ (-w)) * (sqrt (2 * π) * exp ((-w) ^ 2 / 2) * Φ (-w)) := by
                rw [show Φ w = 1 - Φ (-w) from by simpa using Φ_neg (-w)]
          _ = sqrt (2 * π) * (exp ((-w) ^ 2 / 2) * (1 - Φ (-w))) * Φ (-w) := by ring
          _ ≤ sqrt (2 * π) * (1 / 2) * 1 := by
                refine mul_le_mul (mul_le_mul_of_nonneg_left hm hsqrt) (Φ_le_one (-w))
                  (Φ_nonneg (-w)) (mul_nonneg hsqrt (by positivity))
          _ = sqrt (2 * π) / 2 := by ring
      · have hm := exp_mul_one_sub_Φ_le_half hw0.le
        calc
          sqrt (2 * π) * exp (w ^ 2 / 2) * Φ z * (1 - Φ w)
              = Φ z * (sqrt (2 * π) * exp (w ^ 2 / 2) * (1 - Φ w)) := by ring
          _ ≤ 1 * (sqrt (2 * π) * exp (w ^ 2 / 2) * (1 - Φ w)) := by
                refine mul_le_mul (Φ_le_one z) le_rfl ?_ zero_le_one
                exact mul_nonneg (mul_nonneg hsqrt (exp_nonneg _))
                  (sub_nonneg.mpr (Φ_le_one w))
          _ = sqrt (2 * π) * (exp (w ^ 2 / 2) * (1 - Φ w)) := by ring
          _ ≤ sqrt (2 * π) * (1 / 2) := mul_le_mul_of_nonneg_left hm hsqrt
          _ = sqrt (2 * π) / 2 := by ring
  have hM : 0 ≤ sqrt (2 * π) / 2 := by positivity
  exact abs_le.2 ⟨by linarith, hle⟩

/-! ### Continuity, FTC, and pointwise kernel exchange for `steinSolution` -/

lemma continuous_steinSolution (z : ℝ) : Continuous (steinSolution z) := by
  have hIic : ContinuousOn (steinSolution z) (Iic z) := by
    let g : ℝ → ℝ := fun u => √(2 * π) * exp (u ^ 2 / 2) * (1 - Φ z) * Φ u
    have hcont : ContinuousOn g (Iic z) := by
      have := continuous_Φ
      fun_prop
    -- ContinuousOn.congr : ContinuousOn f → EqOn g f → ContinuousOn g
    exact hcont.congr fun u hu => steinSolution_of_le z u hu
  have hIci : ContinuousOn (steinSolution z) (Ici z) := by
    let g : ℝ → ℝ := fun u => √(2 * π) * exp (u ^ 2 / 2) * Φ z * (1 - Φ u)
    have hcont : ContinuousOn g (Ici z) := by
      have := continuous_Φ
      fun_prop
    exact hcont.congr fun u hu => steinSolution_of_ge z u hu
  have hU : (Iic z ∪ Ici z : Set ℝ) = univ := by
    ext x; constructor <;> intro hx
    · trivial
    · exact (le_total x z).elim Or.inl Or.inr
  have hcont : ContinuousOn (steinSolution z) univ := by
    rw [← hU]
    exact hIic.union_of_isClosed hIci isClosed_Iic isClosed_Ici
  exact continuousOn_univ.mp hcont

lemma measurable_steinSolutionDeriv (z : ℝ) : Measurable (steinSolutionDeriv z) :=
  (measurable_id.mul (continuous_steinSolution z).measurable).add (measurable_steinIntegrand z)

lemma intervalIntegrable_steinSolutionDeriv (z a b : ℝ) :
    IntervalIntegrable (steinSolutionDeriv z) volume a b := by
  refine IntervalIntegrable.mono_fun (f := fun _ : ℝ => (2 : ℝ))
    intervalIntegrable_const
    (measurable_steinSolutionDeriv z).aestronglyMeasurable.restrict ?_
  filter_upwards with t
  simpa [Real.norm_eq_abs] using abs_steinSolutionDeriv_le_two z t

/-- FTC for the Stein solution: `f_z(b) - f_z(a) = ∫_a^b f_z'`, using the
pointwise extension `steinSolutionDeriv` (equals the classical derivative off `{z}`). -/
lemma steinSolution_sub_eq_integral_deriv (z a b : ℝ) :
    steinSolution z b - steinSolution z a =
      ∫ t in a..b, steinSolutionDeriv z t := by
  wlog hab : a ≤ b generalizing a b
  · have h := this b a (le_of_not_ge hab)
    -- ∫_a^b = -∫_b^a
    have hsym : ∫ t in a..b, steinSolutionDeriv z t =
        -∫ t in b..a, steinSolutionDeriv z t :=
      intervalIntegral.integral_symm _ _
    linarith [h, hsym]
  rcases eq_or_lt_of_le hab with rfl | hablt
  · simp
  have hcont := continuous_steinSolution z
  have htend (c : ℝ) :
      Tendsto (steinSolution z) (𝓝[>] c) (𝓝 (steinSolution z c)) ∧
        Tendsto (steinSolution z) (𝓝[<] c) (𝓝 (steinSolution z c)) := by
    constructor <;>
      exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hFTC_open {c d : ℝ} (hcd : c < d) (havoid : ∀ x ∈ Ioo c d, x ≠ z) :
      steinSolution z d - steinSolution z c =
        ∫ t in c..d, steinSolutionDeriv z t := by
    have hderiv : ∀ x ∈ Ioo c d, HasDerivAt (steinSolution z) (steinSolutionDeriv z x) x :=
      fun x hx => hasDerivAt_steinSolutionDeriv z x (havoid x hx)
    have hint' := intervalIntegrable_steinSolutionDeriv z c d
    have ha := (htend c).1
    have hb := (htend d).2
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hcd hderiv hint' ha hb).symm
  by_cases hz : z ∈ Ioo a b
  · have haz : a < z := hz.1
    have hzb : z < b := hz.2
    have h1 : steinSolution z z - steinSolution z a =
        ∫ t in a..z, steinSolutionDeriv z t :=
      hFTC_open haz fun x hx => ne_of_lt hx.2
    have h2 : steinSolution z b - steinSolution z z =
        ∫ t in z..b, steinSolutionDeriv z t :=
      hFTC_open hzb fun x hx => ne_of_gt hx.1
    have hsum :=
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_steinSolutionDeriv z a z)
        (intervalIntegrable_steinSolutionDeriv z z b)
    linarith [h1, h2, hsum]
  · have havoid : ∀ x ∈ Ioo a b, x ≠ z := fun x hx hxz => by
      apply hz
      rwa [hxz] at hx
    exact hFTC_open hablt havoid

/-- Shifted FTC form used by the exchange kernel identity. -/
lemma steinSolution_sub_eq_integral_deriv_shift (z w ξ : ℝ) :
    steinSolution z w - steinSolution z (w - ξ) =
      ∫ t in (-ξ)..(0 : ℝ), steinSolutionDeriv z (w + t) := by
  have hFTC := steinSolution_sub_eq_integral_deriv z (w - ξ) w
  have hshift :
      ∫ t in (w - ξ)..w, steinSolutionDeriv z t =
        ∫ t in (-ξ)..(0 : ℝ), steinSolutionDeriv z (w + t) := by
    have h :=
      intervalIntegral.integral_comp_add_right (steinSolutionDeriv z) w
        (a := -ξ) (b := (0 : ℝ))
    convert h.symm using 2 <;> ring_nf
  linarith [hFTC, hshift]

/-! ### Public CDF/PDF forms of private mills helpers -/

/-- Public form of `one_sub_Φ_le_φ_div`. -/
lemma one_sub_cdf_gaussian_le_pdf_div {x : ℝ} (hx : 0 < x) :
    1 - cdf (gaussianReal 0 1) x ≤ gaussianPDFReal 0 1 x / x := by
  simpa [Φ, φ, φ_eq] using one_sub_Φ_le_φ_div hx

/-- Public form of `Φ_neg`. -/
lemma cdf_gaussian_neg (x : ℝ) :
    cdf (gaussianReal 0 1) (-x) = 1 - cdf (gaussianReal 0 1) x := by
  simpa [Φ] using Φ_neg x

/-- Public form of `Φ_zero`. -/
lemma cdf_gaussian_zero : cdf (gaussianReal 0 1) 0 = 1 / 2 := by
  simpa [Φ] using Φ_zero

/-- For `x ≥ 1` and every real `w`, `|f_x(w)| ≤ 2/x`. -/
lemma abs_steinSolution_le_two_div {x w : ℝ} (hx : 1 ≤ x) :
    |steinSolution x w| ≤ 2 / x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
  rcases le_total (x / 2) |w| with hge | hle
  · -- |w| ≥ x/2 ⇒ |f| ≤ 1/|w| ≤ 2/x
    have hw0 : w ≠ 0 := by
      intro h; simp [h] at hge; linarith [half_pos hx0]
    have hwpos : 0 < |w| := abs_pos.mpr hw0
    have hwf := abs_mul_steinSolution_le_one x w
    have hle1 : |steinSolution x w| ≤ 1 / |w| := by
      rw [abs_mul] at hwf
      exact (le_div_iff₀ hwpos).mpr (by linarith)
    have hle2 : 1 / |w| ≤ 2 / x := by
      have hrep : 2 / x = 1 / (x / 2) := by field_simp [hx0.ne']
      rw [hrep]
      exact one_div_le_one_div_of_le (half_pos hx0) hge
    exact hle1.trans hle2
  · -- |w| ≤ x/2 ≤ x: closed form + mills
    have hwx : w ≤ x := by
      have : w ≤ |w| := le_abs_self w
      linarith
    rw [abs_of_nonneg (steinSolution_nonneg x w), steinSolution_of_le x w hwx]
    have hMills := one_sub_Φ_le_φ_div hx0
    have hexp : exp (w ^ 2 / 2) ≤ exp (x ^ 2 / 8) := by
      refine exp_le_exp.mpr ?_
      have : w ^ 2 ≤ (x / 2) ^ 2 := by
        calc
          w ^ 2 = |w| ^ 2 := (sq_abs w).symm
          _ ≤ (x / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hle 2
      nlinarith
    have hne : (√(2 * π) : ℝ) ≠ 0 := sqrt_ne_zero'.2 (by positivity)
    have h1m0 : 0 ≤ 1 - Φ x := sub_nonneg.mpr (Φ_le_one x)
    have h1 :
        √(2 * π) * exp (w ^ 2 / 2) * (1 - Φ x) ≤
          √(2 * π) * exp (x ^ 2 / 8) * (φ x / x) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hexp (sqrt_nonneg _)) hMills h1m0
        (mul_nonneg (sqrt_nonneg _) (exp_nonneg _))
    have h2 :
        √(2 * π) * exp (x ^ 2 / 8) * (φ x / x) ≤ 2 / x := by
      have hφ : φ x = (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) := φ_eq x
      have hmul : exp (x ^ 2 / 8) * exp (-x ^ 2 / 2) =
          exp (-(3 : ℝ) * x ^ 2 / 8) := by
        rw [← exp_add]; congr 1; ring
      have hval :
          √(2 * π) * exp (x ^ 2 / 8) * (φ x / x) =
            exp (-(3 : ℝ) * x ^ 2 / 8) / x := by
        rw [hφ]
        calc
          √(2 * π) * exp (x ^ 2 / 8) * (((√(2 * π))⁻¹ * exp (-x ^ 2 / 2)) / x)
              = (√(2 * π) * (√(2 * π))⁻¹) *
                  (exp (x ^ 2 / 8) * exp (-x ^ 2 / 2)) / x := by ring
          _ = 1 * exp (-(3 : ℝ) * x ^ 2 / 8) / x := by rw [mul_inv_cancel₀ hne, hmul]
          _ = exp (-(3 : ℝ) * x ^ 2 / 8) / x := by ring
      rw [hval]
      have : exp (-(3 : ℝ) * x ^ 2 / 8) ≤ 1 :=
        exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
      exact (div_le_div_of_nonneg_right this hx0.le).trans
        (div_le_div_of_nonneg_right (by norm_num) hx0.le)
    have hΦw : 0 ≤ Φ w := Φ_nonneg w
    have hleft_nn : 0 ≤ √(2 * π) * exp (w ^ 2 / 2) * (1 - Φ x) :=
      mul_nonneg (mul_nonneg (sqrt_nonneg _) (exp_nonneg _)) h1m0
    calc
      √(2 * π) * exp (w ^ 2 / 2) * (1 - Φ x) * Φ w
          ≤ √(2 * π) * exp (w ^ 2 / 2) * (1 - Φ x) * 1 :=
            mul_le_mul_of_nonneg_left (Φ_le_one w) hleft_nn
      _ = √(2 * π) * exp (w ^ 2 / 2) * (1 - Φ x) := mul_one _
      _ ≤ √(2 * π) * exp (x ^ 2 / 8) * (φ x / x) := h1
      _ ≤ 2 / x := h2

end ProbabilityTheory
