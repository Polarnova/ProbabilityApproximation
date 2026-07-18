/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.ChenShao.UniformBerryEsseen

/-!
# Stein bounds for the nonuniform Berry--Esseen argument

This module contains the analytic Stein-solution facts used by the one-sided-truncation proof:
closed forms for the derivative, its two tail bounds, and the integrated Stein identity for a
finite sum.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal

noncomputable section

namespace ProbabilityTheory

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ι → Ω → ℝ}

/-- Closed form of `steinSolutionDeriv` on `{w ≤ x}`. -/
lemma steinSolutionDeriv_of_le {x w : ℝ} (hw : w ≤ x) :
    steinSolutionDeriv x w =
      (1 - cdf (gaussianReal 0 1) x) *
        (1 + w * √(2 * π) * exp (w ^ 2 / 2) * cdf (gaussianReal 0 1) w) := by
  unfold steinSolutionDeriv steinIntegrand
  rw [if_pos hw, steinSolution_of_le x w hw]
  ring

/-- Closed form of `steinSolutionDeriv` on `{x < w}`. -/
lemma steinSolutionDeriv_of_gt {x w : ℝ} (hw : x < w) :
    steinSolutionDeriv x w =
      cdf (gaussianReal 0 1) x *
        (w * √(2 * π) * exp (w ^ 2 / 2) * (1 - cdf (gaussianReal 0 1) w) - 1) := by
  unfold steinSolutionDeriv steinIntegrand
  have hnot : ¬ w ≤ x := not_le.mpr hw
  rw [if_neg hnot, steinSolution_of_ge x w hw.le]
  ring

/-- Bound `|1 + w √(2π) e^{w²/2} Φ(w)| ≤ 2` for `w ≤ 0`. -/
private lemma abs_one_add_left_mills_le_two {w : ℝ} (hw : w ≤ 0) :
    |1 + w * √(2 * π) * exp (w ^ 2 / 2) * cdf (gaussianReal 0 1) w| ≤ 2 := by
  set Φw := cdf (gaussianReal 0 1) w
  set t := w * √(2 * π) * exp (w ^ 2 / 2) * Φw
  have hΦw0 : 0 ≤ Φw := cdf_nonneg (μ := gaussianReal 0 1) w
  have hws : w * √(2 * π) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hw (sqrt_nonneg _)
  have hwse : w * √(2 * π) * exp (w ^ 2 / 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hws (exp_nonneg _)
  have ht_le : t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hwse hΦw0
  have ht_ge : -1 ≤ t := by
    rcases eq_or_lt_of_le hw with rfl | hwlt
    · simp [t, Φw]
    · have hy : 0 < -w := neg_pos.mpr hwlt
      have hMills := one_sub_cdf_gaussian_le_pdf_div hy
      have hΦeq := cdf_gaussian_neg w
      have hΦle0 : Φw ≤ gaussianPDFReal 0 1 (-w) / (-w) := by
        have hrew : Φw = 1 - cdf (gaussianReal 0 1) (-w) := by
          simp only [Φw]
          linarith [hΦeq]
        rw [hrew]
        exact hMills
      have hΦle : Φw ≤ ((√(2 * π))⁻¹ * exp (-w ^ 2 / 2)) / (-w) := by
        have hpdf : gaussianPDFReal 0 1 (-w) =
            (√(2 * π))⁻¹ * exp (-(-w) ^ 2 / 2) := by
          simp [gaussianPDFReal, NNReal.coe_one]
        have hpdf' : gaussianPDFReal 0 1 (-w) =
            (√(2 * π))⁻¹ * exp (-w ^ 2 / 2) := by
          rw [hpdf, neg_sq]
        rwa [hpdf'] at hΦle0
      have hmul :
          w * √(2 * π) * exp (w ^ 2 / 2) * Φw ≥
            w * √(2 * π) * exp (w ^ 2 / 2) *
              (((√(2 * π))⁻¹ * exp (-w ^ 2 / 2)) / (-w)) :=
        mul_le_mul_of_nonpos_left hΦle hwse
      have hsimp :
          w * √(2 * π) * exp (w ^ 2 / 2) *
            (((√(2 * π))⁻¹ * exp (-w ^ 2 / 2)) / (-w)) = -1 := by
        have hne : (√(2 * π) : ℝ) ≠ 0 := sqrt_ne_zero'.2 (by positivity)
        have he : exp (w ^ 2 / 2) * exp (-w ^ 2 / 2) = (1 : ℝ) := by
          rw [← exp_add, show w ^ 2 / 2 + (-w ^ 2 / 2) = 0 by ring, exp_zero]
        calc
          w * √(2 * π) * exp (w ^ 2 / 2) *
                (((√(2 * π))⁻¹ * exp (-w ^ 2 / 2)) / (-w))
              = (w / (-w)) * (√(2 * π) * (√(2 * π))⁻¹) *
                  (exp (w ^ 2 / 2) * exp (-w ^ 2 / 2)) := by ring
          _ = (-1) * 1 * 1 := by
                rw [mul_inv_cancel₀ hne, he]
                have : w / (-w) = -1 := by field_simp [hwlt.ne]
                rw [this]
          _ = -1 := by ring
      simp only [t, Φw] at hmul ⊢
      linarith [hmul, hsimp]
  exact abs_le.2 ⟨by linarith, by linarith⟩

lemma abs_steinSolutionDeriv_le_two_mul_tail
    {x w : ℝ} (hx : 0 < x) (hw : w ≤ 0) :
    |steinSolutionDeriv x w| ≤ 2 * (1 - cdf (gaussianReal 0 1) x) := by
  have hwx : w ≤ x := le_trans hw hx.le
  have ha0 : 0 ≤ 1 - cdf (gaussianReal 0 1) x :=
    sub_nonneg.mpr (cdf_le_one _ _)
  rw [steinSolutionDeriv_of_le hwx, abs_mul, abs_of_nonneg ha0]
  have h := abs_one_add_left_mills_le_two hw
  have hmul := mul_le_mul_of_nonneg_left h ha0
  linarith

private lemma steinSolutionDeriv_nonneg_of_nonneg_le
    {x w : ℝ} (hw0 : 0 ≤ w) (hwx : w ≤ x) :
    0 ≤ steinSolutionDeriv x w := by
  rw [steinSolutionDeriv_of_le hwx]
  refine mul_nonneg (sub_nonneg.mpr (cdf_le_one _ _)) ?_
  have hΦ : 0 ≤ cdf (gaussianReal 0 1) w :=
    cdf_nonneg (μ := gaussianReal 0 1) w
  positivity

/-- Pointwise majorant of `|f'_x|` when `|w| ≤ x/2`, `x ≥ 2`. -/
lemma abs_steinSolutionDeriv_le_majorant_of_abs_le_half
    {x w : ℝ} (hx : 2 ≤ x) (hw : |w| ≤ x / 2) :
    |steinSolutionDeriv x w| ≤
      (1 - cdf (gaussianReal 0 1) x) *
        (1 + √(2 * π) * (x / 2) * exp (x ^ 2 / 8)) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hwx : w ≤ x := by linarith [le_abs_self w]
  have hmaj0 : 0 ≤ 1 - cdf (gaussianReal 0 1) x :=
    sub_nonneg.mpr (cdf_le_one _ _)
  rcases le_or_gt w 0 with hw0 | hw0
  · have h := abs_steinSolutionDeriv_le_two_mul_tail hx0 hw0
    have h2 : (2 : ℝ) ≤ 1 + √(2 * π) * (x / 2) * exp (x ^ 2 / 8) := by
      have hsqrt : (1 : ℝ) ≤ √(2 * π) := by
        rw [Real.le_sqrt (by norm_num) (by positivity)]
        linarith [Real.two_le_pi]
      have hx2 : (1 : ℝ) ≤ x / 2 := by linarith
      have hexp : (1 : ℝ) ≤ exp (x ^ 2 / 8) := one_le_exp (by positivity)
      have hprod1 : (1 : ℝ) ≤ √(2 * π) * (x / 2) :=
        one_le_mul_of_one_le_of_one_le hsqrt hx2
      have hprod : (1 : ℝ) ≤ √(2 * π) * (x / 2) * exp (x ^ 2 / 8) :=
        one_le_mul_of_one_le_of_one_le hprod1 hexp
      linarith
    calc
      |steinSolutionDeriv x w| ≤ 2 * (1 - cdf (gaussianReal 0 1) x) := h
      _ ≤ (1 - cdf (gaussianReal 0 1) x) *
            (1 + √(2 * π) * (x / 2) * exp (x ^ 2 / 8)) := by
          rw [mul_comm (2 : ℝ)]
          exact mul_le_mul_of_nonneg_left h2 hmaj0
  · have hw0' : 0 ≤ w := hw0.le
    have hnn := steinSolutionDeriv_nonneg_of_nonneg_le hw0' hwx
    rw [abs_of_nonneg hnn, steinSolutionDeriv_of_le hwx]
    refine mul_le_mul_of_nonneg_left ?_ hmaj0
    have hΦ : cdf (gaussianReal 0 1) w ≤ 1 := cdf_le_one _ _
    have hnn2 : 0 ≤ w * √(2 * π) * exp (w ^ 2 / 2) := by positivity
    have h1 : w * √(2 * π) * exp (w ^ 2 / 2) * cdf (gaussianReal 0 1) w ≤
        w * √(2 * π) * exp (w ^ 2 / 2) := mul_le_of_le_one_right hnn2 hΦ
    have hexp : exp (w ^ 2 / 2) ≤ exp (x ^ 2 / 8) := by
      refine exp_le_exp.mpr ?_
      have : w ^ 2 ≤ (x / 2) ^ 2 := by
        calc
          w ^ 2 = |w| ^ 2 := (sq_abs w).symm
          _ ≤ (x / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hw 2
      linarith
    have hwle : w ≤ x / 2 := le_trans (le_abs_self w) hw
    have h2 : w * √(2 * π) * exp (w ^ 2 / 2) ≤
        (x / 2) * √(2 * π) * exp (x ^ 2 / 8) := by
      calc
        w * √(2 * π) * exp (w ^ 2 / 2)
            ≤ (x / 2) * √(2 * π) * exp (w ^ 2 / 2) := by gcongr
        _ ≤ (x / 2) * √(2 * π) * exp (x ^ 2 / 8) := by gcongr
    linarith

private lemma integrable_abs_steinSolutionDeriv_sumX
    (hXmeas : ∀ k, Measurable (X k)) (x : ℝ) :
    Integrable (fun ω => |steinSolutionDeriv x (sumX X ω)|) μ :=
  Integrable.of_bound
    (((measurable_steinSolutionDeriv x).comp
      (measurable_sumX hXmeas)).abs).aestronglyMeasurable
    (2 : ℝ)
    (Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using
        abs_steinSolutionDeriv_le_two x (sumX X ω))

/-- Stein equation integrated form: `F(x) − Φ(x) = E[f'_x(W) − W f_x(W)]`. -/
lemma cdf_sub_eq_integral_steinSolutionDeriv_sub_Wf
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (x : ℝ) :
    cdf (μ.map (sumX X)) x - cdf (gaussianReal 0 1) x =
      ∫ ω, steinSolutionDeriv x (sumX X ω) ∂μ -
        ∫ ω, sumX X ω * steinSolution x (sumX X ω) ∂μ := by
  classical
  haveI : IsProbabilityMeasure (μ.map (sumX X)) :=
    isProbabilityMeasure_map_sumX (μ := μ) (X := X) fun i => (hXmeas i).aemeasurable
  have hmeas := measurable_sumX hXmeas
  have hint_f' : Integrable (fun ω => steinSolutionDeriv x (sumX X ω)) μ := by
    refine (integrable_abs_steinSolutionDeriv_sumX (μ := μ) hXmeas x).mono' ?_ ?_
    · exact ((measurable_steinSolutionDeriv x).comp hmeas).aestronglyMeasurable
    · filter_upwards with ω
      simp [Real.norm_eq_abs]
  have hint_Wf := integrable_sumX_mul_steinSolution hX hXmeas x
  have hident :
      ∫ ω, steinIntegrand x (sumX X ω) ∂μ =
        ∫ ω, steinSolutionDeriv x (sumX X ω) ∂μ -
          ∫ ω, sumX X ω * steinSolution x (sumX X ω) ∂μ := by
    have hfun :
        (fun ω => steinIntegrand x (sumX X ω)) =
          fun ω => steinSolutionDeriv x (sumX X ω) -
            sumX X ω * steinSolution x (sumX X ω) := by
      funext ω
      simp only [steinSolutionDeriv]
      ring
    rw [hfun, integral_sub hint_f' hint_Wf]
  have hFeq : cdf (μ.map (sumX X)) x - cdf (gaussianReal 0 1) x =
      ∫ ω, steinIntegrand x (sumX X ω) ∂μ := by
    have hmap :=
      cdf_map_sumX_eq_real (X := X) (μ := μ) (fun i => (hXmeas i).aemeasurable) x
    have h1 : Integrable (fun ω => if sumX X ω ≤ x then (1 : ℝ) else 0) μ := by
      refine Integrable.of_bound ?_ 1 ?_
      · exact (Measurable.ite (measurableSet_le hmeas measurable_const)
          measurable_const measurable_const).aestronglyMeasurable
      · filter_upwards with ω
        split_ifs <;> simp
    have h2 : Integrable (fun _ : Ω => cdf (gaussianReal 0 1) x) μ :=
      integrable_const _
    have heq : ∫ ω, steinIntegrand x (sumX X ω) ∂μ =
        ∫ ω, (if sumX X ω ≤ x then (1 : ℝ) else 0) ∂μ -
          cdf (gaussianReal 0 1) x := by
      have hfun :
          (fun ω => steinIntegrand x (sumX X ω)) =
            fun ω => (if sumX X ω ≤ x then (1 : ℝ) else 0) -
              cdf (gaussianReal 0 1) x := by
        funext ω
        rfl
      rw [hfun, integral_sub h1 h2, integral_const]
      simp [smul_eq_mul]
    have hind : ∫ ω, (if sumX X ω ≤ x then (1 : ℝ) else 0) ∂μ =
        (μ.map (sumX X)).real (Set.Iic x) := by
      have hset : MeasurableSet {ω | sumX X ω ≤ x} :=
        measurableSet_le hmeas measurable_const
      have hmap_apply :
          (μ.map (sumX X)) (Set.Iic x) = μ {ω | sumX X ω ≤ x} := by
        rw [Measure.map_apply hmeas measurableSet_Iic]
        rfl
      rw [show (fun ω => if sumX X ω ≤ x then (1 : ℝ) else 0) =
          ({ω | sumX X ω ≤ x}.indicator fun _ => (1 : ℝ)) by
        funext ω
        simp [Set.indicator]]
      rw [integral_indicator hset, integral_const, smul_eq_mul, mul_one]
      simp only [Measure.real, Measure.restrict_apply_univ, hmap_apply]
    linarith [hmap, heq, hind]
  rw [hFeq, hident]

end ProbabilityTheory
