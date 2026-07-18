/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.ChenShao.Concentration
import ProbabilityApproximation.Stein.IndicatorSolution

/-!
# Uniform Berry–Esseen bound

This module proves a uniform Berry–Esseen bound with constant `30` for independent centered finite
families of unit total variance and finite absolute third moments. The proof uses the half-line
Stein equation, a forward exchange kernel, leave-one-out concentration, and an integrated residual
estimate. It also records the elementary large-error branch of Chen--Shao's truncated-moment bound
with constant `41 / 10`.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal

noncomputable section

namespace ProbabilityTheory

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ι → Ω → ℝ}

/-- Large-error branch: if the truncated moment sum is at least `10/41`, the
CDF error is at most `1 ≤ (41/10) · truncMomentSum`. -/
lemma abs_cdf_sub_le_truncMomentSum_of_large
    (hX : ∀ i, Measurable (X i))
    (x : ℝ)
    (hlarge : (10 : ℝ) / 41 ≤ truncMomentSum (X := X) μ) :
    |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤
      (41 / 10 : ℝ) * truncMomentSum (X := X) μ := by
  haveI : IsProbabilityMeasure (μ.map fun ω ↦ ∑ i, X i ω) :=
    isProbabilityMeasure_map_sumX (μ := μ) (X := X) fun i => (hX i).aemeasurable
  have h1 : |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤ 1 :=
    abs_cdf_sub_le_one _ _ x
  have h41 : (0 : ℝ) ≤ 41 / 10 := by norm_num
  have hge : (1 : ℝ) ≤ (41 / 10) * truncMomentSum (X := X) μ := by
    have : (41 / 10 : ℝ) * (10 / 41) = 1 := by norm_num
    calc
      (1 : ℝ) = (41 / 10) * (10 / 41) := this.symm
      _ ≤ (41 / 10) * truncMomentSum (X := X) μ :=
            mul_le_mul_of_nonneg_left hlarge h41
  exact h1.trans hge

omit [IsProbabilityMeasure μ] in
/-- Under third-moment integrability, the truncated moment sum is dominated by
the full third-moment sum. -/
lemma truncMomentSum_le_thirdMomentSum
    (hX : ∀ i, Measurable (X i))
    (h3 : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ)
    (h2 : ∀ i, MemLp (X i) 2 μ) :
    truncMomentSum (X := X) μ ≤ thirdMomentSum (X := X) μ := by
  refine Finset.sum_le_sum fun i _ => ?_
  set s1 : Set Ω := {ω | 1 < |X i ω|}
  set s2 : Set Ω := {ω | |X i ω| ≤ 1}
  have hset1 : MeasurableSet s1 := measurableSet_lt measurable_const (hX i).abs
  have hset2 : MeasurableSet s2 := measurableSet_le (hX i).abs measurable_const
  have hInd1 :
      (fun ω => if 1 < |X i ω| then (X i ω) ^ 2 else 0) =
        s1.indicator (fun ω => (X i ω) ^ 2) := by
    ext ω; by_cases h : 1 < |X i ω| <;> simp [s1, h, indicator]
  have hInd2 :
      (fun ω => if |X i ω| ≤ 1 then |X i ω| ^ 3 else 0) =
        s2.indicator (fun ω => |X i ω| ^ 3) := by
    ext ω; by_cases h : |X i ω| ≤ 1 <;> simp [s2, h, indicator]
  have hAint : Integrable (fun ω => if 1 < |X i ω| then (X i ω) ^ 2 else 0) μ := by
    rw [hInd1]; exact (h2 i).integrable_sq.integrableOn.integrable_indicator hset1
  have hBint : Integrable (fun ω => if |X i ω| ≤ 1 then |X i ω| ^ 3 else 0) μ := by
    rw [hInd2]; exact (h3 i).integrableOn.integrable_indicator hset2
  have hsum :
      (∫ ω in s1, (X i ω) ^ 2 ∂μ) + ∫ ω in s2, |X i ω| ^ 3 ∂μ =
        ∫ ω, ((if 1 < |X i ω| then (X i ω) ^ 2 else 0) +
          if |X i ω| ≤ 1 then |X i ω| ^ 3 else 0) ∂μ := by
    have hA : ∫ ω in s1, (X i ω) ^ 2 ∂μ =
        ∫ ω, (if 1 < |X i ω| then (X i ω) ^ 2 else 0) ∂μ := by
      rw [hInd1, integral_indicator hset1]
    have hB : ∫ ω in s2, |X i ω| ^ 3 ∂μ =
        ∫ ω, (if |X i ω| ≤ 1 then |X i ω| ^ 3 else 0) ∂μ := by
      rw [hInd2, integral_indicator hset2]
    rw [hA, hB, ← integral_add hAint hBint]
  have hpt :
      ∫ ω, ((if 1 < |X i ω| then (X i ω) ^ 2 else 0) +
        if |X i ω| ≤ 1 then |X i ω| ^ 3 else 0) ∂μ ≤
        ∫ ω, |X i ω| ^ 3 ∂μ :=
    integral_mono (hAint.add hBint) (h3 i) fun ω => trunc_terms_le_abs_cube (X i ω)
  simpa [s1, s2] using hsum.trans_le hpt

/-! ### Pointwise kernel exchange for the indicator Stein solution -/

/-- Pointwise Stein exchange:
`ξ (f_z(w) - f_z(w - ξ)) = ∫ kernelDensity ξ t · f_z'(w + t) dt`. -/
lemma mul_steinSolution_sub_eq_integral_kernel (z w ξ : ℝ) :
    ξ * (steinSolution z w - steinSolution z (w - ξ)) =
      ∫ t : ℝ, kernelDensity ξ t * steinSolutionDeriv z (w + t) := by
  have hshift := steinSolution_sub_eq_integral_deriv_shift z w ξ
  rw [hshift]
  by_cases hξ : 0 ≤ ξ
  · rw [← intervalIntegral.integral_const_mul ξ,
      intervalIntegral.integral_of_le (neg_nonpos.mpr hξ)]
    have hfun :
        (fun t => kernelDensity ξ t * steinSolutionDeriv z (w + t)) =
          (Icc (-ξ) 0).indicator
            (fun t => ξ * steinSolutionDeriv z (w + t)) := by
      funext t
      rw [kernelDensity_eq_indicator_nonneg ξ hξ]
      by_cases ht : t ∈ Icc (-ξ) 0
      · simp [indicator_of_mem ht]
      · simp [indicator_of_notMem ht]
    rw [hfun, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc]
  · have hlt : ξ < 0 := lt_of_not_ge hξ
    have hξ0 : 0 ≤ -ξ := neg_nonneg.mpr hlt.le
    have hsym :
        ∫ t in (-ξ)..(0 : ℝ), steinSolutionDeriv z (w + t) =
          -∫ t in (0 : ℝ)..(-ξ), steinSolutionDeriv z (w + t) :=
      intervalIntegral.integral_symm _ _
    rw [hsym, mul_neg]
    have hrew :
        -(ξ * ∫ t in (0 : ℝ)..(-ξ), steinSolutionDeriv z (w + t)) =
          (-ξ) * ∫ t in (0 : ℝ)..(-ξ), steinSolutionDeriv z (w + t) := by ring
    rw [hrew, ← intervalIntegral.integral_const_mul (-ξ),
      intervalIntegral.integral_of_le hξ0]
    have hfun :
        (fun t => kernelDensity ξ t * steinSolutionDeriv z (w + t)) =
          (Ioc 0 (-ξ)).indicator
            (fun t => (-ξ) * steinSolutionDeriv z (w + t)) := by
      funext t
      rw [kernelDensity_eq_indicator_neg ξ hlt]
      by_cases ht : t ∈ Ioc 0 (-ξ)
      · simp [indicator_of_mem ht]
      · simp [indicator_of_notMem ht]
    rw [hfun, integral_indicator measurableSet_Ioc]

/-! ### Stein identity for independent sums -/

variable [DecidableEq ι]

omit [DecidableEq ι] in
/-- Integrability of `W · f_z(W)`. -/
lemma integrable_sumX_mul_steinSolution
    (hX : ∀ i, MemLp (X i) 2 μ) (hXmeas : ∀ i, Measurable (X i)) (z : ℝ) :
    Integrable (fun ω => sumX X ω * steinSolution z (sumX X ω)) μ := by
  have hW : MemLp (sumX X) 2 μ := by
    change MemLp (fun ω => ∑ i, X i ω) 2 μ
    exact memLp_finsetSum (s := Finset.univ) (fun i _ => hX i)
  have habs := (hW.integrable one_le_two).abs
  have hM : 0 ≤ sqrt (2 * π) / 2 := by positivity
  refine (habs.const_mul (sqrt (2 * π) / 2)).mono' ?_ ?_
  · exact (measurable_sumX hXmeas).aestronglyMeasurable.mul
      ((continuous_steinSolution z).comp_aestronglyMeasurable
        (measurable_sumX hXmeas).aestronglyMeasurable)
  · filter_upwards with ω
    have hf := abs_steinSolution_le_sqrt_two_pi_div_two z (sumX X ω)
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |sumX X ω| * |steinSolution z (sumX X ω)| ≤ |sumX X ω| * (sqrt (2 * π) / 2) := by
        gcongr
      _ = (sqrt (2 * π) / 2) * |sumX X ω| := mul_comm _ _

omit [IsProbabilityMeasure μ] in
/-- Mean-zero leaf: `E[Xᵢ f_z(W⁽ⁱ⁾)] = 0`. -/
lemma integral_X_mul_steinSolution_leaveOneOut_eq_zero
    (hXmeas : ∀ k, Measurable (X k)) (h_indep : iIndepFun X μ)
    (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0) (i : ι) (z : ℝ) :
    ∫ ω, X i ω * steinSolution z (leaveOneOut X i ω) ∂μ = 0 :=
  integral_X_mul_comp_leaveOneOut hXmeas h_indep i (h_mean i) (steinSolution z)
    (continuous_steinSolution z).aestronglyMeasurable

omit [IsProbabilityMeasure μ] in
/-- Exchange leaf for a single coordinate:
`E[Xᵢ (f_z(W) - f_z(W⁽ⁱ⁾))] = E[∫ K_i(t) f_z'(W + t) dt]`. -/
lemma integral_X_mul_steinSolution_sub_eq_kernel
    (_hX : ∀ k, MemLp (X k) 2 μ) (_hXmeas : ∀ k, Measurable (X k))
    (i : ι) (z : ℝ) :
    ∫ ω, X i ω * (steinSolution z (sumX X ω) - steinSolution z (leaveOneOut X i ω)) ∂μ =
      ∫ ω, (∫ t : ℝ,
        kernelDensity (X i ω) t *
          steinSolutionDeriv z (sumX X ω + t)) ∂μ := by
  exact integral_congr_ae (Eventually.of_forall fun ω => by
    dsimp only
    rw [leaveOneOut_eq_sum_sub (X := X) i ω]
    exact mul_steinSolution_sub_eq_integral_kernel z (sumX X ω) (X i ω))

/-- Stein identity for independent mean-zero sums (CGS (2.27) form):
`E[W f_z(W)] = ∑_i E[∫ kernelDensity(Xᵢ,t) f_z'(W + t) dt]`. -/
lemma stein_identity_sum
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (z : ℝ) :
    ∫ ω, sumX X ω * steinSolution z (sumX X ω) ∂μ =
      ∑ i : ι, ∫ ω, (∫ t : ℝ,
        kernelDensity (X i ω) t *
          steinSolutionDeriv z (sumX X ω + t)) ∂μ := by
  -- W f(W) = ∑_i X_i f(W) = ∑_i X_i (f(W) - f(W⁽ⁱ⁾)) + ∑_i X_i f(W⁽ⁱ⁾)
  have hpoint (ω : Ω) :
      sumX X ω * steinSolution z (sumX X ω) =
        ∑ i : ι, X i ω * (steinSolution z (sumX X ω) -
          steinSolution z (leaveOneOut X i ω)) +
        ∑ i : ι, X i ω * steinSolution z (leaveOneOut X i ω) := by
    have hsum1 :
        ∑ i : ι, X i ω * steinSolution z (sumX X ω) =
          sumX X ω * steinSolution z (sumX X ω) := by
      simp only [sumX, Finset.sum_mul]
    have hsum2 :
        ∑ i : ι, X i ω * (steinSolution z (sumX X ω) -
            steinSolution z (leaveOneOut X i ω)) +
          ∑ i : ι, X i ω * steinSolution z (leaveOneOut X i ω) =
        ∑ i : ι, X i ω * steinSolution z (sumX X ω) := by
      rw [← Finset.sum_add_distrib]
      congr 1; funext i; ring
    linarith [hsum1, hsum2]
  have hint1 (i : ι) :
      Integrable (fun ω =>
        X i ω * (steinSolution z (sumX X ω) - steinSolution z (leaveOneOut X i ω))) μ := by
    have hA : Integrable (fun ω => X i ω * steinSolution z (sumX X ω)) μ := by
      have hXi := (hX i).integrable one_le_two
      have hM : 0 ≤ sqrt (2 * π) / 2 := by positivity
      refine (hXi.abs.const_mul (sqrt (2 * π) / 2)).mono' ?_ ?_
      · exact (hXmeas i).aestronglyMeasurable.mul
          ((continuous_steinSolution z).comp_aestronglyMeasurable
            (measurable_sumX hXmeas).aestronglyMeasurable)
      · filter_upwards with ω
        have hf := abs_steinSolution_le_sqrt_two_pi_div_two z (sumX X ω)
        rw [Real.norm_eq_abs, abs_mul]
        calc
          |X i ω| * |steinSolution z (sumX X ω)| ≤ |X i ω| * (sqrt (2 * π) / 2) := by gcongr
          _ = (sqrt (2 * π) / 2) * |X i ω| := mul_comm _ _
    have hB : Integrable (fun ω => X i ω * steinSolution z (leaveOneOut X i ω)) μ := by
      have hXi := (hX i).integrable one_le_two
      have hM : 0 ≤ sqrt (2 * π) / 2 := by positivity
      refine (hXi.abs.const_mul (sqrt (2 * π) / 2)).mono' ?_ ?_
      · exact (hXmeas i).aestronglyMeasurable.mul
          ((continuous_steinSolution z).comp_aestronglyMeasurable
            (measurable_leaveOneOut hXmeas i).aestronglyMeasurable)
      · filter_upwards with ω
        have hf := abs_steinSolution_le_sqrt_two_pi_div_two z (leaveOneOut X i ω)
        rw [Real.norm_eq_abs, abs_mul]
        calc
          |X i ω| * |steinSolution z (leaveOneOut X i ω)| ≤
              |X i ω| * (sqrt (2 * π) / 2) := by gcongr
          _ = (sqrt (2 * π) / 2) * |X i ω| := mul_comm _ _
    have heq :
        (fun ω => X i ω * (steinSolution z (sumX X ω) -
          steinSolution z (leaveOneOut X i ω))) =
          fun ω => X i ω * steinSolution z (sumX X ω) -
            X i ω * steinSolution z (leaveOneOut X i ω) := by
      funext ω; ring
    rw [heq]
    exact hA.sub hB
  have hint2 (i : ι) :
      Integrable (fun ω => X i ω * steinSolution z (leaveOneOut X i ω)) μ := by
    have hXi := (hX i).integrable one_le_two
    have hM : 0 ≤ sqrt (2 * π) / 2 := by positivity
    refine (hXi.abs.const_mul (sqrt (2 * π) / 2)).mono' ?_ ?_
    · exact (hXmeas i).aestronglyMeasurable.mul
        ((continuous_steinSolution z).comp_aestronglyMeasurable
          (measurable_leaveOneOut hXmeas i).aestronglyMeasurable)
    · filter_upwards with ω
      have hf := abs_steinSolution_le_sqrt_two_pi_div_two z (leaveOneOut X i ω)
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |X i ω| * |steinSolution z (leaveOneOut X i ω)| ≤
            |X i ω| * (sqrt (2 * π) / 2) := by gcongr
        _ = (sqrt (2 * π) / 2) * |X i ω| := mul_comm _ _
  have hsplit :
      ∫ ω, sumX X ω * steinSolution z (sumX X ω) ∂μ =
        ∑ i : ι, ∫ ω, X i ω * (steinSolution z (sumX X ω) -
          steinSolution z (leaveOneOut X i ω)) ∂μ +
        ∑ i : ι, ∫ ω, X i ω * steinSolution z (leaveOneOut X i ω) ∂μ := by
    have hfun :
        (fun ω => sumX X ω * steinSolution z (sumX X ω)) =
          fun ω => ∑ i : ι,
            (X i ω * (steinSolution z (sumX X ω) - steinSolution z (leaveOneOut X i ω)) +
              X i ω * steinSolution z (leaveOneOut X i ω)) := by
      funext ω
      calc
        sumX X ω * steinSolution z (sumX X ω)
            = ∑ i, X i ω * (steinSolution z (sumX X ω) -
                steinSolution z (leaveOneOut X i ω)) +
              ∑ i, X i ω * steinSolution z (leaveOneOut X i ω) := hpoint ω
        _ = ∑ i, (X i ω * (steinSolution z (sumX X ω) -
                steinSolution z (leaveOneOut X i ω)) +
              X i ω * steinSolution z (leaveOneOut X i ω)) := by
            rw [← Finset.sum_add_distrib]
    rw [hfun]
    have hint_sum (i : ι) :
        Integrable (fun ω =>
          X i ω * (steinSolution z (sumX X ω) - steinSolution z (leaveOneOut X i ω)) +
            X i ω * steinSolution z (leaveOneOut X i ω)) μ :=
      (hint1 i).add (hint2 i)
    rw [integral_finsetSum _ fun i _ => hint_sum i]
    have hterms :
        ∑ i : ι, ∫ ω,
            (X i ω * (steinSolution z (sumX X ω) - steinSolution z (leaveOneOut X i ω)) +
              X i ω * steinSolution z (leaveOneOut X i ω)) ∂μ =
          ∑ i : ι, (∫ ω, X i ω * (steinSolution z (sumX X ω) -
              steinSolution z (leaveOneOut X i ω)) ∂μ +
            ∫ ω, X i ω * steinSolution z (leaveOneOut X i ω) ∂μ) :=
      Finset.sum_congr rfl fun i _ => integral_add (hint1 i) (hint2 i)
    rw [hterms, Finset.sum_add_distrib]
  have h0 : ∑ i : ι, ∫ ω, X i ω * steinSolution z (leaveOneOut X i ω) ∂μ = 0 := by
    refine Finset.sum_eq_zero fun i _ =>
      integral_X_mul_steinSolution_leaveOneOut_eq_zero hXmeas h_indep h_mean i z
  rw [hsplit, h0, add_zero]
  refine Finset.sum_congr rfl fun i _ =>
    integral_X_mul_steinSolution_sub_eq_kernel hX hXmeas i z

/-- Stein equation rearrangement (pointwise off the diagonal, a.e. form):
`f_z'(w) = w f_z(w) + 1_{w ≤ z} - Φ(z)`. -/
lemma steinSolutionDeriv_eq (z w : ℝ) :
    steinSolutionDeriv z w = w * steinSolution z w + steinIntegrand z w :=
  rfl

/-- Lipschitz bound for the Stein solution from `|f'| ≤ 2`. -/
lemma abs_steinSolution_sub_le (z a b : ℝ) :
    |steinSolution z a - steinSolution z b| ≤ 2 * |a - b| := by
  wlog hba : b ≤ a generalizing a b
  · simpa [abs_sub_comm a b, abs_sub_comm (steinSolution z a)] using
      this b a (le_of_not_ge hba)
  have hFTC := steinSolution_sub_eq_integral_deriv z b a
  have habs :
      |steinSolution z a - steinSolution z b| =
        |∫ s in b..a, steinSolutionDeriv z s| := by rw [hFTC]
  have hint := intervalIntegrable_steinSolutionDeriv z b a
  have hle_int :
      |∫ s in b..a, steinSolutionDeriv z s| ≤
        ∫ s in b..a, |steinSolutionDeriv z s| :=
    intervalIntegral.abs_integral_le_integral_abs hba
  have hle2 :
      ∫ s in b..a, |steinSolutionDeriv z s| ≤ ∫ s in b..a, (2 : ℝ) := by
    refine intervalIntegral.integral_mono_on hba hint.abs
      (Continuous.intervalIntegrable continuous_const _ _) fun _ _ =>
        abs_steinSolutionDeriv_le_two z _
  have h2 : ∫ s in b..a, (2 : ℝ) = 2 * (a - b) := by
    rw [intervalIntegral.integral_const]; simp; ring
  have hlen : |a - b| = a - b := abs_of_nonneg (sub_nonneg.mpr hba)
  calc
    |steinSolution z a - steinSolution z b| ≤ ∫ s in b..a, (2 : ℝ) := by
      rw [habs]; linarith [hle_int, hle2]
    _ = 2 * (a - b) := h2
    _ = 2 * |a - b| := by rw [hlen]

/-- Residual increment bound (CGS-style with `|f'| ≤ 2`, `|f| ≤ √(2π)/2`):
`|(W'+ξ) f(W'+ξ) - (W'+t) f(W'+t)| ≤ (2|W'| + √(2π)/2)(|ξ| + |t|)`. -/
lemma abs_mul_steinSolution_sub_le (z W' ξ t : ℝ) :
    |(W' + ξ) * steinSolution z (W' + ξ) - (W' + t) * steinSolution z (W' + t)| ≤
      (2 * |W'| + sqrt (2 * π) / 2) * (|ξ| + |t|) := by
  set M : ℝ := sqrt (2 * π) / 2
  set W := W' + ξ
  set V := W' + t
  have hLip := abs_steinSolution_sub_le z W V
  have hWV : |W - V| = |ξ - t| := by
    change |(W' + ξ) - (W' + t)| = |ξ - t|
    ring_nf
  have hfW := abs_steinSolution_le_sqrt_two_pi_div_two z W
  have hfV := abs_steinSolution_le_sqrt_two_pi_div_two z V
  have hξt : |ξ - t| ≤ |ξ| + |t| := by
    calc
      |ξ - t| = |ξ + -t| := by ring_nf
      _ ≤ |ξ| + |-t| := abs_add_le _ _
      _ = |ξ| + |t| := by rw [abs_neg]
  have htri :
      |W * steinSolution z W - V * steinSolution z V| ≤
        |W'| * |steinSolution z W - steinSolution z V| +
          |ξ| * |steinSolution z W| + |t| * |steinSolution z V| := by
    calc
      |W * steinSolution z W - V * steinSolution z V|
          = |W' * (steinSolution z W - steinSolution z V) +
              (ξ * steinSolution z W - t * steinSolution z V)| := by
            simp only [W, V]; ring_nf
      _ ≤ |W' * (steinSolution z W - steinSolution z V)| +
            |ξ * steinSolution z W - t * steinSolution z V| := abs_add_le _ _
      _ ≤ |W'| * |steinSolution z W - steinSolution z V| +
            (|ξ| * |steinSolution z W| + |t| * |steinSolution z V|) := by
            gcongr
            · rw [abs_mul]
            · calc
                |ξ * steinSolution z W - t * steinSolution z V|
                    ≤ |ξ * steinSolution z W| + |t * steinSolution z V| := abs_sub _ _
                _ = |ξ| * |steinSolution z W| + |t| * |steinSolution z V| := by
                      simp only [abs_mul]
      _ = |W'| * |steinSolution z W - steinSolution z V| +
            |ξ| * |steinSolution z W| + |t| * |steinSolution z V| := by ring
  have hLip' : |steinSolution z W - steinSolution z V| ≤ 2 * (|ξ| + |t|) := by
    calc
      |steinSolution z W - steinSolution z V| ≤ 2 * |W - V| := hLip
      _ = 2 * |ξ - t| := by rw [hWV]
      _ ≤ 2 * (|ξ| + |t|) := by gcongr
  calc
    |W * steinSolution z W - V * steinSolution z V|
        ≤ |W'| * |steinSolution z W - steinSolution z V| +
            |ξ| * |steinSolution z W| + |t| * |steinSolution z V| := htri
    _ ≤ |W'| * (2 * (|ξ| + |t|)) + |ξ| * M + |t| * M := by
          have h1 : |W'| * |steinSolution z W - steinSolution z V| ≤
              |W'| * (2 * (|ξ| + |t|)) :=
            mul_le_mul_of_nonneg_left hLip' (abs_nonneg _)
          have h2 : |ξ| * |steinSolution z W| ≤ |ξ| * M :=
            mul_le_mul_of_nonneg_left hfW (abs_nonneg _)
          have h3 : |t| * |steinSolution z V| ≤ |t| * M :=
            mul_le_mul_of_nonneg_left hfV (abs_nonneg _)
          linarith
    _ = (2 * |W'| + M) * (|ξ| + |t|) := by ring

/-! ### Forward exchange kernel (CGS form at leave-one-out basepoint) -/

/-- Forward Stein kernel: weight `|ξ|` on the segment joining `0` to `ξ`.
Integrates to `ξ²`; used with `f'(W⁽ⁱ⁾ + t)`. -/
def kernelDensityFwd (ξ t : ℝ) : ℝ :=
  if 0 ≤ ξ then
    if t ∈ Icc 0 ξ then ξ else 0
  else
    if t ∈ Ioc ξ 0 then -ξ else 0

lemma kernelDensityFwd_nonneg (ξ t : ℝ) : 0 ≤ kernelDensityFwd ξ t := by
  unfold kernelDensityFwd
  split_ifs with hξ _ _
  · exact hξ
  · exact le_rfl
  · exact neg_nonneg.mpr (le_of_not_ge hξ)
  · exact le_rfl

lemma kernelDensityFwd_eq_indicator_nonneg (ξ : ℝ) (hξ : 0 ≤ ξ) :
    kernelDensityFwd ξ = (Icc 0 ξ).indicator fun _ => ξ := by
  funext t
  unfold kernelDensityFwd
  rw [if_pos hξ]
  by_cases ht : t ∈ Icc 0 ξ <;> simp [ht, indicator]

lemma kernelDensityFwd_eq_indicator_neg (ξ : ℝ) (hξ : ξ < 0) :
    kernelDensityFwd ξ = (Ioc ξ 0).indicator fun _ => -ξ := by
  funext t
  unfold kernelDensityFwd
  rw [if_neg (not_le.mpr hξ)]
  by_cases ht : t ∈ Ioc ξ 0 <;> simp [ht, indicator]

lemma integrable_kernelDensityFwd (ξ : ℝ) : Integrable (kernelDensityFwd ξ) := by
  by_cases hξ : 0 ≤ ξ
  · rw [kernelDensityFwd_eq_indicator_nonneg ξ hξ]
    refine (integrableOn_const (s := Icc 0 ξ) ?_ (by finiteness)).integrable_indicator
      measurableSet_Icc
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  · have hlt : ξ < 0 := lt_of_not_ge hξ
    rw [kernelDensityFwd_eq_indicator_neg ξ hlt]
    refine (integrableOn_const (s := Ioc ξ 0) ?_ (by finiteness)).integrable_indicator
      measurableSet_Ioc
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top

lemma integral_kernelDensityFwd (ξ : ℝ) : ∫ t : ℝ, kernelDensityFwd ξ t = ξ ^ 2 := by
  by_cases hξ : 0 ≤ ξ
  · rw [kernelDensityFwd_eq_indicator_nonneg ξ hξ, integral_indicator_const ξ measurableSet_Icc]
    have hlen : volume.real (Icc 0 ξ) = ξ - 0 := by
      rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hξ)]
    rw [hlen, smul_eq_mul]; ring
  · have hlt : ξ < 0 := lt_of_not_ge hξ
    rw [kernelDensityFwd_eq_indicator_neg ξ hlt,
      integral_indicator_const (-ξ) measurableSet_Ioc]
    have hlen : volume.real (Ioc ξ 0) = 0 - ξ := by
      rw [measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hlt.le)]
    rw [hlen, smul_eq_mul]; ring

/-- Weighted first moment: `∫ |t| · kernelDensityFwd ξ t = |ξ|³ / 2`. -/
lemma integral_abs_mul_kernelDensityFwd (ξ : ℝ) :
    ∫ t : ℝ, |t| * kernelDensityFwd ξ t = |ξ| ^ 3 / 2 := by
  by_cases hξ : 0 ≤ ξ
  · have hfun :
        (fun t => |t| * kernelDensityFwd ξ t) =
          (Icc 0 ξ).indicator (fun t => |t| * ξ) := by
      funext t
      rw [kernelDensityFwd_eq_indicator_nonneg ξ hξ]
      by_cases ht : t ∈ Icc 0 ξ <;> simp [ht, indicator]
    rw [hfun, integral_indicator measurableSet_Icc]
    have hcongr :
        ∫ t in Icc 0 ξ, |t| * ξ = ξ * ∫ t in Icc 0 ξ, t := by
      calc
        ∫ t in Icc 0 ξ, |t| * ξ = ξ * ∫ t in Icc 0 ξ, |t| := by
          rw [show (fun t => |t| * ξ) = fun t => ξ * |t| by funext; ring,
            integral_const_mul]
        _ = ξ * ∫ t in Icc 0 ξ, t := by
              congr 1
              refine setIntegral_congr_fun measurableSet_Icc fun t ht =>
                abs_of_nonneg ht.1
    have hid : ∫ t in Icc 0 ξ, t = ξ ^ 2 / 2 := by
      have h := integral_id (a := (0 : ℝ)) (b := ξ)
      rw [intervalIntegral.integral_of_le hξ, ← integral_Icc_eq_integral_Ioc] at h
      convert h using 1; ring
    rw [hcongr, hid, abs_of_nonneg hξ]; ring
  · -- ξ < 0: support (ξ,0], weight -ξ; same computation as Concentration
    have hlt : ξ < 0 := lt_of_not_ge hξ
    have hfun :
        (fun t => |t| * kernelDensityFwd ξ t) =
          (Ioc ξ 0).indicator (fun t => |t| * (-ξ)) := by
      funext t
      rw [kernelDensityFwd_eq_indicator_neg ξ hlt]
      by_cases ht : t ∈ Ioc ξ 0 <;> simp [ht, indicator]
    rw [hfun, integral_indicator measurableSet_Ioc]
    have hcongr :
        ∫ t in Ioc ξ 0, |t| * (-ξ) = (-ξ) * ∫ t in Ioc ξ 0, (-t) := by
      calc
        ∫ t in Ioc ξ 0, |t| * (-ξ) = (-ξ) * ∫ t in Ioc ξ 0, |t| := by
          rw [show (fun t => |t| * (-ξ)) = fun t => (-ξ) * |t| by funext; ring,
            integral_const_mul]
        _ = (-ξ) * ∫ t in Ioc ξ 0, (-t) := by
              congr 1
              refine setIntegral_congr_fun measurableSet_Ioc fun t ht =>
                abs_of_nonpos ht.2
    have hid : ∫ t in Ioc ξ 0, (-t) = ξ ^ 2 / 2 := by
      -- ∫_ξ^0 t dt = -ξ²/2, so ∫ (-t) = ξ²/2
      have hpos : ∫ t in ξ..(0 : ℝ), t = -ξ ^ 2 / 2 := by
        have h := integral_id (a := ξ) (b := (0 : ℝ))
        convert h using 1
        ring
      rw [intervalIntegral.integral_of_le hlt.le] at hpos
      -- hpos : ∫ Ioc ξ 0, t = -ξ²/2
      calc
        ∫ t in Ioc ξ 0, (-t) = ∫ t in Ioc ξ 0, (-1 : ℝ) * t := by
          congr 1; funext t; ring
        _ = (-1) * ∫ t in Ioc ξ 0, t := integral_const_mul _ _
        _ = (-1) * (-ξ ^ 2 / 2) := by rw [hpos]
        _ = ξ ^ 2 / 2 := by ring
    rw [hcongr, hid, abs_of_nonpos hlt.le]
    ring

/-- Forward exchange: `ξ (f_z(w+ξ) - f_z(w)) = ∫ kernelDensityFwd ξ t · f_z'(w+t) dt`. -/
lemma mul_steinSolution_add_eq_integral_kernelFwd (z w ξ : ℝ) :
    ξ * (steinSolution z (w + ξ) - steinSolution z w) =
      ∫ t : ℝ, kernelDensityFwd ξ t * steinSolutionDeriv z (w + t) := by
  have hFTC := steinSolution_sub_eq_integral_deriv z w (w + ξ)
  have hshift :
      ∫ t in w..(w + ξ), steinSolutionDeriv z t =
        ∫ t in (0 : ℝ)..ξ, steinSolutionDeriv z (w + t) := by
    have h :=
      intervalIntegral.integral_comp_add_right (steinSolutionDeriv z) w
        (a := (0 : ℝ)) (b := ξ)
    -- h: ∫_0^ξ f'(x+w) = ∫_w^{w+ξ} f'
    have h' :
        ∫ t in (0 : ℝ)..ξ, steinSolutionDeriv z (t + w) =
          ∫ t in w..(w + ξ), steinSolutionDeriv z t := by
      convert h using 2 <;> ring
    have hcomm :
        ∫ t in (0 : ℝ)..ξ, steinSolutionDeriv z (w + t) =
          ∫ t in (0 : ℝ)..ξ, steinSolutionDeriv z (t + w) :=
      intervalIntegral.integral_congr fun t _ => by rw [add_comm]
    linarith [h', hcomm]
  have hdiff :
      steinSolution z (w + ξ) - steinSolution z w =
        ∫ t in (0 : ℝ)..ξ, steinSolutionDeriv z (w + t) := by
    linarith [hFTC, hshift]
  rw [hdiff]
  by_cases hξ : 0 ≤ ξ
  · rw [← intervalIntegral.integral_const_mul ξ, intervalIntegral.integral_of_le hξ]
    have hfun :
        (fun t => kernelDensityFwd ξ t * steinSolutionDeriv z (w + t)) =
          (Icc 0 ξ).indicator (fun t => ξ * steinSolutionDeriv z (w + t)) := by
      funext t
      rw [kernelDensityFwd_eq_indicator_nonneg ξ hξ]
      by_cases ht : t ∈ Icc 0 ξ <;> simp [ht, indicator]
    rw [hfun, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc]
  · have hlt : ξ < 0 := lt_of_not_ge hξ
    have hsym :
        ∫ t in (0 : ℝ)..ξ, steinSolutionDeriv z (w + t) =
          -∫ t in ξ..(0 : ℝ), steinSolutionDeriv z (w + t) :=
      intervalIntegral.integral_symm _ _
    rw [hsym, mul_neg]
    have hrew :
        -(ξ * ∫ t in ξ..(0 : ℝ), steinSolutionDeriv z (w + t)) =
          (-ξ) * ∫ t in ξ..(0 : ℝ), steinSolutionDeriv z (w + t) := by ring
    rw [hrew, ← intervalIntegral.integral_const_mul (-ξ),
      intervalIntegral.integral_of_le hlt.le]
    have hfun :
        (fun t => kernelDensityFwd ξ t * steinSolutionDeriv z (w + t)) =
          (Ioc ξ 0).indicator (fun t => (-ξ) * steinSolutionDeriv z (w + t)) := by
      funext t
      rw [kernelDensityFwd_eq_indicator_neg ξ hlt]
      by_cases ht : t ∈ Ioc ξ 0 <;> simp [ht, indicator]
    rw [hfun, integral_indicator measurableSet_Ioc]

/-- Stein identity at leave-one-out basepoints (CGS form):
`E[W f_z(W)] = ∑_i E[∫ kernelDensityFwd(Xᵢ,t) f_z'(W⁽ⁱ⁾ + t) dt]`. -/
lemma stein_identity_sum_leaveOneOut
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (z : ℝ) :
    ∫ ω, sumX X ω * steinSolution z (sumX X ω) ∂μ =
      ∑ i : ι, ∫ ω, (∫ t : ℝ,
        kernelDensityFwd (X i ω) t *
          steinSolutionDeriv z (leaveOneOut X i ω + t)) ∂μ := by
  -- Same decomposition as `stein_identity_sum`, with forward kernel at W⁽ⁱ⁾
  have hpoint (ω : Ω) :
      sumX X ω * steinSolution z (sumX X ω) =
        ∑ i : ι, X i ω * (steinSolution z (sumX X ω) -
          steinSolution z (leaveOneOut X i ω)) +
        ∑ i : ι, X i ω * steinSolution z (leaveOneOut X i ω) := by
    have hsum1 :
        ∑ i : ι, X i ω * steinSolution z (sumX X ω) =
          sumX X ω * steinSolution z (sumX X ω) := by
      simp only [sumX, Finset.sum_mul]
    have hsum2 :
        ∑ i : ι, X i ω * (steinSolution z (sumX X ω) -
            steinSolution z (leaveOneOut X i ω)) +
          ∑ i : ι, X i ω * steinSolution z (leaveOneOut X i ω) =
        ∑ i : ι, X i ω * steinSolution z (sumX X ω) := by
      rw [← Finset.sum_add_distrib]
      congr 1; funext i; ring
    linarith [hsum1, hsum2]
  have hint1 (i : ι) :
      Integrable (fun ω =>
        X i ω * (steinSolution z (sumX X ω) - steinSolution z (leaveOneOut X i ω))) μ := by
    have hA : Integrable (fun ω => X i ω * steinSolution z (sumX X ω)) μ := by
      have hXi := (hX i).integrable one_le_two
      refine (hXi.abs.const_mul (sqrt (2 * π) / 2)).mono' ?_ ?_
      · exact (hXmeas i).aestronglyMeasurable.mul
          ((continuous_steinSolution z).comp_aestronglyMeasurable
            (measurable_sumX hXmeas).aestronglyMeasurable)
      · filter_upwards with ω
        have hf := abs_steinSolution_le_sqrt_two_pi_div_two z (sumX X ω)
        rw [Real.norm_eq_abs, abs_mul]
        calc
          |X i ω| * |steinSolution z (sumX X ω)| ≤ |X i ω| * (sqrt (2 * π) / 2) := by gcongr
          _ = (sqrt (2 * π) / 2) * |X i ω| := mul_comm _ _
    have hB : Integrable (fun ω => X i ω * steinSolution z (leaveOneOut X i ω)) μ := by
      have hXi := (hX i).integrable one_le_two
      refine (hXi.abs.const_mul (sqrt (2 * π) / 2)).mono' ?_ ?_
      · exact (hXmeas i).aestronglyMeasurable.mul
          ((continuous_steinSolution z).comp_aestronglyMeasurable
            (measurable_leaveOneOut hXmeas i).aestronglyMeasurable)
      · filter_upwards with ω
        have hf := abs_steinSolution_le_sqrt_two_pi_div_two z (leaveOneOut X i ω)
        rw [Real.norm_eq_abs, abs_mul]
        calc
          |X i ω| * |steinSolution z (leaveOneOut X i ω)| ≤
              |X i ω| * (sqrt (2 * π) / 2) := by gcongr
          _ = (sqrt (2 * π) / 2) * |X i ω| := mul_comm _ _
    have heq :
        (fun ω => X i ω * (steinSolution z (sumX X ω) -
          steinSolution z (leaveOneOut X i ω))) =
          fun ω => X i ω * steinSolution z (sumX X ω) -
            X i ω * steinSolution z (leaveOneOut X i ω) := by
      funext ω; ring
    rw [heq]; exact hA.sub hB
  have hint2 (i : ι) :
      Integrable (fun ω => X i ω * steinSolution z (leaveOneOut X i ω)) μ := by
    have hXi := (hX i).integrable one_le_two
    refine (hXi.abs.const_mul (sqrt (2 * π) / 2)).mono' ?_ ?_
    · exact (hXmeas i).aestronglyMeasurable.mul
        ((continuous_steinSolution z).comp_aestronglyMeasurable
          (measurable_leaveOneOut hXmeas i).aestronglyMeasurable)
    · filter_upwards with ω
      have hf := abs_steinSolution_le_sqrt_two_pi_div_two z (leaveOneOut X i ω)
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |X i ω| * |steinSolution z (leaveOneOut X i ω)| ≤
            |X i ω| * (sqrt (2 * π) / 2) := by gcongr
        _ = (sqrt (2 * π) / 2) * |X i ω| := mul_comm _ _
  have hsplit :
      ∫ ω, sumX X ω * steinSolution z (sumX X ω) ∂μ =
        ∑ i : ι, ∫ ω, X i ω * (steinSolution z (sumX X ω) -
          steinSolution z (leaveOneOut X i ω)) ∂μ +
        ∑ i : ι, ∫ ω, X i ω * steinSolution z (leaveOneOut X i ω) ∂μ := by
    have hfun :
        (fun ω => sumX X ω * steinSolution z (sumX X ω)) =
          fun ω => ∑ i : ι,
            (X i ω * (steinSolution z (sumX X ω) - steinSolution z (leaveOneOut X i ω)) +
              X i ω * steinSolution z (leaveOneOut X i ω)) := by
      funext ω
      calc
        sumX X ω * steinSolution z (sumX X ω)
            = ∑ i, X i ω * (steinSolution z (sumX X ω) -
                steinSolution z (leaveOneOut X i ω)) +
              ∑ i, X i ω * steinSolution z (leaveOneOut X i ω) := hpoint ω
        _ = ∑ i, (X i ω * (steinSolution z (sumX X ω) -
                steinSolution z (leaveOneOut X i ω)) +
              X i ω * steinSolution z (leaveOneOut X i ω)) := by
            rw [← Finset.sum_add_distrib]
    rw [hfun]
    have hint_sum (i : ι) :
        Integrable (fun ω =>
          X i ω * (steinSolution z (sumX X ω) - steinSolution z (leaveOneOut X i ω)) +
            X i ω * steinSolution z (leaveOneOut X i ω)) μ :=
      (hint1 i).add (hint2 i)
    rw [integral_finsetSum _ fun i _ => hint_sum i]
    have hterms :
        ∑ i : ι, ∫ ω,
            (X i ω * (steinSolution z (sumX X ω) - steinSolution z (leaveOneOut X i ω)) +
              X i ω * steinSolution z (leaveOneOut X i ω)) ∂μ =
          ∑ i : ι, (∫ ω, X i ω * (steinSolution z (sumX X ω) -
              steinSolution z (leaveOneOut X i ω)) ∂μ +
            ∫ ω, X i ω * steinSolution z (leaveOneOut X i ω) ∂μ) :=
      Finset.sum_congr rfl fun i _ => integral_add (hint1 i) (hint2 i)
    rw [hterms, Finset.sum_add_distrib]
  have h0 : ∑ i : ι, ∫ ω, X i ω * steinSolution z (leaveOneOut X i ω) ∂μ = 0 :=
    Finset.sum_eq_zero fun i _ =>
      integral_X_mul_steinSolution_leaveOneOut_eq_zero hXmeas h_indep h_mean i z
  rw [hsplit, h0, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  dsimp only
  have hW : sumX X ω = leaveOneOut X i ω + X i ω := leaveOneOut_add (X := X) i ω
  rw [hW]
  exact mul_steinSolution_add_eq_integral_kernelFwd z (leaveOneOut X i ω) (X i ω)

/-- On the support of `kernelDensityFwd`, `|t| ≤ |ξ|`. -/
lemma abs_t_le_abs_xi_of_mem_kernelDensityFwd {ξ t : ℝ}
    (h : kernelDensityFwd ξ t ≠ 0) : |t| ≤ |ξ| := by
  by_cases hξ : 0 ≤ ξ
  · have ht : t ∈ Icc 0 ξ := by
      by_contra hn
      exact h (by rw [kernelDensityFwd_eq_indicator_nonneg ξ hξ, indicator_of_notMem hn])
    rw [abs_of_nonneg hξ, abs_of_nonneg ht.1]
    exact ht.2
  · have hlt : ξ < 0 := lt_of_not_ge hξ
    have ht : t ∈ Ioc ξ 0 := by
      by_contra hn
      exact h (by rw [kernelDensityFwd_eq_indicator_neg ξ hlt, indicator_of_notMem hn])
    rw [abs_of_nonpos hlt.le, abs_of_nonpos ht.2]
    exact neg_le_neg_iff.mpr ht.1.le

/-- Integrated residual majorant: `∫ (|ξ| + |t|) K_fwd = (3/2)|ξ|³`. -/
lemma integral_abs_add_mul_kernelDensityFwd (ξ : ℝ) :
    ∫ t : ℝ, (|ξ| + |t|) * kernelDensityFwd ξ t = (3 / 2 : ℝ) * |ξ| ^ 3 := by
  have heq : (fun t => (|ξ| + |t|) * kernelDensityFwd ξ t) =
      fun t => |ξ| * kernelDensityFwd ξ t + |t| * kernelDensityFwd ξ t := by
    funext t; ring
  have hIntξ : Integrable (fun t => |ξ| * kernelDensityFwd ξ t) :=
    (integrable_kernelDensityFwd ξ).const_mul _
  have hIntt : Integrable (fun t => |t| * kernelDensityFwd ξ t) := by
    refine hIntξ.mono' ?_ ?_
    · exact measurable_id.abs.aestronglyMeasurable.mul
        (integrable_kernelDensityFwd ξ).aestronglyMeasurable
    · filter_upwards with t
      have hk := kernelDensityFwd_nonneg ξ t
      have hle : |t| * kernelDensityFwd ξ t ≤ |ξ| * kernelDensityFwd ξ t := by
        by_cases hzero : kernelDensityFwd ξ t = 0
        · simp [hzero]
        · exact mul_le_mul_of_nonneg_right
            (abs_t_le_abs_xi_of_mem_kernelDensityFwd hzero) hk
      simpa [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg hk,
        abs_of_nonneg (abs_nonneg ξ)] using hle
  rw [heq, integral_add hIntξ hIntt, integral_const_mul, integral_kernelDensityFwd,
    integral_abs_mul_kernelDensityFwd]
  calc
    |ξ| * ξ ^ 2 + |ξ| ^ 3 / 2 = |ξ| * |ξ| ^ 2 + |ξ| ^ 3 / 2 := by rw [sq_abs]
    _ = |ξ| ^ 3 + |ξ| ^ 3 / 2 := by ring
    _ = (3 / 2 : ℝ) * |ξ| ^ 3 := by ring

/-! ### Explicit constant and large-error branch -/

/-- The universal constant in the third-moment uniform Berry--Esseen bound. -/
def thirdMomentBerryEsseenConstant : ℝ := 30

lemma thirdMomentBerryEsseenConstant_pos : 0 < thirdMomentBerryEsseenConstant := by
  norm_num [thirdMomentBerryEsseenConstant]

omit [DecidableEq ι] in
/-- Large-error third-moment branch: if `γ ≥ 1/30` then `|F-Φ| ≤ 30 γ`. -/
lemma abs_cdf_sub_le_thirdMomentSum_of_large
    (hX : ∀ i, Measurable (X i))
    (x : ℝ)
    (hlarge : (1 : ℝ) / thirdMomentBerryEsseenConstant ≤ thirdMomentSum (X := X) μ) :
    |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤
      thirdMomentBerryEsseenConstant * thirdMomentSum (X := X) μ := by
  haveI : IsProbabilityMeasure (μ.map fun ω ↦ ∑ i, X i ω) :=
    isProbabilityMeasure_map_sumX (μ := μ) (X := X) fun i => (hX i).aemeasurable
  have h1 : |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤ 1 :=
    abs_cdf_sub_le_one _ _ x
  have hC : (0 : ℝ) ≤ thirdMomentBerryEsseenConstant :=
    thirdMomentBerryEsseenConstant_pos.le
  have hge : (1 : ℝ) ≤ thirdMomentBerryEsseenConstant * thirdMomentSum (X := X) μ := by
    have : thirdMomentBerryEsseenConstant * (1 / thirdMomentBerryEsseenConstant) = 1 := by
      field_simp [thirdMomentBerryEsseenConstant]
    calc
      (1 : ℝ) = thirdMomentBerryEsseenConstant * (1 / thirdMomentBerryEsseenConstant) :=
        this.symm
      _ ≤ thirdMomentBerryEsseenConstant * thirdMomentSum (X := X) μ :=
            mul_le_mul_of_nonneg_left hlarge hC
  exact h1.trans hge

/-! ### Residual majorant under independence -/

/-- Residual majorant for one leave-one-out summand under independence. -/
lemma expected_residual_majorant_one
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (i : ι) :
    ∫ ω, (2 * |leaveOneOut X i ω| + sqrt (2 * π) / 2) *
        ((3 : ℝ) / 2) * |X i ω| ^ 3 ∂μ ≤
      (2 + sqrt (2 * π) / 2) * ((3 : ℝ) / 2) * ∫ ω, |X i ω| ^ 3 ∂μ := by
  set M : ℝ := sqrt (2 * π) / 2
  have hWabs := integral_abs_leaveOneOut_le_one hX h_indep h_mean hvar i
  have hInd := indepFun_leaveOneOut (X := X) (μ := μ) hXmeas h_indep i
  have hIntW : Integrable (fun ω => |leaveOneOut X i ω|) μ :=
    ((memLp_leaveOneOut hX i).integrable one_le_two).abs
  have hIntX3 : Integrable (fun ω => |X i ω| ^ 3) μ := h3 i
  have hindep_abs :
      IndepFun (fun ω => |leaveOneOut X i ω|) (fun ω => |X i ω| ^ 3) μ :=
    hInd.comp measurable_id.abs (measurable_id.abs.pow_const 3)
  have hprod :
      ∫ ω, |leaveOneOut X i ω| * |X i ω| ^ 3 ∂μ =
        (∫ ω, |leaveOneOut X i ω| ∂μ) * (∫ ω, |X i ω| ^ 3 ∂μ) :=
    hindep_abs.integral_mul_eq_mul_integral hIntW.aestronglyMeasurable
      hIntX3.aestronglyMeasurable
  have hInt_prod : Integrable (fun ω => |leaveOneOut X i ω| * |X i ω| ^ 3) μ :=
    hindep_abs.integrable_mul hIntW hIntX3
  -- Integrand = 3 * |W'| * |X|³ + (3/2) M |X|³
  have heq :
      (fun ω => (2 * |leaveOneOut X i ω| + M) * ((3 : ℝ) / 2) * |X i ω| ^ 3) =
        fun ω => (3 : ℝ) * (|leaveOneOut X i ω| * |X i ω| ^ 3) +
          ((3 : ℝ) / 2 * M) * |X i ω| ^ 3 := by
    funext ω; ring
  rw [heq]
  have hInt1 : Integrable (fun ω => (3 : ℝ) * (|leaveOneOut X i ω| * |X i ω| ^ 3)) μ :=
    hInt_prod.const_mul 3
  have hInt2 : Integrable (fun ω => ((3 : ℝ) / 2 * M) * |X i ω| ^ 3) μ :=
    hIntX3.const_mul _
  rw [integral_add hInt1 hInt2, integral_const_mul, integral_const_mul, hprod]
  set EX3 := ∫ ω, |X i ω| ^ 3 ∂μ
  set EW := ∫ ω, |leaveOneOut X i ω| ∂μ
  -- Goal: 3 * EW * EX3 + (3/2 * M) * EX3 ≤ (2 + M) * (3/2) * EX3
  have hmain : (3 : ℝ) * EW * EX3 + (3 / 2 * M) * EX3 ≤ (2 + M) * (3 / 2) * EX3 := by
    have hEX0 : 0 ≤ EX3 := integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _
    have hEW0 : 0 ≤ EW := integral_nonneg fun _ => abs_nonneg _
    have hle : (3 : ℝ) * EW + 3 / 2 * M ≤ (2 + M) * (3 / 2) := by
      have : EW ≤ (1 : ℝ) := hWabs
      nlinarith
    calc
      (3 : ℝ) * EW * EX3 + (3 / 2 * M) * EX3
          = ((3 : ℝ) * EW + 3 / 2 * M) * EX3 := by ring
      _ ≤ ((2 + M) * (3 / 2)) * EX3 := mul_le_mul_of_nonneg_right hle hEX0
      _ = (2 + M) * (3 / 2) * EX3 := by ring
  convert hmain using 1
  all_goals ring

lemma sum_expected_residual_majorant_le
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ) :
    ∑ i : ι, ∫ ω, (2 * |leaveOneOut X i ω| + sqrt (2 * π) / 2) *
        ((3 : ℝ) / 2) * |X i ω| ^ 3 ∂μ ≤
      (2 + sqrt (2 * π) / 2) * ((3 : ℝ) / 2) * thirdMomentSum (X := X) μ := by
  refine (Finset.sum_le_sum fun i _ =>
    expected_residual_majorant_one hX hXmeas h_indep h_mean hvar h3 i).trans_eq ?_
  simp only [thirdMomentSum, Finset.mul_sum]

/-! ### Pointwise Stein expansion under the forward kernel -/

lemma measurable_kernelDensityFwd_right (ξ : ℝ) : Measurable (kernelDensityFwd ξ) := by
  by_cases hξ : 0 ≤ ξ
  · rw [kernelDensityFwd_eq_indicator_nonneg ξ hξ]
    exact measurable_const.indicator measurableSet_Icc
  · have hlt : ξ < 0 := lt_of_not_ge hξ
    rw [kernelDensityFwd_eq_indicator_neg ξ hlt]
    exact measurable_const.indicator measurableSet_Ioc

/-- Integrability of `K · g` when `|g| ≤ C`. -/
lemma integrable_kernelDensityFwd_mul_of_abs_le (ξ : ℝ) (C : ℝ) {g : ℝ → ℝ}
    (_hC : 0 ≤ C) (hg : ∀ t, |g t| ≤ C) (hg_m : Measurable g) :
    Integrable (fun t => kernelDensityFwd ξ t * g t) := by
  have hdom : Integrable (fun t => C * kernelDensityFwd ξ t) :=
    (integrable_kernelDensityFwd ξ).const_mul C
  refine hdom.mono' ?_ ?_
  · exact ((measurable_kernelDensityFwd_right ξ).mul hg_m).aestronglyMeasurable
  · filter_upwards with t
    have hk := kernelDensityFwd_nonneg ξ t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
    calc
      kernelDensityFwd ξ t * |g t| ≤ kernelDensityFwd ξ t * C := by gcongr; exact hg t
      _ = C * kernelDensityFwd ξ t := mul_comm _ _

lemma integrable_kernelDensityFwd_mul_steinSolutionDeriv (z W' ξ : ℝ) :
    Integrable (fun t => kernelDensityFwd ξ t * steinSolutionDeriv z (W' + t)) :=
  integrable_kernelDensityFwd_mul_of_abs_le ξ 2 (by norm_num)
    (fun t => abs_steinSolutionDeriv_le_two z (W' + t))
    ((measurable_steinSolutionDeriv z).comp (measurable_const.add measurable_id))

lemma integrable_kernelDensityFwd_mul_mul_steinSolution (z W' ξ : ℝ) :
    Integrable (fun t =>
      kernelDensityFwd ξ t * ((W' + t) * steinSolution z (W' + t))) :=
  integrable_kernelDensityFwd_mul_of_abs_le ξ 1 (by norm_num)
    (fun t => by simpa [abs_mul] using abs_mul_steinSolution_le_one z (W' + t))
    ((measurable_const.add measurable_id).mul
      ((continuous_steinSolution z).measurable.comp (measurable_const.add measurable_id)))

lemma integrable_kernelDensityFwd_mul_indicator_le (z W' ξ : ℝ) :
    Integrable (fun t =>
      kernelDensityFwd ξ t * (if W' + t ≤ z then (1 : ℝ) else 0)) :=
  integrable_kernelDensityFwd_mul_of_abs_le ξ 1 (by norm_num)
    (fun t => by split_ifs <;> norm_num)
    (Measurable.ite (measurableSet_le (measurable_const.add measurable_id) measurable_const)
      measurable_const measurable_const)

lemma integrable_kernelDensityFwd_mul_steinIntegrand (z W' ξ : ℝ) :
    Integrable (fun t => kernelDensityFwd ξ t * steinIntegrand z (W' + t)) :=
  integrable_kernelDensityFwd_mul_of_abs_le ξ 1 (by norm_num)
    (fun t => steinIntegrand_abs_le z (W' + t))
    ((measurable_steinIntegrand z).comp (measurable_const.add measurable_id))

/-- Pointwise Stein expansion under the forward kernel:
`∫ K f' = ∫ K (W'+t)f + ∫ K 1_{W'+t≤z} − Φ · ξ²`. -/
lemma integral_kernelFwd_mul_steinSolutionDeriv_expand (z W' ξ : ℝ) :
    ∫ t : ℝ, kernelDensityFwd ξ t * steinSolutionDeriv z (W' + t) =
      (∫ t : ℝ, kernelDensityFwd ξ t * ((W' + t) * steinSolution z (W' + t))) +
      (∫ t : ℝ, kernelDensityFwd ξ t * (if W' + t ≤ z then (1 : ℝ) else 0)) -
      cdf (gaussianReal 0 1) z * ξ ^ 2 := by
  have hIntA := integrable_kernelDensityFwd_mul_mul_steinSolution z W' ξ
  have hIntS := integrable_kernelDensityFwd_mul_steinIntegrand z W' ξ
  have hIntInd := integrable_kernelDensityFwd_mul_indicator_le z W' ξ
  have hΦ : Integrable (fun t => cdf (gaussianReal 0 1) z * kernelDensityFwd ξ t) :=
    (integrable_kernelDensityFwd ξ).const_mul _
  have hfun :
      (fun t => kernelDensityFwd ξ t * steinSolutionDeriv z (W' + t)) =
        fun t => kernelDensityFwd ξ t * ((W' + t) * steinSolution z (W' + t)) +
          kernelDensityFwd ξ t * steinIntegrand z (W' + t) := by
    funext t
    rw [steinSolutionDeriv_eq, mul_add]
  have hS :
      (fun t => kernelDensityFwd ξ t * steinIntegrand z (W' + t)) =
        fun t => kernelDensityFwd ξ t * (if W' + t ≤ z then (1 : ℝ) else 0) -
          cdf (gaussianReal 0 1) z * kernelDensityFwd ξ t := by
    funext t
    simp only [steinIntegrand, mul_sub, mul_comm (cdf _ _)]
  rw [hfun, integral_add hIntA hIntS, hS, integral_sub hIntInd hΦ, integral_const_mul,
    integral_kernelDensityFwd]
  ring

/-- Dominating integrability for the residual majorant in `t`. -/
lemma integrable_abs_add_mul_kernelDensityFwd (ξ : ℝ) :
    Integrable (fun t => (|ξ| + |t|) * kernelDensityFwd ξ t) := by
  have h1 : Integrable (fun t => |ξ| * kernelDensityFwd ξ t) :=
    (integrable_kernelDensityFwd ξ).const_mul _
  have h2 : Integrable (fun t => |t| * kernelDensityFwd ξ t) := by
    refine h1.mono' ?_ ?_
    · exact measurable_id.abs.aestronglyMeasurable.mul
        (integrable_kernelDensityFwd ξ).aestronglyMeasurable
    · filter_upwards with t
      have hk := kernelDensityFwd_nonneg ξ t
      have hle : |t| * kernelDensityFwd ξ t ≤ |ξ| * kernelDensityFwd ξ t := by
        by_cases hz : kernelDensityFwd ξ t = 0
        · simp [hz]
        · exact mul_le_mul_of_nonneg_right
            (abs_t_le_abs_xi_of_mem_kernelDensityFwd hz) hk
      simpa [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg hk,
        abs_of_nonneg (abs_nonneg ξ)] using hle
  have heq : (fun t => (|ξ| + |t|) * kernelDensityFwd ξ t) =
      fun t => |ξ| * kernelDensityFwd ξ t + |t| * kernelDensityFwd ξ t := by
    funext t; ring
  rw [heq]; exact h1.add h2

/-- Integrated residual bound (pointwise in `(W', ξ)`):
`|∫ ((W'+ξ)f − (W'+t)f) K dt| ≤ (2|W'| + √(2π)/2) · (3/2) |ξ|³`. -/
lemma abs_integral_residual_kernelFwd_le (z W' ξ : ℝ) :
    |∫ t : ℝ, kernelDensityFwd ξ t *
        ((W' + ξ) * steinSolution z (W' + ξ) -
          (W' + t) * steinSolution z (W' + t))| ≤
      (2 * |W'| + sqrt (2 * π) / 2) * ((3 : ℝ) / 2) * |ξ| ^ 3 := by
  set M : ℝ := sqrt (2 * π) / 2
  set g : ℝ → ℝ := fun t =>
    (W' + ξ) * steinSolution z (W' + ξ) - (W' + t) * steinSolution z (W' + t)
  have hK0 := kernelDensityFwd_nonneg (ξ := ξ)
  have hgm : Measurable g :=
    measurable_const.sub
      ((measurable_const.add measurable_id).mul
        ((continuous_steinSolution z).measurable.comp (measurable_const.add measurable_id)))
  have hg_le : ∀ t, |g t| ≤ (2 * |W'| + M) * (|ξ| + |t|) := fun t =>
    abs_mul_steinSolution_sub_le z W' ξ t
  have hInt_maj : Integrable (fun t =>
      (2 * |W'| + M) * ((|ξ| + |t|) * kernelDensityFwd ξ t)) :=
    (integrable_abs_add_mul_kernelDensityFwd ξ).const_mul _
  have hInt : Integrable (fun t => kernelDensityFwd ξ t * g t) := by
    refine hInt_maj.mono' ?_ ?_
    · exact ((measurable_kernelDensityFwd_right ξ).mul hgm).aestronglyMeasurable
    · filter_upwards with t
      have hk := hK0 t
      have hb := hg_le t
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
      calc
        kernelDensityFwd ξ t * |g t| ≤
            kernelDensityFwd ξ t * ((2 * |W'| + M) * (|ξ| + |t|)) := by gcongr
        _ = (2 * |W'| + M) * ((|ξ| + |t|) * kernelDensityFwd ξ t) := by ring
  have hstep :
      ∫ t, |kernelDensityFwd ξ t * g t| ≤
        ∫ t, (2 * |W'| + M) * ((|ξ| + |t|) * kernelDensityFwd ξ t) := by
    refine integral_mono hInt.abs hInt_maj fun t => ?_
    have hk := hK0 t
    have hb := hg_le t
    rw [abs_mul, abs_of_nonneg hk]
    calc
      kernelDensityFwd ξ t * |g t| ≤
          kernelDensityFwd ξ t * ((2 * |W'| + M) * (|ξ| + |t|)) := by gcongr
      _ = (2 * |W'| + M) * ((|ξ| + |t|) * kernelDensityFwd ξ t) := by ring
  have hval :
      ∫ t, (2 * |W'| + M) * ((|ξ| + |t|) * kernelDensityFwd ξ t) =
        (2 * |W'| + M) * ((3 : ℝ) / 2 * |ξ| ^ 3) := by
    rw [integral_const_mul, integral_abs_add_mul_kernelDensityFwd]
  calc
    |∫ t, kernelDensityFwd ξ t * g t| ≤ ∫ t, |kernelDensityFwd ξ t * g t| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t, (2 * |W'| + M) * ((|ξ| + |t|) * kernelDensityFwd ξ t) := hstep
    _ = (2 * |W'| + M) * ((3 : ℝ) / 2 * |ξ| ^ 3) := hval
    _ = (2 * |W'| + M) * ((3 : ℝ) / 2) * |ξ| ^ 3 := by ring

/-- Residual majorant coefficient: `(3/2)(2 + √(2π)/2) ≤ 6`. -/
lemma residualMajorantCoeff_le_six :
    (2 + sqrt (2 * π) / 2) * ((3 : ℝ) / 2) ≤ 6 := by
  have hsq : sqrt (2 * π) ≤ 4 := by
    have h2π : (2 * π : ℝ) ≤ 16 := by
      have : (π : ℝ) ≤ 8 := (pi_le_four).trans (by norm_num)
      nlinarith
    have h := sqrt_le_sqrt h2π
    have : sqrt (16 : ℝ) = 4 := by norm_num
    rwa [this] at h
  nlinarith [hsq]



/-! ### Expected forward kernels (deterministic CGS kernels) -/

/-- Joint measurability of `(ξ, t) ↦ kernelDensityFwd ξ t`. -/
lemma measurable_uncurry_kernelDensityFwd :
    Measurable (Function.uncurry kernelDensityFwd) := by
  have hfun :
      Function.uncurry kernelDensityFwd =
        fun p : ℝ × ℝ =>
          if 0 ≤ p.1 then
            (if p.2 ∈ Icc 0 p.1 then p.1 else 0)
          else
            (if p.2 ∈ Ioc p.1 0 then -p.1 else 0) := by
    funext p
    simp only [Function.uncurry, kernelDensityFwd]
  rw [hfun]
  have hIcc : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Icc 0 p.1} := by
    have : {p : ℝ × ℝ | p.2 ∈ Icc 0 p.1} = {p | 0 ≤ p.2} ∩ {p | p.2 ≤ p.1} := by
      ext p; simp [mem_Icc, and_comm]
    rw [this]
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have hIoc : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Ioc p.1 0} := by
    have : {p : ℝ × ℝ | p.2 ∈ Ioc p.1 0} = {p | p.1 < p.2} ∩ {p | p.2 ≤ 0} := by
      ext p; simp [mem_Ioc]
    rw [this]
    exact (measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  refine Measurable.ite (measurableSet_le measurable_const measurable_fst) ?_ ?_
  · exact Measurable.ite hIcc measurable_fst measurable_const
  · exact Measurable.ite hIoc measurable_fst.neg measurable_const

lemma measurable_kernelDensityFwd_left (t : ℝ) : Measurable (fun ξ => kernelDensityFwd ξ t) :=
  measurable_uncurry_kernelDensityFwd.comp (measurable_id.prodMk measurable_const)

/-- Expected forward Stein kernel `Khat_i(t) = E[kernelDensityFwd(Xᵢ, t)]`. -/
noncomputable def expectedKernelFwd (i : ι) (t : ℝ) : ℝ :=
  ∫ ω, kernelDensityFwd (X i ω) t ∂μ

omit [Fintype ι] [IsProbabilityMeasure μ] [DecidableEq ι] in
lemma expectedKernelFwd_nonneg (i : ι) (t : ℝ) :
    0 ≤ expectedKernelFwd (X := X) (μ := μ) i t :=
  integral_nonneg fun _ => kernelDensityFwd_nonneg _ _

omit [Fintype ι] [DecidableEq ι] in
lemma measurable_kernelDensityFwd_pair (i : ι) (hXmeas : Measurable (X i)) :
    Measurable fun p : Ω × ℝ => kernelDensityFwd (X i p.1) p.2 :=
  measurable_uncurry_kernelDensityFwd.comp
    ((hXmeas.comp measurable_fst).prodMk measurable_snd)

omit [Fintype ι] [IsProbabilityMeasure μ] [DecidableEq ι] in
/-- The uncurry `(ω, t) ↦ K(Xᵢ(ω), t)` is integrable on `μ.prod volume`. -/
lemma integrable_uncurry_kernelDensityFwd (i : ι)
    (hX : MemLp (X i) 2 μ) (hXmeas : Measurable (X i)) :
    Integrable (fun p : Ω × ℝ => kernelDensityFwd (X i p.1) p.2) (μ.prod volume) := by
  have hsm : AEStronglyMeasurable
      (fun p : Ω × ℝ => kernelDensityFwd (X i p.1) p.2) (μ.prod volume) :=
    (measurable_kernelDensityFwd_pair i hXmeas).aestronglyMeasurable
  rw [integrable_prod_iff hsm]
  constructor
  · exact Eventually.of_forall fun ω => integrable_kernelDensityFwd (X i ω)
  · have heq :
        (fun ω => ∫ t : ℝ, ‖kernelDensityFwd (X i ω) t‖) =
          fun ω => (X i ω) ^ 2 := by
      funext ω
      have hnn : ∀ t, 0 ≤ kernelDensityFwd (X i ω) t := kernelDensityFwd_nonneg _
      have habs :
          (fun t => ‖kernelDensityFwd (X i ω) t‖) =
            fun t => kernelDensityFwd (X i ω) t :=
        funext fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hnn t)]
      rw [habs, integral_kernelDensityFwd]
    rw [heq]
    exact hX.integrable_sq

omit [Fintype ι] [DecidableEq ι] in
lemma integral_expectedKernelFwd (i : ι)
    (hX : MemLp (X i) 2 μ) (hXmeas : Measurable (X i)) :
    ∫ t : ℝ, expectedKernelFwd (X := X) (μ := μ) i t =
      ∫ ω, (X i ω) ^ 2 ∂μ := by
  have hInt := integrable_uncurry_kernelDensityFwd i hX hXmeas
  have hswap := integral_prod_symm (μ := μ) (ν := volume)
      (fun p : Ω × ℝ => kernelDensityFwd (X i p.1) p.2) hInt
  have hleft :
      ∫ ω, (∫ t : ℝ, kernelDensityFwd (X i ω) t) ∂μ =
        ∫ ω, (X i ω) ^ 2 ∂μ :=
    integral_congr_ae (Eventually.of_forall fun ω => integral_kernelDensityFwd (X i ω))
  have hprod := integral_prod
      (fun p : Ω × ℝ => kernelDensityFwd (X i p.1) p.2) hInt
  calc
    ∫ t, expectedKernelFwd (X := X) (μ := μ) i t
        = ∫ t, (∫ ω, kernelDensityFwd (X i ω) t ∂μ) := rfl
    _ = ∫ p : Ω × ℝ, kernelDensityFwd (X i p.1) p.2 ∂(μ.prod volume) := by
          rw [← hswap]
    _ = ∫ ω, (∫ t, kernelDensityFwd (X i ω) t) ∂μ := hprod
    _ = ∫ ω, (X i ω) ^ 2 ∂μ := hleft

omit [DecidableEq ι] in
lemma sum_integral_expectedKernelFwd_eq_one
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1) :
    ∑ i : ι, ∫ t : ℝ, expectedKernelFwd (X := X) (μ := μ) i t = 1 := by
  have h : ∑ i : ι, ∫ t : ℝ, expectedKernelFwd (X := X) (μ := μ) i t =
      ∑ i : ι, ∫ ω, (X i ω) ^ 2 ∂μ :=
    Finset.sum_congr rfl fun i _ => integral_expectedKernelFwd i (hX i) (hXmeas i)
  rw [h, sum_integral_sq_eq_one hX h_mean hvar]

omit [Fintype ι] [IsProbabilityMeasure μ] [DecidableEq ι] in
/-- Product-space integrability of residual majorant weight `(|ξ|+|t|)K`. -/
lemma integrable_uncurry_abs_add_mul_kernel (i : ι)
    (_hX : MemLp (X i) 2 μ) (h3 : Integrable (fun ω => |X i ω| ^ 3) μ)
    (hXmeas : Measurable (X i)) :
    Integrable (fun p : Ω × ℝ =>
      (|X i p.1| + |p.2|) * kernelDensityFwd (X i p.1) p.2) (μ.prod volume) := by
  have hsm : AEStronglyMeasurable
      (fun p : Ω × ℝ => (|X i p.1| + |p.2|) * kernelDensityFwd (X i p.1) p.2)
      (μ.prod volume) :=
    ((((hXmeas.comp measurable_fst).abs.add measurable_snd.abs).mul
      (measurable_kernelDensityFwd_pair i hXmeas))).aestronglyMeasurable
  rw [integrable_prod_iff hsm]
  constructor
  · exact Eventually.of_forall fun ω => integrable_abs_add_mul_kernelDensityFwd (X i ω)
  · have heq :
        (fun ω => ∫ t : ℝ, ‖(|X i ω| + |t|) * kernelDensityFwd (X i ω) t‖) =
          fun ω => (3 / 2 : ℝ) * |X i ω| ^ 3 := by
      funext ω
      have hnn : ∀ t, 0 ≤ (|X i ω| + |t|) * kernelDensityFwd (X i ω) t := fun t =>
        mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (kernelDensityFwd_nonneg _ _)
      have habs :
          (fun t => ‖(|X i ω| + |t|) * kernelDensityFwd (X i ω) t‖) =
            fun t => (|X i ω| + |t|) * kernelDensityFwd (X i ω) t :=
        funext fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hnn t)]
      rw [habs, integral_abs_add_mul_kernelDensityFwd]
    rw [heq]
    exact h3.const_mul _


/-! ### Residual masses and integrability -/

/-- Leave-one-out kernel integral of `f'`: equals `Xᵢ(f(W)-f(W⁽ⁱ⁾))`. -/
noncomputable def leaveOneOutKernelDerivIntegral (z : ℝ) (i : ι) (ω : Ω) : ℝ :=
  ∫ t : ℝ, kernelDensityFwd (X i ω) t *
    steinSolutionDeriv z (leaveOneOut X i ω + t)

omit [MeasurableSpace Ω] in
lemma leaveOneOutKernelDerivIntegral_eq (z : ℝ) (i : ι) (ω : Ω) :
    leaveOneOutKernelDerivIntegral (X := X) z i ω =
      X i ω * (steinSolution z (sumX X ω) - steinSolution z (leaveOneOut X i ω)) := by
  have hW : sumX X ω = leaveOneOut X i ω + X i ω := leaveOneOut_add (X := X) i ω
  simp only [leaveOneOutKernelDerivIntegral]
  have h := mul_steinSolution_add_eq_integral_kernelFwd z (leaveOneOut X i ω) (X i ω)
  rw [← h, hW]

lemma integrable_leaveOneOutKernelDerivIntegral
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (z : ℝ) (i : ι) :
    Integrable (leaveOneOutKernelDerivIntegral (X := X) z i) μ := by
  have heq : leaveOneOutKernelDerivIntegral (X := X) z i =
      fun ω => X i ω * (steinSolution z (sumX X ω) - steinSolution z (leaveOneOut X i ω)) :=
    funext fun ω => leaveOneOutKernelDerivIntegral_eq z i ω
  rw [heq]
  have hA : Integrable (fun ω => X i ω * steinSolution z (sumX X ω)) μ := by
    have hXi := (hX i).integrable one_le_two
    refine (hXi.abs.const_mul (sqrt (2 * π) / 2)).mono' ?_ ?_
    · exact (hXmeas i).aestronglyMeasurable.mul
        ((continuous_steinSolution z).comp_aestronglyMeasurable
          (measurable_sumX hXmeas).aestronglyMeasurable)
    · filter_upwards with ω
      have hf := abs_steinSolution_le_sqrt_two_pi_div_two z (sumX X ω)
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |X i ω| * |steinSolution z (sumX X ω)| ≤ |X i ω| * (sqrt (2 * π) / 2) := by gcongr
        _ = (sqrt (2 * π) / 2) * |X i ω| := mul_comm _ _
  have hB : Integrable (fun ω => X i ω * steinSolution z (leaveOneOut X i ω)) μ := by
    have hXi := (hX i).integrable one_le_two
    refine (hXi.abs.const_mul (sqrt (2 * π) / 2)).mono' ?_ ?_
    · exact (hXmeas i).aestronglyMeasurable.mul
        ((continuous_steinSolution z).comp_aestronglyMeasurable
          (measurable_leaveOneOut hXmeas i).aestronglyMeasurable)
    · filter_upwards with ω
      have hf := abs_steinSolution_le_sqrt_two_pi_div_two z (leaveOneOut X i ω)
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |X i ω| * |steinSolution z (leaveOneOut X i ω)| ≤
            |X i ω| * (sqrt (2 * π) / 2) := by gcongr
        _ = (sqrt (2 * π) / 2) * |X i ω| := mul_comm _ _
  have hfun :
      (fun ω => X i ω * (steinSolution z (sumX X ω) - steinSolution z (leaveOneOut X i ω))) =
        fun ω => X i ω * steinSolution z (sumX X ω) -
          X i ω * steinSolution z (leaveOneOut X i ω) := by
    funext ω; ring
  rw [hfun]; exact hA.sub hB

/-- Kernel-smoothed indicator mass (leave-one-out). -/
noncomputable def kernelIndicatorMass (z : ℝ) (i : ι) (ω : Ω) : ℝ :=
  ∫ t : ℝ, kernelDensityFwd (X i ω) t *
    (if leaveOneOut X i ω + t ≤ z then (1 : ℝ) else 0)

/-- Kernel-smoothed Stein product mass (leave-one-out). -/
noncomputable def kernelSteinProductMass (z : ℝ) (i : ι) (ω : Ω) : ℝ :=
  ∫ t : ℝ, kernelDensityFwd (X i ω) t *
    ((leaveOneOut X i ω + t) * steinSolution z (leaveOneOut X i ω + t))

omit [MeasurableSpace Ω] in
lemma kernel_masses_of_expand (z : ℝ) (i : ι) (ω : Ω) :
    leaveOneOutKernelDerivIntegral (X := X) z i ω =
      kernelSteinProductMass (X := X) z i ω + kernelIndicatorMass (X := X) z i ω -
        cdf (gaussianReal 0 1) z * (X i ω) ^ 2 := by
  simpa [leaveOneOutKernelDerivIntegral, kernelSteinProductMass, kernelIndicatorMass] using
    integral_kernelFwd_mul_steinSolutionDeriv_expand z (leaveOneOut X i ω) (X i ω)

omit [MeasurableSpace Ω] in
lemma abs_kernelSteinProductMass_le (z : ℝ) (i : ι) (ω : Ω) :
    |kernelSteinProductMass (X := X) z i ω| ≤ (X i ω) ^ 2 := by
  have hInt := integrable_kernelDensityFwd_mul_mul_steinSolution z
    (leaveOneOut X i ω) (X i ω)
  have hstep :
      ∫ t, |kernelDensityFwd (X i ω) t *
          ((leaveOneOut X i ω + t) * steinSolution z (leaveOneOut X i ω + t))| ≤
        ∫ t, kernelDensityFwd (X i ω) t := by
    refine integral_mono hInt.abs (integrable_kernelDensityFwd (X i ω)) fun t => ?_
    have hk := kernelDensityFwd_nonneg (X i ω) t
    have hw := abs_mul_steinSolution_le_one z (leaveOneOut X i ω + t)
    rw [abs_mul, abs_of_nonneg hk]
    have hwf : |(leaveOneOut X i ω + t) * steinSolution z (leaveOneOut X i ω + t)| ≤ 1 := by
      simpa [abs_mul] using hw
    calc
      kernelDensityFwd (X i ω) t *
          |(leaveOneOut X i ω + t) * steinSolution z (leaveOneOut X i ω + t)| ≤
        kernelDensityFwd (X i ω) t * 1 := mul_le_mul_of_nonneg_left hwf hk
      _ = kernelDensityFwd (X i ω) t := mul_one _
  calc
    |kernelSteinProductMass (X := X) z i ω|
        ≤ ∫ t, |kernelDensityFwd (X i ω) t *
            ((leaveOneOut X i ω + t) * steinSolution z (leaveOneOut X i ω + t))| := by
          simpa [kernelSteinProductMass] using
            (abs_integral_le_integral_abs :
              |∫ t, kernelDensityFwd (X i ω) t *
                ((leaveOneOut X i ω + t) * steinSolution z (leaveOneOut X i ω + t))| ≤ _)
    _ ≤ ∫ t, kernelDensityFwd (X i ω) t := hstep
    _ = (X i ω) ^ 2 := integral_kernelDensityFwd _

omit [MeasurableSpace Ω] in
lemma abs_kernelIndicatorMass_le (z : ℝ) (i : ι) (ω : Ω) :
    |kernelIndicatorMass (X := X) z i ω| ≤ (X i ω) ^ 2 := by
  have hInt := integrable_kernelDensityFwd_mul_indicator_le z
    (leaveOneOut X i ω) (X i ω)
  have hstep :
      ∫ t, |kernelDensityFwd (X i ω) t *
          (if leaveOneOut X i ω + t ≤ z then (1 : ℝ) else 0)| ≤
        ∫ t, kernelDensityFwd (X i ω) t := by
    refine integral_mono hInt.abs (integrable_kernelDensityFwd (X i ω)) fun t => ?_
    have hk := kernelDensityFwd_nonneg (X i ω) t
    rw [abs_mul, abs_of_nonneg hk]
    split_ifs <;> simp [hk]
  calc
    |kernelIndicatorMass (X := X) z i ω|
        ≤ ∫ t, |kernelDensityFwd (X i ω) t *
            (if leaveOneOut X i ω + t ≤ z then (1 : ℝ) else 0)| := by
          simpa [kernelIndicatorMass] using
            (abs_integral_le_integral_abs :
              |∫ t, kernelDensityFwd (X i ω) t *
                (if leaveOneOut X i ω + t ≤ z then (1 : ℝ) else 0)| ≤ _)
    _ ≤ ∫ t, kernelDensityFwd (X i ω) t := hstep
    _ = (X i ω) ^ 2 := integral_kernelDensityFwd _

omit [IsProbabilityMeasure μ] in
lemma integrable_kernelSteinProductMass
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (z : ℝ) (i : ι) :
    Integrable (kernelSteinProductMass (X := X) z i) μ := by
  have hdom := (hX i).integrable_sq
  have huncurry_int : Integrable
      (fun p : Ω × ℝ => kernelDensityFwd (X i p.1) p.2 *
        ((leaveOneOut X i p.1 + p.2) *
          steinSolution z (leaveOneOut X i p.1 + p.2))) (μ.prod volume) := by
    have hK := integrable_uncurry_kernelDensityFwd i (hX i) (hXmeas i)
    have hsm : AEStronglyMeasurable
        (fun p : Ω × ℝ => kernelDensityFwd (X i p.1) p.2 *
          ((leaveOneOut X i p.1 + p.2) *
            steinSolution z (leaveOneOut X i p.1 + p.2))) (μ.prod volume) := by
      refine ((measurable_kernelDensityFwd_pair i (hXmeas i)).mul ?_).aestronglyMeasurable
      exact ((measurable_leaveOneOut hXmeas i |>.comp measurable_fst).add measurable_snd).mul
        ((continuous_steinSolution z).measurable.comp
          ((measurable_leaveOneOut hXmeas i |>.comp measurable_fst).add measurable_snd))
    refine hK.mono' hsm ?_
    filter_upwards with p
    have hk := kernelDensityFwd_nonneg (X i p.1) p.2
    have hw := abs_mul_steinSolution_le_one z (leaveOneOut X i p.1 + p.2)
    have hwf : |(leaveOneOut X i p.1 + p.2) * steinSolution z (leaveOneOut X i p.1 + p.2)| ≤ 1 := by
      simpa [abs_mul] using hw
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
    calc
      kernelDensityFwd (X i p.1) p.2 *
          |(leaveOneOut X i p.1 + p.2) * steinSolution z (leaveOneOut X i p.1 + p.2)| ≤
        kernelDensityFwd (X i p.1) p.2 * 1 := mul_le_mul_of_nonneg_left hwf hk
      _ = kernelDensityFwd (X i p.1) p.2 := mul_one _
  -- `integral_prod_left`: ω ↦ ∫_t f(ω,t) is integrable
  exact huncurry_int.integral_prod_left

omit [IsProbabilityMeasure μ] in
lemma integrable_kernelIndicatorMass
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (z : ℝ) (i : ι) :
    Integrable (kernelIndicatorMass (X := X) z i) μ := by
  have hK := integrable_uncurry_kernelDensityFwd i (hX i) (hXmeas i)
  have hsm : AEStronglyMeasurable
      (fun p : Ω × ℝ => kernelDensityFwd (X i p.1) p.2 *
        (if leaveOneOut X i p.1 + p.2 ≤ z then (1 : ℝ) else 0)) (μ.prod volume) := by
    refine ((measurable_kernelDensityFwd_pair i (hXmeas i)).mul ?_).aestronglyMeasurable
    exact Measurable.ite
      (measurableSet_le
        ((measurable_leaveOneOut hXmeas i |>.comp measurable_fst).add measurable_snd)
        measurable_const)
      measurable_const measurable_const
  have huncurry_int : Integrable
      (fun p : Ω × ℝ => kernelDensityFwd (X i p.1) p.2 *
        (if leaveOneOut X i p.1 + p.2 ≤ z then (1 : ℝ) else 0)) (μ.prod volume) := by
    refine hK.mono' hsm ?_
    filter_upwards with p
    have hk := kernelDensityFwd_nonneg (X i p.1) p.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
    split_ifs <;> simp [hk]
  exact huncurry_int.integral_prod_left

/-- Residual identity (CGS (3.20) form with random kernels):
`∑ E[kernelIndicatorMass] − Φ = E[W f] − ∑ E[kernelSteinProductMass]`. -/
lemma residual_identity_indicator_sub_Phi
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (z : ℝ) :
    (∑ i : ι, ∫ ω, kernelIndicatorMass (X := X) z i ω ∂μ) -
        cdf (gaussianReal 0 1) z =
      (∫ ω, sumX X ω * steinSolution z (sumX X ω) ∂μ) -
        ∑ i : ι, ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ := by
  have hstein := stein_identity_sum_leaveOneOut hX hXmeas h_indep h_mean z
  have hsq := sum_integral_sq_eq_one hX h_mean hvar
  -- For each i: E[∫ K f'] = E[A] + E[B] - Φ E[X²]
  have hterm (i : ι) :
      ∫ ω, leaveOneOutKernelDerivIntegral (X := X) z i ω ∂μ =
        ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ +
          ∫ ω, kernelIndicatorMass (X := X) z i ω ∂μ -
          cdf (gaussianReal 0 1) z * ∫ ω, (X i ω) ^ 2 ∂μ := by
    have hA := integrable_kernelSteinProductMass hX hXmeas z i
    have hB := integrable_kernelIndicatorMass hX hXmeas z i
    have hX2 := (hX i).integrable_sq
    have hΦc : Integrable
        (fun ω => cdf (gaussianReal 0 1) z * (X i ω) ^ 2) μ := hX2.const_mul _
    have hAB := hA.add hB
    have heq : (fun ω => leaveOneOutKernelDerivIntegral (X := X) z i ω) =
        fun ω => (kernelSteinProductMass (X := X) z i ω +
            kernelIndicatorMass (X := X) z i ω) -
          cdf (gaussianReal 0 1) z * (X i ω) ^ 2 :=
      funext fun ω => by
        have h := kernel_masses_of_expand (X := X) z i ω
        linarith [h]
    calc
      ∫ ω, leaveOneOutKernelDerivIntegral (X := X) z i ω ∂μ =
          ∫ ω, (kernelSteinProductMass (X := X) z i ω +
              kernelIndicatorMass (X := X) z i ω) -
            cdf (gaussianReal 0 1) z * (X i ω) ^ 2 ∂μ := by rw [heq]
      _ = (∫ ω, kernelSteinProductMass (X := X) z i ω +
              kernelIndicatorMass (X := X) z i ω ∂μ) -
            ∫ ω, cdf (gaussianReal 0 1) z * (X i ω) ^ 2 ∂μ :=
        integral_sub hAB hΦc
      _ = (∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ +
              ∫ ω, kernelIndicatorMass (X := X) z i ω ∂μ) -
            cdf (gaussianReal 0 1) z * ∫ ω, (X i ω) ^ 2 ∂μ := by
          rw [integral_add hA hB, integral_const_mul]
  have hsum :
      ∑ i, ∫ ω, leaveOneOutKernelDerivIntegral (X := X) z i ω ∂μ =
        ∑ i, ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ +
          ∑ i, ∫ ω, kernelIndicatorMass (X := X) z i ω ∂μ -
          cdf (gaussianReal 0 1) z * ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ := by
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have hstein' :
      ∫ ω, sumX X ω * steinSolution z (sumX X ω) ∂μ =
        ∑ i, ∫ ω, leaveOneOutKernelDerivIntegral (X := X) z i ω ∂μ := hstein
  rw [hstein', hsum, hsq]
  ring



/-! ### Residual O(γ) bound via product residual majorant -/

/-- Pointwise product residual integrated against the forward kernel. -/
noncomputable def kernelProductResidual (z : ℝ) (i : ι) (ω : Ω) : ℝ :=
  ∫ t : ℝ, kernelDensityFwd (X i ω) t *
    ((sumX X ω) * steinSolution z (sumX X ω) -
      (leaveOneOut X i ω + t) * steinSolution z (leaveOneOut X i ω + t))

omit [MeasurableSpace Ω] in
lemma abs_kernelProductResidual_le (z : ℝ) (i : ι) (ω : Ω) :
    |kernelProductResidual (X := X) z i ω| ≤
      (2 * |leaveOneOut X i ω| + sqrt (2 * π) / 2) * ((3 : ℝ) / 2) * |X i ω| ^ 3 := by
  have hW : sumX X ω = leaveOneOut X i ω + X i ω := leaveOneOut_add (X := X) i ω
  simpa [kernelProductResidual, hW] using
    abs_integral_residual_kernelFwd_le z (leaveOneOut X i ω) (X i ω)

omit [MeasurableSpace Ω] in
lemma kernelProductResidual_eq (z : ℝ) (i : ι) (ω : Ω) :
    kernelProductResidual (X := X) z i ω =
      sumX X ω * steinSolution z (sumX X ω) * (X i ω) ^ 2 -
        kernelSteinProductMass (X := X) z i ω := by
  have hK := integral_kernelDensityFwd (X i ω)
  have hc :
      ∫ t : ℝ, kernelDensityFwd (X i ω) t *
          (sumX X ω * steinSolution z (sumX X ω)) =
        sumX X ω * steinSolution z (sumX X ω) * (X i ω) ^ 2 := by
    have heq : (fun t => kernelDensityFwd (X i ω) t *
        (sumX X ω * steinSolution z (sumX X ω))) =
        fun t => (sumX X ω * steinSolution z (sumX X ω)) * kernelDensityFwd (X i ω) t := by
      funext t; ring
    rw [heq, integral_const_mul, hK]
  have hsub :
      (fun t => kernelDensityFwd (X i ω) t *
          (sumX X ω * steinSolution z (sumX X ω) -
            (leaveOneOut X i ω + t) * steinSolution z (leaveOneOut X i ω + t))) =
        fun t => kernelDensityFwd (X i ω) t * (sumX X ω * steinSolution z (sumX X ω)) -
          kernelDensityFwd (X i ω) t *
            ((leaveOneOut X i ω + t) * steinSolution z (leaveOneOut X i ω + t)) := by
    funext t; ring
  have hInt1 : Integrable (fun t =>
      kernelDensityFwd (X i ω) t * (sumX X ω * steinSolution z (sumX X ω))) := by
    have heq : (fun t => kernelDensityFwd (X i ω) t *
        (sumX X ω * steinSolution z (sumX X ω))) =
        fun t => (sumX X ω * steinSolution z (sumX X ω)) * kernelDensityFwd (X i ω) t := by
      funext t; ring
    rw [heq]; exact (integrable_kernelDensityFwd _).const_mul _
  have hInt2 := integrable_kernelDensityFwd_mul_mul_steinSolution z
    (leaveOneOut X i ω) (X i ω)
  simp only [kernelProductResidual, kernelSteinProductMass]
  rw [hsub, integral_sub hInt1 hInt2, hc]

omit [IsProbabilityMeasure μ] in
/-- Integrability of the product residual (dominated by the third-moment majorant). -/
lemma integrable_kernelProductResidual
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (_h_indep : iIndepFun X μ) (_h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (_hvar : ∑ k, variance (X k) μ = 1)
    (_h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (z : ℝ) (i : ι) :
    Integrable (kernelProductResidual (X := X) z i) μ := by
  -- residual = Wf * X² - product mass; both integrable
  have hA := integrable_kernelSteinProductMass hX hXmeas z i
  have hWfX2 : Integrable
      (fun ω => sumX X ω * steinSolution z (sumX X ω) * (X i ω) ^ 2) μ := by
    -- |Wf| ≤ 1 so |Wf X²| ≤ X²
    have hX2 := (hX i).integrable_sq
    refine hX2.mono' ?_ ?_
    · exact (measurable_sumX hXmeas).mul
        ((continuous_steinSolution z).measurable.comp (measurable_sumX hXmeas)) |>.mul
        ((hXmeas i).pow_const 2) |>.aestronglyMeasurable
    · filter_upwards with ω
      have hwf : |sumX X ω| * |steinSolution z (sumX X ω)| ≤ 1 := by
        simpa [abs_mul] using abs_mul_steinSolution_le_one z (sumX X ω)
      have hx2 : 0 ≤ (X i ω) ^ 2 := sq_nonneg _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hx2]
      calc
        |sumX X ω| * |steinSolution z (sumX X ω)| * (X i ω) ^ 2 ≤
            1 * (X i ω) ^ 2 := mul_le_mul_of_nonneg_right hwf hx2
        _ = (X i ω) ^ 2 := one_mul _
  have heq : kernelProductResidual (X := X) z i =
      fun ω => sumX X ω * steinSolution z (sumX X ω) * (X i ω) ^ 2 -
        kernelSteinProductMass (X := X) z i ω :=
    funext fun ω => kernelProductResidual_eq z i ω
  rw [heq]; exact hWfX2.sub hA

/-- Expected absolute product residual ≤ independence majorant. -/
lemma expected_abs_kernelProductResidual_le
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (z : ℝ) (i : ι) :
    ∫ ω, |kernelProductResidual (X := X) z i ω| ∂μ ≤
      (2 + sqrt (2 * π) / 2) * ((3 : ℝ) / 2) * ∫ ω, |X i ω| ^ 3 ∂μ := by
  have hIntR := integrable_kernelProductResidual hX hXmeas h_indep h_mean hvar h3 z i
  -- majorant integrability from expected_residual_majorant_one setup
  have hW : Integrable (fun ω => |leaveOneOut X i ω|) μ :=
    ((memLp_leaveOneOut hX i).integrable one_le_two).abs
  have hX3 := h3 i
  have hInd := indepFun_leaveOneOut (X := X) (μ := μ) hXmeas h_indep i
  have hindep_abs :
      IndepFun (fun ω => |leaveOneOut X i ω|) (fun ω => |X i ω| ^ 3) μ :=
    hInd.comp measurable_id.abs (measurable_id.abs.pow_const 3)
  have hprod_int := hindep_abs.integrable_mul hW hX3
  set M : ℝ := sqrt (2 * π) / 2
  have heq :
      (fun ω => (2 * |leaveOneOut X i ω| + M) * ((3 : ℝ) / 2) * |X i ω| ^ 3) =
        fun ω => (3 : ℝ) * (|leaveOneOut X i ω| * |X i ω| ^ 3) +
          ((3 : ℝ) / 2 * M) * |X i ω| ^ 3 := by
    funext ω; ring
  have hIntMaj : Integrable
      (fun ω => (2 * |leaveOneOut X i ω| + M) * ((3 : ℝ) / 2) * |X i ω| ^ 3) μ := by
    rw [heq]; exact (hprod_int.const_mul 3).add (hX3.const_mul _)
  have hle := abs_kernelProductResidual_le (X := X) z i
  have hmono := integral_mono hIntR.abs hIntMaj fun ω => by
    simpa [Real.norm_eq_abs, M] using hle ω
  -- RHS of majorant integral ≤ (2+M)*(3/2)*E|X|³
  have hmaj := expected_residual_majorant_one hX hXmeas h_indep h_mean hvar h3 i
  exact hmono.trans (by simpa [M] using hmaj)

/-- Sum of expected absolute product residuals ≤ 6γ. -/
lemma sum_expected_abs_kernelProductResidual_le
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (z : ℝ) :
    ∑ i : ι, ∫ ω, |kernelProductResidual (X := X) z i ω| ∂μ ≤
      (2 + sqrt (2 * π) / 2) * ((3 : ℝ) / 2) * thirdMomentSum (X := X) μ := by
  refine (Finset.sum_le_sum fun i _ =>
    expected_abs_kernelProductResidual_le hX hXmeas h_indep h_mean hvar h3 z i).trans_eq ?_
  simp only [thirdMomentSum, Finset.mul_sum]

/-! ### Residual bound via independence factorization (expected kernels) -/

/-- Stein product of leave-one-out at shift `t` is integrable (bounded by 1). -/
lemma integrable_leaveOneOut_mul_steinSolution
    (_hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (z t : ℝ) (i : ι) :
    Integrable (fun ω =>
      (leaveOneOut X i ω + t) * steinSolution z (leaveOneOut X i ω + t)) μ := by
  -- | (W'+t) f(W'+t) | ≤ 1
  refine integrable_const (μ := μ) (1 : ℝ) |>.mono' ?_ ?_
  · exact ((measurable_leaveOneOut hXmeas i).add_const t).mul
      ((continuous_steinSolution z).measurable.comp
        ((measurable_leaveOneOut hXmeas i).add_const t)) |>.aestronglyMeasurable
  · filter_upwards with ω
    have h := abs_mul_steinSolution_le_one z (leaveOneOut X i ω + t)
    simpa [Real.norm_eq_abs, abs_mul] using h

omit [Fintype ι] [DecidableEq ι] in
/-- Kernel density at fixed `t` is integrable (dominated by `|Xᵢ|`). -/
lemma integrable_kernelDensityFwd_eval (i : ι)
    (hX : MemLp (X i) 2 μ) (hXmeas : Measurable (X i)) (t : ℝ) :
    Integrable (fun ω => kernelDensityFwd (X i ω) t) μ := by
  -- 0 ≤ K(ξ,t) ≤ |ξ|
  have hle : ∀ ξ, kernelDensityFwd ξ t ≤ |ξ| := by
    intro ξ
    by_cases hξ : 0 ≤ ξ
    · rw [kernelDensityFwd_eq_indicator_nonneg ξ hξ]
      by_cases ht : t ∈ Icc 0 ξ
      · simp [indicator_of_mem ht, abs_of_nonneg hξ]
      · simp [indicator_of_notMem ht, abs_nonneg]
    · have hlt : ξ < 0 := lt_of_not_ge hξ
      rw [kernelDensityFwd_eq_indicator_neg ξ hlt]
      by_cases ht : t ∈ Ioc ξ 0
      · simp [indicator_of_mem ht, abs_of_nonpos hlt.le]
      · simp [indicator_of_notMem ht, abs_nonneg]
  have hXi := (hX.integrable one_le_two).abs
  refine hXi.mono' ?_ ?_
  · exact (measurable_kernelDensityFwd_left t |>.comp hXmeas).aestronglyMeasurable
  · filter_upwards with ω
    have hk := kernelDensityFwd_nonneg (X i ω) t
    rw [Real.norm_eq_abs, abs_of_nonneg hk]
    exact hle (X i ω)

/-- Factorization at fixed `t` by leave-one-out independence. -/
lemma integral_stein_mul_kernel_eq_mul
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ)
    (z : ℝ) (i : ι) (t : ℝ) :
    ∫ ω, ((leaveOneOut X i ω + t) * steinSolution z (leaveOneOut X i ω + t)) *
        kernelDensityFwd (X i ω) t ∂μ =
      (∫ ω, (leaveOneOut X i ω + t) * steinSolution z (leaveOneOut X i ω + t) ∂μ) *
        expectedKernelFwd (X := X) (μ := μ) i t := by
  have hInd := indepFun_leaveOneOut (X := X) (μ := μ) hXmeas h_indep i
  have hg : Measurable fun w : ℝ => (w + t) * steinSolution z (w + t) :=
    (measurable_id.add_const t).mul
      ((continuous_steinSolution z).measurable.comp (measurable_id.add_const t))
  have hK : Measurable fun ξ : ℝ => kernelDensityFwd ξ t :=
    measurable_kernelDensityFwd_left t
  have hindep :
      IndepFun (fun ω => (leaveOneOut X i ω + t) * steinSolution z (leaveOneOut X i ω + t))
        (fun ω => kernelDensityFwd (X i ω) t) μ :=
    hInd.comp hg hK
  have hIntg := integrable_leaveOneOut_mul_steinSolution hX hXmeas z t i
  have hIntK := integrable_kernelDensityFwd_eval i (hX i) (hXmeas i) t
  -- integral (g * K) = (∫ g) * (∫ K)
  have h := hindep.integral_mul_eq_mul_integral hIntg.aestronglyMeasurable
    hIntK.aestronglyMeasurable
  simpa [expectedKernelFwd] using h

/-- `|E[W f · Xᵢ²] - E[Aᵢ]| ≤ residual majorant` (product residual). -/
lemma abs_expected_Wf_Xsq_sub_productMass_le
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (z : ℝ) (i : ι) :
    |(∫ ω, sumX X ω * steinSolution z (sumX X ω) * (X i ω) ^ 2 ∂μ) -
      ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ| ≤
      (2 + sqrt (2 * π) / 2) * ((3 : ℝ) / 2) * ∫ ω, |X i ω| ^ 3 ∂μ := by
  have hA := integrable_kernelSteinProductMass hX hXmeas z i
  have hWfX2 : Integrable
      (fun ω => sumX X ω * steinSolution z (sumX X ω) * (X i ω) ^ 2) μ := by
    have hX2 := (hX i).integrable_sq
    refine hX2.mono' ?_ ?_
    · exact (measurable_sumX hXmeas).mul
        ((continuous_steinSolution z).measurable.comp (measurable_sumX hXmeas)) |>.mul
        ((hXmeas i).pow_const 2) |>.aestronglyMeasurable
    · filter_upwards with ω
      have hwf : |sumX X ω| * |steinSolution z (sumX X ω)| ≤ 1 := by
        simpa [abs_mul] using abs_mul_steinSolution_le_one z (sumX X ω)
      have hx2 : 0 ≤ (X i ω) ^ 2 := sq_nonneg _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hx2]
      calc
        |sumX X ω| * |steinSolution z (sumX X ω)| * (X i ω) ^ 2 ≤
            1 * (X i ω) ^ 2 := mul_le_mul_of_nonneg_right hwf hx2
        _ = (X i ω) ^ 2 := one_mul _
  have heq : ∫ ω, kernelProductResidual (X := X) z i ω ∂μ =
      ∫ ω, sumX X ω * steinSolution z (sumX X ω) * (X i ω) ^ 2 ∂μ -
        ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ := by
    have hfun : kernelProductResidual (X := X) z i =
        fun ω => sumX X ω * steinSolution z (sumX X ω) * (X i ω) ^ 2 -
          kernelSteinProductMass (X := X) z i ω :=
      funext fun ω => kernelProductResidual_eq z i ω
    rw [hfun, integral_sub hWfX2 hA]
  rw [← heq]
  exact (abs_integral_le_integral_abs).trans
    (expected_abs_kernelProductResidual_le hX hXmeas h_indep h_mean hvar h3 z i)

/-- Sum form: `|∑ E[W f Xᵢ²] - ∑ E[Aᵢ]| ≤ 6γ`. -/
lemma abs_sum_expected_Wf_Xsq_sub_productMass_le
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (z : ℝ) :
    |(∑ i : ι, ∫ ω, sumX X ω * steinSolution z (sumX X ω) * (X i ω) ^ 2 ∂μ) -
      ∑ i : ι, ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ| ≤
      (2 + sqrt (2 * π) / 2) * ((3 : ℝ) / 2) * thirdMomentSum (X := X) μ := by
  refine le_trans ?_
    (sum_expected_abs_kernelProductResidual_le hX hXmeas h_indep h_mean hvar h3 z)
  have hterm (i : ι) :
      |∫ ω, sumX X ω * steinSolution z (sumX X ω) * (X i ω) ^ 2 ∂μ -
        ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ| ≤
        ∫ ω, |kernelProductResidual (X := X) z i ω| ∂μ := by
    have hA := integrable_kernelSteinProductMass hX hXmeas z i
    have hWfX2 : Integrable
        (fun ω => sumX X ω * steinSolution z (sumX X ω) * (X i ω) ^ 2) μ := by
      have hX2 := (hX i).integrable_sq
      refine hX2.mono' ?_ ?_
      · exact (measurable_sumX hXmeas).mul
          ((continuous_steinSolution z).measurable.comp (measurable_sumX hXmeas)) |>.mul
          ((hXmeas i).pow_const 2) |>.aestronglyMeasurable
      · filter_upwards with ω
        have hwf : |sumX X ω| * |steinSolution z (sumX X ω)| ≤ 1 := by
          simpa [abs_mul] using abs_mul_steinSolution_le_one z (sumX X ω)
        have hx2 : 0 ≤ (X i ω) ^ 2 := sq_nonneg _
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hx2]
        calc
          |sumX X ω| * |steinSolution z (sumX X ω)| * (X i ω) ^ 2 ≤
              1 * (X i ω) ^ 2 := mul_le_mul_of_nonneg_right hwf hx2
          _ = (X i ω) ^ 2 := one_mul _
    have heq : ∫ ω, kernelProductResidual (X := X) z i ω ∂μ =
        ∫ ω, sumX X ω * steinSolution z (sumX X ω) * (X i ω) ^ 2 ∂μ -
          ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ := by
      have hfun : kernelProductResidual (X := X) z i =
          fun ω => sumX X ω * steinSolution z (sumX X ω) * (X i ω) ^ 2 -
            kernelSteinProductMass (X := X) z i ω :=
        funext fun ω => kernelProductResidual_eq z i ω
      rw [hfun, integral_sub hWfX2 hA]
    rw [← heq]; exact abs_integral_le_integral_abs
  calc
    |(∑ i, ∫ ω, sumX X ω * steinSolution z (sumX X ω) * (X i ω) ^ 2 ∂μ) -
        ∑ i, ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ|
        = |∑ i, (∫ ω, sumX X ω * steinSolution z (sumX X ω) * (X i ω) ^ 2 ∂μ -
            ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ)| := by
          rw [← Finset.sum_sub_distrib]
    _ ≤ ∑ i, |∫ ω, sumX X ω * steinSolution z (sumX X ω) * (X i ω) ^ 2 ∂μ -
            ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∫ ω, |kernelProductResidual (X := X) z i ω| ∂μ :=
        Finset.sum_le_sum fun i _ => hterm i


/-! ### Expected-kernel Fubini for product mass -/

omit [IsProbabilityMeasure μ] in
/-- Product-space integrability of `K · (W'+t)f`. -/
lemma integrable_uncurry_kernel_mul_steinProduct
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (z : ℝ) (i : ι) :
    Integrable (fun p : Ω × ℝ =>
      kernelDensityFwd (X i p.1) p.2 *
        ((leaveOneOut X i p.1 + p.2) *
          steinSolution z (leaveOneOut X i p.1 + p.2))) (μ.prod volume) := by
  have hK := integrable_uncurry_kernelDensityFwd i (hX i) (hXmeas i)
  have hsm : AEStronglyMeasurable
      (fun p : Ω × ℝ => kernelDensityFwd (X i p.1) p.2 *
        ((leaveOneOut X i p.1 + p.2) *
          steinSolution z (leaveOneOut X i p.1 + p.2))) (μ.prod volume) :=
    ((measurable_kernelDensityFwd_pair i (hXmeas i)).mul
      (((measurable_leaveOneOut hXmeas i).comp measurable_fst |>.add measurable_snd).mul
        ((continuous_steinSolution z).measurable.comp
          ((measurable_leaveOneOut hXmeas i).comp measurable_fst |>.add
            measurable_snd)))).aestronglyMeasurable
  refine hK.mono' hsm ?_
  filter_upwards with p
  have hk := kernelDensityFwd_nonneg (X i p.1) p.2
  have hw : |(leaveOneOut X i p.1 + p.2) *
      steinSolution z (leaveOneOut X i p.1 + p.2)| ≤ 1 := by
    simpa [abs_mul] using abs_mul_steinSolution_le_one z (leaveOneOut X i p.1 + p.2)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
  exact (mul_le_mul_of_nonneg_left hw hk).trans_eq (mul_one _)

/-- `E[Aᵢ] = ∫_t E[(W⁽ⁱ⁾+t)f] · Khatᵢ(t) dt`. -/
lemma expected_kernelSteinProductMass_eq_integral_expected
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ)
    (z : ℝ) (i : ι) :
    ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ =
      ∫ t : ℝ,
        (∫ ω, (leaveOneOut X i ω + t) * steinSolution z (leaveOneOut X i ω + t) ∂μ) *
          expectedKernelFwd (X := X) (μ := μ) i t := by
  set g : Ω × ℝ → ℝ := fun p =>
    kernelDensityFwd (X i p.1) p.2 *
      ((leaveOneOut X i p.1 + p.2) * steinSolution z (leaveOneOut X i p.1 + p.2))
  have hInt : Integrable g (μ.prod volume) :=
    integrable_uncurry_kernel_mul_steinProduct hX hXmeas z i
  have hA_eq : ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ =
      ∫ p, g p ∂(μ.prod volume) := by
    change ∫ ω, (∫ t : ℝ, g (ω, t)) ∂μ = ∫ p, g p ∂(μ.prod volume)
    exact integral_integral hInt
  have hswap : ∫ p, g p ∂(μ.prod volume) = ∫ t : ℝ, ∫ ω, g (ω, t) ∂μ :=
    integral_prod_symm g hInt
  rw [hA_eq, hswap]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  calc
    ∫ ω, g (ω, t) ∂μ =
        ∫ ω, ((leaveOneOut X i ω + t) * steinSolution z (leaveOneOut X i ω + t)) *
          kernelDensityFwd (X i ω) t ∂μ := by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      dsimp [g]; ring
    _ = (∫ ω, (leaveOneOut X i ω + t) * steinSolution z (leaveOneOut X i ω + t) ∂μ) *
          expectedKernelFwd (X := X) (μ := μ) i t :=
      integral_stein_mul_kernel_eq_mul hX hXmeas h_indep z i t


/-! ### Support for pure residual O(γ) -/

/-- Young: `a * b² ≤ a³/3 + (2/3) b³` for `a, b ≥ 0`. -/
lemma young_abs_mul_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b ^ 2 ≤ a ^ 3 / 3 + (2 : ℝ) / 3 * b ^ 3 := by
  -- Identity: a³ + 2b³ - 3ab² = (a - b)²(a + 2b) ≥ 0
  have h : 0 ≤ (a - b) ^ 2 * (a + 2 * b) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have h' : a ^ 3 + 2 * b ^ 3 - 3 * a * b ^ 2 = (a - b) ^ 2 * (a + 2 * b) := by ring
  linarith [h'.symm ▸ h]

omit [Fintype ι] [IsProbabilityMeasure μ] [DecidableEq ι] in
/-- Integrability of `(ω,t) ↦ |t| · K(Xᵢω,t)` on `μ.prod volume`. -/
lemma integrable_uncurry_abs_t_mul_kernel (i : ι)
    (_hX : MemLp (X i) 2 μ) (hXmeas : Measurable (X i))
    (h3 : Integrable (fun ω => |X i ω| ^ 3) μ) :
    Integrable (fun p : Ω × ℝ => |p.2| * kernelDensityFwd (X i p.1) p.2)
      (μ.prod volume) := by
  have hsm : AEStronglyMeasurable
      (fun p : Ω × ℝ => |p.2| * kernelDensityFwd (X i p.1) p.2) (μ.prod volume) :=
    (measurable_snd.abs.mul (measurable_kernelDensityFwd_pair i hXmeas)).aestronglyMeasurable
  have hmaj : Integrable
      (fun p : Ω × ℝ => |X i p.1| * kernelDensityFwd (X i p.1) p.2) (μ.prod volume) := by
    have hsm' : AEStronglyMeasurable
        (fun p : Ω × ℝ => |X i p.1| * kernelDensityFwd (X i p.1) p.2) (μ.prod volume) :=
      ((hXmeas.abs.comp measurable_fst).mul
        (measurable_kernelDensityFwd_pair i hXmeas)).aestronglyMeasurable
    rw [integrable_prod_iff hsm']
    constructor
    · refine Eventually.of_forall fun ω => ?_
      have h := (integrable_kernelDensityFwd (X i ω)).const_mul (|X i ω|)
      -- h : Integrable (fun t => |X| * K t)
      exact h
    · have heq :
          (fun ω => ∫ t : ℝ, ‖|X i ω| * kernelDensityFwd (X i ω) t‖) =
            fun ω => |X i ω| ^ 3 := by
        funext ω
        have hnn : ∀ t, 0 ≤ |X i ω| * kernelDensityFwd (X i ω) t := fun t =>
          mul_nonneg (abs_nonneg _) (kernelDensityFwd_nonneg _ _)
        have habs :
            (fun t => ‖|X i ω| * kernelDensityFwd (X i ω) t‖) =
              fun t => |X i ω| * kernelDensityFwd (X i ω) t :=
          funext fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hnn t)]
        rw [habs, integral_const_mul, integral_kernelDensityFwd]
        -- |X| * X² = |X|³
        calc
          |X i ω| * (X i ω) ^ 2 = |X i ω| * |X i ω| ^ 2 := by rw [← sq_abs]
          _ = |X i ω| ^ 3 := by ring
      rw [heq]; exact h3
  refine hmaj.mono' hsm ?_
  filter_upwards with p
  have hk := kernelDensityFwd_nonneg (X i p.1) p.2
  have hle : |p.2| * kernelDensityFwd (X i p.1) p.2 ≤
      |X i p.1| * kernelDensityFwd (X i p.1) p.2 := by
    by_cases hz : kernelDensityFwd (X i p.1) p.2 = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_right
        (abs_t_le_abs_xi_of_mem_kernelDensityFwd hz) hk
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hk)]
  exact hle

omit [Fintype ι] [DecidableEq ι] in
/-- `∫ |t| · Khatᵢ(t) dt = (1/2) E|Xᵢ|³`. -/
lemma integral_abs_mul_expectedKernelFwd (i : ι)
    (hX : MemLp (X i) 2 μ) (hXmeas : Measurable (X i))
    (h3 : Integrable (fun ω => |X i ω| ^ 3) μ) :
    ∫ t : ℝ, |t| * expectedKernelFwd (X := X) (μ := μ) i t =
      (1 / 2 : ℝ) * ∫ ω, |X i ω| ^ 3 ∂μ := by
  let g : Ω × ℝ → ℝ := fun p => |p.2| * kernelDensityFwd (X i p.1) p.2
  have hInt : Integrable g (μ.prod volume) :=
    integrable_uncurry_abs_t_mul_kernel i hX hXmeas h3
  have h1 :
      ∫ t : ℝ, |t| * expectedKernelFwd (X := X) (μ := μ) i t =
        ∫ t : ℝ, ∫ (ω : Ω), g (ω, t) ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    change |t| * ∫ ω, kernelDensityFwd (X i ω) t ∂μ =
      ∫ ω, |t| * kernelDensityFwd (X i ω) t ∂μ
    exact (integral_const_mul |t| _).symm
  have h2 :
      ∫ t : ℝ, ∫ (ω : Ω), g (ω, t) ∂μ =
        ∫ (ω : Ω), (∫ t : ℝ, g (ω, t)) ∂μ :=
    (integral_integral_swap (f := fun (ω : Ω) (t : ℝ) => g (ω, t)) (by
      convert hInt using 1
      ext p
      cases p with | mk ω t => rfl)).symm
  have h3a :
      ∫ (ω : Ω), (∫ t : ℝ, g (ω, t)) ∂μ =
        ∫ (ω : Ω), |X i ω| ^ 3 / 2 ∂μ :=
    integral_congr_ae (Eventually.of_forall fun ω => by
      change ∫ t : ℝ, |t| * kernelDensityFwd (X i ω) t = |X i ω| ^ 3 / 2
      exact integral_abs_mul_kernelDensityFwd _)
  calc
    ∫ t, |t| * expectedKernelFwd (X := X) (μ := μ) i t =
        ∫ t, ∫ ω, g (ω, t) ∂μ := h1
    _ = ∫ ω, (∫ t, g (ω, t)) ∂μ := h2
    _ = ∫ ω, |X i ω| ^ 3 / 2 ∂μ := h3a
    _ = (1 / 2 : ℝ) * ∫ ω, |X i ω| ^ 3 ∂μ := by
          rw [show (fun ω => |X i ω| ^ 3 / 2) =
              fun ω => (1 / 2 : ℝ) * |X i ω| ^ 3 by funext; ring]
          exact integral_const_mul _ _


omit [Fintype ι] [DecidableEq ι] in
/-- `Khatᵢ` is integrable. -/
lemma integrable_expectedKernelFwd (i : ι)
    (hX : MemLp (X i) 2 μ) (hXmeas : Measurable (X i)) :
    Integrable (expectedKernelFwd (X := X) (μ := μ) i) := by
  have h := (integrable_uncurry_kernelDensityFwd i hX hXmeas).integral_prod_right
  exact h

/-- Hölder/Young product form: `(E|Y|)(E Y²) ≤ E|Y|³` on a probability space. -/
lemma integral_abs_mul_integral_sq_le
    {Y : Ω → ℝ} (_hYmeas : Measurable Y)
    (h1 : Integrable (fun ω => |Y ω|) μ)
    (h2 : Integrable (fun ω => Y ω ^ 2) μ)
    (h3 : Integrable (fun ω => |Y ω| ^ 3) μ) :
    (∫ ω, |Y ω| ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) ≤ ∫ ω, |Y ω| ^ 3 ∂μ := by
  have hprod : Integrable (fun p : Ω × Ω => |Y p.1| * Y p.2 ^ 2) (μ.prod μ) :=
    h1.mul_prod h2
  have hL :
      ∫ p : Ω × Ω, |Y p.1| * Y p.2 ^ 2 ∂(μ.prod μ) =
        (∫ ω, |Y ω| ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) :=
    integral_prod_mul (fun ω => |Y ω|) (fun ω => Y ω ^ 2)
  have hInt1 : Integrable (fun p : Ω × Ω => |Y p.1| ^ 3 / 3) (μ.prod μ) := by
    have h := (h3.const_mul (1 / 3 : ℝ)).comp_fst (ν := μ)
    convert h using 1
    ext p; ring
  have hInt2 : Integrable (fun p : Ω × Ω => (2 / 3 : ℝ) * |Y p.2| ^ 3) (μ.prod μ) :=
    (h3.const_mul (2 / 3 : ℝ)).comp_snd μ
  have hmaj : Integrable
      (fun p : Ω × Ω => |Y p.1| ^ 3 / 3 + (2 / 3 : ℝ) * |Y p.2| ^ 3) (μ.prod μ) :=
    hInt1.add hInt2
  have hR :
      ∫ p : Ω × Ω, |Y p.1| ^ 3 / 3 + (2 / 3 : ℝ) * |Y p.2| ^ 3 ∂(μ.prod μ) =
        ∫ ω, |Y ω| ^ 3 ∂μ := by
    rw [integral_add hInt1 hInt2]
    have h1' : ∫ p : Ω × Ω, |Y p.1| ^ 3 / 3 ∂(μ.prod μ) =
        (1 / 3 : ℝ) * ∫ ω, |Y ω| ^ 3 ∂μ := by
      have heq : (fun p : Ω × Ω => |Y p.1| ^ 3 / 3) =
          fun p => (1 / 3 : ℝ) * |Y p.1| ^ 3 := by
        ext p; ring
      rw [heq, integral_const_mul]
      have h := integral_fun_fst (μ := μ) (ν := μ) (fun ω : Ω => |Y ω| ^ 3)
      rw [probReal_univ, one_smul] at h
      exact congrArg ((1 / 3 : ℝ) * ·) h
    have h2' : ∫ p : Ω × Ω, (2 / 3 : ℝ) * |Y p.2| ^ 3 ∂(μ.prod μ) =
        (2 / 3 : ℝ) * ∫ ω, |Y ω| ^ 3 ∂μ := by
      rw [integral_const_mul]
      have h := integral_fun_snd (μ := μ) (ν := μ) (fun ω : Ω => |Y ω| ^ 3)
      rw [probReal_univ, one_smul] at h
      exact congrArg ((2 / 3 : ℝ) * ·) h
    linarith
  have hpt :
      ∫ p : Ω × Ω, |Y p.1| * Y p.2 ^ 2 ∂(μ.prod μ) ≤
        ∫ p : Ω × Ω, |Y p.1| ^ 3 / 3 + (2 / 3 : ℝ) * |Y p.2| ^ 3 ∂(μ.prod μ) := by
    refine integral_mono hprod hmaj fun p => ?_
    have ha : 0 ≤ |Y p.1| := abs_nonneg _
    have hb : 0 ≤ |Y p.2| := abs_nonneg _
    have : |Y p.1| * Y p.2 ^ 2 = |Y p.1| * |Y p.2| ^ 2 := by rw [← sq_abs]
    rw [this]
    exact young_abs_mul_sq ha hb
  calc
    (∫ ω, |Y ω| ∂μ) * (∫ ω, Y ω ^ 2 ∂μ)
        = ∫ p : Ω × Ω, |Y p.1| * Y p.2 ^ 2 ∂(μ.prod μ) := hL.symm
    _ ≤ ∫ p : Ω × Ω, |Y p.1| ^ 3 / 3 + (2 / 3 : ℝ) * |Y p.2| ^ 3 ∂(μ.prod μ) := hpt
    _ = ∫ ω, |Y ω| ^ 3 ∂μ := hR

/-- One-coordinate expected-kernel residual mass:
`E|X| · E X² + (1/2) E|X|³ ≤ (3/2) E|X|³`. -/
lemma expected_abs_mul_sq_add_half_le
    {Y : Ω → ℝ} (hYmeas : Measurable Y)
    (h1 : Integrable (fun ω => |Y ω|) μ)
    (h2 : Integrable (fun ω => Y ω ^ 2) μ)
    (h3 : Integrable (fun ω => |Y ω| ^ 3) μ) :
    (∫ ω, |Y ω| ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) + (1 / 2 : ℝ) * ∫ ω, |Y ω| ^ 3 ∂μ ≤
      (3 / 2 : ℝ) * ∫ ω, |Y ω| ^ 3 ∂μ := by
  have hY := integral_abs_mul_integral_sq_le hYmeas h1 h2 h3
  have hnn : 0 ≤ ∫ ω, |Y ω| ^ 3 ∂μ :=
    integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _
  linarith

/-- Per-coordinate residual:
`|E[Wf]·E[Xᵢ²] − E[Aᵢ]| ≤ (2 + √(2π)/2)·(3/2)·E|Xᵢ|³`. -/
lemma abs_cWf_mul_sq_sub_productMass_le
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (z : ℝ) (i : ι) :
    |(∫ ω, sumX X ω * steinSolution z (sumX X ω) ∂μ) *
          (∫ ω, (X i ω) ^ 2 ∂μ) -
        ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ| ≤
      (2 + sqrt (2 * π) / 2) * ((3 : ℝ) / 2) * ∫ ω, |X i ω| ^ 3 ∂μ := by
  set M : ℝ := sqrt (2 * π) / 2
  set cWf : ℝ := ∫ ω, sumX X ω * steinSolution z (sumX X ω) ∂μ
  set cWpf : ℝ :=
    ∫ ω, leaveOneOut X i ω * steinSolution z (leaveOneOut X i ω) ∂μ
  set EX2 := ∫ ω, (X i ω) ^ 2 ∂μ
  set EX3 := ∫ ω, |X i ω| ^ 3 ∂μ
  set EX := ∫ ω, |X i ω| ∂μ
  set EW := ∫ ω, |leaveOneOut X i ω| ∂μ
  have hAbsX : Integrable (fun ω => |X i ω|) μ :=
    ((hX i).integrable one_le_two).abs
  have hX2 : Integrable (fun ω => (X i ω) ^ 2) μ := (hX i).integrable_sq
  have hWabs : Integrable (fun ω => |leaveOneOut X i ω|) μ :=
    ((memLp_leaveOneOut hX i).integrable one_le_two).abs
  have hWle : EW ≤ 1 := integral_abs_leaveOneOut_le_one hX h_indep h_mean hvar i
  have hYoung : EX * EX2 ≤ EX3 :=
    integral_abs_mul_integral_sq_le (hXmeas i) hAbsX hX2 (h3 i)
  have hInd := indepFun_leaveOneOut (X := X) (μ := μ) hXmeas h_indep i
  have hEX20 : 0 ≤ EX2 := integral_nonneg fun _ => sq_nonneg _
  have hEX30 : 0 ≤ EX3 := integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _
  have hM0 : 0 ≤ M := by positivity
  have hEW0 : 0 ≤ EW := integral_nonneg fun _ => abs_nonneg _
  have hEX0 : 0 ≤ EX := integral_nonneg fun _ => abs_nonneg _
  have hWf_int : Integrable (fun ω => sumX X ω * steinSolution z (sumX X ω)) μ :=
    integrable_sumX_mul_steinSolution hX hXmeas z
  have hWpf_int : Integrable
      (fun ω => leaveOneOut X i ω * steinSolution z (leaveOneOut X i ω)) μ := by
    refine (integrable_const (1 : ℝ)).mono' ?_ ?_
    · exact (measurable_leaveOneOut hXmeas i).mul
        ((continuous_steinSolution z).measurable.comp
          (measurable_leaveOneOut hXmeas i)) |>.aestronglyMeasurable
    · filter_upwards with ω
      have h := abs_mul_steinSolution_le_one z (leaveOneOut X i ω)
      simpa [Real.norm_eq_abs, abs_mul] using h
  -- Bound |cWf - cWpf| ≤ (2EW + M) EX
  have hdiff :
      |cWf - cWpf| ≤ (2 * EW + M) * EX := by
    have hInt_diff := hWf_int.sub hWpf_int
    have hEQ : cWf - cWpf =
        ∫ ω, sumX X ω * steinSolution z (sumX X ω) -
          leaveOneOut X i ω * steinSolution z (leaveOneOut X i ω) ∂μ := by
      simp only [cWf, cWpf, ← integral_sub hWf_int hWpf_int]
    rw [hEQ]
    refine (abs_integral_le_integral_abs).trans ?_
    have hindep_abs :
        IndepFun (fun ω => |leaveOneOut X i ω|) (fun ω => |X i ω|) μ :=
      hInd.comp measurable_id.abs measurable_id.abs
    have hWX := hindep_abs.integrable_mul hWabs hAbsX
    have hMaj : Integrable
        (fun ω => (2 * |leaveOneOut X i ω| + M) * |X i ω|) μ := by
      have heq :
          (fun ω => (2 * |leaveOneOut X i ω| + M) * |X i ω|) =
            fun ω => 2 * (|leaveOneOut X i ω| * |X i ω|) + M * |X i ω| := by
        ext ω; ring
      rw [heq]; exact (hWX.const_mul 2).add (hAbsX.const_mul M)
    refine (integral_mono hInt_diff.abs hMaj fun ω => ?_).trans_eq ?_
    · simp only [Pi.sub_apply]
      have hWsum : sumX X ω = leaveOneOut X i ω + X i ω :=
        leaveOneOut_add (X := X) i ω
      rw [hWsum]
      simpa [M, add_zero] using
        abs_mul_steinSolution_sub_le z (leaveOneOut X i ω) (X i ω) 0
    · have heq :
          (fun ω => (2 * |leaveOneOut X i ω| + M) * |X i ω|) =
            fun ω => 2 * (|leaveOneOut X i ω| * |X i ω|) + M * |X i ω| := by
        ext ω; ring
      calc
        ∫ ω, (2 * |leaveOneOut X i ω| + M) * |X i ω| ∂μ =
            ∫ ω, 2 * (|leaveOneOut X i ω| * |X i ω|) + M * |X i ω| ∂μ := by
          simp only [heq]
        _ = 2 * ∫ ω, |leaveOneOut X i ω| * |X i ω| ∂μ +
              M * ∫ ω, |X i ω| ∂μ := by
          rw [integral_add (by
                convert hWX.const_mul 2 using 1
                ext ω; rfl) (hAbsX.const_mul M), integral_const_mul,
            integral_const_mul]
        _ = 2 * ((∫ ω, |leaveOneOut X i ω| ∂μ) * ∫ ω, |X i ω| ∂μ) +
              M * ∫ ω, |X i ω| ∂μ := by
          have hprod :=
            hindep_abs.integral_mul_eq_mul_integral hWabs.aestronglyMeasurable
              hAbsX.aestronglyMeasurable
          have hprod' :
              ∫ ω, |leaveOneOut X i ω| * |X i ω| ∂μ =
                (∫ ω, |leaveOneOut X i ω| ∂μ) * ∫ ω, |X i ω| ∂μ := by
            simpa [Pi.mul_apply] using hprod
          rw [hprod']
        _ = (2 * EW + M) * EX := by
          simp only [EW, EX]; ring
  -- |cWf EX2 - cWpf EX2| ≤ (2+M) EX3
  have hterm1 : |cWf * EX2 - cWpf * EX2| ≤ (2 + M) * EX3 := by
    have habs : |cWf * EX2 - cWpf * EX2| = |cWf - cWpf| * EX2 := by
      rw [← sub_mul, abs_mul, abs_of_nonneg hEX20]
    rw [habs]
    have h1 : |cWf - cWpf| * EX2 ≤ (2 * EW + M) * EX * EX2 :=
      mul_le_mul_of_nonneg_right hdiff hEX20
    have h2 : (2 * EW + M) * (EX * EX2) ≤ (2 + M) * EX3 := by
      have hle : 2 * EW + M ≤ 2 + M := by linarith [hWle]
      have hY : EX * EX2 ≤ EX3 := hYoung
      nlinarith [hle, hY, hEX0, hEX20, hEX30, hM0, hEW0]
    exact le_trans h1 (by simpa [mul_assoc] using h2)
  -- Independence: cWpf * EX2 = E[W'f · X²]
  have hWpf_X2 :
      cWpf * EX2 =
        ∫ ω, (leaveOneOut X i ω * steinSolution z (leaveOneOut X i ω)) *
          (X i ω) ^ 2 ∂μ := by
    have hindep_f :
        IndepFun
          (fun ω => leaveOneOut X i ω * steinSolution z (leaveOneOut X i ω))
          (fun ω => (X i ω) ^ 2) μ :=
      hInd.comp
        (measurable_id.mul ((continuous_steinSolution z).measurable.comp measurable_id))
        (measurable_id.pow_const 2)
    exact
      (hindep_f.integral_mul_eq_mul_integral hWpf_int.aestronglyMeasurable
          hX2.aestronglyMeasurable).symm
  -- Pointwise: |W'f X² - A| ≤ (2|W'|+M)(|X|³/2)
  have hpt (ω : Ω) :
      |leaveOneOut X i ω * steinSolution z (leaveOneOut X i ω) * (X i ω) ^ 2 -
          kernelSteinProductMass (X := X) z i ω| ≤
        (2 * |leaveOneOut X i ω| + M) * (|X i ω| ^ 3 / 2) := by
    set W' := leaveOneOut X i ω
    set ξ := X i ω
    have hK := integral_kernelDensityFwd ξ
    have hInt1 : Integrable
        (fun t => kernelDensityFwd ξ t * (W' * steinSolution z W')) := by
      have heq :
          (fun t => kernelDensityFwd ξ t * (W' * steinSolution z W')) =
            fun t => (W' * steinSolution z W') * kernelDensityFwd ξ t := by
        funext t; ring
      rw [heq]; exact (integrable_kernelDensityFwd _).const_mul _
    have hInt2 := integrable_kernelDensityFwd_mul_mul_steinSolution z W' ξ
    have hsub :
        (fun t => kernelDensityFwd ξ t *
          (W' * steinSolution z W' - (W' + t) * steinSolution z (W' + t))) =
          fun t => kernelDensityFwd ξ t * (W' * steinSolution z W') -
            kernelDensityFwd ξ t * ((W' + t) * steinSolution z (W' + t)) := by
      funext t; ring
    have hInt := hInt1.sub hInt2
    have hrep :
        W' * steinSolution z W' * ξ ^ 2 - kernelSteinProductMass (X := X) z i ω =
          ∫ t, kernelDensityFwd ξ t *
            (W' * steinSolution z W' - (W' + t) * steinSolution z (W' + t)) := by
      simp only [kernelSteinProductMass, W', ξ]
      have hc :
          ∫ t, kernelDensityFwd ξ t * (W' * steinSolution z W') =
            W' * steinSolution z W' * ξ ^ 2 := by
        have heq :
            (fun t => kernelDensityFwd ξ t * (W' * steinSolution z W')) =
              fun t => (W' * steinSolution z W') * kernelDensityFwd ξ t := by
          funext t; ring
        rw [heq, integral_const_mul, hK]
      rw [hsub, integral_sub hInt1 hInt2, hc]
    rw [hrep]
    have hMajT : Integrable
        (fun t => (2 * |W'| + M) * (|t| * kernelDensityFwd ξ t)) := by
      have h2 : Integrable (fun t => |t| * kernelDensityFwd ξ t) := by
        refine ((integrable_kernelDensityFwd ξ).const_mul (|ξ|)).mono' ?_ ?_
        · exact measurable_id.abs.aestronglyMeasurable.mul
            (integrable_kernelDensityFwd ξ).aestronglyMeasurable
        · filter_upwards with t
          have hk := kernelDensityFwd_nonneg ξ t
          have hle : |t| * kernelDensityFwd ξ t ≤ |ξ| * kernelDensityFwd ξ t := by
            by_cases hz : kernelDensityFwd ξ t = 0
            · simp [hz]
            · exact mul_le_mul_of_nonneg_right
                (abs_t_le_abs_xi_of_mem_kernelDensityFwd hz) hk
          simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk,
            abs_of_nonneg (abs_nonneg ξ)] using hle
      exact h2.const_mul _
    have hInt' : Integrable
        (fun t => kernelDensityFwd ξ t *
          (W' * steinSolution z W' - (W' + t) * steinSolution z (W' + t))) := by
      have heq :
          (fun t => kernelDensityFwd ξ t *
            (W' * steinSolution z W' - (W' + t) * steinSolution z (W' + t))) =
            fun t => kernelDensityFwd ξ t * (W' * steinSolution z W') -
              kernelDensityFwd ξ t * ((W' + t) * steinSolution z (W' + t)) := by
        funext t; ring
      rw [heq]; exact hInt1.sub hInt2
    have hstep :
        |∫ t, kernelDensityFwd ξ t *
          (W' * steinSolution z W' - (W' + t) * steinSolution z (W' + t))| ≤
          (2 * |W'| + M) * (|ξ| ^ 3 / 2) := by
      refine (abs_integral_le_integral_abs).trans ?_
      refine (integral_mono hInt'.abs hMajT fun t => ?_).trans_eq ?_
      · have hk := kernelDensityFwd_nonneg ξ t
        have hbnd :
            |W' * steinSolution z W' - (W' + t) * steinSolution z (W' + t)| ≤
              (2 * |W'| + M) * |t| := by
          have h := abs_mul_steinSolution_sub_le z W' 0 t
          simpa [M, abs_zero, add_zero, zero_mul, zero_add] using h
        simp only [abs_mul, abs_of_nonneg hk]
        calc
          kernelDensityFwd ξ t *
              |W' * steinSolution z W' - (W' + t) * steinSolution z (W' + t)| ≤
            kernelDensityFwd ξ t * ((2 * |W'| + M) * |t|) := by gcongr
          _ = (2 * |W'| + M) * (|t| * kernelDensityFwd ξ t) := by ring
      · rw [integral_const_mul, integral_abs_mul_kernelDensityFwd]
    exact hstep
  -- Integrability of W'f X² - A
  have hWpfX2_int : Integrable
      (fun ω => leaveOneOut X i ω * steinSolution z (leaveOneOut X i ω) *
        (X i ω) ^ 2) μ := by
    refine hX2.mono' ?_ ?_
    · exact (measurable_leaveOneOut hXmeas i).mul
        ((continuous_steinSolution z).measurable.comp
          (measurable_leaveOneOut hXmeas i)) |>.mul
        ((hXmeas i).pow_const 2) |>.aestronglyMeasurable
    · filter_upwards with ω
      have hw : |leaveOneOut X i ω * steinSolution z (leaveOneOut X i ω)| ≤ 1 := by
        simpa [abs_mul] using abs_mul_steinSolution_le_one z (leaveOneOut X i ω)
      have hx2 : 0 ≤ (X i ω) ^ 2 := sq_nonneg _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx2]
      calc
        |leaveOneOut X i ω * steinSolution z (leaveOneOut X i ω)| * (X i ω) ^ 2 ≤
            1 * (X i ω) ^ 2 := mul_le_mul_of_nonneg_right hw hx2
        _ = (X i ω) ^ 2 := one_mul _
  have hA_int := integrable_kernelSteinProductMass hX hXmeas z i
  have hDiff_int := hWpfX2_int.sub hA_int
  -- Maj integrability via independence
  have hindep3 :
      IndepFun (fun ω => |leaveOneOut X i ω|) (fun ω => |X i ω| ^ 3) μ :=
    hInd.comp measurable_id.abs (measurable_id.abs.pow_const 3)
  have hW3 := hindep3.integrable_mul hWabs (h3 i)
  have hMaj_int : Integrable
      (fun ω => (2 * |leaveOneOut X i ω| + M) * (|X i ω| ^ 3 / 2)) μ := by
    have heq :
        (fun ω => (2 * |leaveOneOut X i ω| + M) * (|X i ω| ^ 3 / 2)) =
          fun ω =>
            1 * ((fun ω => |leaveOneOut X i ω|) * fun ω => |X i ω| ^ 3) ω +
              (M / 2) * |X i ω| ^ 3 := by
      ext ω; simp [Pi.mul_apply]; ring
    rw [heq]
    exact (hW3.const_mul 1).add ((h3 i).const_mul (M / 2))
  have hterm2 :
      |cWpf * EX2 - ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ| ≤
        (1 + M / 2) * EX3 := by
    rw [hWpf_X2]
    have hEQ :
        ∫ ω, (leaveOneOut X i ω * steinSolution z (leaveOneOut X i ω)) *
            (X i ω) ^ 2 ∂μ -
          ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ =
        ∫ ω, (leaveOneOut X i ω * steinSolution z (leaveOneOut X i ω)) *
            (X i ω) ^ 2 -
          kernelSteinProductMass (X := X) z i ω ∂μ := by
      rw [integral_sub hWpfX2_int hA_int]
    rw [hEQ]
    refine (abs_integral_le_integral_abs).trans ?_
    refine (integral_mono hDiff_int.abs hMaj_int fun ω => ?_).trans ?_
    · simpa [Pi.sub_apply] using hpt ω
    · have hprod :=
        hindep3.integral_mul_eq_mul_integral hWabs.aestronglyMeasurable
          (h3 i).aestronglyMeasurable
      calc
        ∫ ω, (2 * |leaveOneOut X i ω| + M) * (|X i ω| ^ 3 / 2) ∂μ =
            ∫ ω, ((fun ω => |leaveOneOut X i ω|) * fun ω => |X i ω| ^ 3) ω +
              (M / 2) * |X i ω| ^ 3 ∂μ := by
          congr 1; ext ω; simp [Pi.mul_apply]; ring
        _ = ∫ ω, ((fun ω => |leaveOneOut X i ω|) * fun ω => |X i ω| ^ 3) ω ∂μ +
              (M / 2) * ∫ ω, |X i ω| ^ 3 ∂μ := by
          rw [integral_add hW3 ((h3 i).const_mul (M / 2)), integral_const_mul]
        _ = (∫ ω, |leaveOneOut X i ω| ∂μ) * ∫ ω, |X i ω| ^ 3 ∂μ +
              (M / 2) * ∫ ω, |X i ω| ^ 3 ∂μ := by rw [hprod]
        _ = (EW + M / 2) * EX3 := by simp only [EW, EX3]; ring
        _ ≤ (1 + M / 2) * EX3 := by nlinarith [hWle, hEX30, hM0, hEW0]
  -- Combine
  have hfinal :
      |cWf * EX2 - ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ| ≤
        (2 + M) * ((3 : ℝ) / 2) * EX3 := by
    calc
      |cWf * EX2 - ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ|
          ≤ |cWf * EX2 - cWpf * EX2| +
            |cWpf * EX2 - ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ| :=
          abs_sub_le _ _ _
      _ ≤ (2 + M) * EX3 + (1 + M / 2) * EX3 := add_le_add hterm1 hterm2
      _ = (2 + M + 1 + M / 2) * EX3 := by ring
      _ = (3 + (3 / 2) * M) * EX3 := by ring
      _ ≤ (2 + M) * ((3 : ℝ) / 2) * EX3 := by
          -- 3 + 1.5 M ≤ 1.5 (2 + M) = 3 + 1.5 M, equality!
          nlinarith [hM0, hEX30]
  simpa [M, EX3] using hfinal

/-- `|∑ E[kernelIndicatorMass] − Φ| ≤ 6γ` via residual identity and the
independence residual majorant. -/
lemma abs_sum_EB_sub_Phi_le
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (z : ℝ) :
    |(∑ i : ι, ∫ ω, kernelIndicatorMass (X := X) z i ω ∂μ) -
      cdf (gaussianReal 0 1) z| ≤
      6 * thirdMomentSum (X := X) μ := by
  set γ : ℝ := thirdMomentSum (X := X) μ
  have hid := residual_identity_indicator_sub_Phi hX hXmeas h_indep h_mean hvar z
  rw [hid]
  set cWf : ℝ := ∫ ω, sumX X ω * steinSolution z (sumX X ω) ∂μ with hcWf_def
  have hsq := sum_integral_sq_eq_one hX h_mean hvar
  have hdecomp :
      cWf - ∑ i, ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ =
        ∑ i, (cWf * (∫ ω, (X i ω) ^ 2 ∂μ) -
          ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ) := by
    have hc : cWf = cWf * ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ := by rw [hsq, mul_one]
    have hc' : cWf * ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ =
        ∑ i, cWf * ∫ ω, (X i ω) ^ 2 ∂μ := by rw [Finset.mul_sum]
    calc
      cWf - ∑ i, ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ
          = cWf * ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ -
              ∑ i, ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ := by rw [← hc]
      _ = ∑ i, cWf * ∫ ω, (X i ω) ^ 2 ∂μ -
              ∑ i, ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ := by rw [hc']
      _ = ∑ i, (cWf * ∫ ω, (X i ω) ^ 2 ∂μ -
              ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ) := by
            rw [← Finset.sum_sub_distrib]
  change |cWf - ∑ i, ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ| ≤ 6 * γ
  rw [hdecomp]
  have hsum_le :
      |∑ i, (cWf * (∫ ω, (X i ω) ^ 2 ∂μ) -
          ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ)| ≤
        (2 + sqrt (2 * π) / 2) * ((3 : ℝ) / 2) * γ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm (i : ι) :
        |cWf * (∫ ω, (X i ω) ^ 2 ∂μ) -
            ∫ ω, kernelSteinProductMass (X := X) z i ω ∂μ| ≤
          (2 + sqrt (2 * π) / 2) * ((3 : ℝ) / 2) * ∫ ω, |X i ω| ^ 3 ∂μ := by
      simpa [cWf, hcWf_def] using
        abs_cWf_mul_sq_sub_productMass_le hX hXmeas h_indep h_mean hvar h3 z i
    refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
    have hsum :
        ∑ i, (2 + sqrt (2 * π) / 2) * ((3 : ℝ) / 2) * ∫ ω, |X i ω| ^ 3 ∂μ =
          (2 + sqrt (2 * π) / 2) * ((3 : ℝ) / 2) * γ := by
      simp only [γ, thirdMomentSum, Finset.mul_sum]
    exact hsum.le
  refine hsum_le.trans ?_
  have hγ0 : 0 ≤ γ := thirdMomentSum_nonneg h3
  have hcoeff := residualMajorantCoeff_le_six
  nlinarith [hcoeff, hγ0]

/-! ### Concentration upgrade: `|F - sum E[B_i]| = O(gamma)` -/

/-- CGS (3.30) coefficient: `sqrt 2 * (3/2) + 2(sqrt 2 + 1)`. -/
def concentrationUpgradeCoeff : ℝ :=
  Real.sqrt 2 * ((3 : ℝ) / 2) + 2 * (Real.sqrt 2 + 1)

lemma concentrationUpgradeCoeff_nonneg : 0 ≤ concentrationUpgradeCoeff := by
  unfold concentrationUpgradeCoeff; positivity

lemma concentrationUpgradeCoeff_add_six_le_thirty :
    concentrationUpgradeCoeff + 6 ≤ thirdMomentBerryEsseenConstant := by
  have hsqrt : Real.sqrt 2 ≤ (2 : ℝ) := by
    have h := sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ 4)
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]
    rwa [h4] at h
  have hbound :
      Real.sqrt 2 * ((3 : ℝ) / 2) + 2 * (Real.sqrt 2 + 1) + 6 ≤ 30 := by
    nlinarith [hsqrt]
  simpa [concentrationUpgradeCoeff, thirdMomentBerryEsseenConstant] using hbound

/-- CDF of the leave-one-out sum. -/
noncomputable def leaveOneOutCdf (i : ι) (x : ℝ) : ℝ :=
  μ.real {ω | leaveOneOut X i ω ≤ x}

omit [IsProbabilityMeasure μ] in
lemma leaveOneOutCdf_nonneg (i : ι) (x : ℝ) :
    0 ≤ leaveOneOutCdf (X := X) (μ := μ) i x :=
  measureReal_nonneg

lemma leaveOneOutCdf_le_one (i : ι) (x : ℝ) :
    leaveOneOutCdf (X := X) (μ := μ) i x ≤ 1 := by
  have : μ {ω | leaveOneOut X i ω ≤ x} ≤ 1 := prob_le_one
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2 this

lemma leaveOneOutCdf_mono (i : ι) {u v : ℝ} (huv : u ≤ v) :
    leaveOneOutCdf (X := X) (μ := μ) i u ≤ leaveOneOutCdf (X := X) (μ := μ) i v :=
  measureReal_mono (fun _ h => h.trans huv) (measure_ne_top _ _)

lemma measurable_leaveOneOutCdf (i : ι) :
    Measurable (leaveOneOutCdf (X := X) (μ := μ) i) :=
  Monotone.measurable fun _ _ h => leaveOneOutCdf_mono i h

omit [IsProbabilityMeasure μ] in
/-- Indicator integral equals leave-one-out CDF. -/
lemma integral_leaveOneOut_indicator_eq_cdf
    (hXmeas : ∀ k, Measurable (X k)) (i : ι) (y : ℝ) :
    ∫ ω, (if leaveOneOut X i ω ≤ y then (1 : ℝ) else 0) ∂μ =
      leaveOneOutCdf (X := X) (μ := μ) i y := by
  have hset : MeasurableSet {ω | leaveOneOut X i ω ≤ y} :=
    measurableSet_le (measurable_leaveOneOut hXmeas i) measurable_const
  have heq :
      (fun ω => if leaveOneOut X i ω ≤ y then (1 : ℝ) else 0) =
        ({ω | leaveOneOut X i ω ≤ y}).indicator fun _ => (1 : ℝ) := by
    ext ω; by_cases h : leaveOneOut X i ω ≤ y <;> simp [h, indicator]
  rw [heq, integral_indicator hset, integral_const, smul_eq_mul, mul_one]
  simp [leaveOneOutCdf, measureReal_def]

/-- `|F_{W^{(i)}}(u) - F_{W^{(i)}}(v)| ≤ sqrt2 |u-v| + 2(sqrt2+1)γ`. -/
lemma abs_leaveOneOutCdf_sub_le
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (i : ι) (u v : ℝ) :
    |leaveOneOutCdf (X := X) (μ := μ) i u -
        leaveOneOutCdf (X := X) (μ := μ) i v| ≤
      Real.sqrt 2 * |u - v| +
        2 * (Real.sqrt 2 + 1) * thirdMomentSum (X := X) μ := by
  wlog huv : u ≤ v generalizing u v
  · simpa [abs_sub_comm u v,
      abs_sub_comm (leaveOneOutCdf (X := X) (μ := μ) i u)] using
      this v u (le_of_not_ge huv)
  have hmeas_u : MeasurableSet {ω | leaveOneOut X i ω ≤ u} :=
    measurableSet_le (measurable_leaveOneOut hXmeas i) measurable_const
  have hsub : {ω | leaveOneOut X i ω ≤ u} ⊆ {ω | leaveOneOut X i ω ≤ v} :=
    fun _ h => h.trans huv
  have hdiff' :
      leaveOneOutCdf (X := X) (μ := μ) i v -
          leaveOneOutCdf (X := X) (μ := μ) i u =
        μ.real ({ω | leaveOneOut X i ω ≤ v} \
          {ω | leaveOneOut X i ω ≤ u}) := by
    simp only [leaveOneOutCdf]
    exact (measureReal_sdiff hsub hmeas_u).symm
  have hsubset :
      {ω | leaveOneOut X i ω ≤ v} \ {ω | leaveOneOut X i ω ≤ u} ⊆
        {ω | u ≤ leaveOneOut X i ω ∧ leaveOneOut X i ω ≤ v} := by
    intro ω h
    have h' : leaveOneOut X i ω ≤ v ∧ ¬ leaveOneOut X i ω ≤ u := by
      simpa [Set.mem_sdiff, mem_setOf_eq] using h
    exact ⟨le_of_lt (lt_of_not_ge h'.2), h'.1⟩
  have hle :
      leaveOneOutCdf (X := X) (μ := μ) i v -
          leaveOneOutCdf (X := X) (μ := μ) i u ≤
        μ.real {ω | u ≤ leaveOneOut X i ω ∧ leaveOneOut X i ω ≤ v} := by
    rw [hdiff']
    exact measureReal_mono hsubset (measure_ne_top _ _)
  have hconc :=
    concentration_leaveOneOut hX hXmeas h_indep h_mean hvar h3 i huv
  have habs :
      |leaveOneOutCdf (X := X) (μ := μ) i u -
          leaveOneOutCdf (X := X) (μ := μ) i v| =
        leaveOneOutCdf (X := X) (μ := μ) i v -
          leaveOneOutCdf (X := X) (μ := μ) i u := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (leaveOneOutCdf_mono i huv))]
  calc
    |leaveOneOutCdf (X := X) (μ := μ) i u -
          leaveOneOutCdf (X := X) (μ := μ) i v|
        = leaveOneOutCdf (X := X) (μ := μ) i v -
            leaveOneOutCdf (X := X) (μ := μ) i u := habs
    _ ≤ Real.sqrt 2 * (v - u) +
          2 * (Real.sqrt 2 + 1) * thirdMomentSum (X := X) μ :=
        hle.trans hconc
    _ = Real.sqrt 2 * |u - v| +
          2 * (Real.sqrt 2 + 1) * thirdMomentSum (X := X) μ := by
        rw [abs_sub_comm u v, abs_of_nonneg (sub_nonneg.mpr huv)]


/-- `P(W <= z) = E[leaveOneOutCdf(z - X_i)]` by leave-one-out independence. -/
lemma cdf_sumX_eq_integral_leaveOneOutCdf
    (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ)
    (i : ι) (z : ℝ) :
    cdf (μ.map (sumX X)) z =
      ∫ ω, leaveOneOutCdf (X := X) (μ := μ) i (z - X i ω) ∂μ := by
  haveI : IsProbabilityMeasure (μ.map (sumX X)) :=
    isProbabilityMeasure_map_sumX (μ := μ) (X := X) fun j => (hXmeas j).aemeasurable
  have hWmeas := measurable_sumX hXmeas
  have hF : cdf (μ.map (sumX X)) z = μ.real {ω | sumX X ω ≤ z} := by
    rw [cdf_map_sumX_eq_real (fun j => (hXmeas j).aemeasurable)]
    simp only [Measure.real, Measure.map_apply hWmeas measurableSet_Iic]
    rfl
  have hInd := indepFun_leaveOneOut (X := X) (μ := μ) hXmeas h_indep i
  set f : ℝ × ℝ → ℝ := fun p => if p.1 + p.2 ≤ z then (1 : ℝ) else 0
  have hf_meas : Measurable f :=
    Measurable.ite (measurableSet_le (measurable_fst.add measurable_snd) measurable_const)
      measurable_const measurable_const
  have hf_int : Integrable f
      ((μ.map (leaveOneOut X i)).prod (μ.map (X i))) := by
    refine (integrable_const (1 : ℝ)).mono' hf_meas.aestronglyMeasurable ?_
    filter_upwards with p
    simp only [f, Real.norm_eq_abs]
    split_ifs <;> norm_num
  have hmap_eq :=
    hInd.map_prod_eq_prod_map_map
      (measurable_leaveOneOut hXmeas i).aemeasurable (hXmeas i).aemeasurable
  have hpair : AEMeasurable (fun ω => (leaveOneOut X i ω, X i ω)) μ :=
    (measurable_leaveOneOut hXmeas i).aemeasurable.prodMk (hXmeas i).aemeasurable
  have hind_ind :
      μ.real {ω | sumX X ω ≤ z} =
        ∫ ω, (if sumX X ω ≤ z then (1 : ℝ) else 0) ∂μ := by
    have hset : MeasurableSet {ω | sumX X ω ≤ z} :=
      measurableSet_le hWmeas measurable_const
    have heq :
        (fun ω => if sumX X ω ≤ z then (1 : ℝ) else 0) =
          ({ω | sumX X ω ≤ z}).indicator fun _ => (1 : ℝ) := by
      ext ω; by_cases h : sumX X ω ≤ z <;> simp [h, indicator]
    rw [heq, integral_indicator hset, integral_const, smul_eq_mul, mul_one]
    simp [measureReal_def]
  have hleft :
      ∫ ω, (if sumX X ω ≤ z then (1 : ℝ) else 0) ∂μ =
        ∫ p, f p ∂((μ.map (leaveOneOut X i)).prod (μ.map (X i))) := by
    have h1 :
        ∫ ω, (if sumX X ω ≤ z then (1 : ℝ) else 0) ∂μ =
          ∫ ω, f (leaveOneOut X i ω, X i ω) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun ω => by
        simp only [f, leaveOneOut_add (X := X) i ω])
    have h2 :
        ∫ ω, f (leaveOneOut X i ω, X i ω) ∂μ =
          ∫ p, f p ∂(μ.map fun ω => (leaveOneOut X i ω, X i ω)) :=
      (integral_map hpair hf_meas.aestronglyMeasurable).symm
    rw [h1, h2, hmap_eq]
  have hright :
      ∫ p, f p ∂((μ.map (leaveOneOut X i)).prod (μ.map (X i))) =
        ∫ ω, leaveOneOutCdf (X := X) (μ := μ) i (z - X i ω) ∂μ := by
    -- Iterate as ∫_ξ ∫_w f(w,ξ) via product swap
    have hswap := integral_prod_symm f hf_int
    rw [hswap]
    have hinner (ξ : ℝ) :
        ∫ w, f (w, ξ) ∂(μ.map (leaveOneOut X i)) =
          leaveOneOutCdf (X := X) (μ := μ) i (z - ξ) := by
      have hfξ : AEStronglyMeasurable (fun w : ℝ => f (w, ξ))
          (μ.map (leaveOneOut X i)) :=
        (Measurable.ite
          (measurableSet_le (measurable_id.add_const ξ) measurable_const)
          measurable_const measurable_const).aestronglyMeasurable
      have hmap :=
        integral_map (measurable_leaveOneOut hXmeas i).aemeasurable hfξ
      have heq :
          (fun ω => f (leaveOneOut X i ω, ξ)) =
            fun ω => if leaveOneOut X i ω ≤ z - ξ then (1 : ℝ) else 0 := by
        ext ω
        simp only [f]
        by_cases h : leaveOneOut X i ω + ξ ≤ z
        · have : leaveOneOut X i ω ≤ z - ξ := by linarith
          simp [h, this]
        · have : ¬ leaveOneOut X i ω ≤ z - ξ := by linarith
          simp [h, this]
      calc
        ∫ w, f (w, ξ) ∂(μ.map (leaveOneOut X i)) =
            ∫ ω, f (leaveOneOut X i ω, ξ) ∂μ := hmap
        _ = ∫ ω, (if leaveOneOut X i ω ≤ z - ξ then (1 : ℝ) else 0) ∂μ := by rw [heq]
        _ = leaveOneOutCdf (X := X) (μ := μ) i (z - ξ) :=
              integral_leaveOneOut_indicator_eq_cdf hXmeas i (z - ξ)
    have hcong :
        ∫ ξ, (∫ w, f (w, ξ) ∂(μ.map (leaveOneOut X i))) ∂(μ.map (X i)) =
          ∫ ξ, leaveOneOutCdf (X := X) (μ := μ) i (z - ξ) ∂(μ.map (X i)) :=
      integral_congr_ae (Eventually.of_forall hinner)
    rw [hcong]
    exact integral_map (hXmeas i).aemeasurable
      (f := fun ξ => leaveOneOutCdf (X := X) (μ := μ) i (z - ξ))
      ((measurable_leaveOneOutCdf i).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable
  rw [hF, hind_ind, hleft, hright]

omit [IsProbabilityMeasure μ] in
/-- Product integrability of `K * 1_{W'+t <= z}`. -/
lemma integrable_uncurry_kernel_mul_indicator
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (z : ℝ) (i : ι) :
    Integrable (fun p : Ω × ℝ =>
      kernelDensityFwd (X i p.1) p.2 *
        (if leaveOneOut X i p.1 + p.2 ≤ z then (1 : ℝ) else 0)) (μ.prod volume) := by
  have hK := integrable_uncurry_kernelDensityFwd i (hX i) (hXmeas i)
  have hsm : AEStronglyMeasurable
      (fun p : Ω × ℝ => kernelDensityFwd (X i p.1) p.2 *
        (if leaveOneOut X i p.1 + p.2 ≤ z then (1 : ℝ) else 0)) (μ.prod volume) := by
    refine ((measurable_kernelDensityFwd_pair i (hXmeas i)).mul ?_).aestronglyMeasurable
    exact Measurable.ite
      (measurableSet_le
        ((measurable_leaveOneOut hXmeas i |>.comp measurable_fst).add measurable_snd)
        measurable_const)
      measurable_const measurable_const
  refine hK.mono' hsm ?_
  filter_upwards with p
  have hk := kernelDensityFwd_nonneg (X i p.1) p.2
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
  split_ifs <;> simp [hk]

/-- Independence factorization for kernel indicator at fixed `t`. -/
lemma integral_indicator_mul_kernel_eq_mul
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ)
    (z : ℝ) (i : ι) (t : ℝ) :
    ∫ ω, (if leaveOneOut X i ω + t ≤ z then (1 : ℝ) else 0) *
        kernelDensityFwd (X i ω) t ∂μ =
      leaveOneOutCdf (X := X) (μ := μ) i (z - t) *
        expectedKernelFwd (X := X) (μ := μ) i t := by
  have hInd := indepFun_leaveOneOut (X := X) (μ := μ) hXmeas h_indep i
  have hg : Measurable fun w : ℝ => if w + t ≤ z then (1 : ℝ) else 0 :=
    Measurable.ite (measurableSet_le (measurable_id.add_const t) measurable_const)
      measurable_const measurable_const
  have hK : Measurable fun ξ : ℝ => kernelDensityFwd ξ t :=
    measurable_kernelDensityFwd_left t
  have hindep :
      IndepFun (fun ω => if leaveOneOut X i ω + t ≤ z then (1 : ℝ) else 0)
        (fun ω => kernelDensityFwd (X i ω) t) μ :=
    hInd.comp hg hK
  have hIntg : Integrable
      (fun ω => if leaveOneOut X i ω + t ≤ z then (1 : ℝ) else 0) μ := by
    refine (integrable_const (1 : ℝ)).mono' ?_ ?_
    · exact (hg.comp (measurable_leaveOneOut hXmeas i)).aestronglyMeasurable
    · filter_upwards with ω; split_ifs <;> simp
  have hIntK := integrable_kernelDensityFwd_eval i (hX i) (hXmeas i) t
  have hmul :=
    hindep.integral_mul_eq_mul_integral hIntg.aestronglyMeasurable hIntK.aestronglyMeasurable
  have hcdf :
      ∫ ω, (if leaveOneOut X i ω + t ≤ z then (1 : ℝ) else 0) ∂μ =
        leaveOneOutCdf (X := X) (μ := μ) i (z - t) := by
    have heq :
        (fun ω => if leaveOneOut X i ω + t ≤ z then (1 : ℝ) else 0) =
          fun ω => if leaveOneOut X i ω ≤ z - t then (1 : ℝ) else 0 := by
      ext ω
      by_cases h : leaveOneOut X i ω + t ≤ z
      · have : leaveOneOut X i ω ≤ z - t := by linarith
        simp [h, this]
      · have : ¬ leaveOneOut X i ω ≤ z - t := by linarith
        simp [h, this]
    rw [heq, integral_leaveOneOut_indicator_eq_cdf hXmeas i]
  simpa [expectedKernelFwd, hcdf] using hmul

/-- `E[B_i] = integral leaveOneOutCdf(z-t) * Khat_i(t) dt`. -/
lemma expected_kernelIndicatorMass_eq_integral_expected
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ)
    (z : ℝ) (i : ι) :
    ∫ ω, kernelIndicatorMass (X := X) z i ω ∂μ =
      ∫ t : ℝ, leaveOneOutCdf (X := X) (μ := μ) i (z - t) *
        expectedKernelFwd (X := X) (μ := μ) i t := by
  set g : Ω × ℝ → ℝ := fun p =>
    kernelDensityFwd (X i p.1) p.2 *
      (if leaveOneOut X i p.1 + p.2 ≤ z then (1 : ℝ) else 0)
  have hInt : Integrable g (μ.prod volume) :=
    integrable_uncurry_kernel_mul_indicator hX hXmeas z i
  have hB_eq : ∫ ω, kernelIndicatorMass (X := X) z i ω ∂μ =
      ∫ p, g p ∂(μ.prod volume) := by
    change ∫ ω, (∫ t : ℝ, g (ω, t)) ∂μ = ∫ p, g p ∂(μ.prod volume)
    exact integral_integral hInt
  have hswap : ∫ p, g p ∂(μ.prod volume) = ∫ t : ℝ, ∫ ω, g (ω, t) ∂μ :=
    integral_prod_symm g hInt
  rw [hB_eq, hswap]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  calc
    ∫ ω, g (ω, t) ∂μ =
        ∫ ω, (if leaveOneOut X i ω + t ≤ z then (1 : ℝ) else 0) *
          kernelDensityFwd (X i ω) t ∂μ :=
      integral_congr_ae (Eventually.of_forall fun ω => by dsimp [g]; ring)
    _ = leaveOneOutCdf (X := X) (μ := μ) i (z - t) *
          expectedKernelFwd (X := X) (μ := μ) i t :=
      integral_indicator_mul_kernel_eq_mul hX hXmeas h_indep z i t

omit [Fintype ι] [DecidableEq ι] in
/-- Integrability of `|t| * Khat_i`. -/
lemma integrable_abs_mul_expectedKernelFwd (i : ι)
    (hX : MemLp (X i) 2 μ) (hXmeas : Measurable (X i))
    (h3 : Integrable (fun ω => |X i ω| ^ 3) μ) :
    Integrable (fun t => |t| * expectedKernelFwd (X := X) (μ := μ) i t) := by
  have hUnc := integrable_uncurry_abs_t_mul_kernel i hX hXmeas h3
  have hR := hUnc.integral_prod_right
  have heq :
      (fun t => ∫ ω, |t| * kernelDensityFwd (X i ω) t ∂μ) =
        fun t => |t| * expectedKernelFwd (X := X) (μ := μ) i t := by
    funext t
    calc
      ∫ ω, |t| * kernelDensityFwd (X i ω) t ∂μ =
          |t| * ∫ ω, kernelDensityFwd (X i ω) t ∂μ :=
        integral_const_mul _ _
      _ = |t| * expectedKernelFwd (X := X) (μ := μ) i t := rfl
  convert hR using 1
  exact heq.symm


omit [DecidableEq ι] in
/-- One-coordinate integrated concentration majorant. -/
lemma integral_conc_majorant_mul_expectedKernel_le
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (i : ι) :
    ∫ t : ℝ,
        (Real.sqrt 2 * (|t| + ∫ ω, |X i ω| ∂μ) +
          2 * (Real.sqrt 2 + 1) * thirdMomentSum (X := X) μ) *
          expectedKernelFwd (X := X) (μ := μ) i t ≤
      Real.sqrt 2 * ((3 : ℝ) / 2) * ∫ ω, |X i ω| ^ 3 ∂μ +
        2 * (Real.sqrt 2 + 1) * thirdMomentSum (X := X) μ *
          ∫ ω, (X i ω) ^ 2 ∂μ := by
  set Khat := expectedKernelFwd (X := X) (μ := μ) i
  set EX := ∫ ω, |X i ω| ∂μ
  set EX2 := ∫ ω, (X i ω) ^ 2 ∂μ
  set EX3 := ∫ ω, |X i ω| ^ 3 ∂μ
  set γ := thirdMomentSum (X := X) μ
  set C := 2 * (Real.sqrt 2 + 1) * γ
  have hKint := integrable_expectedKernelFwd i (hX i) (hXmeas i)
  have hAbsK : ∫ t, |t| * Khat t = (1 / 2 : ℝ) * EX3 :=
    integral_abs_mul_expectedKernelFwd i (hX i) (hXmeas i) (h3 i)
  have hInt_absK := integrable_abs_mul_expectedKernelFwd i (hX i) (hXmeas i) (h3 i)
  have hEX2 : EX2 = ∫ t, Khat t :=
    (integral_expectedKernelFwd i (hX i) (hXmeas i)).symm
  have hAbsX : Integrable (fun ω => |X i ω|) μ :=
    ((hX i).integrable one_le_two).abs
  have hYoung : EX * EX2 ≤ EX3 :=
    integral_abs_mul_integral_sq_le (hXmeas i) hAbsX ((hX i).integrable_sq) (h3 i)
  have hEX30 : 0 ≤ EX3 :=
    integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _
  have hval :
      ∫ t, (Real.sqrt 2 * (|t| + EX) + C) * Khat t =
        Real.sqrt 2 * (EX3 / 2) + Real.sqrt 2 * EX * EX2 + C * EX2 := by
    have heq :
        (fun t => (Real.sqrt 2 * (|t| + EX) + C) * Khat t) =
          fun t => Real.sqrt 2 * (|t| * Khat t) + (Real.sqrt 2 * EX + C) * Khat t := by
      funext t; ring
    have hA := hInt_absK.const_mul (Real.sqrt 2)
    have hB := hKint.const_mul (Real.sqrt 2 * EX + C)
    rw [heq, integral_add hA hB, integral_const_mul, integral_const_mul, hAbsK, ← hEX2]
    ring
  have hle :
      Real.sqrt 2 * (EX3 / 2) + Real.sqrt 2 * EX * EX2 + C * EX2 ≤
        Real.sqrt 2 * ((3 : ℝ) / 2) * EX3 + C * EX2 := by
    nlinarith [sqrt_nonneg (2 : ℝ), hYoung, hEX30]
  calc
    ∫ t, (Real.sqrt 2 * (|t| + EX) + C) * Khat t =
        Real.sqrt 2 * (EX3 / 2) + Real.sqrt 2 * EX * EX2 + C * EX2 := hval
    _ ≤ Real.sqrt 2 * ((3 : ℝ) / 2) * EX3 + C * EX2 := hle
    _ = Real.sqrt 2 * ((3 : ℝ) / 2) * ∫ ω, |X i ω| ^ 3 ∂μ +
          2 * (Real.sqrt 2 + 1) * γ * ∫ ω, (X i ω) ^ 2 ∂μ := by
      simp only [EX3, EX2, C, γ]

/-- `|F - leaveOneOutCdf(z-t)| ≤ sqrt2(|t| + E|X|) + Cγ`. -/
lemma abs_cdf_sub_leaveOneOutCdf_shift_le
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (i : ι) (z t : ℝ) :
    |cdf (μ.map (sumX X)) z - leaveOneOutCdf (X := X) (μ := μ) i (z - t)| ≤
      Real.sqrt 2 * (|t| + ∫ ω, |X i ω| ∂μ) +
        2 * (Real.sqrt 2 + 1) * thirdMomentSum (X := X) μ := by
  set γ := thirdMomentSum (X := X) μ
  set Cγ := 2 * (Real.sqrt 2 + 1) * γ
  set EX := ∫ ω, |X i ω| ∂μ
  have hFeq := cdf_sumX_eq_integral_leaveOneOutCdf hXmeas h_indep i z
  rw [hFeq]
  have hInt_cdf : Integrable
      (fun ω => leaveOneOutCdf (X := X) (μ := μ) i (z - X i ω)) μ := by
    refine (integrable_const (1 : ℝ)).mono' ?_ ?_
    · exact ((measurable_leaveOneOutCdf i).comp
        (measurable_const.sub (hXmeas i))).aestronglyMeasurable
    · filter_upwards with ω
      have hnn := leaveOneOutCdf_nonneg (X := X) (μ := μ) i (z - X i ω)
      have hle := leaveOneOutCdf_le_one (X := X) (μ := μ) i (z - X i ω)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]; exact hle
  have hconst : Integrable
      (fun _ : Ω => leaveOneOutCdf (X := X) (μ := μ) i (z - t)) μ :=
    integrable_const _
  have hsub :
      |∫ ω, leaveOneOutCdf (X := X) (μ := μ) i (z - X i ω) ∂μ -
          leaveOneOutCdf (X := X) (μ := μ) i (z - t)| ≤
        ∫ ω, |leaveOneOutCdf (X := X) (μ := μ) i (z - X i ω) -
          leaveOneOutCdf (X := X) (μ := μ) i (z - t)| ∂μ := by
    set c := leaveOneOutCdf (X := X) (μ := μ) i (z - t)
    have habs :=
      abs_integral_le_integral_abs
        (f := fun ω => leaveOneOutCdf (X := X) (μ := μ) i (z - X i ω) - c)
        (μ := μ)
    have heq :
        ∫ ω, leaveOneOutCdf (X := X) (μ := μ) i (z - X i ω) - c ∂μ =
          ∫ ω, leaveOneOutCdf (X := X) (μ := μ) i (z - X i ω) ∂μ - c := by
      have hc : c = ∫ _ : Ω, c ∂μ := by simp [c]
      calc
        ∫ ω, leaveOneOutCdf (X := X) (μ := μ) i (z - X i ω) - c ∂μ =
            ∫ ω, leaveOneOutCdf (X := X) (μ := μ) i (z - X i ω) ∂μ -
              ∫ _ : Ω, c ∂μ :=
          integral_sub hInt_cdf hconst
        _ = ∫ ω, leaveOneOutCdf (X := X) (μ := μ) i (z - X i ω) ∂μ - c := by
              rw [← hc]
    rwa [heq] at habs
  refine hsub.trans ?_
  have hAbsX : Integrable (fun ω => |X i ω|) μ :=
    ((hX i).integrable one_le_two).abs
  have hXt : Integrable (fun ω => |X i ω - t|) μ := by
    refine (hAbsX.add (integrable_const |t|)).mono' ?_ ?_
    · exact ((hXmeas i).sub_const t).abs.aestronglyMeasurable
    · filter_upwards with ω
      have : |X i ω - t| ≤ |X i ω| + |t| := abs_sub _ _
      simpa [Real.norm_eq_abs] using this
  have hMaj1 : Integrable (fun ω => Real.sqrt 2 * |X i ω - t| + Cγ) μ :=
    (hXt.const_mul (Real.sqrt 2)).add (integrable_const Cγ)
  have hpoint (ω : Ω) :
      |leaveOneOutCdf (X := X) (μ := μ) i (z - X i ω) -
          leaveOneOutCdf (X := X) (μ := μ) i (z - t)| ≤
        Real.sqrt 2 * |X i ω - t| + Cγ := by
    have h := abs_leaveOneOutCdf_sub_le hX hXmeas h_indep h_mean hvar h3 i
      (z - X i ω) (z - t)
    have hlen : |(z - X i ω) - (z - t)| = |X i ω - t| := by
      calc
        |(z - X i ω) - (z - t)| = |t - X i ω| := by ring_nf
        _ = |X i ω - t| := abs_sub_comm _ _
    rw [hlen] at h
    simpa [Cγ, γ] using h
  have hmono1 :
      ∫ ω, |leaveOneOutCdf (X := X) (μ := μ) i (z - X i ω) -
          leaveOneOutCdf (X := X) (μ := μ) i (z - t)| ∂μ ≤
        ∫ ω, Real.sqrt 2 * |X i ω - t| + Cγ ∂μ :=
    integral_mono (hInt_cdf.sub hconst).abs hMaj1 fun ω => by
      simpa [Pi.sub_apply, Real.norm_eq_abs] using hpoint ω
  have hmono2 :
      ∫ ω, Real.sqrt 2 * |X i ω - t| + Cγ ∂μ ≤
        Real.sqrt 2 * (|t| + EX) + Cγ := by
    have hMaj2 : Integrable (fun ω => Real.sqrt 2 * (|X i ω| + |t|) + Cγ) μ :=
      ((hAbsX.add (integrable_const |t|)).const_mul (Real.sqrt 2)).add
        (integrable_const Cγ)
    have hle :
        ∫ ω, Real.sqrt 2 * |X i ω - t| + Cγ ∂μ ≤
          ∫ ω, Real.sqrt 2 * (|X i ω| + |t|) + Cγ ∂μ :=
      integral_mono hMaj1 hMaj2 fun ω => by
        have : |X i ω - t| ≤ |X i ω| + |t| := abs_sub _ _
        nlinarith [sqrt_nonneg (2 : ℝ), this]
    refine hle.trans_eq ?_
    have heq :
        (fun ω => Real.sqrt 2 * (|X i ω| + |t|) + Cγ) =
          fun ω => Real.sqrt 2 * |X i ω| + (Real.sqrt 2 * |t| + Cγ) := by
      funext ω; ring
    have hA := hAbsX.const_mul (Real.sqrt 2)
    have hB : Integrable (fun _ : Ω => Real.sqrt 2 * |t| + Cγ) μ :=
      integrable_const _
    rw [heq, integral_add hA hB, integral_const_mul, integral_const]
    simp only [smul_eq_mul, Measure.real, measure_univ, ENNReal.toReal_one, EX]
    ring
  exact hmono1.trans hmono2

/-- Concentration upgrade (CGS 3.30):
`|F(z) - sum E[B_i]| ≤ concentrationUpgradeCoeff * γ`. -/
lemma abs_cdf_sub_sum_EB_le
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (z : ℝ) :
    |cdf (μ.map (sumX X)) z -
        ∑ i : ι, ∫ ω, kernelIndicatorMass (X := X) z i ω ∂μ| ≤
      concentrationUpgradeCoeff * thirdMomentSum (X := X) μ := by
  set γ := thirdMomentSum (X := X) μ
  set F := cdf (μ.map (sumX X)) z
  set Cγ := 2 * (Real.sqrt 2 + 1) * γ
  have hγ0 : 0 ≤ γ := thirdMomentSum_nonneg h3
  haveI : IsProbabilityMeasure (μ.map (sumX X)) :=
    isProbabilityMeasure_map_sumX (μ := μ) (X := X) fun j => (hXmeas j).aemeasurable
  have hsq := sum_integral_sq_eq_one hX h_mean hvar
  have hKsum := sum_integral_expectedKernelFwd_eq_one hX hXmeas h_mean hvar
  have hF_decomp :
      F = ∑ i, ∫ t : ℝ, F * expectedKernelFwd (X := X) (μ := μ) i t := by
    calc
      F = F * 1 := (mul_one F).symm
      _ = F * ∑ i, ∫ t, expectedKernelFwd (X := X) (μ := μ) i t := by rw [hKsum]
      _ = ∑ i, F * ∫ t, expectedKernelFwd (X := X) (μ := μ) i t := by
            rw [Finset.mul_sum]
      _ = ∑ i, ∫ t, F * expectedKernelFwd (X := X) (μ := μ) i t := by
            refine Finset.sum_congr rfl fun i _ => ?_
            exact (integral_const_mul F _).symm
  have hB (i : ι) :=
    expected_kernelIndicatorMass_eq_integral_expected hX hXmeas h_indep z i
  have hone (i : ι) :
      |(∫ t : ℝ, F * expectedKernelFwd (X := X) (μ := μ) i t) -
          (∫ t : ℝ, leaveOneOutCdf (X := X) (μ := μ) i (z - t) *
            expectedKernelFwd (X := X) (μ := μ) i t)| ≤
        Real.sqrt 2 * ((3 : ℝ) / 2) * ∫ ω, |X i ω| ^ 3 ∂μ +
          2 * (Real.sqrt 2 + 1) * γ * ∫ ω, (X i ω) ^ 2 ∂μ := by
    set Khat := expectedKernelFwd (X := X) (μ := μ) i
    set EX := ∫ ω, |X i ω| ∂μ
    have hKint := integrable_expectedKernelFwd i (hX i) (hXmeas i)
    have hK0 (t : ℝ) : 0 ≤ Khat t := expectedKernelFwd_nonneg i t
    have hF_int : Integrable (fun t => F * Khat t) := hKint.const_mul F
    have hcdf_int : Integrable
        (fun t => leaveOneOutCdf (X := X) (μ := μ) i (z - t) * Khat t) := by
      refine hKint.mono' ?_ ?_
      · exact ((measurable_leaveOneOutCdf i).comp
          (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
          hKint.aestronglyMeasurable
      · filter_upwards with t
        have hk := hK0 t
        have hle := leaveOneOutCdf_le_one (X := X) (μ := μ) i (z - t)
        have hnn := leaveOneOutCdf_nonneg (X := X) (μ := μ) i (z - t)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk, abs_of_nonneg hnn]
        simpa using mul_le_mul_of_nonneg_right hle hk
    have hdiff_eq :
        (∫ t, F * Khat t) -
            (∫ t, leaveOneOutCdf (X := X) (μ := μ) i (z - t) * Khat t) =
          ∫ t, (F - leaveOneOutCdf (X := X) (μ := μ) i (z - t)) * Khat t := by
      have heq :
          (fun t => (F - leaveOneOutCdf (X := X) (μ := μ) i (z - t)) * Khat t) =
            fun t => F * Khat t -
              leaveOneOutCdf (X := X) (μ := μ) i (z - t) * Khat t := by
        funext t; ring
      calc
        (∫ t, F * Khat t) -
              (∫ t, leaveOneOutCdf (X := X) (μ := μ) i (z - t) * Khat t) =
            ∫ t, F * Khat t -
              leaveOneOutCdf (X := X) (μ := μ) i (z - t) * Khat t :=
          (integral_sub hF_int hcdf_int).symm
        _ = ∫ t, (F - leaveOneOutCdf (X := X) (μ := μ) i (z - t)) * Khat t := by
              simp only [← heq]
    rw [hdiff_eq]
    have hdiff_int : Integrable
        (fun t => (F - leaveOneOutCdf (X := X) (μ := μ) i (z - t)) * Khat t) := by
      have heq :
          (fun t => (F - leaveOneOutCdf (X := X) (μ := μ) i (z - t)) * Khat t) =
            fun t => F * Khat t -
              leaveOneOutCdf (X := X) (μ := μ) i (z - t) * Khat t := by
        funext t; ring
      rw [heq]; exact hF_int.sub hcdf_int
    have habs :
        |∫ t, (F - leaveOneOutCdf (X := X) (μ := μ) i (z - t)) * Khat t| ≤
          ∫ t, |F - leaveOneOutCdf (X := X) (μ := μ) i (z - t)| * Khat t := by
      refine (abs_integral_le_integral_abs).trans_eq ?_
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      have hk := hK0 t
      calc
        |(F - leaveOneOutCdf (X := X) (μ := μ) i (z - t)) * Khat t| =
            |F - leaveOneOutCdf (X := X) (μ := μ) i (z - t)| * |Khat t| :=
          abs_mul _ _
        _ = |F - leaveOneOutCdf (X := X) (μ := μ) i (z - t)| * Khat t := by
              rw [abs_of_nonneg hk]
    have hLeft : Integrable
        (fun t => |F - leaveOneOutCdf (X := X) (μ := μ) i (z - t)| * Khat t) := by
      have heq :
          (fun t => |F - leaveOneOutCdf (X := X) (μ := μ) i (z - t)| * Khat t) =
            fun t => ‖(F - leaveOneOutCdf (X := X) (μ := μ) i (z - t)) * Khat t‖ := by
        funext t
        have hk := hK0 t
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
      rw [heq]; exact hdiff_int.abs
    have hRight : Integrable
        (fun t => (Real.sqrt 2 * (|t| + EX) + Cγ) * Khat t) := by
      have hInt_absK :=
        integrable_abs_mul_expectedKernelFwd i (hX i) (hXmeas i) (h3 i)
      have heq :
          (fun t => (Real.sqrt 2 * (|t| + EX) + Cγ) * Khat t) =
            fun t => Real.sqrt 2 * (|t| * Khat t) +
              (Real.sqrt 2 * EX + Cγ) * Khat t := by
        funext t; ring
      rw [heq]
      exact (hInt_absK.const_mul (Real.sqrt 2)).add
        (hKint.const_mul (Real.sqrt 2 * EX + Cγ))
    have hmono :
        ∫ t, |F - leaveOneOutCdf (X := X) (μ := μ) i (z - t)| * Khat t ≤
          ∫ t, (Real.sqrt 2 * (|t| + EX) + Cγ) * Khat t := by
      refine integral_mono hLeft hRight fun t => ?_
      have hpt :=
        abs_cdf_sub_leaveOneOutCdf_shift_le hX hXmeas h_indep h_mean hvar h3 i z t
      exact mul_le_mul_of_nonneg_right (by simpa [F, EX, Cγ, γ] using hpt) (hK0 t)
    have hval := integral_conc_majorant_mul_expectedKernel_le hX hXmeas h3 i
    exact habs.trans (hmono.trans (by simpa [EX, Cγ, γ] using hval))
  -- Bound each coordinate, then sum; avoid rewriting F inside summands
  have hsum_bound :
      ∑ i : ι, |(∫ t : ℝ, F * expectedKernelFwd (X := X) (μ := μ) i t) -
          (∫ t : ℝ, leaveOneOutCdf (X := X) (μ := μ) i (z - t) *
            expectedKernelFwd (X := X) (μ := μ) i t)| ≤
        concentrationUpgradeCoeff * γ := by
    refine (Finset.sum_le_sum fun i _ => hone i).trans ?_
    have hsum :
        ∑ i, (Real.sqrt 2 * ((3 : ℝ) / 2) * ∫ ω, |X i ω| ^ 3 ∂μ +
            2 * (Real.sqrt 2 + 1) * γ * ∫ ω, (X i ω) ^ 2 ∂μ) =
          concentrationUpgradeCoeff * γ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, γ, thirdMomentSum, hsq,
        concentrationUpgradeCoeff]
      ring
    exact hsum.le
  have hmain :
      |F - ∑ i, ∫ ω, kernelIndicatorMass (X := X) z i ω ∂μ| ≤
        ∑ i : ι, |(∫ t : ℝ, F * expectedKernelFwd (X := X) (μ := μ) i t) -
            (∫ t : ℝ, leaveOneOutCdf (X := X) (μ := μ) i (z - t) *
              expectedKernelFwd (X := X) (μ := μ) i t)| := by
    have h2 :
        ∑ i, ∫ ω, kernelIndicatorMass (X := X) z i ω ∂μ =
          ∑ i, (∫ t, leaveOneOutCdf (X := X) (μ := μ) i (z - t) *
            expectedKernelFwd (X := X) (μ := μ) i t) :=
      Finset.sum_congr rfl fun i _ => hB i
    have h3' :
        F - ∑ i, ∫ ω, kernelIndicatorMass (X := X) z i ω ∂μ =
          (∑ i, ∫ t, F * expectedKernelFwd (X := X) (μ := μ) i t) -
            (∑ i, ∫ t, leaveOneOutCdf (X := X) (μ := μ) i (z - t) *
              expectedKernelFwd (X := X) (μ := μ) i t) :=
      congr_arg₂ (· - ·) hF_decomp h2
    have h4 :
        (∑ i, ∫ t, F * expectedKernelFwd (X := X) (μ := μ) i t) -
            (∑ i, ∫ t, leaveOneOutCdf (X := X) (μ := μ) i (z - t) *
              expectedKernelFwd (X := X) (μ := μ) i t) =
          ∑ i, ((∫ t, F * expectedKernelFwd (X := X) (μ := μ) i t) -
            (∫ t, leaveOneOutCdf (X := X) (μ := μ) i (z - t) *
              expectedKernelFwd (X := X) (μ := μ) i t)) := by
      rw [← Finset.sum_sub_distrib]
    rw [h3', h4]
    exact Finset.abs_sum_le_sum_abs _ _
  exact hmain.trans hsum_bound

/-! ### Pure linear third-moment Berry-Esseen -/

/-- Pure linear third-moment Berry-Esseen: `|F-Phi| ≤ 30 γ` for all `γ`. -/
theorem uniformBerryEsseen_thirdMoment
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (x : ℝ) :
    |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤
      thirdMomentBerryEsseenConstant * thirdMomentSum (X := X) μ := by
  set γ := thirdMomentSum (X := X) μ
  set F := cdf (μ.map (sumX X)) x
  set Phi := cdf (gaussianReal 0 1) x
  set EB := ∑ i : ι, ∫ ω, kernelIndicatorMass (X := X) x i ω ∂μ
  have hγ0 : 0 ≤ γ := thirdMomentSum_nonneg h3
  have hres := abs_sum_EB_sub_Phi_le hX hXmeas h_indep h_mean hvar h3 x
  have hconc := abs_cdf_sub_sum_EB_le hX hXmeas h_indep h_mean hvar h3 x
  have htri : |F - Phi| ≤ |F - EB| + |EB - Phi| := abs_sub_le F EB Phi
  have hsum : |F - EB| + |EB - Phi| ≤
      concentrationUpgradeCoeff * γ + 6 * γ :=
    add_le_add (by simpa [F, EB] using hconc) (by simpa [EB, Phi, γ] using hres)
  have hcoeff := concentrationUpgradeCoeff_add_six_le_thirty
  calc
    |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x|
        = |F - Phi| := by
          simp only [F, Phi]
          rfl
    _ ≤ |F - EB| + |EB - Phi| := htri
    _ ≤ concentrationUpgradeCoeff * γ + 6 * γ := hsum
    _ = (concentrationUpgradeCoeff + 6) * γ := by ring
    _ ≤ thirdMomentBerryEsseenConstant * γ :=
          mul_le_mul_of_nonneg_right hcoeff hγ0

/-- Unconditional bound: `|F-Phi| ≤ 30 * max(γ, 1/30)`. -/
theorem uniformBerryEsseen_thirdMoment_max
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (x : ℝ) :
    |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤
      thirdMomentBerryEsseenConstant *
        max (thirdMomentSum (X := X) μ)
          ((1 : ℝ) / thirdMomentBerryEsseenConstant) := by
  set γ : ℝ := thirdMomentSum (X := X) μ
  set C : ℝ := thirdMomentBerryEsseenConstant
  have hC0 : (0 : ℝ) ≤ C := thirdMomentBerryEsseenConstant_pos.le
  have h := uniformBerryEsseen_thirdMoment hX hXmeas h_indep h_mean hvar h3 x
  exact h.trans (mul_le_mul_of_nonneg_left (le_max_left γ (1 / C)) hC0)

end ProbabilityTheory
