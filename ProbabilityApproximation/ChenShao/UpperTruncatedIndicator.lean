/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.ChenShao.ExponentialConcentration
import ProbabilityApproximation.ChenShao.UpperTruncatedExpectedKernel

/-!
# Indicator residual for the upper-truncated sum

This module bounds the indicator component `R₂,₁` in the expected-kernel decomposition following
Chen--Shao (2005), Section 6.  Proposition 6.1 is applied to the leave-one-out distribution, while
the exact zeroth and first absolute moments of the forward kernel close the coordinate sum.
-/

open MeasureTheory ProbabilityTheory Real Set Filter

noncomputable section

namespace ProbabilityTheory

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ι → Ω → ℝ}

/-- Exponentially weighted continuity of the CDF of the upper-truncated leave-one-out sum. -/
lemma abs_upperTruncatedLeaveOneOutCdf_sub_le_exp
    [DecidableEq ι]
    (hXmeas : ∀ i, Measurable (X i)) (h_indep : iIndepFun X μ)
    (hX2 : ∀ i, MemLp (X i) 2 μ) (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1)
    (h3 : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ)
    (i : ι) (u v : ℝ) :
    |leaveOneOutCdf (X := upperTruncatedFamily X) (μ := μ) i u -
        leaveOneOutCdf (X := upperTruncatedFamily X) (μ := μ) i v| ≤
      Real.exp (-(min u v) / 2) *
        (24 * |u - v| + 48 * thirdMomentSum X μ) := by
  wlog huv : u ≤ v generalizing u v
  · simpa [min_comm, abs_sub_comm u v,
      abs_sub_comm
        (leaveOneOutCdf (X := upperTruncatedFamily X) (μ := μ) i u)] using
      this v u (le_of_not_ge huv)
  let Y := upperTruncatedFamily X
  have hYmeas : ∀ j, Measurable (Y j) := measurable_upperTruncatedFamily hXmeas
  have hmeas_u : MeasurableSet {ω | leaveOneOut Y i ω ≤ u} :=
    measurableSet_le (measurable_leaveOneOut hYmeas i) measurable_const
  have hsubset : {ω | leaveOneOut Y i ω ≤ u} ⊆ {ω | leaveOneOut Y i ω ≤ v} :=
    fun _ h => h.trans huv
  have hdiff :
      leaveOneOutCdf (X := Y) (μ := μ) i v -
          leaveOneOutCdf (X := Y) (μ := μ) i u =
        μ.real ({ω | leaveOneOut Y i ω ≤ v} \ {ω | leaveOneOut Y i ω ≤ u}) := by
    simp only [leaveOneOutCdf]
    exact (measureReal_sdiff hsubset hmeas_u).symm
  have hsdiff_subset :
      {ω | leaveOneOut Y i ω ≤ v} \ {ω | leaveOneOut Y i ω ≤ u} ⊆
        {ω | leaveOneOut Y i ω ∈ Icc u v} := by
    intro ω hω
    have hω' : leaveOneOut Y i ω ≤ v ∧ ¬leaveOneOut Y i ω ≤ u := by
      simpa [Set.mem_sdiff, mem_setOf_eq] using hω
    exact ⟨le_of_lt (lt_of_not_ge hω'.2), hω'.1⟩
  have hmeasure :
      leaveOneOutCdf (X := Y) (μ := μ) i v -
          leaveOneOutCdf (X := Y) (μ := μ) i u ≤
        μ.real {ω | leaveOneOut Y i ω ∈ Icc u v} := by
    rw [hdiff]
    exact measureReal_mono hsdiff_subset (measure_ne_top _ _)
  have hconc :
      μ.real {ω | leaveOneOut Y i ω ∈ Icc u v} ≤
        Real.exp (-u / 2) *
          (24 * (v - u) + 48 * thirdMomentSum X μ) := by
    simpa only [Y, leaveOneOut, upperTruncatedFamily, Function.comp_apply] using
      (chenShao_exponentialConcentration_upperTruncated
        hXmeas h_indep hX2 h_mean hvar h3 i huv)
  have habs :
      |leaveOneOutCdf (X := Y) (μ := μ) i u -
          leaveOneOutCdf (X := Y) (μ := μ) i v| =
        leaveOneOutCdf (X := Y) (μ := μ) i v -
          leaveOneOutCdf (X := Y) (μ := μ) i u := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (leaveOneOutCdf_mono i huv))]
  calc
    |leaveOneOutCdf (X := Y) (μ := μ) i u -
        leaveOneOutCdf (X := Y) (μ := μ) i v| =
        leaveOneOutCdf (X := Y) (μ := μ) i v -
          leaveOneOutCdf (X := Y) (μ := μ) i u := habs
    _ ≤ Real.exp (-u / 2) *
        (24 * (v - u) + 48 * thirdMomentSum X μ) := hmeasure.trans hconc
    _ = Real.exp (-(min u v) / 2) *
        (24 * |u - v| + 48 * thirdMomentSum X μ) := by
      rw [min_eq_left huv, abs_of_nonpos (sub_nonpos.mpr huv)]
      ring

private lemma integral_indicator_sumX_eq_cdf
    [DecidableEq ι] {Y : ι → Ω → ℝ}
    (hYmeas : ∀ i, Measurable (Y i)) (z : ℝ) :
    ∫ ω, (if sumX Y ω ≤ z then (1 : ℝ) else 0) ∂μ =
      cdf (μ.map (sumX Y)) z := by
  have hsumMeas := measurable_sumX hYmeas
  have hset : MeasurableSet {ω | sumX Y ω ≤ z} :=
    measurableSet_le hsumMeas measurable_const
  have heq :
      (fun ω => if sumX Y ω ≤ z then (1 : ℝ) else 0) =
        ({ω | sumX Y ω ≤ z}).indicator fun _ => (1 : ℝ) := by
    ext ω
    by_cases h : sumX Y ω ≤ z <;> simp [h, indicator]
  have hintegral :
      ∫ ω, (if sumX Y ω ≤ z then (1 : ℝ) else 0) ∂μ =
        μ.real {ω | sumX Y ω ≤ z} := by
    rw [heq, integral_indicator hset, integral_const, smul_eq_mul, mul_one]
    simp [measureReal_def]
  have hcdf :
      cdf (μ.map (sumX Y)) z = μ.real {ω | sumX Y ω ≤ z} := by
    rw [cdf_map_sumX_eq_real (fun i => (hYmeas i).aemeasurable)]
    simp only [Measure.real, Measure.map_apply hsumMeas measurableSet_Iic]
    rfl
  exact hintegral.trans hcdf.symm

private lemma integral_upperTruncatedIndicator_eq_integral_leaveOneOutCdf
    [DecidableEq ι]
    (hXmeas : ∀ i, Measurable (X i)) (h_indep : iIndepFun X μ)
    (i : ι) (z : ℝ) :
    ∫ ω, (if upperTruncatedSum X ω ≤ z then (1 : ℝ) else 0) ∂μ =
      ∫ ω, leaveOneOutCdf (X := upperTruncatedFamily X) (μ := μ) i
        (z - upperTruncatedFamily X i ω) ∂μ := by
  have hYmeas := measurable_upperTruncatedFamily hXmeas
  have hYindep := iIndepFun_upperTruncatedFamily h_indep
  change ∫ ω, (if sumX (upperTruncatedFamily X) ω ≤ z then (1 : ℝ) else 0) ∂μ = _
  rw [integral_indicator_sumX_eq_cdf hYmeas z,
    cdf_sumX_eq_integral_leaveOneOutCdf hYmeas hYindep i z]

private lemma integral_upperTruncatedLeaveOneOut_shift_indicator_eq_cdf
    [DecidableEq ι]
    (hXmeas : ∀ i, Measurable (X i)) (i : ι) (z t : ℝ) :
    ∫ ω, (if leaveOneOut (upperTruncatedFamily X) i ω + t ≤ z
      then (1 : ℝ) else 0) ∂μ =
      leaveOneOutCdf (X := upperTruncatedFamily X) (μ := μ) i (z - t) := by
  have hYmeas := measurable_upperTruncatedFamily hXmeas
  have hfun :
      (fun ω => if leaveOneOut (upperTruncatedFamily X) i ω + t ≤ z
        then (1 : ℝ) else 0) =
        fun ω => if leaveOneOut (upperTruncatedFamily X) i ω ≤ z - t
          then (1 : ℝ) else 0 := by
    funext ω
    by_cases h : leaveOneOut (upperTruncatedFamily X) i ω + t ≤ z
    · have h' : leaveOneOut (upperTruncatedFamily X) i ω ≤ z - t := by linarith
      simp [h, h']
    · have h' : ¬leaveOneOut (upperTruncatedFamily X) i ω ≤ z - t := by linarith
      simp [h, h']
  rw [hfun, integral_leaveOneOut_indicator_eq_cdf hYmeas i]

omit [Fintype ι] [IsProbabilityMeasure μ] in
private lemma upperTruncatedExpectedKernel_eq_zero_of_one_lt
    [DecidableEq ι] (i : ι) {t : ℝ} (ht : 1 < t) :
    upperTruncatedExpectedKernel X μ i t = 0 := by
  rw [upperTruncatedExpectedKernel, expectedKernelFwd]
  have hzero :
      (fun ω => kernelDensityFwd (upperTruncatedFamily X i ω) t) =ᵐ[μ]
        (0 : Ω → ℝ) := by
    filter_upwards with ω
    let y := upperTruncatedFamily X i ω
    change kernelDensityFwd y t = (0 : ℝ)
    have hy : y ≤ 1 := upperTruncateOne_le_one (X i ω)
    by_cases hy0 : 0 ≤ y
    · have ht_not : t ∉ Icc 0 y := by
        simp only [mem_Icc, not_and_or]
        exact Or.inr (not_le.mpr (by linarith))
      rw [kernelDensityFwd_eq_indicator_nonneg y hy0, indicator_of_notMem ht_not]
    · have hyneg : y < 0 := lt_of_not_ge hy0
      have ht_not : t ∉ Ioc y 0 := by
        simp only [mem_Ioc, not_and_or]
        exact Or.inr (not_le.mpr (by linarith))
      rw [kernelDensityFwd_eq_indicator_neg y hyneg, indicator_of_notMem ht_not]
  rw [integral_congr_ae hzero]
  simp

private lemma exp_half_le_two_indicator : Real.exp (1 / 2) ≤ 2 := by
  exact (Real.exp_le_two_add_div_two_sub (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).trans
    (by norm_num)

private lemma exp_neg_min_sub_le_two_mul_exp
    {y t z : ℝ} (hy : y ≤ 1) (ht : t ≤ 1) :
    Real.exp (-(min (z - y) (z - t)) / 2) ≤ 2 * Real.exp (-z / 2) := by
  have hmin : z - 1 ≤ min (z - y) (z - t) := by
    exact le_min (by linarith) (by linarith)
  calc
    Real.exp (-(min (z - y) (z - t)) / 2) ≤
        Real.exp (-(z - 1) / 2) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (1 / 2) * Real.exp (-z / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ 2 * Real.exp (-z / 2) :=
      mul_le_mul_of_nonneg_right exp_half_le_two_indicator (Real.exp_pos _).le

omit [Fintype ι] [IsProbabilityMeasure μ] in
/-- The upper-truncated coordinate has an integrable absolute third power. -/
lemma integrable_abs_cube_upperTruncatedFamily
    (hXmeas : ∀ i, Measurable (X i))
    (h3 : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ) (i : ι) :
    Integrable (fun ω => |upperTruncatedFamily X i ω| ^ 3) μ := by
  refine (h3 i).mono' ?_ ?_
  · exact ((measurable_upperTruncatedFamily hXmeas i).abs.pow_const 3).aestronglyMeasurable
  · filter_upwards with ω
    rw [Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (abs_nonneg (upperTruncatedFamily X i ω)) 3)]
    have hle : |upperTruncatedFamily X i ω| ≤ |X i ω| := by
      simpa only [upperTruncatedFamily, Function.comp_apply] using
        abs_upperTruncateOne_le_abs (X i ω)
    gcongr

omit [Fintype ι] [IsProbabilityMeasure μ] in
/-- One-sided truncation does not increase the absolute third moment. -/
lemma integral_abs_cube_upperTruncatedFamily_le
    (hXmeas : ∀ i, Measurable (X i))
    (h3 : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ) (i : ι) :
    ∫ ω, |upperTruncatedFamily X i ω| ^ 3 ∂μ ≤
      ∫ ω, |X i ω| ^ 3 ∂μ := by
  have hbar3 := integrable_abs_cube_upperTruncatedFamily hXmeas h3 i
  exact integral_mono hbar3 (h3 i) fun ω => by
    have hle : |upperTruncatedFamily X i ω| ≤ |X i ω| := by
      simpa only [upperTruncatedFamily, Function.comp_apply] using
        abs_upperTruncateOne_le_abs (X i ω)
    gcongr

/-- Exact first absolute moment of the expected forward kernel of an upper-truncated coordinate. -/
lemma integral_abs_mul_upperTruncatedExpectedKernel
    [DecidableEq ι]
    (hX2 : ∀ i, MemLp (X i) 2 μ) (hXmeas : ∀ i, Measurable (X i))
    (h3 : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ) (i : ι) :
    ∫ t : ℝ, |t| * upperTruncatedExpectedKernel X μ i t =
      (1 / 2 : ℝ) * ∫ ω, |upperTruncatedFamily X i ω| ^ 3 ∂μ := by
  exact integral_abs_mul_expectedKernelFwd i
    (memLp_upperTruncatedFamily hXmeas hX2 i)
    (measurable_upperTruncatedFamily hXmeas i)
    (integrable_abs_cube_upperTruncatedFamily hXmeas h3 i)

/-- The coordinate absolute first moment times expected-kernel mass is controlled by its absolute
third moment. -/
lemma integral_abs_upperTruncatedFamily_mul_integral_upperTruncatedExpectedKernel_le
    [DecidableEq ι]
    (hX2 : ∀ i, MemLp (X i) 2 μ) (hXmeas : ∀ i, Measurable (X i))
    (h3 : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ) (i : ι) :
    (∫ ω, |upperTruncatedFamily X i ω| ∂μ) *
        (∫ t : ℝ, upperTruncatedExpectedKernel X μ i t) ≤
      ∫ ω, |upperTruncatedFamily X i ω| ^ 3 ∂μ := by
  let Y := upperTruncatedFamily X
  have hYmeas : ∀ j, Measurable (Y j) := measurable_upperTruncatedFamily hXmeas
  have hY2 : ∀ j, MemLp (Y j) 2 μ := memLp_upperTruncatedFamily hXmeas hX2
  have hY3 := integrable_abs_cube_upperTruncatedFamily hXmeas h3 i
  rw [integral_upperTruncatedExpectedKernel hX2 hXmeas i]
  exact integral_abs_mul_integral_sq_le (hYmeas i)
    ((hY2 i).integrable one_le_two).abs (hY2 i).integrable_sq hY3

/-- Summed absolute first kernel moments are at most one half of the original third-moment sum. -/
lemma sum_integral_abs_mul_upperTruncatedExpectedKernel_le
    [DecidableEq ι]
    (hX2 : ∀ i, MemLp (X i) 2 μ) (hXmeas : ∀ i, Measurable (X i))
    (h3 : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ) :
    ∑ i : ι, ∫ t : ℝ, |t| * upperTruncatedExpectedKernel X μ i t ≤
      (1 / 2 : ℝ) * thirdMomentSum X μ := by
  have hbar :
      ∑ i : ι, ∫ ω, |upperTruncatedFamily X i ω| ^ 3 ∂μ ≤
        thirdMomentSum X μ := by
    unfold thirdMomentSum
    exact Finset.sum_le_sum fun i _ =>
      integral_abs_cube_upperTruncatedFamily_le hXmeas h3 i
  calc
    ∑ i : ι, ∫ t : ℝ, |t| * upperTruncatedExpectedKernel X μ i t =
        ∑ i : ι, (1 / 2 : ℝ) *
          ∫ ω, |upperTruncatedFamily X i ω| ^ 3 ∂μ :=
      Finset.sum_congr rfl fun i _ =>
        integral_abs_mul_upperTruncatedExpectedKernel hX2 hXmeas h3 i
    _ = (1 / 2 : ℝ) *
        ∑ i : ι, ∫ ω, |upperTruncatedFamily X i ω| ^ 3 ∂μ := by
      rw [Finset.mul_sum]
    _ ≤ (1 / 2 : ℝ) * thirdMomentSum X μ :=
      mul_le_mul_of_nonneg_left hbar (by norm_num)

/-- Summed products of coordinate absolute first moments and expected-kernel masses are at most the
original third-moment sum. -/
lemma sum_integral_abs_upperTruncatedFamily_mul_integral_upperTruncatedExpectedKernel_le
    [DecidableEq ι]
    (hX2 : ∀ i, MemLp (X i) 2 μ) (hXmeas : ∀ i, Measurable (X i))
    (h3 : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ) :
    ∑ i : ι, (∫ ω, |upperTruncatedFamily X i ω| ∂μ) *
        (∫ t : ℝ, upperTruncatedExpectedKernel X μ i t) ≤
      thirdMomentSum X μ := by
  calc
    ∑ i : ι, (∫ ω, |upperTruncatedFamily X i ω| ∂μ) *
        (∫ t : ℝ, upperTruncatedExpectedKernel X μ i t) ≤
        ∑ i : ι, ∫ ω, |upperTruncatedFamily X i ω| ^ 3 ∂μ :=
      Finset.sum_le_sum fun i _ =>
        integral_abs_upperTruncatedFamily_mul_integral_upperTruncatedExpectedKernel_le
          hX2 hXmeas h3 i
    _ ≤ thirdMomentSum X μ := by
      unfold thirdMomentSum
      exact Finset.sum_le_sum fun i _ =>
        integral_abs_cube_upperTruncatedFamily_le hXmeas h3 i

private lemma abs_upperTruncatedIndicatorExpectation_sub_leaveOneOutCdf_le
    [DecidableEq ι]
    (hXmeas : ∀ i, Measurable (X i)) (h_indep : iIndepFun X μ)
    (hX2 : ∀ i, MemLp (X i) 2 μ) (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1)
    (h3 : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ)
    (i : ι) (z t : ℝ) (ht : t ≤ 1) :
    |(∫ ω, (if upperTruncatedSum X ω ≤ z then (1 : ℝ) else 0) ∂μ) -
        leaveOneOutCdf (X := upperTruncatedFamily X) (μ := μ) i (z - t)| ≤
      Real.exp (-z / 2) *
        (48 * (|t| + ∫ ω, |upperTruncatedFamily X i ω| ∂μ) +
          96 * thirdMomentSum X μ) := by
  let Y := upperTruncatedFamily X
  let γ := thirdMomentSum X μ
  let E := Real.exp (-z / 2)
  have hYmeas : ∀ j, Measurable (Y j) := measurable_upperTruncatedFamily hXmeas
  have hY2 : ∀ j, MemLp (Y j) 2 μ := memLp_upperTruncatedFamily hXmeas hX2
  have hγ0 : 0 ≤ γ := thirdMomentSum_nonneg h3
  have hAeq := integral_upperTruncatedIndicator_eq_integral_leaveOneOutCdf
    (X := X) hXmeas h_indep i z
  rw [hAeq]
  have hIntCdf : Integrable
      (fun ω => leaveOneOutCdf (X := Y) (μ := μ) i (z - Y i ω)) μ := by
    refine (integrable_const (μ := μ) (1 : ℝ)).mono' ?_ ?_
    · exact ((measurable_leaveOneOutCdf i).comp
        (measurable_const.sub (hYmeas i))).aestronglyMeasurable
    · filter_upwards with ω
      have h0 := leaveOneOutCdf_nonneg (X := Y) (μ := μ) i (z - Y i ω)
      have h1 := leaveOneOutCdf_le_one (X := Y) (μ := μ) i (z - Y i ω)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact h1
  let c := leaveOneOutCdf (X := Y) (μ := μ) i (z - t)
  have hconst : Integrable (fun _ : Ω => c) μ := integrable_const _
  have hsub :
      |(∫ ω, leaveOneOutCdf (X := Y) (μ := μ) i (z - Y i ω) ∂μ) - c| ≤
        ∫ ω, |leaveOneOutCdf (X := Y) (μ := μ) i (z - Y i ω) - c| ∂μ := by
    have habs := abs_integral_le_integral_abs
      (f := fun ω => leaveOneOutCdf (X := Y) (μ := μ) i (z - Y i ω) - c)
      (μ := μ)
    have heq :
        ∫ ω, leaveOneOutCdf (X := Y) (μ := μ) i (z - Y i ω) - c ∂μ =
          (∫ ω, leaveOneOutCdf (X := Y) (μ := μ) i (z - Y i ω) ∂μ) - c := by
      have hc : c = ∫ _ : Ω, c ∂μ := by simp [c]
      calc
        ∫ ω, leaveOneOutCdf (X := Y) (μ := μ) i (z - Y i ω) - c ∂μ =
            (∫ ω, leaveOneOutCdf (X := Y) (μ := μ) i (z - Y i ω) ∂μ) -
              ∫ _ : Ω, c ∂μ := integral_sub hIntCdf hconst
        _ = (∫ ω, leaveOneOutCdf (X := Y) (μ := μ) i (z - Y i ω) ∂μ) - c := by
          rw [← hc]
    rwa [heq] at habs
  refine hsub.trans ?_
  have hYabs : Integrable (fun ω => |Y i ω|) μ :=
    ((hY2 i).integrable one_le_two).abs
  have hmajorant : Integrable
      (fun ω => E * (48 * (|t| + |Y i ω|) + 96 * γ)) μ := by
    have heq :
        (fun ω => E * (48 * (|t| + |Y i ω|) + 96 * γ)) =
          fun ω => (48 * E) * |Y i ω| + E * (48 * |t| + 96 * γ) := by
      funext ω
      ring
    rw [heq]
    exact (hYabs.const_mul (48 * E)).add (integrable_const _)
  have hpoint (ω : Ω) :
      |leaveOneOutCdf (X := Y) (μ := μ) i (z - Y i ω) - c| ≤
        E * (48 * (|t| + |Y i ω|) + 96 * γ) := by
    have hconc := abs_upperTruncatedLeaveOneOutCdf_sub_le_exp
      hXmeas h_indep hX2 h_mean hvar h3 i (z - Y i ω) (z - t)
    have hy : Y i ω ≤ 1 := upperTruncateOne_le_one (X i ω)
    have hexp := exp_neg_min_sub_le_two_mul_exp (z := z) hy ht
    have hlen : |(z - Y i ω) - (z - t)| = |Y i ω - t| := by
      calc
        |(z - Y i ω) - (z - t)| = |t - Y i ω| := by ring_nf
        _ = |Y i ω - t| := abs_sub_comm _ _
    rw [hlen] at hconc
    have hcoef0 : 0 ≤ 24 * |Y i ω - t| + 48 * γ := by positivity
    have hwidth :
        24 * |Y i ω - t| + 48 * γ ≤
          24 * (|Y i ω| + |t|) + 48 * γ := by
      have h := abs_sub (Y i ω) t
      linarith
    calc
      |leaveOneOutCdf (X := Y) (μ := μ) i (z - Y i ω) - c| ≤
          Real.exp (-(min (z - Y i ω) (z - t)) / 2) *
            (24 * |Y i ω - t| + 48 * γ) := by simpa [c, Y, γ] using hconc
      _ ≤ (2 * E) * (24 * |Y i ω - t| + 48 * γ) :=
        mul_le_mul_of_nonneg_right (by simpa [E] using hexp) hcoef0
      _ ≤ (2 * E) * (24 * (|Y i ω| + |t|) + 48 * γ) :=
        mul_le_mul_of_nonneg_left hwidth (mul_nonneg (by norm_num) (Real.exp_pos _).le)
      _ = E * (48 * (|t| + |Y i ω|) + 96 * γ) := by ring
  have hmono :
      ∫ ω, |leaveOneOutCdf (X := Y) (μ := μ) i (z - Y i ω) - c| ∂μ ≤
        ∫ ω, E * (48 * (|t| + |Y i ω|) + 96 * γ) ∂μ :=
    integral_mono (hIntCdf.sub hconst).abs hmajorant fun ω => by
      simpa [Pi.sub_apply, Real.norm_eq_abs] using hpoint ω
  refine hmono.trans_eq ?_
  have heq :
      (fun ω => E * (48 * (|t| + |Y i ω|) + 96 * γ)) =
        fun ω => (48 * E) * |Y i ω| + E * (48 * |t| + 96 * γ) := by
    funext ω
    ring
  rw [heq, integral_add (hYabs.const_mul (48 * E)) (integrable_const _),
    integral_const_mul]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  dsimp [E, γ, Y]
  ring

private lemma abs_upperTruncatedR21_coordinate_le
    [DecidableEq ι]
    (hXmeas : ∀ i, Measurable (X i)) (h_indep : iIndepFun X μ)
    (hX2 : ∀ i, MemLp (X i) 2 μ) (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1)
    (h3 : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ)
    (i : ι) (z : ℝ) :
    |∫ t : ℝ,
      ((∫ ω, (if upperTruncatedSum X ω ≤ z then (1 : ℝ) else 0) ∂μ) -
        ∫ ω, (if leaveOneOut (upperTruncatedFamily X) i ω + t ≤ z
          then (1 : ℝ) else 0) ∂μ) *
        upperTruncatedExpectedKernel X μ i t| ≤
      Real.exp (-z / 2) *
        (72 * (∫ ω, |upperTruncatedFamily X i ω| ^ 3 ∂μ) +
          96 * thirdMomentSum X μ *
            (∫ ω, upperTruncatedFamily X i ω ^ 2 ∂μ)) := by
  let Y := upperTruncatedFamily X
  let K := upperTruncatedExpectedKernel X μ i
  let A : ℝ := ∫ ω, (if upperTruncatedSum X ω ≤ z then (1 : ℝ) else 0) ∂μ
  let F := leaveOneOutCdf (X := Y) (μ := μ) i
  let EY : ℝ := ∫ ω, |Y i ω| ∂μ
  let EY2 : ℝ := ∫ ω, Y i ω ^ 2 ∂μ
  let EY3 : ℝ := ∫ ω, |Y i ω| ^ 3 ∂μ
  let γ := thirdMomentSum X μ
  let E := Real.exp (-z / 2)
  have hYmeas : ∀ j, Measurable (Y j) := measurable_upperTruncatedFamily hXmeas
  have hY2 : ∀ j, MemLp (Y j) 2 μ := memLp_upperTruncatedFamily hXmeas hX2
  have hY3 : Integrable (fun ω => |Y i ω| ^ 3) μ :=
    integrable_abs_cube_upperTruncatedFamily hXmeas h3 i
  have hYabs : Integrable (fun ω => |Y i ω|) μ :=
    ((hY2 i).integrable one_le_two).abs
  have hKint : Integrable K := integrable_upperTruncatedExpectedKernel hX2 hXmeas i
  have hK0 (t : ℝ) : 0 ≤ K t := upperTruncatedExpectedKernel_nonneg i t
  have hshift (t : ℝ) :
      (∫ ω, (if leaveOneOut Y i ω + t ≤ z then (1 : ℝ) else 0) ∂μ) =
        F (z - t) := by
    simpa only [Y, F] using
      integral_upperTruncatedLeaveOneOut_shift_indicator_eq_cdf
        (X := X) hXmeas i z t
  have hFKint : Integrable (fun t : ℝ => F (z - t) * K t) := by
    refine hKint.mono' ?_ ?_
    · exact (((measurable_leaveOneOutCdf i).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
          hKint.aestronglyMeasurable)
    · filter_upwards with t
      have hF0 := leaveOneOutCdf_nonneg (X := Y) (μ := μ) i (z - t)
      have hF1 := leaveOneOutCdf_le_one (X := Y) (μ := μ) i (z - t)
      dsimp only [F]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hF0, abs_of_nonneg (hK0 t)]
      exact mul_le_of_le_one_left (hK0 t) hF1
  have hresidualInt : Integrable (fun t : ℝ =>
      (A - ∫ ω, (if leaveOneOut Y i ω + t ≤ z then (1 : ℝ) else 0) ∂μ) *
        K t) := by
    have heq :
        (fun t : ℝ =>
          (A - ∫ ω, (if leaveOneOut Y i ω + t ≤ z then (1 : ℝ) else 0) ∂μ) *
            K t) =
          fun t : ℝ => A * K t - F (z - t) * K t := by
      funext t
      rw [hshift]
      ring
    rw [heq]
    exact (hKint.const_mul A).sub hFKint
  have hAbsK : Integrable (fun t : ℝ => |t| * K t) := by
    simpa only [K, upperTruncatedExpectedKernel] using
      integrable_abs_mul_expectedKernelFwd i (hY2 i) (hYmeas i) hY3
  have hmajorant : Integrable (fun t : ℝ =>
      E * (48 * (|t| + EY) + 96 * γ) * K t) := by
    have heq :
        (fun t : ℝ => E * (48 * (|t| + EY) + 96 * γ) * K t) =
          fun t : ℝ => (48 * E) * (|t| * K t) +
            (E * (48 * EY + 96 * γ)) * K t := by
      funext t
      ring
    rw [heq]
    exact (hAbsK.const_mul (48 * E)).add
      (hKint.const_mul (E * (48 * EY + 96 * γ)))
  have hpoint (t : ℝ) :
      |(A - ∫ ω, (if leaveOneOut Y i ω + t ≤ z then (1 : ℝ) else 0) ∂μ) *
          K t| ≤
        E * (48 * (|t| + EY) + 96 * γ) * K t := by
    by_cases ht : t ≤ 1
    · have hbound := abs_upperTruncatedIndicatorExpectation_sub_leaveOneOutCdf_le
        hXmeas h_indep hX2 h_mean hvar h3 i z t ht
      have hD :
          |A - ∫ ω, (if leaveOneOut Y i ω + t ≤ z then (1 : ℝ) else 0) ∂μ| ≤
            E * (48 * (|t| + EY) + 96 * γ) := by
        rw [hshift]
        simpa only [A, E, EY, γ, Y, F] using hbound
      rw [abs_mul, abs_of_nonneg (hK0 t)]
      exact mul_le_mul_of_nonneg_right hD (hK0 t)
    · have hKzero : K t = 0 := by
        simpa only [K] using upperTruncatedExpectedKernel_eq_zero_of_one_lt
          (X := X) (μ := μ) i (lt_of_not_ge ht)
      simp [hKzero]
  have habs :
      |∫ t : ℝ,
        (A - ∫ ω, (if leaveOneOut Y i ω + t ≤ z then (1 : ℝ) else 0) ∂μ) *
          K t| ≤
        ∫ t : ℝ, E * (48 * (|t| + EY) + 96 * γ) * K t := by
    calc
      |∫ t : ℝ,
          (A - ∫ ω, (if leaveOneOut Y i ω + t ≤ z then (1 : ℝ) else 0) ∂μ) *
            K t| ≤
          ∫ t : ℝ,
            |(A - ∫ ω, (if leaveOneOut Y i ω + t ≤ z then (1 : ℝ) else 0) ∂μ) *
              K t| := abs_integral_le_integral_abs
      _ ≤ ∫ t : ℝ, E * (48 * (|t| + EY) + 96 * γ) * K t :=
        integral_mono hresidualInt.abs hmajorant hpoint
  refine habs.trans ?_
  have hAbsMass :
      ∫ t : ℝ, |t| * K t = (1 / 2 : ℝ) * EY3 := by
    simpa only [K, EY3, Y] using
      integral_abs_mul_upperTruncatedExpectedKernel hX2 hXmeas h3 i
  have hKmass : ∫ t : ℝ, K t = EY2 := by
    simpa only [K, EY2, Y] using integral_upperTruncatedExpectedKernel hX2 hXmeas i
  have hYoung : EY * EY2 ≤ EY3 := by
    dsimp only [EY, EY2, EY3]
    exact integral_abs_mul_integral_sq_le (hYmeas i) hYabs (hY2 i).integrable_sq hY3
  have hvalue :
      ∫ t : ℝ, E * (48 * (|t| + EY) + 96 * γ) * K t =
        E * (48 * ((1 / 2 : ℝ) * EY3 + EY * EY2) + 96 * γ * EY2) := by
    have heq :
        (fun t : ℝ => E * (48 * (|t| + EY) + 96 * γ) * K t) =
          fun t : ℝ => (48 * E) * (|t| * K t) +
            (E * (48 * EY + 96 * γ)) * K t := by
      funext t
      ring
    rw [heq, integral_add (hAbsK.const_mul (48 * E))
      (hKint.const_mul (E * (48 * EY + 96 * γ))),
      integral_const_mul, integral_const_mul, hAbsMass, hKmass]
    ring
  rw [hvalue]
  have hinner :
      48 * ((1 / 2 : ℝ) * EY3 + EY * EY2) + 96 * γ * EY2 ≤
        72 * EY3 + 96 * γ * EY2 := by
    linarith
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hle := mul_le_mul_of_nonneg_left hinner hE0
  simpa only [A, K, Y, E, EY3, EY2, γ] using hle

/-- Chen--Shao (2005), Section 6: the indicator residual has exponential decay with an explicit
absolute constant.  The proof in fact holds for every `z`; in particular it supplies the `z ≥ 2`
branch used by the upper-truncated nonuniform theorem. -/
theorem abs_upperTruncatedR21_le_exp_thirdMomentSum
    [DecidableEq ι]
    (hXmeas : ∀ i, Measurable (X i)) (h_indep : iIndepFun X μ)
    (hX2 : ∀ i, MemLp (X i) 2 μ) (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1)
    (h3 : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ)
    (z : ℝ) :
    |upperTruncatedR21 X μ z| ≤
      168 * Real.exp (-z / 2) * thirdMomentSum X μ := by
  let γ := thirdMomentSum X μ
  let E := Real.exp (-z / 2)
  let S3 := ∑ i : ι, ∫ ω, |upperTruncatedFamily X i ω| ^ 3 ∂μ
  let S2 := ∑ i : ι, ∫ ω, upperTruncatedFamily X i ω ^ 2 ∂μ
  have hγ0 : 0 ≤ γ := thirdMomentSum_nonneg h3
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hS3 : S3 ≤ γ := by
    dsimp only [S3, γ]
    unfold thirdMomentSum
    exact Finset.sum_le_sum fun i _ =>
      integral_abs_cube_upperTruncatedFamily_le hXmeas h3 i
  have hS2 : S2 ≤ 1 := by
    simpa only [S2] using
      sum_integral_sq_upperTruncatedFamily_le hXmeas hX2 h_mean hvar
  unfold upperTruncatedR21
  calc
    |∑ i : ι, ∫ t : ℝ,
        ((∫ ω, (if upperTruncatedSum X ω ≤ z then (1 : ℝ) else 0) ∂μ) -
          ∫ ω, (if leaveOneOut (upperTruncatedFamily X) i ω + t ≤ z
            then (1 : ℝ) else 0) ∂μ) *
          upperTruncatedExpectedKernel X μ i t| ≤
        ∑ i : ι, |∫ t : ℝ,
          ((∫ ω, (if upperTruncatedSum X ω ≤ z then (1 : ℝ) else 0) ∂μ) -
            ∫ ω, (if leaveOneOut (upperTruncatedFamily X) i ω + t ≤ z
              then (1 : ℝ) else 0) ∂μ) *
            upperTruncatedExpectedKernel X μ i t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : ι, E *
        (72 * (∫ ω, |upperTruncatedFamily X i ω| ^ 3 ∂μ) +
          96 * γ * (∫ ω, upperTruncatedFamily X i ω ^ 2 ∂μ)) :=
      Finset.sum_le_sum fun i _ => by
        simpa only [E, γ] using
          abs_upperTruncatedR21_coordinate_le
            hXmeas h_indep hX2 h_mean hvar h3 i z
    _ = E * (72 * S3 + 96 * γ * S2) := by
      calc
        ∑ i : ι, E *
            (72 * (∫ ω, |upperTruncatedFamily X i ω| ^ 3 ∂μ) +
              96 * γ * (∫ ω, upperTruncatedFamily X i ω ^ 2 ∂μ)) =
            ∑ i : ι, ((72 * E) *
                (∫ ω, |upperTruncatedFamily X i ω| ^ 3 ∂μ) +
              (96 * E * γ) *
                (∫ ω, upperTruncatedFamily X i ω ^ 2 ∂μ)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        _ = (∑ i : ι, (72 * E) *
              (∫ ω, |upperTruncatedFamily X i ω| ^ 3 ∂μ)) +
            ∑ i : ι, (96 * E * γ) *
              (∫ ω, upperTruncatedFamily X i ω ^ 2 ∂μ) :=
          Finset.sum_add_distrib
        _ = (72 * E) * S3 + (96 * E * γ) * S2 := by
          rw [Finset.mul_sum, Finset.mul_sum]
        _ = E * (72 * S3 + 96 * γ * S2) := by ring
    _ ≤ E * (72 * γ + 96 * γ * 1) := by
      apply mul_le_mul_of_nonneg_left _ hE0
      exact add_le_add
        (mul_le_mul_of_nonneg_left hS3 (by norm_num))
        (mul_le_mul_of_nonneg_left hS2 (mul_nonneg (by norm_num) hγ0))
    _ = 168 * Real.exp (-z / 2) * thirdMomentSum X μ := by
      dsimp [E, γ]
      ring

end ProbabilityTheory
