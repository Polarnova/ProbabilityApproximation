/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-!
# Mathlib-native leaves for Chen–Shao (SPEC §7.1)

Measurability, map measures, CDF bridges, and variance additivity under independence.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace ProbabilityTheory

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ι → Ω → ℝ}

/-- Sum of the coordinate random variables. -/
def sumX (X : ι → Ω → ℝ) : Ω → ℝ := fun ω ↦ ∑ i, X i ω

lemma measurable_sumX (hX : ∀ i, Measurable (X i)) : Measurable (sumX X) :=
  Finset.measurable_fun_sum _ fun i _ ↦ hX i

omit [IsProbabilityMeasure μ] in
lemma aemeasurable_sumX (hX : ∀ i, AEMeasurable (X i) μ) : AEMeasurable (sumX X) μ :=
  Finset.aemeasurable_fun_sum _ fun i _ ↦ hX i

lemma isProbabilityMeasure_map_sumX (hX : ∀ i, AEMeasurable (X i) μ) :
    IsProbabilityMeasure (μ.map (sumX X)) :=
  Measure.isProbabilityMeasure_map (aemeasurable_sumX hX)

lemma cdf_map_sumX_eq_real (hX : ∀ i, AEMeasurable (X i) μ) (x : ℝ) :
    cdf (μ.map (sumX X)) x = (μ.map (sumX X)).real (Iic x) := by
  let ν := μ.map (sumX X)
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_map_sumX (μ := μ) (X := X) hX
  exact cdf_eq_real (μ := ν) x

variable [DecidableEq ι]

/-- Leave-one-out sum. -/
def leaveOneOut (X : ι → Ω → ℝ) (i : ι) : Ω → ℝ :=
  fun ω ↦ ∑ j ∈ Finset.univ.erase i, X j ω

omit [MeasurableSpace Ω] in
lemma leaveOneOut_add (i : ι) (ω : Ω) : sumX X ω = leaveOneOut X i ω + X i ω := by
  simp only [sumX, leaveOneOut]
  exact (Finset.sum_erase_add (fun j ↦ X j ω) (s := Finset.univ) (Finset.mem_univ i)).symm

lemma measurable_leaveOneOut (hX : ∀ i, Measurable (X i)) (i : ι) :
    Measurable (leaveOneOut X i) :=
  Finset.measurable_fun_sum _ fun j _ ↦ hX j

omit [MeasurableSpace Ω] in
lemma leaveOneOut_eq_sum_sub (i : ι) (ω : Ω) :
    leaveOneOut X i ω = (∑ j, X j ω) - X i ω := by
  simp only [leaveOneOut]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]

omit [IsProbabilityMeasure μ] in
/-- Leave-one-out sum is independent of the excluded coordinate. -/
lemma indepFun_leaveOneOut (hX : ∀ i, Measurable (X i)) (h_indep : iIndepFun X μ) (i : ι) :
    IndepFun (leaveOneOut X i) (X i) μ := by
  have h := h_indep.indepFun_finsetSum_of_notMem hX
    (s := Finset.univ.erase i) (i := i) (Finset.notMem_erase i _)
  -- h : IndepFun (∑ j ∈ univ.erase i, X j) (X i) μ
  convert h using 2
  ext ω
  simp [leaveOneOut]

lemma variance_eq_integral_sq {Y : Ω → ℝ} (hY : MemLp Y 2 μ) (h0 : ∫ ω, Y ω ∂μ = 0) :
    variance Y μ = ∫ ω, (Y ω) ^ 2 ∂μ := by
  rw [variance_eq_sub hY, h0]
  simp

omit [DecidableEq ι] [IsProbabilityMeasure μ] in
lemma variance_sum_iIndepFun (hX : ∀ i, MemLp (X i) 2 μ) (h_indep : iIndepFun X μ) :
    variance (∑ i : ι, X i) μ = ∑ i : ι, variance (X i) μ :=
  IndepFun.variance_sum (s := Finset.univ) (fun i _ ↦ hX i)
    (fun _ _ _ _ hij ↦ h_indep.indepFun hij)

omit [DecidableEq ι] [IsProbabilityMeasure μ] in
lemma variance_sumX_eq_one (hX : ∀ i, MemLp (X i) 2 μ) (h_indep : iIndepFun X μ)
    (hvar : ∑ i, variance (X i) μ = 1) : variance (∑ i, X i) μ = 1 :=
  (variance_sum_iIndepFun hX h_indep).trans hvar

omit [DecidableEq ι] in
/-- Under centering, the sum of coordinate second moments is the sum of coordinate variances. -/
lemma sum_integral_sq_eq_one
    (hX : ∀ i, MemLp (X i) 2 μ) (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1) :
    ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ = 1 := by
  have h : ∑ i, variance (X i) μ = ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ :=
    Finset.sum_congr rfl fun i _ ↦ variance_eq_integral_sq (hX i) (h_mean i)
  rwa [← h]

omit [Fintype ι] [DecidableEq ι] [IsProbabilityMeasure μ] in
/-- Mean of a finite sum of centered summands. -/
lemma integral_finsetSum_eq_zero
    (s : Finset ι) (hX : ∀ i, Integrable (X i) μ)
    (h0 : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    ∫ ω, (∑ i ∈ s, X i ω) ∂μ = 0 := by
  rw [integral_finsetSum _ fun i _ => hX i]
  exact Finset.sum_eq_zero fun i _ => h0 i

omit [Fintype ι] [DecidableEq ι] in
/-- For independent centered summands, the second moment of a finite sum is the sum of the
coordinate second moments. -/
lemma integral_sq_finsetSum_eq
    (s : Finset ι) (hX2 : ∀ i, MemLp (X i) 2 μ)
    (h_indep : iIndepFun X μ) (h0 : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    ∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂μ = ∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ := by
  have hmem : MemLp (fun ω => ∑ i ∈ s, X i ω) 2 μ :=
    memLp_finsetSum s fun i _ => hX2 i
  have hmean0 : ∫ ω, (∑ i ∈ s, X i ω) ∂μ = 0 :=
    integral_finsetSum_eq_zero (X := X) s (fun i => (hX2 i).integrable one_le_two) h0
  have hfun : (∑ i ∈ s, X i) = fun ω => ∑ i ∈ s, X i ω := by
    funext ω
    simp [Finset.sum_apply]
  have hvar : variance (∑ i ∈ s, X i) μ = ∑ i ∈ s, variance (X i) μ :=
    IndepFun.variance_sum (fun i _ => hX2 i) fun i _ j _ hij => h_indep.indepFun hij
  have hvarS : variance (fun ω => ∑ i ∈ s, X i ω) μ =
      ∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂μ := by
    rw [variance_eq_sub hmem, hmean0]
    simp
  have hvari : ∀ i ∈ s, variance (X i) μ = ∫ ω, (X i ω) ^ 2 ∂μ := fun i _ =>
    variance_eq_integral_sq (hX2 i) (h0 i)
  calc
    ∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂μ =
        variance (fun ω => ∑ i ∈ s, X i ω) μ := hvarS.symm
    _ = variance (∑ i ∈ s, X i) μ := by rw [hfun]
    _ = ∑ i ∈ s, variance (X i) μ := hvar
    _ = ∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ := Finset.sum_congr rfl hvari

omit [IsProbabilityMeasure μ] [DecidableEq ι] in
lemma integrableOn_sq_of_memLp2 {Y : Ω → ℝ} (hY : MemLp Y 2 μ) (s : Set Ω) :
    IntegrableOn (fun ω ↦ (Y ω) ^ 2) s μ :=
  hY.integrable_sq.integrableOn

omit [IsProbabilityMeasure μ] in
/-- On `{|Y| ≤ t}`, `|Y|³ ≤ t · Y²`. -/
lemma integrableOn_abs_cube_trunc {Y : Ω → ℝ} (hYmeas : Measurable Y) (hY : MemLp Y 2 μ)
    {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun ω ↦ |Y ω| ^ 3) {ω | |Y ω| ≤ t} μ := by
  have hset : MeasurableSet {ω | |Y ω| ≤ t} :=
    measurableSet_le hYmeas.abs measurable_const
  have h2 := hY.integrable_sq
  have h_ind :
      Integrable (fun ω ↦ ({ω | |Y ω| ≤ t}).indicator (fun ω ↦ |Y ω| ^ 3) ω) μ := by
    refine (h2.const_mul t).mono' ?_ ?_
    · exact (hYmeas.abs.pow_const 3).aestronglyMeasurable.indicator hset
    · filter_upwards with ω
      by_cases hω : |Y ω| ≤ t
      · rw [indicator_of_mem (show ω ∈ {ω | |Y ω| ≤ t} from hω)]
        have hnn : 0 ≤ |Y ω| ^ 3 := pow_nonneg (abs_nonneg _) _
        rw [norm_eq_abs, abs_of_nonneg hnn]
        calc
          |Y ω| ^ 3 = |Y ω| ^ 2 * |Y ω| := by ring
          _ ≤ |Y ω| ^ 2 * t := by gcongr
          _ = t * (Y ω) ^ 2 := by rw [sq_abs, mul_comm]
      · rw [indicator_of_notMem (show ω ∉ {ω | |Y ω| ≤ t} from hω)]
        simp [mul_nonneg, ht, sq_nonneg]
  rwa [integrable_indicator_iff hset] at h_ind

end ProbabilityTheory
