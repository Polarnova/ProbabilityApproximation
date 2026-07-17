/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import ProbabilityApproximation.ChenShao.Leaves

/-!
# Truncated moments and leave-one-out concentration leaves (Chen–Shao / CGS)

Defines `truncMomentSum` (β₂ + β₃), the Stein exchange kernel `kernelDensity`, and
leave-one-out independence / moment comparisons used by uniform truncated Berry–Esseen
estimates (CGS Ch. 3 / Chen–Shao Prop. 3.2).
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal intervalIntegral

noncomputable section

namespace ProbabilityTheory

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ι → Ω → ℝ}

/-! ### Truncated moment sum -/

/-- Truncated moment sum `β₂ + β₃` at level 1 (CGS (3.5) / Chen–Shao). -/
def truncMomentSum (X : ι → Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∑ i : ι, ((∫ ω in {ω | 1 < |X i ω|}, (X i ω) ^ 2 ∂μ) +
    ∫ ω in {ω | |X i ω| ≤ 1}, |X i ω| ^ 3 ∂μ)

omit [IsProbabilityMeasure μ] in
lemma truncMomentSum_nonneg (hX : ∀ i, Measurable (X i)) :
    0 ≤ truncMomentSum (X := X) μ := by
  refine Finset.sum_nonneg fun i _ => add_nonneg ?_ ?_
  · exact setIntegral_nonneg (measurableSet_lt measurable_const (hX i).abs)
      fun _ _ => sq_nonneg _
  · exact setIntegral_nonneg (measurableSet_le (hX i).abs measurable_const)
      fun _ _ => pow_nonneg (abs_nonneg _) _

/-- Pointwise: `1_{|ξ|>1} ξ² + 1_{|ξ|≤1} |ξ|³ ≤ |ξ|³`. -/
lemma trunc_terms_le_abs_cube (ξ : ℝ) :
    (if 1 < |ξ| then ξ ^ 2 else 0) + (if |ξ| ≤ 1 then |ξ| ^ 3 else 0) ≤ |ξ| ^ 3 := by
  by_cases h : 1 < |ξ|
  · have hnot : ¬ |ξ| ≤ 1 := not_le.mpr h
    simp only [if_pos h, if_neg hnot, add_zero]
    have h1 : 1 ≤ |ξ| := le_of_lt h
    calc
      ξ ^ 2 = 1 * ξ ^ 2 := by ring
      _ ≤ |ξ| * ξ ^ 2 := by gcongr
      _ = |ξ| * |ξ| ^ 2 := by rw [sq_abs]
      _ = |ξ| ^ 3 := by ring
  · have hle : |ξ| ≤ 1 := le_of_not_gt h
    simp only [if_neg h, if_pos hle, zero_add, le_refl]

/-- Absolute value of a CDF difference is at most 1. -/
lemma abs_cdf_sub_le_one (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x : ℝ) : |cdf μ x - cdf ν x| ≤ 1 := by
  have hμ0 := cdf_nonneg μ x
  have hμ1 := cdf_le_one μ x
  have hν0 := cdf_nonneg ν x
  have hν1 := cdf_le_one ν x
  rw [abs_le]
  constructor <;> linarith

/-! ### Elementary comparisons (Chen–Shao (F1)) -/

/-- Chen–Shao (F1) / CGS (5.8): `min(x, y) ≥ x - x²/(4y)` for `x ≥ 0`, `y > 0`. -/
lemma min_ge_sub_sq_div {x y : ℝ} (_hx : 0 ≤ x) (hy : 0 < y) :
    x - x ^ 2 / (4 * y) ≤ min x y := by
  by_cases hxy : x ≤ y
  · simp only [min_eq_left hxy]
    have : 0 ≤ x ^ 2 / (4 * y) := div_nonneg (sq_nonneg _) (by positivity)
    linarith
  · have hyx : y ≤ x := le_of_not_ge hxy
    simp only [min_eq_right hyx]
    have h4 : 0 < 4 * y := by positivity
    have : x - y ≤ x ^ 2 / (4 * y) := by
      rw [le_div_iff₀ h4]
      nlinarith [sq_nonneg (x - 2 * y)]
    linarith

/-! ### Stein exchange kernel -/

/-- Stein exchange kernel for a real increment `ξ` at lag `t` (CGS form).

Weight is nonnegative and equals `|ξ|` on the interval joining `0` and `-ξ`.
Integrates to `ξ²` (a density after normalizing by `∑ E ξᵢ²`). -/
def kernelDensity (ξ t : ℝ) : ℝ :=
  if 0 ≤ ξ then
    if t ∈ Icc (-ξ) 0 then ξ else 0
  else
    if t ∈ Ioc 0 (-ξ) then -ξ else 0

lemma kernelDensity_nonneg (ξ t : ℝ) : 0 ≤ kernelDensity ξ t := by
  unfold kernelDensity
  split_ifs with hξ _ _
  · exact hξ
  · exact le_rfl
  · exact neg_nonneg.mpr (le_of_not_ge hξ)
  · exact le_rfl

lemma measurable_kernelDensity_right (ξ : ℝ) : Measurable (kernelDensity ξ) := by
  classical
  unfold kernelDensity
  split_ifs with hξ
  · exact Measurable.ite (measurableSet_Icc.preimage measurable_id) measurable_const
      measurable_const
  · exact Measurable.ite (measurableSet_Ioc.preimage measurable_id) measurable_const
      measurable_const

lemma kernelDensity_eq_indicator_nonneg (ξ : ℝ) (hξ : 0 ≤ ξ) :
    kernelDensity ξ = (Icc (-ξ) 0).indicator fun _ => ξ := by
  funext t
  unfold kernelDensity
  rw [if_pos hξ]
  by_cases ht : t ∈ Icc (-ξ) 0 <;> simp [ht, indicator]

lemma kernelDensity_eq_indicator_neg (ξ : ℝ) (hξ : ξ < 0) :
    kernelDensity ξ = (Ioc 0 (-ξ)).indicator fun _ => -ξ := by
  funext t
  unfold kernelDensity
  rw [if_neg (not_le.mpr hξ)]
  by_cases ht : t ∈ Ioc 0 (-ξ) <;> simp [ht, indicator]

private lemma measureReal_volume_Icc {a b : ℝ} (h : a ≤ b) :
    volume.real (Icc a b) = b - a := by
  rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr h)]

private lemma measureReal_volume_Ioc {a b : ℝ} (h : a ≤ b) :
    volume.real (Ioc a b) = b - a := by
  rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr h)]

lemma integrable_kernelDensity (ξ : ℝ) : Integrable (kernelDensity ξ) := by
  by_cases hξ : 0 ≤ ξ
  · rw [kernelDensity_eq_indicator_nonneg ξ hξ]
    refine (integrableOn_const (s := Icc (-ξ) 0) ?_ (by finiteness)).integrable_indicator
      measurableSet_Icc
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  · have hlt : ξ < 0 := lt_of_not_ge hξ
    rw [kernelDensity_eq_indicator_neg ξ hlt]
    refine (integrableOn_const (s := Ioc 0 (-ξ)) ?_ (by finiteness)).integrable_indicator
      measurableSet_Ioc
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top

/-- The exchange kernel integrates to `ξ²`.

Related: the absolute first moment is `|ξ|³/2` (see `integral_abs_mul_kernelDensity`);
under `∑ E ξᵢ² = 1` the expected kernel is a probability density with mean absolute
value `γ/2`. -/
lemma integral_kernelDensity (ξ : ℝ) : ∫ t : ℝ, kernelDensity ξ t = ξ ^ 2 := by
  by_cases hξ : 0 ≤ ξ
  · rw [kernelDensity_eq_indicator_nonneg ξ hξ, integral_indicator_const ξ measurableSet_Icc,
      measureReal_volume_Icc (neg_nonpos.mpr hξ), smul_eq_mul]
    ring
  · have hlt : ξ < 0 := lt_of_not_ge hξ
    rw [kernelDensity_eq_indicator_neg ξ hlt, integral_indicator_const (-ξ) measurableSet_Ioc,
      measureReal_volume_Ioc (neg_nonneg.mpr hlt.le), smul_eq_mul]
    ring

private lemma integral_id_Icc {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Icc a b, t = (b ^ 2 - a ^ 2) / 2 := by
  have h := integral_id (a := a) (b := b)
  rw [intervalIntegral.integral_of_le hab] at h
  rwa [← integral_Icc_eq_integral_Ioc] at h

/-- Weighted first-moment identity: `∫ |t| · kernelDensity ξ t = |ξ|³ / 2`. -/
lemma integral_abs_mul_kernelDensity (ξ : ℝ) :
    ∫ t : ℝ, |t| * kernelDensity ξ t = |ξ| ^ 3 / 2 := by
  by_cases hξ : 0 ≤ ξ
  · have hfun :
        (fun t => |t| * kernelDensity ξ t) =
          (Icc (-ξ) 0).indicator (fun t => |t| * ξ) := by
      funext t
      rw [kernelDensity_eq_indicator_nonneg ξ hξ]
      by_cases ht : t ∈ Icc (-ξ) 0
      · simp [indicator_of_mem ht]
      · simp [indicator_of_notMem ht]
    rw [hfun, integral_indicator measurableSet_Icc]
    have hcongr :
        ∫ t in Icc (-ξ) 0, |t| * ξ = ξ * ∫ t in Icc (-ξ) 0, (-t) := by
      calc
        ∫ t in Icc (-ξ) 0, |t| * ξ
            = ∫ t in Icc (-ξ) 0, ξ * |t| := by
              refine setIntegral_congr_fun measurableSet_Icc fun _ _ => mul_comm _ _
        _ = ξ * ∫ t in Icc (-ξ) 0, |t| := integral_const_mul _ _
        _ = ξ * ∫ t in Icc (-ξ) 0, (-t) := by
              congr 1
              refine setIntegral_congr_fun measurableSet_Icc fun t ht => abs_of_nonpos ht.2
    rw [hcongr, show (fun t : ℝ => -t) = fun t => (-1 : ℝ) * t by funext; ring,
      integral_const_mul, integral_id_Icc (neg_nonpos.mpr hξ), abs_of_nonneg hξ]
    ring
  · have hlt : ξ < 0 := lt_of_not_ge hξ
    have hξ0 : 0 ≤ -ξ := neg_nonneg.mpr hlt.le
    have hfun :
        (fun t => |t| * kernelDensity ξ t) =
          (Ioc 0 (-ξ)).indicator (fun t => |t| * (-ξ)) := by
      funext t
      rw [kernelDensity_eq_indicator_neg ξ hlt]
      by_cases ht : t ∈ Ioc 0 (-ξ)
      · simp [indicator_of_mem ht]
      · simp [indicator_of_notMem ht]
    rw [hfun, integral_indicator measurableSet_Ioc]
    have hcongr :
        ∫ t in Ioc 0 (-ξ), |t| * (-ξ) = (-ξ) * ∫ t in Ioc 0 (-ξ), t := by
      calc
        ∫ t in Ioc 0 (-ξ), |t| * (-ξ)
            = ∫ t in Ioc 0 (-ξ), (-ξ) * |t| := by
              refine setIntegral_congr_fun measurableSet_Ioc fun _ _ => mul_comm _ _
        _ = (-ξ) * ∫ t in Ioc 0 (-ξ), |t| := integral_const_mul _ _
        _ = (-ξ) * ∫ t in Ioc 0 (-ξ), t := by
              congr 1
              refine setIntegral_congr_fun measurableSet_Ioc fun t ht => abs_of_nonneg ht.1.le
    rw [hcongr, ← integral_Icc_eq_integral_Ioc, integral_id_Icc hξ0, abs_of_neg hlt]
    ring

/-! ### Leave-one-out independence and moments -/

variable [DecidableEq ι]

omit [IsProbabilityMeasure μ] in
/-- Mean-zero and independence: `E[Xᵢ · g(W⁽ⁱ⁾)] = 0`. -/
lemma integral_X_mul_comp_leaveOneOut
    (hX : ∀ j, Measurable (X j)) (h_indep : iIndepFun X μ) (i : ι)
    (h_mean : ∫ ω, X i ω ∂μ = 0) (g : ℝ → ℝ)
    (hg : AEStronglyMeasurable g (μ.map (leaveOneOut X i))) :
    ∫ ω, X i ω * g (leaveOneOut X i ω) ∂μ = 0 := by
  have hInd := (indepFun_leaveOneOut (X := X) (μ := μ) hX h_indep i).symm
  have h := hInd.integral_fun_comp_mul_comp (f := (id : ℝ → ℝ)) (g := g)
    (hX i).aemeasurable (measurable_leaveOneOut hX i).aemeasurable
    measurable_id.aestronglyMeasurable hg
  simpa [h_mean] using h

omit [IsProbabilityMeasure μ] in
/-- Leave-one-out sum is in `L²` when each summand is. -/
lemma memLp_leaveOneOut (hX : ∀ j, MemLp (X j) 2 μ) (i : ι) :
    MemLp (leaveOneOut X i) 2 μ :=
  memLp_finsetSum (s := Finset.univ.erase i) (fun j _ => hX j)

omit [IsProbabilityMeasure μ] in
/-- Variance of the leave-one-out sum is `1 - Var(Xᵢ)` under independence and total variance 1. -/
lemma variance_leaveOneOut
    (hX : ∀ j, MemLp (X j) 2 μ) (h_indep : iIndepFun X μ)
    (hvar : ∑ j, variance (X j) μ = 1) (i : ι) :
    variance (leaveOneOut X i) μ = 1 - variance (X i) μ := by
  have hsum :
      variance (∑ j ∈ Finset.univ.erase i, X j) μ =
        ∑ j ∈ Finset.univ.erase i, variance (X j) μ :=
    IndepFun.variance_sum (fun j _ => hX j) fun j _ k _ hjk => h_indep.indepFun hjk
  have hloo : leaveOneOut X i = ∑ j ∈ Finset.univ.erase i, X j := by
    ext ω
    simp only [leaveOneOut, Finset.sum_apply]
  rw [hloo, hsum]
  have htot :
      ∑ j : ι, variance (X j) μ =
        ∑ j ∈ Finset.univ.erase i, variance (X j) μ + variance (X i) μ := by
    rw [← Finset.sum_erase_add (s := Finset.univ) (f := fun j => variance (X j) μ)
      (Finset.mem_univ i)]
  linarith

omit [IsProbabilityMeasure μ] in
/-- Hence `Var(W⁽ⁱ⁾) ≤ 1`. -/
lemma variance_leaveOneOut_le_one
    (hX : ∀ j, MemLp (X j) 2 μ) (h_indep : iIndepFun X μ)
    (hvar : ∑ j, variance (X j) μ = 1) (i : ι) :
    variance (leaveOneOut X i) μ ≤ 1 := by
  rw [variance_leaveOneOut hX h_indep hvar i]
  linarith [variance_nonneg (X i) μ]

/-- Mean of the leave-one-out sum vanishes when every summand is centered. -/
lemma integral_leaveOneOut_eq_zero
    (hX : ∀ j, MemLp (X j) 2 μ) (h_mean : ∀ j, ∫ ω, X j ω ∂μ = 0) (i : ι) :
    ∫ ω, leaveOneOut X i ω ∂μ = 0 := by
  simp only [leaveOneOut]
  rw [integral_finsetSum _ fun j _ => (hX j).integrable one_le_two]
  exact Finset.sum_eq_zero fun j _ => h_mean j

/-- Under mean zero summands, `E[(W⁽ⁱ⁾)²] = Var(W⁽ⁱ⁾) ≤ 1`. -/
lemma integral_sq_leaveOneOut_le_one
    (hX : ∀ j, MemLp (X j) 2 μ) (h_indep : iIndepFun X μ)
    (h_mean : ∀ j, ∫ ω, X j ω ∂μ = 0)
    (hvar : ∑ j, variance (X j) μ = 1) (i : ι) :
    ∫ ω, (leaveOneOut X i ω) ^ 2 ∂μ ≤ 1 := by
  have hmem := memLp_leaveOneOut (X := X) (μ := μ) hX i
  have hmean0 := integral_leaveOneOut_eq_zero (X := X) (μ := μ) hX h_mean i
  have hvar_eq : variance (leaveOneOut X i) μ = ∫ ω, (leaveOneOut X i ω) ^ 2 ∂μ :=
    variance_eq_integral_sq hmem hmean0
  rw [← hvar_eq]
  exact variance_leaveOneOut_le_one hX h_indep hvar i

/-- On a probability space, `E|Y| ≤ √(E Y²)` via nonnegativity of variance. -/
lemma integral_abs_le_sqrt_integral_sq {Y : Ω → ℝ} (hY : MemLp Y 2 μ) :
    ∫ ω, |Y ω| ∂μ ≤ √(∫ ω, (Y ω) ^ 2 ∂μ) := by
  have habs : MemLp (abs ∘ Y) 2 μ := hY.abs
  have hsub := variance_eq_sub habs
  have hnn : 0 ≤ variance (abs ∘ Y) μ := variance_nonneg _ _
  have hsq : (∫ ω, |Y ω| ∂μ) ^ 2 ≤ ∫ ω, |Y ω| ^ 2 ∂μ := by
    have : variance (abs ∘ Y) μ =
        (∫ ω, |Y ω| ^ 2 ∂μ) - (∫ ω, |Y ω| ∂μ) ^ 2 := by
      convert hsub using 2 <;> rfl
    linarith
  have hY2 : ∫ ω, |Y ω| ^ 2 ∂μ = ∫ ω, (Y ω) ^ 2 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with ω
    exact sq_abs _
  rw [hY2] at hsq
  exact le_sqrt_of_sq_le hsq

/-- Consequently `E|W⁽ⁱ⁾| ≤ 1` under the standing mean-zero / total-variance-1 hypotheses. -/
lemma integral_abs_leaveOneOut_le_one
    (hX : ∀ j, MemLp (X j) 2 μ) (h_indep : iIndepFun X μ)
    (h_mean : ∀ j, ∫ ω, X j ω ∂μ = 0)
    (hvar : ∑ j, variance (X j) μ = 1) (i : ι) :
    ∫ ω, |leaveOneOut X i ω| ∂μ ≤ 1 := by
  have hmem := memLp_leaveOneOut (X := X) (μ := μ) hX i
  have hsq := integral_sq_leaveOneOut_le_one hX h_indep h_mean hvar i
  calc
    ∫ ω, |leaveOneOut X i ω| ∂μ ≤ √(∫ ω, (leaveOneOut X i ω) ^ 2 ∂μ) :=
      integral_abs_le_sqrt_integral_sq hmem
    _ ≤ √1 := sqrt_le_sqrt hsq
    _ = 1 := sqrt_one

/-! ### Kernel mass on `{|t| ≤ δ}` -/

lemma mem_Icc_kernel_abs_le_iff {ξ δ t : ℝ} (_hξ : 0 ≤ ξ) (_hδ : 0 ≤ δ) :
    (t ∈ Icc (-ξ) 0 ∧ |t| ≤ δ) ↔ t ∈ Icc (-min δ ξ) 0 := by
  simp only [mem_Icc]
  constructor
  · intro ⟨⟨_, ht0⟩, habs⟩
    have habs' : -t ≤ δ := by rwa [abs_of_nonpos ht0] at habs
    refine ⟨?_, ht0⟩
    have : -t ≤ min δ ξ := le_min habs' (by linarith)
    linarith
  · intro ⟨hmin, ht0⟩
    refine ⟨⟨?_, ht0⟩, ?_⟩
    · have : min δ ξ ≤ ξ := min_le_right _ _
      linarith
    · have : -t ≤ min δ ξ := by linarith
      have : -t ≤ δ := le_trans this (min_le_left _ _)
      rwa [abs_of_nonpos ht0]

lemma mem_Ioc_kernel_abs_le_iff {ξ δ t : ℝ} (_hξ : ξ < 0) (_hδ : 0 ≤ δ) :
    (t ∈ Ioc 0 (-ξ) ∧ |t| ≤ δ) ↔ t ∈ Ioc 0 (min δ (-ξ)) := by
  simp only [mem_Ioc]
  constructor
  · intro ⟨⟨ht0, htx⟩, habs⟩
    have habs' : t ≤ δ := by rwa [abs_of_pos ht0] at habs
    exact ⟨ht0, le_min habs' htx⟩
  · intro ⟨ht0, htm⟩
    refine ⟨⟨ht0, le_trans htm (min_le_right _ _)⟩, ?_⟩
    have : t ≤ δ := le_trans htm (min_le_left _ _)
    rwa [abs_of_pos ht0]

/-- Mass of the exchange kernel on `{|t| ≤ δ}` equals `|ξ| · min(δ, |ξ|)`. -/
lemma integral_kernelDensity_abs_le (ξ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∫ t : ℝ, (if |t| ≤ δ then kernelDensity ξ t else 0) = |ξ| * min δ |ξ| := by
  by_cases hξ : 0 ≤ ξ
  · have hfun :
        (fun t => if |t| ≤ δ then kernelDensity ξ t else 0) =
          (Icc (-min δ ξ) 0).indicator fun _ => ξ := by
      funext t
      rw [kernelDensity_eq_indicator_nonneg ξ hξ]
      by_cases htδ : |t| ≤ δ
      · by_cases ht : t ∈ Icc (-ξ) 0
        · have hmem : t ∈ Icc (-min δ ξ) 0 :=
            (mem_Icc_kernel_abs_le_iff hξ hδ).mp ⟨ht, htδ⟩
          rw [if_pos htδ, indicator_of_mem ht, indicator_of_mem hmem]
        · have hnot : t ∉ Icc (-min δ ξ) 0 := fun hm =>
            ht ((mem_Icc_kernel_abs_le_iff hξ hδ).mpr hm).1
          rw [if_pos htδ, indicator_of_notMem ht, indicator_of_notMem hnot]
      · have hnot : t ∉ Icc (-min δ ξ) 0 := fun hm =>
          htδ ((mem_Icc_kernel_abs_le_iff hξ hδ).mpr hm).2
        rw [if_neg htδ, indicator_of_notMem hnot]
    rw [hfun, integral_indicator_const ξ measurableSet_Icc]
    have hlen : -min δ ξ ≤ 0 := neg_nonpos.mpr (le_min hδ hξ)
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hlen),
      smul_eq_mul, abs_of_nonneg hξ, sub_neg_eq_add, zero_add, mul_comm]
  · have hlt : ξ < 0 := lt_of_not_ge hξ
    have hξabs : 0 ≤ -ξ := neg_nonneg.mpr hlt.le
    have hfun :
        (fun t => if |t| ≤ δ then kernelDensity ξ t else 0) =
          (Ioc 0 (min δ (-ξ))).indicator fun _ => -ξ := by
      funext t
      rw [kernelDensity_eq_indicator_neg ξ hlt]
      by_cases htδ : |t| ≤ δ
      · by_cases ht : t ∈ Ioc 0 (-ξ)
        · have hmem : t ∈ Ioc 0 (min δ (-ξ)) :=
            (mem_Ioc_kernel_abs_le_iff hlt hδ).mp ⟨ht, htδ⟩
          rw [if_pos htδ, indicator_of_mem ht, indicator_of_mem hmem]
        · have hnot : t ∉ Ioc 0 (min δ (-ξ)) := fun hm =>
            ht ((mem_Ioc_kernel_abs_le_iff hlt hδ).mpr hm).1
          rw [if_pos htδ, indicator_of_notMem ht, indicator_of_notMem hnot]
      · have hnot : t ∉ Ioc 0 (min δ (-ξ)) := fun hm =>
          htδ ((mem_Ioc_kernel_abs_le_iff hlt hδ).mpr hm).2
        rw [if_neg htδ, indicator_of_notMem hnot]
    rw [hfun, integral_indicator_const (-ξ) measurableSet_Ioc]
    have hlen : 0 ≤ min δ (-ξ) - 0 := by
      have : 0 ≤ min δ (-ξ) := le_min hδ hξabs
      linarith
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal hlen, smul_eq_mul,
      abs_of_neg hlt, sub_zero, mul_comm]

/-- From (F1): `|ξ| · min(δ, |ξ|) ≥ ξ² - |ξ|³ / (4δ)` for `δ > 0`. -/
lemma abs_mul_min_ge_sq_sub {ξ δ : ℝ} (hδ : 0 < δ) :
    ξ ^ 2 - |ξ| ^ 3 / (4 * δ) ≤ |ξ| * min δ |ξ| := by
  have hx : 0 ≤ |ξ| := abs_nonneg _
  have h := min_ge_sub_sq_div (x := |ξ|) (y := δ) hx hδ
  have h' := mul_le_mul_of_nonneg_left h hx
  -- h' : |ξ| * (|ξ| - |ξ|²/(4δ)) ≤ |ξ| * min |ξ| δ
  have hrew : |ξ| * (|ξ| - |ξ| ^ 2 / (4 * δ)) = ξ ^ 2 - |ξ| ^ 3 / (4 * δ) := by
    have h1 : |ξ| * |ξ| = ξ ^ 2 := by rw [← pow_two, sq_abs]
    have h2 : |ξ| * (|ξ| ^ 2) = |ξ| ^ 3 := by ring
    rw [mul_sub, h1, mul_div_assoc', h2]
  rw [← hrew, min_comm]
  exact h'

/-! ### Concentration ramp (clamp form) -/

/-- Concentration ramp centered at `(a+b)/2` with height `(b-a)/2+δ` (CGS (3.32)).

This is the unique 1-Lipschitz extension of the centered identity on
`[a-δ, b+δ]` that saturates outside. On the linear region it equals
`w - (a+b)/2`, and `|f| ≤ (b-a)/2 + δ`. -/
def concRamp (a b δ : ℝ) (w : ℝ) : ℝ :=
  max (-((b - a) / 2 + δ)) (min ((b - a) / 2 + δ) (w - (a + b) / 2))

lemma abs_concRamp_le {a b δ w : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    |concRamp a b δ w| ≤ (b - a) / 2 + δ := by
  set h : ℝ := (b - a) / 2 + δ
  have hh0 : 0 ≤ h := add_nonneg (div_nonneg (sub_nonneg.mpr hab) two_pos.le) hδ
  have h1 : -h ≤ concRamp a b δ w := by
    simp only [concRamp]; exact le_max_left _ _
  have h2 : concRamp a b δ w ≤ h := by
    simp only [concRamp]
    exact max_le (by linarith) (min_le_left _ _)
  rw [abs_le]
  constructor <;> linarith

private lemma abs_min_const_sub (c x y : ℝ) : |min c x - min c y| ≤ |x - y| :=
  (abs_min_sub_min_le_max c x c y).trans (by simp)

private lemma abs_max_const_sub (c x y : ℝ) : |max x c - max y c| ≤ |x - y| :=
  abs_max_sub_max_le_abs x y c

/-- The concentration ramp is 1-Lipschitz. -/
lemma abs_concRamp_sub_le (a b δ x y : ℝ) :
    |concRamp a b δ x - concRamp a b δ y| ≤ |x - y| := by
  set h : ℝ := (b - a) / 2 + δ
  set m : ℝ := (a + b) / 2
  have h1 :
      |max (-h) (min h (x - m)) - max (-h) (min h (y - m))| ≤
        |min h (x - m) - min h (y - m)| := by
    simpa [max_comm] using abs_max_const_sub (-h) (min h (x - m)) (min h (y - m))
  have h2 := abs_min_const_sub h (x - m) (y - m)
  simp only [concRamp]
  calc
    |max (-h) (min h (x - m)) - max (-h) (min h (y - m))|
        ≤ |min h (x - m) - min h (y - m)| := h1
    _ ≤ |(x - m) - (y - m)| := h2
    _ = |x - y| := by ring_nf

lemma lipschitzWith_concRamp (a b δ : ℝ) : LipschitzWith 1 (concRamp a b δ) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul]
  exact abs_concRamp_sub_le a b δ x y

lemma continuous_concRamp (a b δ : ℝ) : Continuous (concRamp a b δ) :=
  (lipschitzWith_concRamp a b δ).continuous

/-- On the linear region `[a-δ, b+δ]`, the ramp equals the centered identity. -/
lemma concRamp_of_mem_Icc {a b δ w : ℝ} (_hδ : 0 ≤ δ) (_hab : a ≤ b)
    (hw : w ∈ Icc (a - δ) (b + δ)) :
    concRamp a b δ w = w - (a + b) / 2 := by
  set h : ℝ := (b - a) / 2 + δ
  set m : ℝ := (a + b) / 2
  have hlow : -h ≤ w - m := by
    have : a - δ - m = -h := by simp only [m, h]; ring
    linarith [hw.1]
  have hhigh : w - m ≤ h := by
    have : b + δ - m = h := by simp only [m, h]; ring
    linarith [hw.2]
  simp only [concRamp]
  rw [min_eq_right hhigh, max_eq_right hlow]

/-- For `a ≤ w ≤ b` and `|t| ≤ δ`, `w+t` lies in the linear region. -/
lemma add_mem_linear_region {a b δ w t : ℝ} (hw : w ∈ Icc a b) (ht : |t| ≤ δ) :
    w + t ∈ Icc (a - δ) (b + δ) := by
  constructor
  · have : -δ ≤ t := neg_le_of_abs_le ht
    linarith [hw.1]
  · have : t ≤ δ := le_of_abs_le ht
    linarith [hw.2]

/-! ### Cauchy–Schwarz upper bound helpers -/

/-- `(E|Y| + E|Z|)² ≤ 2 (E Y² + E Z²)`. -/
lemma integral_abs_add_sq_le {Y Z : Ω → ℝ} (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    (∫ ω, |Y ω| ∂μ + ∫ ω, |Z ω| ∂μ) ^ 2 ≤
      2 * (∫ ω, (Y ω) ^ 2 ∂μ + ∫ ω, (Z ω) ^ 2 ∂μ) := by
  have hYabs := integral_abs_le_sqrt_integral_sq hY
  have hZabs := integral_abs_le_sqrt_integral_sq hZ
  have hYnn : 0 ≤ ∫ ω, (Y ω) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hZnn : 0 ≤ ∫ ω, (Z ω) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hYa : 0 ≤ ∫ ω, |Y ω| ∂μ := integral_nonneg fun _ => abs_nonneg _
  have hZa : 0 ≤ ∫ ω, |Z ω| ∂μ := integral_nonneg fun _ => abs_nonneg _
  -- (√a + √b)² ≤ 2(a+b)
  set a := ∫ ω, (Y ω) ^ 2 ∂μ
  set b := ∫ ω, (Z ω) ^ 2 ∂μ
  have h1 : ∫ ω, |Y ω| ∂μ ≤ √a := hYabs
  have h2 : ∫ ω, |Z ω| ∂μ ≤ √b := hZabs
  have hsum : ∫ ω, |Y ω| ∂μ + ∫ ω, |Z ω| ∂μ ≤ √a + √b := by linarith
  have hsq : (∫ ω, |Y ω| ∂μ + ∫ ω, |Z ω| ∂μ) ^ 2 ≤ (√a + √b) ^ 2 := by
    gcongr
  have h2ab : (√a + √b) ^ 2 ≤ 2 * (a + b) := by
    nlinarith [sq_sqrt hYnn, sq_sqrt hZnn, sq_nonneg (√a - √b)]
  linarith

/-- Under total variance 1 and mean zero, `E|W⁽ⁱ⁾| + E|Xᵢ| ≤ √2`. -/
lemma integral_abs_leaveOneOut_add_X_le_sqrt_two
    (hX : ∀ j, MemLp (X j) 2 μ) (h_indep : iIndepFun X μ)
    (h_mean : ∀ j, ∫ ω, X j ω ∂μ = 0)
    (hvar : ∑ j, variance (X j) μ = 1) (i : ι) :
    ∫ ω, |leaveOneOut X i ω| ∂μ + ∫ ω, |X i ω| ∂μ ≤ √2 := by
  have hW := memLp_leaveOneOut (X := X) (μ := μ) hX i
  have hXi := hX i
  have hbound := integral_abs_add_sq_le hW hXi
  have hWsq : ∫ ω, (leaveOneOut X i ω) ^ 2 ∂μ ≤ 1 - variance (X i) μ := by
    have hmean0 := integral_leaveOneOut_eq_zero (X := X) (μ := μ) hX h_mean i
    have := variance_eq_integral_sq hW hmean0
    have hv := variance_leaveOneOut hX h_indep hvar i
    linarith
  have hXsq : ∫ ω, (X i ω) ^ 2 ∂μ = variance (X i) μ := by
    exact (variance_eq_integral_sq hXi (h_mean i)).symm
  have hsumsq : ∫ ω, (leaveOneOut X i ω) ^ 2 ∂μ + ∫ ω, (X i ω) ^ 2 ∂μ ≤ 1 := by
    linarith
  have hnn : 0 ≤ ∫ ω, |leaveOneOut X i ω| ∂μ + ∫ ω, |X i ω| ∂μ :=
    add_nonneg (integral_nonneg fun _ => abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _)
  have hsqle : (∫ ω, |leaveOneOut X i ω| ∂μ + ∫ ω, |X i ω| ∂μ) ^ 2 ≤ 2 := by
    have : 2 * (∫ ω, (leaveOneOut X i ω) ^ 2 ∂μ + ∫ ω, (X i ω) ^ 2 ∂μ) ≤ 2 * 1 := by
      gcongr
    linarith [hbound]
  exact le_sqrt_of_sq_le hsqle

/-- Pointwise: `|y · concRamp a b δ y| ≤ ((b-a)/2 + δ) · |y|`. -/
lemma abs_mul_concRamp_le {a b δ y : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    |y * concRamp a b δ y| ≤ ((b - a) / 2 + δ) * |y| := by
  calc
    |y * concRamp a b δ y| = |y| * |concRamp a b δ y| := abs_mul _ _
    _ ≤ |y| * ((b - a) / 2 + δ) := by
        gcongr
        exact abs_concRamp_le (w := y) hδ hab
    _ = ((b - a) / 2 + δ) * |y| := mul_comm _ _

/-- Integrable bound form used by the concentration upper estimate. -/
lemma abs_integral_mul_concRamp_le {Y : Ω → ℝ} {a b δ : ℝ}
    (hY : MemLp Y 2 μ) (hYmeas : AEStronglyMeasurable Y μ)
    (hδ : 0 ≤ δ) (hab : a ≤ b) :
    |∫ ω, Y ω * concRamp a b δ (Y ω) ∂μ| ≤
      ((b - a) / 2 + δ) * ∫ ω, |Y ω| ∂μ := by
  have hcont := continuous_concRamp a b δ
  have hcomp : AEStronglyMeasurable (fun ω => concRamp a b δ (Y ω)) μ :=
    hcont.comp_aestronglyMeasurable hYmeas
  have hprod_meas : AEStronglyMeasurable (fun ω => Y ω * concRamp a b δ (Y ω)) μ :=
    hYmeas.mul hcomp
  have hY1 : Integrable Y μ := hY.integrable one_le_two
  have habsY : Integrable (fun ω => |Y ω|) μ := hY1.abs
  have hR : 0 ≤ (b - a) / 2 + δ :=
    add_nonneg (div_nonneg (sub_nonneg.mpr hab) two_pos.le) hδ
  have hdom : Integrable (fun ω => Y ω * concRamp a b δ (Y ω)) μ := by
    refine (habsY.const_mul ((b - a) / 2 + δ)).mono' hprod_meas ?_
    filter_upwards with ω
    have hpt := abs_mul_concRamp_le (y := Y ω) hδ hab
    simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg hR, mul_comm] using hpt
  have hle :
      |∫ ω, Y ω * concRamp a b δ (Y ω) ∂μ| ≤
        ∫ ω, |Y ω * concRamp a b δ (Y ω)| ∂μ :=
    abs_integral_le_integral_abs
  refine hle.trans ?_
  have hpoint : ∀ ω, |Y ω * concRamp a b δ (Y ω)| ≤ ((b - a) / 2 + δ) * |Y ω| :=
    fun ω => abs_mul_concRamp_le hδ hab
  calc
    ∫ ω, |Y ω * concRamp a b δ (Y ω)| ∂μ ≤ ∫ ω, ((b - a) / 2 + δ) * |Y ω| ∂μ :=
      integral_mono hdom.abs (habsY.const_mul _) hpoint
    _ = ((b - a) / 2 + δ) * ∫ ω, |Y ω| ∂μ := integral_const_mul _ _

/-- Bound for the leave-one-out Stein term against the concentration ramp:
`|E[W⁽ⁱ⁾ f(W⁽ⁱ⁾)]| ≤ ((b-a)/2 + δ)`. -/
lemma abs_integral_leaveOneOut_mul_concRamp_le
    (hX : ∀ j, MemLp (X j) 2 μ) (hXmeas : ∀ j, Measurable (X j))
    (h_indep : iIndepFun X μ) (h_mean : ∀ j, ∫ ω, X j ω ∂μ = 0)
    (hvar : ∑ j, variance (X j) μ = 1) (i : ι)
    {a b δ : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    |∫ ω, leaveOneOut X i ω * concRamp a b δ (leaveOneOut X i ω) ∂μ| ≤
      (b - a) / 2 + δ := by
  have hW := memLp_leaveOneOut (X := X) (μ := μ) hX i
  have hWmeas : AEStronglyMeasurable (leaveOneOut X i) μ :=
    (measurable_leaveOneOut hXmeas i).aestronglyMeasurable
  have h1 := abs_integral_mul_concRamp_le (Y := leaveOneOut X i) hW hWmeas hδ hab
  have h2 := integral_abs_leaveOneOut_le_one hX h_indep h_mean hvar i
  have hR : 0 ≤ (b - a) / 2 + δ :=
    add_nonneg (div_nonneg (sub_nonneg.mpr hab) two_pos.le) hδ
  calc
    |∫ ω, leaveOneOut X i ω * concRamp a b δ (leaveOneOut X i ω) ∂μ|
        ≤ ((b - a) / 2 + δ) * ∫ ω, |leaveOneOut X i ω| ∂μ := h1
    _ ≤ ((b - a) / 2 + δ) * 1 := by gcongr
    _ = (b - a) / 2 + δ := mul_one _

/-! ### Integral form of the ramp and Stein exchange kernel identity -/

/-- Indicator of the linear region `[a-δ, b+δ]`. -/
def concInd (a b δ : ℝ) (s : ℝ) : ℝ :=
  (Icc (a - δ) (b + δ)).indicator (fun _ => (1 : ℝ)) s

lemma measurable_concInd (a b δ : ℝ) : Measurable (concInd a b δ) :=
  measurable_const.indicator measurableSet_Icc

lemma concInd_nonneg (a b δ s : ℝ) : 0 ≤ concInd a b δ s := by
  unfold concInd; by_cases h : s ∈ Icc (a - δ) (b + δ) <;> simp [indicator, h]

lemma concInd_le_one (a b δ s : ℝ) : concInd a b δ s ≤ 1 := by
  unfold concInd; by_cases h : s ∈ Icc (a - δ) (b + δ) <;> simp [indicator, h]

lemma concInd_eq_one {a b δ s : ℝ} (hs : s ∈ Icc (a - δ) (b + δ)) :
    concInd a b δ s = 1 :=
  indicator_of_mem hs _

lemma intervalIntegrable_concInd (a b δ x y : ℝ) :
    IntervalIntegrable (concInd a b δ) volume x y := by
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound measure_Ioc_lt_top ?_ (1 : ℝ) ?_
  · exact (measurable_concInd a b δ).aestronglyMeasurable.restrict
  · filter_upwards with s
    simp only [Real.norm_eq_abs, abs_of_nonneg (concInd_nonneg a b δ s)]
    exact concInd_le_one a b δ s

private lemma integral_const_one_Ioc {p q : ℝ} (hpq : p ≤ q) :
    ∫ _ in Ioc p q, (1 : ℝ) = q - p := by
  rw [integral_const, measureReal_restrict_apply_univ, measureReal_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hpq), smul_eq_mul, mul_one]

/-- Outside the support on the left (except possibly a null endpoint), the integrand vanishes. -/
lemma integral_concInd_Ioc_left_of_support {a b δ lo hi : ℝ}
    (_hδ : 0 ≤ δ) (_hab : a ≤ b) (_hle : lo ≤ hi) (hhi : hi ≤ a - δ) :
    ∫ s in Ioc lo hi, concInd a b δ s = 0 := by
  apply integral_eq_zero_of_ae
  refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) hi] with s hs_ne hs_mem
  have hs_lt : s < hi := lt_of_le_of_ne hs_mem.2 hs_ne
  have : s < a - δ := hs_lt.trans_le hhi
  have hnot : s ∉ Icc (a - δ) (b + δ) := fun ⟨ha, _⟩ => by linarith
  simp [concInd, indicator_of_notMem hnot]

/-- Strictly to the right of the support, the integrand vanishes. -/
lemma integral_concInd_Ioc_right_of_support {a b δ lo hi : ℝ}
    (_hδ : 0 ≤ δ) (_hab : a ≤ b) (_hle : lo ≤ hi) (hlo : b + δ ≤ lo) :
    ∫ s in Ioc lo hi, concInd a b δ s = 0 := by
  apply integral_eq_zero_of_ae
  refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
  filter_upwards with s hs_mem
  have hnot : s ∉ Icc (a - δ) (b + δ) := fun ⟨_, hb⟩ => by
    have : lo < s := hs_mem.1
    linarith
  simp [concInd, indicator_of_notMem hnot]

/-- On an interval contained in the support, the integral equals length. -/
lemma integral_concInd_eq_one_on_Ioc {a b δ lo hi : ℝ}
    (hle : lo ≤ hi) (hlo : a - δ ≤ lo) (hhi : hi ≤ b + δ) :
    ∫ s in Ioc lo hi, concInd a b δ s = hi - lo := by
  have hcongr : (concInd a b δ) =ᵐ[volume.restrict (Ioc lo hi)] fun _ => (1 : ℝ) := by
    refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
    filter_upwards with s hs
    exact concInd_eq_one ⟨hlo.trans (le_of_lt hs.1), le_trans hs.2 hhi⟩
  rw [integral_congr_ae hcongr, integral_const_one_Ioc hle]

/-- Integral form of the concentration ramp (CGS (3.32)). -/
def concRampIntegral (a b δ : ℝ) (w : ℝ) : ℝ :=
  ∫ s in ((a + b) / 2)..w, concInd a b δ s

/-- The integral ramp coincides with the clamp form. -/
lemma concRampIntegral_eq_concRamp {a b δ w : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    concRampIntegral a b δ w = concRamp a b δ w := by
  set m := (a + b) / 2 with hm
  set R := (b - a) / 2 + δ with hR
  have hleft : a - δ = m - R := by simp only [m, R]; ring
  have hright : b + δ = m + R := by simp only [m, R]; ring
  have hm_low : a - δ ≤ m := by simp only [m]; linarith
  have hm_high : m ≤ b + δ := by simp only [m]; linarith
  have hclamp : concRamp a b δ w = max (-R) (min R (w - m)) := by
    simp only [concRamp, m, R]
  rw [hclamp]
  rcases le_or_gt w (m - R) with hw_left | hw_gt_left
  · have hramp : concRampIntegral a b δ w = -∫ s in w..m, concInd a b δ s := by
      simp only [concRampIntegral]
      rw [show (a + b) / 2 = m from hm.symm, intervalIntegral.integral_symm]
    have hsplit :
        ∫ s in w..m, concInd a b δ s =
          (∫ s in w..(m - R), concInd a b δ s) + ∫ s in (m - R)..m, concInd a b δ s :=
      (intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_concInd a b δ w (m - R))
        (intervalIntegrable_concInd a b δ (m - R) m)).symm
    have h0 : ∫ s in w..(m - R), concInd a b δ s = 0 := by
      rw [intervalIntegral.integral_of_le hw_left]
      exact integral_concInd_Ioc_left_of_support hδ hab hw_left hleft.symm.le
    have hone : ∫ s in (m - R)..m, concInd a b δ s = R := by
      have hle : m - R ≤ m := by linarith
      rw [intervalIntegral.integral_of_le hle,
        integral_concInd_eq_one_on_Ioc hle hleft.le hm_high]
      ring
    have htot : ∫ s in w..m, concInd a b δ s = R := by linarith [hsplit, h0, hone]
    rw [hramp, htot, min_eq_right (by linarith : w - m ≤ R),
      max_eq_left (by linarith : w - m ≤ -R)]
  · rcases le_or_gt w (m + R) with hw_mid | hw_right
    · have hw_mem_low : a - δ ≤ w := by linarith [hleft]
      have hw_mem_high : w ≤ b + δ := by linarith [hright]
      by_cases hwm : m ≤ w
      · have hramp : concRampIntegral a b δ w = w - m := by
          simp only [concRampIntegral]
          rw [show (a + b) / 2 = m from hm.symm, intervalIntegral.integral_of_le hwm,
            integral_concInd_eq_one_on_Ioc hwm hm_low hw_mem_high]
        rw [hramp, min_eq_right (by linarith), max_eq_right (by linarith)]
      · have hwm' : w ≤ m := le_of_not_ge hwm
        have hramp : concRampIntegral a b δ w = w - m := by
          simp only [concRampIntegral]
          rw [show (a + b) / 2 = m from hm.symm, intervalIntegral.integral_symm,
            intervalIntegral.integral_of_le hwm',
            integral_concInd_eq_one_on_Ioc hwm' hw_mem_low hm_high]
          ring
        rw [hramp, min_eq_right (by linarith), max_eq_right (by linarith)]
    · have hwm : m ≤ w := by linarith
      have hsplit :
          ∫ s in m..w, concInd a b δ s =
            (∫ s in m..(m + R), concInd a b δ s) + ∫ s in (m + R)..w, concInd a b δ s :=
        (intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_concInd a b δ m (m + R))
          (intervalIntegrable_concInd a b δ (m + R) w)).symm
      have hone : ∫ s in m..(m + R), concInd a b δ s = R := by
        have hle : m ≤ m + R := by linarith
        rw [intervalIntegral.integral_of_le hle,
          integral_concInd_eq_one_on_Ioc hle hm_low hright.symm.le]
        ring
      have h0 : ∫ s in (m + R)..w, concInd a b δ s = 0 := by
        have hle : m + R ≤ w := le_of_lt hw_right
        rw [intervalIntegral.integral_of_le hle]
        exact integral_concInd_Ioc_right_of_support hδ hab hle hright.le
      have hramp : concRampIntegral a b δ w = R := by
        simp only [concRampIntegral]
        rw [show (a + b) / 2 = m from hm.symm]
        linarith [hsplit, hone, h0]
      rw [hramp, min_eq_left (by linarith), max_eq_right (by linarith)]

lemma intervalIntegrable_concInd_shift (a b δ w x y : ℝ) :
    IntervalIntegrable (fun t => concInd a b δ (w + t)) volume x y := by
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound measure_Ioc_lt_top ?_ (1 : ℝ) ?_
  · exact ((measurable_concInd a b δ).comp
      (continuous_const_add w).measurable).aestronglyMeasurable.restrict
  · filter_upwards with t
    simp only [Real.norm_eq_abs, abs_of_nonneg (concInd_nonneg a b δ _)]
    exact concInd_le_one a b δ _

/-- Telescoping identity for the integral ramp along a step of size `ξ`. -/
lemma concRampIntegral_sub_shift (a b δ w ξ : ℝ) :
    concRampIntegral a b δ w - concRampIntegral a b δ (w - ξ) =
      ∫ t in (-ξ)..(0 : ℝ), concInd a b δ (w + t) := by
  have h1 := intervalIntegrable_concInd a b δ ((a + b) / 2) (w - ξ)
  have h2 := intervalIntegrable_concInd a b δ (w - ξ) w
  have hsub : concRampIntegral a b δ w - concRampIntegral a b δ (w - ξ) =
      ∫ s in (w - ξ)..w, concInd a b δ s := by
    simp only [concRampIntegral]
    linarith [intervalIntegral.integral_add_adjacent_intervals h1 h2]
  rw [hsub]
  -- ∫_{w-ξ}^w f s = ∫_{-ξ}^0 f(t+w) = ∫_{-ξ}^0 f(w+t)
  have h :=
    intervalIntegral.integral_comp_add_right (concInd a b δ) w (a := -ξ) (b := (0 : ℝ))
  -- h : ∫ in (-ξ)..0, f(x+w) = ∫ in (-ξ+w)..(0+w), f
  have h' : ∫ t in (-ξ)..(0 : ℝ), concInd a b δ (t + w) =
      ∫ s in (w - ξ)..w, concInd a b δ s := by
    convert h using 2
    · ring
    · ring
  have h'' : ∫ t in (-ξ)..(0 : ℝ), concInd a b δ (w + t) =
      ∫ t in (-ξ)..(0 : ℝ), concInd a b δ (t + w) := by
    refine intervalIntegral.integral_congr fun t _ => by ring_nf
  linarith

/-- Pointwise Stein exchange kernel identity for the integral ramp. -/
lemma mul_concRampIntegral_sub_eq_integral_kernel (a b δ w ξ : ℝ) :
    ξ * (concRampIntegral a b δ w - concRampIntegral a b δ (w - ξ)) =
      ∫ t : ℝ, kernelDensity ξ t * concInd a b δ (w + t) := by
  rw [concRampIntegral_sub_shift]
  by_cases hξ : 0 ≤ ξ
  · -- LHS: ξ * ∫_{-ξ}^0 concInd(w+t) = ∫_{-ξ}^0 ξ * concInd(w+t)
    rw [← intervalIntegral.integral_const_mul ξ,
      intervalIntegral.integral_of_le (neg_nonpos.mpr hξ)]
    have hfun :
        (fun t => kernelDensity ξ t * concInd a b δ (w + t)) =
          (Icc (-ξ) 0).indicator (fun t => ξ * concInd a b δ (w + t)) := by
      funext t
      rw [kernelDensity_eq_indicator_nonneg ξ hξ]
      by_cases ht : t ∈ Icc (-ξ) 0
      · simp [indicator_of_mem ht]
      · simp [indicator_of_notMem ht]
    rw [hfun, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc]
  · have hlt : ξ < 0 := lt_of_not_ge hξ
    have hξ0 : 0 ≤ -ξ := neg_nonneg.mpr hlt.le
    have hsym :
        ∫ t in (-ξ)..(0 : ℝ), concInd a b δ (w + t) =
          -∫ t in (0 : ℝ)..(-ξ), concInd a b δ (w + t) :=
      intervalIntegral.integral_symm _ _
    rw [hsym, mul_neg]
    have hrew : -(ξ * ∫ t in (0 : ℝ)..(-ξ), concInd a b δ (w + t)) =
        (-ξ) * ∫ t in (0 : ℝ)..(-ξ), concInd a b δ (w + t) := by ring
    rw [hrew, ← intervalIntegral.integral_const_mul (-ξ),
      intervalIntegral.integral_of_le hξ0]
    have hfun :
        (fun t => kernelDensity ξ t * concInd a b δ (w + t)) =
          (Ioc 0 (-ξ)).indicator (fun t => (-ξ) * concInd a b δ (w + t)) := by
      funext t
      rw [kernelDensity_eq_indicator_neg ξ hlt]
      by_cases ht : t ∈ Ioc 0 (-ξ)
      · simp [indicator_of_mem ht]
      · simp [indicator_of_notMem ht]
    rw [hfun, integral_indicator measurableSet_Ioc]

/-- Pointwise Stein exchange identity for the clamp ramp (via equality with the integral form). -/
lemma mul_concRamp_sub_eq_integral_kernel {a b δ w ξ : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    ξ * (concRamp a b δ w - concRamp a b δ (w - ξ)) =
      ∫ t : ℝ, kernelDensity ξ t * concInd a b δ (w + t) := by
  rw [← concRampIntegral_eq_concRamp hδ hab,
    ← concRampIntegral_eq_concRamp hδ hab (w := w - ξ)]
  exact mul_concRampIntegral_sub_eq_integral_kernel a b δ w ξ

/-- On `{a ≤ w ≤ b}`, the kernel mass lower-bounds the exchange integrand. -/
lemma integral_kernel_mul_concInd_ge {a b δ w ξ : ℝ}
    (hδ : 0 ≤ δ) (hw : w ∈ Icc a b) :
    |ξ| * min δ |ξ| ≤ ∫ t : ℝ, kernelDensity ξ t * concInd a b δ (w + t) := by
  have hfun_le :
      (fun t => if |t| ≤ δ then kernelDensity ξ t else 0) ≤
        fun t => kernelDensity ξ t * concInd a b δ (w + t) := by
    intro t
    have hk : 0 ≤ kernelDensity ξ t := kernelDensity_nonneg ξ t
    by_cases ht : |t| ≤ δ
    · have h1 : concInd a b δ (w + t) = 1 :=
        concInd_eq_one (add_mem_linear_region hw ht)
      simp only [if_pos ht, h1, mul_one, le_refl]
    · simp only [if_neg ht]
      exact mul_nonneg hk (concInd_nonneg a b δ _)
  have hInt_rhs : Integrable (fun t => kernelDensity ξ t * concInd a b δ (w + t)) := by
    refine (integrable_kernelDensity ξ).mono' ?_ ?_
    · exact ((measurable_kernelDensity_right ξ).mul
        ((measurable_concInd a b δ).comp (continuous_const_add w).measurable)).aestronglyMeasurable
    · filter_upwards with t
      have hk : 0 ≤ kernelDensity ξ t := kernelDensity_nonneg ξ t
      have hi : 0 ≤ concInd a b δ (w + t) := concInd_nonneg a b δ _
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk, abs_of_nonneg hi]
      exact mul_le_of_le_one_right hk (concInd_le_one a b δ _)
  have hInt_lhs : Integrable (fun t => if |t| ≤ δ then kernelDensity ξ t else 0) := by
    refine (integrable_kernelDensity ξ).mono' ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      exact Measurable.ite (measurableSet_le measurable_id.abs measurable_const)
        (measurable_kernelDensity_right ξ) measurable_const
    · filter_upwards with t
      by_cases ht : |t| ≤ δ
      · simp only [if_pos ht, Real.norm_eq_abs, abs_of_nonneg (kernelDensity_nonneg ξ t),
          le_refl]
      · simp only [if_neg ht, norm_zero]
        exact kernelDensity_nonneg ξ t
  have hge := integral_mono hInt_lhs hInt_rhs hfun_le
  rwa [integral_kernelDensity_abs_le ξ hδ] at hge

/-! ### Leave-two-out independence -/

omit [IsProbabilityMeasure μ] [MeasurableSpace Ω] in
/-- `W⁽ⁱ⁾ - Xⱼ` is the sum over indices other than `i` and `j`. -/
lemma leaveOneOut_sub_eq_sum (i j : ι) (hij : j ≠ i) :
    (fun ω => leaveOneOut X i ω - X j ω) = ∑ k ∈ (Finset.univ.erase i).erase j, X k := by
  ext ω
  have hj : j ∈ Finset.univ.erase i := by simp [hij]
  calc
    leaveOneOut X i ω - X j ω
        = ∑ k ∈ Finset.univ.erase i, X k ω - X j ω := by simp [leaveOneOut]
    _ = ∑ k ∈ (Finset.univ.erase i).erase j, X k ω := by
        rw [← Finset.sum_erase_add (s := Finset.univ.erase i) (f := fun k => X k ω) hj]
        ring
    _ = (∑ k ∈ (Finset.univ.erase i).erase j, X k) ω := (Finset.sum_apply _ _ _).symm

omit [IsProbabilityMeasure μ] in
/-- For `j ≠ i`, the coordinate `Xⱼ` is independent of `W⁽ⁱ⁾ - Xⱼ`. -/
lemma indepFun_X_leaveTwoOut
    (hX : ∀ k, Measurable (X k)) (h_indep : iIndepFun X μ) (i j : ι) (hij : j ≠ i) :
    IndepFun (X j) (fun ω => leaveOneOut X i ω - X j ω) μ := by
  have hj_not : j ∉ (Finset.univ.erase i).erase j := Finset.notMem_erase j _
  have h := h_indep.indepFun_finsetSum_of_notMem hX hj_not
  convert h.symm using 1
  exact leaveOneOut_sub_eq_sum (X := X) i j hij

omit [IsProbabilityMeasure μ] in
/-- Mean-zero exchange leaf: `E[Xⱼ · g(W⁽ⁱ⁾ - Xⱼ)] = 0` for `j ≠ i`. -/
lemma integral_X_mul_comp_leaveTwoOut
    (hX : ∀ k, Measurable (X k)) (h_indep : iIndepFun X μ) (i j : ι) (hij : j ≠ i)
    (h_mean : ∫ ω, X j ω ∂μ = 0) (g : ℝ → ℝ)
    (hg : AEStronglyMeasurable g (μ.map (fun ω => leaveOneOut X i ω - X j ω))) :
    ∫ ω, X j ω * g (leaveOneOut X i ω - X j ω) ∂μ = 0 := by
  have hInd := indepFun_X_leaveTwoOut (X := X) (μ := μ) hX h_indep i j hij
  have h := hInd.integral_fun_comp_mul_comp (f := (id : ℝ → ℝ)) (g := g)
    (hX j).aemeasurable
    ((measurable_leaveOneOut hX i).sub (hX j)).aemeasurable
    measurable_id.aestronglyMeasurable hg
  simpa [h_mean] using h

/-! ### Probabilistic Stein exchange for leave-one-out -/

lemma integrable_X_mul_concRamp_leaveOneOut
    (hX : ∀ j, MemLp (X j) 2 μ) (hXmeas : ∀ j, Measurable (X j))
    (i j : ι) {a b δ : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    Integrable (fun ω => X j ω * concRamp a b δ (leaveOneOut X i ω)) μ := by
  have hR : 0 ≤ (b - a) / 2 + δ :=
    add_nonneg (div_nonneg (sub_nonneg.mpr hab) two_pos.le) hδ
  have habs := ((hX j).integrable one_le_two).abs
  refine (habs.const_mul ((b - a) / 2 + δ)).mono' ?_ ?_
  · exact (hXmeas j).aestronglyMeasurable.mul
      ((continuous_concRamp a b δ).comp_aestronglyMeasurable
        (measurable_leaveOneOut hXmeas i).aestronglyMeasurable)
  · filter_upwards with ω
    have hf := abs_concRamp_le (w := leaveOneOut X i ω) hδ hab
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |X j ω| * |concRamp a b δ (leaveOneOut X i ω)| ≤ |X j ω| * ((b - a) / 2 + δ) := by
        gcongr
      _ = ((b - a) / 2 + δ) * |X j ω| := mul_comm _ _

lemma integrable_X_mul_concRamp_sub
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (i j : ι) {a b δ : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    Integrable (fun ω => X j ω * concRamp a b δ (leaveOneOut X i ω - X j ω)) μ := by
  have hR : 0 ≤ (b - a) / 2 + δ :=
    add_nonneg (div_nonneg (sub_nonneg.mpr hab) two_pos.le) hδ
  have habs := ((hX j).integrable one_le_two).abs
  refine (habs.const_mul ((b - a) / 2 + δ)).mono' ?_ ?_
  · exact (hXmeas j).aestronglyMeasurable.mul
      ((continuous_concRamp a b δ).comp_aestronglyMeasurable
        ((measurable_leaveOneOut hXmeas i).sub (hXmeas j)).aestronglyMeasurable)
  · filter_upwards with ω
    have hf := abs_concRamp_le (w := leaveOneOut X i ω - X j ω) hδ hab
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |X j ω| * |concRamp a b δ (leaveOneOut X i ω - X j ω)| ≤
          |X j ω| * ((b - a) / 2 + δ) := by gcongr
      _ = ((b - a) / 2 + δ) * |X j ω| := mul_comm _ _

lemma integral_leaveOneOut_mul_concRamp_eq_sum
    (hX : ∀ j, MemLp (X j) 2 μ) (hXmeas : ∀ j, Measurable (X j))
    (i : ι) {a b δ : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    ∫ ω, leaveOneOut X i ω * concRamp a b δ (leaveOneOut X i ω) ∂μ =
      ∑ j ∈ Finset.univ.erase i,
        ∫ ω, X j ω * concRamp a b δ (leaveOneOut X i ω) ∂μ := by
  have hpoint : ∀ ω,
      leaveOneOut X i ω * concRamp a b δ (leaveOneOut X i ω) =
        ∑ j ∈ Finset.univ.erase i, X j ω * concRamp a b δ (leaveOneOut X i ω) := by
    intro ω; simp only [leaveOneOut, Finset.sum_mul]
  simp_rw [hpoint]
  exact integral_finsetSum _ fun j _ =>
    integrable_X_mul_concRamp_leaveOneOut hX hXmeas i j hδ hab

lemma integral_X_mul_concRamp_eq_exchange_add
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (i j : ι) {a b δ : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    ∫ ω, X j ω * concRamp a b δ (leaveOneOut X i ω) ∂μ =
      ∫ ω, X j ω * (concRamp a b δ (leaveOneOut X i ω) -
        concRamp a b δ (leaveOneOut X i ω - X j ω)) ∂μ +
      ∫ ω, X j ω * concRamp a b δ (leaveOneOut X i ω - X j ω) ∂μ := by
  have h1 := integrable_X_mul_concRamp_leaveOneOut hX hXmeas i j hδ hab
  have h2 := integrable_X_mul_concRamp_sub hX hXmeas i j hδ hab
  have h3 : Integrable (fun ω =>
      X j ω * concRamp a b δ (leaveOneOut X i ω) -
      X j ω * concRamp a b δ (leaveOneOut X i ω - X j ω)) μ := h1.sub h2
  calc
    ∫ ω, X j ω * concRamp a b δ (leaveOneOut X i ω) ∂μ
        = ∫ ω, (X j ω * concRamp a b δ (leaveOneOut X i ω) -
            X j ω * concRamp a b δ (leaveOneOut X i ω - X j ω) +
            X j ω * concRamp a b δ (leaveOneOut X i ω - X j ω)) ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun ω => by ring)
    _ = ∫ ω, (X j ω * concRamp a b δ (leaveOneOut X i ω) -
            X j ω * concRamp a b δ (leaveOneOut X i ω - X j ω)) ∂μ +
          ∫ ω, X j ω * concRamp a b δ (leaveOneOut X i ω - X j ω) ∂μ :=
        integral_add h3 h2
    _ = ∫ ω, X j ω * (concRamp a b δ (leaveOneOut X i ω) -
            concRamp a b δ (leaveOneOut X i ω - X j ω)) ∂μ +
          ∫ ω, X j ω * concRamp a b δ (leaveOneOut X i ω - X j ω) ∂μ := by
          congr 1
          refine integral_congr_ae (Eventually.of_forall fun ω => by ring)

omit [IsProbabilityMeasure μ] in
lemma integral_X_mul_concRamp_sub_eq_zero
    (hXmeas : ∀ k, Measurable (X k)) (h_indep : iIndepFun X μ)
    (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (i j : ι) (hij : j ≠ i) {a b δ : ℝ} :
    ∫ ω, X j ω * concRamp a b δ (leaveOneOut X i ω - X j ω) ∂μ = 0 :=
  integral_X_mul_comp_leaveTwoOut hXmeas h_indep i j hij (h_mean j) (concRamp a b δ)
    (continuous_concRamp a b δ).aestronglyMeasurable

omit [IsProbabilityMeasure μ] in
lemma integral_X_mul_concRamp_leaveOneOut_eq_zero
    (hXmeas : ∀ k, Measurable (X k)) (h_indep : iIndepFun X μ)
    (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (i : ι) {a b δ : ℝ} :
    ∫ ω, X i ω * concRamp a b δ (leaveOneOut X i ω) ∂μ = 0 :=
  integral_X_mul_comp_leaveOneOut hXmeas h_indep i (h_mean i) (concRamp a b δ)
    (continuous_concRamp a b δ).aestronglyMeasurable

/-- Stein exchange identity (CGS (3.34)):
`E[W⁽ⁱ⁾ f(W⁽ⁱ⁾)] - E[Xᵢ f(W⁽ⁱ⁾ - Xᵢ)] = ∑ⱼ E[Xⱼ (f(W⁽ⁱ⁾) - f(W⁽ⁱ⁾ - Xⱼ))]`. -/
lemma stein_exchange_leaveOneOut
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (i : ι) {a b δ : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    ∫ ω, leaveOneOut X i ω * concRamp a b δ (leaveOneOut X i ω) ∂μ -
      ∫ ω, X i ω * concRamp a b δ (leaveOneOut X i ω - X i ω) ∂μ =
      ∑ j : ι, ∫ ω, X j ω * (concRamp a b δ (leaveOneOut X i ω) -
        concRamp a b δ (leaveOneOut X i ω - X j ω)) ∂μ := by
  have hWsum := integral_leaveOneOut_mul_concRamp_eq_sum hX hXmeas i hδ hab
  have hj_ne : ∀ j ∈ Finset.univ.erase i,
      ∫ ω, X j ω * concRamp a b δ (leaveOneOut X i ω) ∂μ =
        ∫ ω, X j ω * (concRamp a b δ (leaveOneOut X i ω) -
          concRamp a b δ (leaveOneOut X i ω - X j ω)) ∂μ := by
    intro j hj
    have hij : j ≠ i := Finset.ne_of_mem_erase hj
    have hsplit := integral_X_mul_concRamp_eq_exchange_add hX hXmeas i j hδ hab
    have h0 :=
      integral_X_mul_concRamp_sub_eq_zero hXmeas h_indep h_mean i j hij (a := a) (b := b) (δ := δ)
    linarith
  have hi_term :
      ∫ ω, X i ω * (concRamp a b δ (leaveOneOut X i ω) -
        concRamp a b δ (leaveOneOut X i ω - X i ω)) ∂μ =
      -∫ ω, X i ω * concRamp a b δ (leaveOneOut X i ω - X i ω) ∂μ := by
    have hsplit := integral_X_mul_concRamp_eq_exchange_add hX hXmeas i i hδ hab
    have h0 :=
      integral_X_mul_concRamp_leaveOneOut_eq_zero hXmeas h_indep h_mean i
        (a := a) (b := b) (δ := δ)
    linarith
  have hsum_erase :
      ∑ j ∈ Finset.univ.erase i,
          ∫ ω, X j ω * (concRamp a b δ (leaveOneOut X i ω) -
            concRamp a b δ (leaveOneOut X i ω - X j ω)) ∂μ =
        ∑ j ∈ Finset.univ.erase i,
          ∫ ω, X j ω * concRamp a b δ (leaveOneOut X i ω) ∂μ :=
    Finset.sum_congr rfl fun j hj => (hj_ne j hj).symm
  set term : ι → ℝ := fun j =>
    ∫ ω, X j ω * (concRamp a b δ (leaveOneOut X i ω) -
      concRamp a b δ (leaveOneOut X i ω - X j ω)) ∂μ
  have htot : ∑ j : ι, term j = ∑ j ∈ Finset.univ.erase i, term j + term i :=
    (Finset.sum_erase_add (s := Finset.univ) (f := term) (Finset.mem_univ i)).symm
  change _ = ∑ j : ι, term j
  rw [htot]
  simp only [term] at hsum_erase hi_term ⊢
  rw [hsum_erase, ← hWsum, hi_term]
  ring

/-- Exchange RHS equals the integrated kernel form. -/
lemma stein_exchange_eq_kernel_integral
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (i : ι) {a b δ : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    ∫ ω, leaveOneOut X i ω * concRamp a b δ (leaveOneOut X i ω) ∂μ -
      ∫ ω, X i ω * concRamp a b δ (leaveOneOut X i ω - X i ω) ∂μ =
      ∑ j : ι, ∫ ω, (∫ t : ℝ,
        kernelDensity (X j ω) t *
          concInd a b δ (leaveOneOut X i ω + t)) ∂μ := by
  rw [stein_exchange_leaveOneOut hX hXmeas h_indep h_mean i hδ hab]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  exact mul_concRamp_sub_eq_integral_kernel hδ hab

/-! ### Kernel mass weights (lower-bound infrastructure) -/

/-- Kernel mass weight `|ξ| min(δ, |ξ|)`. -/
def kernelMass (δ ξ : ℝ) : ℝ := |ξ| * min δ |ξ|

lemma kernelMass_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (ξ : ℝ) : 0 ≤ kernelMass δ ξ :=
  mul_nonneg (abs_nonneg _) (le_min hδ (abs_nonneg _))

lemma kernelMass_le_mul_abs {δ ξ : ℝ} (hδ : 0 ≤ δ) :
    kernelMass δ ξ ≤ δ * |ξ| := by
  unfold kernelMass
  exact (mul_le_mul_of_nonneg_left (min_le_left δ |ξ|) (abs_nonneg _)).trans_eq (mul_comm _ _)

lemma measurable_kernelMass (δ : ℝ) : Measurable (kernelMass δ) :=
  measurable_id.abs.mul (measurable_const.min measurable_id.abs)

lemma continuous_kernelMass (δ : ℝ) : Continuous (kernelMass δ) :=
  continuous_abs.mul (continuous_const.min continuous_abs)

lemma memLp_kernelMass {Y : Ω → ℝ} (hY : MemLp Y 2 μ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hYmeas : AEStronglyMeasurable Y μ) :
    MemLp (fun ω => kernelMass δ (Y ω)) 2 μ := by
  have hmeas : AEStronglyMeasurable (fun ω => kernelMass δ (Y ω)) μ :=
    (continuous_kernelMass δ).comp_aestronglyMeasurable hYmeas
  refine MemLp.mono (hY.abs.const_mul δ) hmeas ?_
  filter_upwards with ω
  calc
    ‖kernelMass δ (Y ω)‖ = kernelMass δ (Y ω) :=
      Real.norm_of_nonneg (kernelMass_nonneg hδ _)
    _ ≤ δ * |Y ω| := kernelMass_le_mul_abs hδ
    _ = ‖δ * |Y ω|‖ := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hδ, abs_abs]

/-- Hölder/CS for real L² products: `|∫ f g| ≤ √(∫ f²) √(∫ g²)`. -/
lemma abs_integral_mul_le_sqrt_sq {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ ω, f ω * g ω ∂μ| ≤ √(∫ ω, (f ω) ^ 2 ∂μ) * √(∫ ω, (g ω) ^ 2 ∂μ) := by
  have h1 : |∫ ω, f ω * g ω ∂μ| ≤ ∫ ω, ‖f ω‖ * ‖g ω‖ ∂μ := by
    refine (abs_integral_le_integral_abs).trans ?_
    exact le_of_eq (integral_congr_ae (Eventually.of_forall fun ω => by
      dsimp only
      rw [abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]))
  have hf2 : MemLp f (ENNReal.ofReal 2) μ := by
    convert hf using 1; simp [ENNReal.ofReal_ofNat]
  have hg2 : MemLp g (ENNReal.ofReal 2) μ := by
    convert hg using 1; simp [ENNReal.ofReal_ofNat]
  have hHolder := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf2 hg2
  have h2 : ∫ ω, ‖f ω‖ ^ (2 : ℝ) ∂μ = ∫ ω, (f ω) ^ 2 ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp [Real.norm_eq_abs, sq_abs]
  have h3 : ∫ ω, ‖g ω‖ ^ (2 : ℝ) ∂μ = ∫ ω, (g ω) ^ 2 ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp [Real.norm_eq_abs, sq_abs]
  calc
    |∫ ω, f ω * g ω ∂μ| ≤ ∫ ω, ‖f ω‖ * ‖g ω‖ ∂μ := h1
    _ ≤ (∫ ω, ‖f ω‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ ω, ‖g ω‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hHolder
    _ = √(∫ ω, (f ω) ^ 2 ∂μ) * √(∫ ω, (g ω) ^ 2 ∂μ) := by
        rw [h2, h3, ← sqrt_eq_rpow, ← sqrt_eq_rpow]

/-- `|Cov(Y,Z)| ≤ √(Var Y · Var Z)`. -/
lemma abs_covariance_le_sqrt_variance {Y Z : Ω → ℝ}
    (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    |covariance Y Z μ| ≤ √(variance Y μ * variance Z μ) := by
  set Yc : Ω → ℝ := fun ω => Y ω - ∫ ω', Y ω' ∂μ
  set Zc : Ω → ℝ := fun ω => Z ω - ∫ ω', Z ω' ∂μ
  have hYc : MemLp Yc 2 μ := by
    have h := hY.sub (memLp_const (∫ ω, Y ω ∂μ))
    convert h using 1
    ext ω; simp [Yc, Pi.sub_apply]
  have hZc : MemLp Zc 2 μ := by
    have h := hZ.sub (memLp_const (∫ ω, Z ω ∂μ))
    convert h using 1
    ext ω; simp [Zc, Pi.sub_apply]
  have hcs := abs_integral_mul_le_sqrt_sq hYc hZc
  have hvY : ∫ ω, (Yc ω) ^ 2 ∂μ = variance Y μ := by
    simpa [Yc] using (variance_eq_integral hY.aemeasurable).symm
  have hvZ : ∫ ω, (Zc ω) ^ 2 ∂μ = variance Z μ := by
    simpa [Zc] using (variance_eq_integral hZ.aemeasurable).symm
  change |∫ ω, Yc ω * Zc ω ∂μ| ≤ √(variance Y μ * variance Z μ)
  calc
    |∫ ω, Yc ω * Zc ω ∂μ| ≤ √(∫ ω, (Yc ω) ^ 2 ∂μ) * √(∫ ω, (Zc ω) ^ 2 ∂μ) := hcs
    _ = √(variance Y μ) * √(variance Z μ) := by rw [hvY, hvZ]
    _ = √(variance Y μ * variance Z μ) := by rw [sqrt_mul (variance_nonneg Y μ)]

/-- Kernel mass sum `S = ∑ⱼ |Xⱼ| min(δ, |Xⱼ|)`. -/
def kernelMassSum (δ : ℝ) (X : ι → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑ j, kernelMass δ (X j ω)

omit [DecidableEq ι] in
lemma memLp_kernelMassSum (hX : ∀ j, MemLp (X j) 2 μ) (hXmeas : ∀ j, Measurable (X j))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    MemLp (kernelMassSum δ X) 2 μ :=
  memLp_finsetSum (s := Finset.univ) fun j _ =>
    memLp_kernelMass (hX j) hδ (hXmeas j).aestronglyMeasurable

lemma variance_kernelMass_le
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ) (hYmeas : AEStronglyMeasurable Y μ)
    (h_mean : ∫ ω, Y ω ∂μ = 0) {δ : ℝ} (hδ : 0 ≤ δ) :
    variance (fun ω => kernelMass δ (Y ω)) μ ≤ δ ^ 2 * variance Y μ := by
  have hmem := memLp_kernelMass hY hδ hYmeas
  have h1 := variance_le_expectation_sq hmem.aestronglyMeasurable
  have h2 : ∫ ω, (kernelMass δ (Y ω)) ^ 2 ∂μ ≤ δ ^ 2 * ∫ ω, (Y ω) ^ 2 ∂μ := by
    calc
      ∫ ω, (kernelMass δ (Y ω)) ^ 2 ∂μ ≤ ∫ ω, (δ * |Y ω|) ^ 2 ∂μ := by
        refine integral_mono hmem.integrable_sq (hY.abs.const_mul δ).integrable_sq fun ω => ?_
        have hle := kernelMass_le_mul_abs (ξ := Y ω) hδ
        have h0 := kernelMass_nonneg hδ (Y ω)
        have h1' : 0 ≤ δ * |Y ω| := mul_nonneg hδ (abs_nonneg _)
        exact sq_le_sq' (by nlinarith) (by nlinarith [hle])
      _ = ∫ ω, δ ^ 2 * (Y ω) ^ 2 ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        dsimp only
        rw [mul_pow, sq_abs]
      _ = δ ^ 2 * ∫ ω, (Y ω) ^ 2 ∂μ := integral_const_mul _ _
  have hEX2 : ∫ ω, (Y ω) ^ 2 ∂μ = variance Y μ :=
    (variance_eq_integral_sq hY h_mean).symm
  calc
    variance (fun ω => kernelMass δ (Y ω)) μ ≤ ∫ ω, (kernelMass δ (Y ω)) ^ 2 ∂μ := h1
    _ ≤ δ ^ 2 * ∫ ω, (Y ω) ^ 2 ∂μ := h2
    _ = δ ^ 2 * variance Y μ := by rw [hEX2]

set_option maxHeartbeats 800000 in
lemma variance_kernelMassSum_le
    (hX : ∀ j, MemLp (X j) 2 μ) (hXmeas : ∀ j, Measurable (X j))
    (h_indep : iIndepFun X μ) (h_mean : ∀ j, ∫ ω, X j ω ∂μ = 0)
    {δ : ℝ} (hδ : 0 ≤ δ) (hvar : ∑ j, variance (X j) μ = 1) :
    variance (kernelMassSum δ X) μ ≤ δ ^ 2 := by
  have hmem : ∀ j, MemLp (fun ω => kernelMass δ (X j ω)) 2 μ := fun j =>
    memLp_kernelMass (hX j) hδ (hXmeas j).aestronglyMeasurable
  have hY : (fun j : ι => fun ω => kernelMass δ (X j ω)) = fun j => kernelMass δ ∘ X j := rfl
  have hsum :
      variance (∑ j : ι, fun ω => kernelMass δ (X j ω)) μ =
        ∑ j, variance (fun ω => kernelMass δ (X j ω)) μ :=
    IndepFun.variance_sum (fun j _ => hmem j) fun j _ k _ hjk =>
      (h_indep.indepFun hjk).comp (measurable_kernelMass δ) (measurable_kernelMass δ)
  have hdef : kernelMassSum δ X = ∑ j : ι, fun ω => kernelMass δ (X j ω) := by
    ext ω; simp only [kernelMassSum, Finset.sum_apply]
  rw [hdef, hsum]
  calc
    ∑ j, variance (fun ω => kernelMass δ (X j ω)) μ ≤
        ∑ j, δ ^ 2 * variance (X j) μ :=
      Finset.sum_le_sum fun j _ =>
        variance_kernelMass_le (hX j) (hXmeas j).aestronglyMeasurable (h_mean j) hδ
    _ = δ ^ 2 * ∑ j, variance (X j) μ := by rw [Finset.mul_sum]
    _ = δ ^ 2 := by rw [hvar, mul_one]

/-- Third-moment sum `∑ᵢ E|Xᵢ|³`. -/
def thirdMomentSum (X : ι → Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∑ i : ι, ∫ ω, |X i ω| ^ 3 ∂μ

omit [IsProbabilityMeasure μ] [DecidableEq ι] in
lemma thirdMomentSum_nonneg (hX : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ) :
    0 ≤ thirdMomentSum (X := X) μ :=
  Finset.sum_nonneg fun i _ => integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _

/-- `E[S] ≥ 1 - γ/(4δ)` for `S = ∑ |Xⱼ| min(δ,|Xⱼ|)` and `γ = ∑ E|Xⱼ|³`. -/
lemma integral_kernelMassSum_ge
    (hX : ∀ j, MemLp (X j) 2 μ) (hXmeas : ∀ j, Measurable (X j))
    (h_mean : ∀ j, ∫ ω, X j ω ∂μ = 0)
    (hvar : ∑ j, variance (X j) μ = 1)
    (h3 : ∀ j, Integrable (fun ω => |X j ω| ^ 3) μ)
    {δ : ℝ} (hδ : 0 < δ) :
    1 - thirdMomentSum (X := X) μ / (4 * δ) ≤ ∫ ω, kernelMassSum δ X ω ∂μ := by
  have hδ0 : 0 ≤ δ := hδ.le
  have hintS : Integrable (kernelMassSum δ X) μ :=
    (memLp_kernelMassSum hX hXmeas hδ0).integrable one_le_two
  have hpt : ∀ ω,
      ∑ j, (X j ω) ^ 2 - (∑ j, |X j ω| ^ 3) / (4 * δ) ≤ kernelMassSum δ X ω := by
    intro ω
    have h1 : ∑ j, ((X j ω) ^ 2 - |X j ω| ^ 3 / (4 * δ)) ≤
        ∑ j, kernelMass δ (X j ω) :=
      Finset.sum_le_sum fun j _ => abs_mul_min_ge_sq_sub (ξ := X j ω) hδ
    have h2 : ∑ j, ((X j ω) ^ 2 - |X j ω| ^ 3 / (4 * δ)) =
        ∑ j, (X j ω) ^ 2 - ∑ j, |X j ω| ^ 3 / (4 * δ) := Finset.sum_sub_distrib _ _
    have h3' : ∑ j, |X j ω| ^ 3 / (4 * δ) = (∑ j, |X j ω| ^ 3) / (4 * δ) := by
      simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
    rwa [h2, h3'] at h1
  have hA : Integrable (fun ω => ∑ j, (X j ω) ^ 2) μ :=
    integrable_finsetSum (s := Finset.univ) fun j _ => (hX j).integrable_sq
  have hB : Integrable (fun ω => (∑ j, |X j ω| ^ 3) / (4 * δ)) μ :=
    (integrable_finsetSum (s := Finset.univ) fun j _ => h3 j).div_const (4 * δ)
  have hL : Integrable
      (fun ω => ∑ j, (X j ω) ^ 2 - (∑ j, |X j ω| ^ 3) / (4 * δ)) μ := hA.sub hB
  have hle := integral_mono hL hintS hpt
  have hEX2 : ∫ ω, ∑ j, (X j ω) ^ 2 ∂μ = 1 := by
    rw [integral_finsetSum _ fun j _ => (hX j).integrable_sq]
    conv_lhs => arg 2; ext j; rw [← variance_eq_integral_sq (hX j) (h_mean j)]
    exact hvar
  have hE3 : ∫ ω, ∑ j, |X j ω| ^ 3 ∂μ = thirdMomentSum (X := X) μ := by
    rw [integral_finsetSum _ fun j _ => h3 j]; rfl
  have hLval :
      ∫ ω, ∑ j, (X j ω) ^ 2 - (∑ j, |X j ω| ^ 3) / (4 * δ) ∂μ =
        1 - thirdMomentSum (X := X) μ / (4 * δ) := by
    rw [integral_sub hA hB, hEX2, integral_div, hE3]
  rwa [hLval] at hle

lemma abs_integral_X_mul_concRamp_sub_le
    (hX : ∀ j, MemLp (X j) 2 μ) (hXmeas : ∀ j, Measurable (X j))
    (i : ι) {a b δ : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    |∫ ω, X i ω * concRamp a b δ (leaveOneOut X i ω - X i ω) ∂μ| ≤
      ((b - a) / 2 + δ) * ∫ ω, |X i ω| ∂μ := by
  have h2 := integrable_X_mul_concRamp_sub hX hXmeas i i hδ hab
  have hle := abs_integral_le_integral_abs (μ := μ)
    (f := fun ω => X i ω * concRamp a b δ (leaveOneOut X i ω - X i ω))
  refine hle.trans ?_
  have hpoint : ∀ ω,
      |X i ω * concRamp a b δ (leaveOneOut X i ω - X i ω)| ≤
        ((b - a) / 2 + δ) * |X i ω| := by
    intro ω
    calc
      |X i ω * concRamp a b δ (leaveOneOut X i ω - X i ω)| =
          |X i ω| * |concRamp a b δ (leaveOneOut X i ω - X i ω)| := abs_mul _ _
      _ ≤ |X i ω| * ((b - a) / 2 + δ) := by
          gcongr; exact abs_concRamp_le hδ hab
      _ = ((b - a) / 2 + δ) * |X i ω| := mul_comm _ _
  have habs := ((hX i).integrable one_le_two).abs
  calc
    ∫ ω, |X i ω * concRamp a b δ (leaveOneOut X i ω - X i ω)| ∂μ ≤
        ∫ ω, ((b - a) / 2 + δ) * |X i ω| ∂μ :=
      integral_mono h2.abs (habs.const_mul _) hpoint
    _ = ((b - a) / 2 + δ) * ∫ ω, |X i ω| ∂μ := integral_const_mul _ _

/-- Upper bound for the Stein exchange LHS: `|E[W f] - E[Xᵢ f(W-Xᵢ)]| ≤ √2 · R`. -/
lemma abs_stein_exchange_le
    (hX : ∀ j, MemLp (X j) 2 μ) (hXmeas : ∀ j, Measurable (X j))
    (h_indep : iIndepFun X μ) (h_mean : ∀ j, ∫ ω, X j ω ∂μ = 0)
    (hvar : ∑ j, variance (X j) μ = 1)
    (i : ι) {a b δ : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    |∫ ω, leaveOneOut X i ω * concRamp a b δ (leaveOneOut X i ω) ∂μ -
      ∫ ω, X i ω * concRamp a b δ (leaveOneOut X i ω - X i ω) ∂μ| ≤
      √2 * ((b - a) / 2 + δ) := by
  have h1' := abs_integral_mul_concRamp_le
    (Y := leaveOneOut X i) (memLp_leaveOneOut hX i)
    (measurable_leaveOneOut hXmeas i).aestronglyMeasurable hδ hab
  have h2 := abs_integral_X_mul_concRamp_sub_le hX hXmeas i hδ hab
  have hsum := integral_abs_leaveOneOut_add_X_le_sqrt_two hX h_indep h_mean hvar i
  have hR : 0 ≤ (b - a) / 2 + δ :=
    add_nonneg (div_nonneg (sub_nonneg.mpr hab) two_pos.le) hδ
  calc
    |_ - _| ≤ |∫ ω, leaveOneOut X i ω * concRamp a b δ (leaveOneOut X i ω) ∂μ| +
        |∫ ω, X i ω * concRamp a b δ (leaveOneOut X i ω - X i ω) ∂μ| :=
      abs_sub _ _
    _ ≤ ((b - a) / 2 + δ) * ∫ ω, |leaveOneOut X i ω| ∂μ +
        ((b - a) / 2 + δ) * ∫ ω, |X i ω| ∂μ := by gcongr <;> first | exact h1' | exact h2
    _ = ((b - a) / 2 + δ) *
        (∫ ω, |leaveOneOut X i ω| ∂μ + ∫ ω, |X i ω| ∂μ) := by ring
    _ ≤ ((b - a) / 2 + δ) * √2 := by gcongr
    _ = √2 * ((b - a) / 2 + δ) := mul_comm _ _

/-! ### Indicator of the leave-one-out interval and lower bound -/

/-- Real indicator of `{a ≤ W⁽ⁱ⁾ ≤ b}`. -/
def leaveOneOutInterval (X : ι → Ω → ℝ) (i : ι) (a b : ℝ) : Ω → ℝ :=
  fun ω => if a ≤ leaveOneOut X i ω ∧ leaveOneOut X i ω ≤ b then (1 : ℝ) else 0

lemma leaveOneOutInterval_eq_indicator (X : ι → Ω → ℝ) (i : ι) (a b : ℝ) :
    leaveOneOutInterval X i a b =
      ({ω | a ≤ leaveOneOut X i ω ∧ leaveOneOut X i ω ≤ b}).indicator fun _ => (1 : ℝ) := by
  ext ω
  by_cases h : a ≤ leaveOneOut X i ω ∧ leaveOneOut X i ω ≤ b
  · simp [leaveOneOutInterval, h, Set.indicator_of_mem]
  · simp [leaveOneOutInterval, h, Set.indicator_of_notMem]

lemma measurable_leaveOneOutInterval
    (hXmeas : ∀ j, Measurable (X j)) (i : ι) (a b : ℝ) :
    Measurable (leaveOneOutInterval X i a b) := by
  rw [leaveOneOutInterval_eq_indicator]
  refine Measurable.indicator measurable_const ?_
  exact (measurableSet_le measurable_const (measurable_leaveOneOut hXmeas i)).inter
    (measurableSet_le (measurable_leaveOneOut hXmeas i) measurable_const)

lemma leaveOneOutInterval_nonneg (X : ι → Ω → ℝ) (i : ι) (a b : ℝ) (ω : Ω) :
    0 ≤ leaveOneOutInterval X i a b ω := by
  unfold leaveOneOutInterval; split_ifs <;> norm_num

lemma leaveOneOutInterval_le_one (X : ι → Ω → ℝ) (i : ι) (a b : ℝ) (ω : Ω) :
    leaveOneOutInterval X i a b ω ≤ 1 := by
  unfold leaveOneOutInterval; split_ifs <;> norm_num

lemma memLp_leaveOneOutInterval
    (hXmeas : ∀ j, Measurable (X j)) (i : ι) (a b : ℝ) :
    MemLp (leaveOneOutInterval X i a b) 2 μ := by
  rw [leaveOneOutInterval_eq_indicator]
  exact memLp_indicator_const 2
    ((measurableSet_le measurable_const (measurable_leaveOneOut hXmeas i)).inter
      (measurableSet_le (measurable_leaveOneOut hXmeas i) measurable_const))
    (1 : ℝ) (Or.inr (measure_ne_top μ _))

lemma measurableSet_leaveOneOutInterval
    (hXmeas : ∀ j, Measurable (X j)) (i : ι) (a b : ℝ) :
    MeasurableSet {ω | a ≤ leaveOneOut X i ω ∧ leaveOneOut X i ω ≤ b} :=
  (measurableSet_le measurable_const (measurable_leaveOneOut hXmeas i)).inter
    (measurableSet_le (measurable_leaveOneOut hXmeas i) measurable_const)

lemma integral_leaveOneOutInterval
    (hXmeas : ∀ j, Measurable (X j)) (i : ι) (a b : ℝ) :
    ∫ ω, leaveOneOutInterval X i a b ω ∂μ =
      μ.real {ω | a ≤ leaveOneOut X i ω ∧ leaveOneOut X i ω ≤ b} := by
  have hms := measurableSet_leaveOneOutInterval hXmeas i a b
  rw [leaveOneOutInterval_eq_indicator, integral_indicator hms, integral_const,
    measureReal_restrict_apply_univ, smul_eq_mul, mul_one]

/-- Pointwise nonnegativity of the Stein kernel integrand. -/
lemma integral_kernel_mul_concInd_nonneg (a b δ w ξ : ℝ) :
    0 ≤ ∫ t : ℝ, kernelDensity ξ t * concInd a b δ (w + t) := by
  exact integral_nonneg fun t =>
    mul_nonneg (kernelDensity_nonneg ξ t) (concInd_nonneg a b δ _)

/-- Integrability of the factored exchange term `Xⱼ (f(W) - f(W-Xⱼ))`. -/
lemma integrable_X_mul_concRamp_diff
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (i j : ι) {a b δ : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    Integrable (fun ω =>
      X j ω * (concRamp a b δ (leaveOneOut X i ω) -
        concRamp a b δ (leaveOneOut X i ω - X j ω))) μ := by
  have h1 := integrable_X_mul_concRamp_leaveOneOut hX hXmeas i j hδ hab
  have h2 := integrable_X_mul_concRamp_sub hX hXmeas i j hδ hab
  have hEq : (fun ω =>
      X j ω * (concRamp a b δ (leaveOneOut X i ω) -
        concRamp a b δ (leaveOneOut X i ω - X j ω))) =
      (fun ω => X j ω * concRamp a b δ (leaveOneOut X i ω)) -
        fun ω => X j ω * concRamp a b δ (leaveOneOut X i ω - X j ω) := by
    ext ω
    simp only [Pi.sub_apply]
    ring
  rw [hEq]
  exact h1.sub h2

/-- Stein exchange dominates the indicator–kernel-mass product (CGS (3.34)–(3.35)). -/
lemma stein_exchange_ge_indicator_kernelMass
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (i : ι) {a b δ : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    ∫ ω, leaveOneOutInterval X i a b ω * kernelMassSum δ X ω ∂μ ≤
      ∫ ω, leaveOneOut X i ω * concRamp a b δ (leaveOneOut X i ω) ∂μ -
        ∫ ω, X i ω * concRamp a b δ (leaveOneOut X i ω - X i ω) ∂μ := by
  have hex := stein_exchange_eq_kernel_integral hX hXmeas h_indep h_mean i hδ hab
  -- Pointwise kernel integral at each ω
  set Kint : Ω → ι → ℝ := fun ω j =>
    ∫ t : ℝ, kernelDensity (X j ω) t * concInd a b δ (leaveOneOut X i ω + t)
  have hpt : ∀ ω,
      leaveOneOutInterval X i a b ω * kernelMassSum δ X ω ≤ ∑ j : ι, Kint ω j := by
    intro ω
    by_cases hw : a ≤ leaveOneOut X i ω ∧ leaveOneOut X i ω ≤ b
    · have hI : leaveOneOutInterval X i a b ω = 1 := by simp [leaveOneOutInterval, hw]
      have hmem : leaveOneOut X i ω ∈ Icc a b := ⟨hw.1, hw.2⟩
      rw [hI, one_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      exact integral_kernel_mul_concInd_ge hδ hmem
    · have hI : leaveOneOutInterval X i a b ω = 0 := by simp [leaveOneOutInterval, hw]
      rw [hI, zero_mul]
      exact Finset.sum_nonneg fun j _ =>
        integral_kernel_mul_concInd_nonneg a b δ _ _
  have hKint_eq : ∀ ω j,
      Kint ω j =
        X j ω * (concRamp a b δ (leaveOneOut X i ω) -
          concRamp a b δ (leaveOneOut X i ω - X j ω)) := fun ω j =>
    (mul_concRamp_sub_eq_integral_kernel hδ hab).symm
  have hRHS_eq : (fun ω => ∑ j : ι, Kint ω j) =
      fun ω => ∑ j : ι,
        X j ω * (concRamp a b δ (leaveOneOut X i ω) -
          concRamp a b δ (leaveOneOut X i ω - X j ω)) := by
    ext ω
    refine Finset.sum_congr rfl fun j _ => hKint_eq ω j
  have hRHS_int : Integrable (fun ω => ∑ j : ι, Kint ω j) μ := by
    rw [hRHS_eq]
    exact integrable_finsetSum (s := Finset.univ) fun j _ =>
      integrable_X_mul_concRamp_diff hX hXmeas i j hδ hab
  have hmeasS : Measurable (kernelMassSum δ X) :=
    Finset.measurable_fun_sum Finset.univ fun j _ =>
      (measurable_kernelMass δ).comp (hXmeas j)
  have hLHS_int : Integrable
      (fun ω => leaveOneOutInterval X i a b ω * kernelMassSum δ X ω) μ := by
    have hS := (memLp_kernelMassSum hX hXmeas hδ).integrable one_le_two
    refine hS.mono' ?_ ?_
    · exact (measurable_leaveOneOutInterval hXmeas i a b).aestronglyMeasurable.mul
        hmeasS.aestronglyMeasurable
    · filter_upwards with ω
      have hA0 := leaveOneOutInterval_nonneg X i a b ω
      have hA1 := leaveOneOutInterval_le_one X i a b ω
      have hSn : 0 ≤ kernelMassSum δ X ω :=
        Finset.sum_nonneg fun j _ => kernelMass_nonneg hδ (X j ω)
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hA0, abs_of_nonneg hSn]
      exact mul_le_of_le_one_left hSn hA1
  have hge := integral_mono hLHS_int hRHS_int hpt
  have hsum :
      ∫ ω, ∑ j : ι, Kint ω j ∂μ =
        ∑ j : ι, ∫ ω, Kint ω j ∂μ := by
    rw [hRHS_eq]
    have hint := fun j => integrable_X_mul_concRamp_diff hX hXmeas i j hδ hab
    rw [integral_finsetSum _ fun j _ => hint j]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    exact (hKint_eq ω j).symm
  -- Connect ∑ⱼ ∫ Kint to the exchange identity
  have hex' :
      ∑ j : ι, ∫ ω, Kint ω j ∂μ =
        ∫ ω, leaveOneOut X i ω * concRamp a b δ (leaveOneOut X i ω) ∂μ -
          ∫ ω, X i ω * concRamp a b δ (leaveOneOut X i ω - X i ω) ∂μ := by
    have hcongr : ∑ j : ι, ∫ ω, Kint ω j ∂μ =
        ∑ j : ι, ∫ ω, (∫ t : ℝ,
          kernelDensity (X j ω) t *
            concInd a b δ (leaveOneOut X i ω + t)) ∂μ := by
      refine Finset.sum_congr rfl fun j _ => ?_
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      rfl
    rw [hcongr, ← hex]
  calc
    ∫ ω, leaveOneOutInterval X i a b ω * kernelMassSum δ X ω ∂μ ≤
        ∫ ω, ∑ j : ι, Kint ω j ∂μ := hge
    _ = ∑ j : ι, ∫ ω, Kint ω j ∂μ := hsum
    _ = ∫ ω, leaveOneOut X i ω * concRamp a b δ (leaveOneOut X i ω) ∂μ -
          ∫ ω, X i ω * concRamp a b δ (leaveOneOut X i ω - X i ω) ∂μ := hex'

/-- CS lower bound: `E[1_A S] ≥ E[S] P(A) - √(Var S)`. -/
lemma integral_indicator_kernelMass_ge
    (hX : ∀ j, MemLp (X j) 2 μ) (hXmeas : ∀ j, Measurable (X j))
    (i : ι) (a b : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ ω, kernelMassSum δ X ω ∂μ) *
        (∫ ω, leaveOneOutInterval X i a b ω ∂μ) -
      √(variance (kernelMassSum δ X) μ) ≤
      ∫ ω, leaveOneOutInterval X i a b ω * kernelMassSum δ X ω ∂μ := by
  set A := leaveOneOutInterval X i a b
  set S := kernelMassSum δ X
  have hA : MemLp A 2 μ := memLp_leaveOneOutInterval (μ := μ) hXmeas i a b
  have hS : MemLp S 2 μ := memLp_kernelMassSum hX hXmeas hδ
  have hA2 : ∫ ω, (A ω) ^ 2 ∂μ = ∫ ω, A ω ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    change A ω ^ 2 = A ω
    dsimp [A, leaveOneOutInterval]
    split_ifs <;> norm_num
  have hA_le1 : ∫ ω, A ω ∂μ ≤ 1 := by
    have h1 : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
    exact (integral_mono (hA.integrable one_le_two) h1
      (fun ω => leaveOneOutInterval_le_one X i a b ω)).trans_eq (by simp)
  have hA0 : 0 ≤ ∫ ω, A ω ∂μ :=
    integral_nonneg fun ω => leaveOneOutInterval_nonneg X i a b ω
  have hvarA : variance A μ ≤ 1 := by
    have hsub : variance A μ = ∫ ω, (A ω) ^ 2 ∂μ - (∫ ω, A ω ∂μ) ^ 2 :=
      variance_eq_sub hA
    rw [hsub, hA2]
    nlinarith [sq_nonneg (∫ ω, A ω ∂μ)]
  have hsqrtA : √(variance A μ) ≤ 1 := by
    refine sqrt_le_iff.mpr ?_
    constructor
    · exact zero_le_one
    · simpa using hvarA
  have hcov' : |covariance A S μ| ≤ √(variance S μ) := by
    have h := abs_covariance_le_sqrt_variance hA hS
    rw [sqrt_mul (variance_nonneg A μ)] at h
    exact h.trans (mul_le_of_le_one_left (sqrt_nonneg _) hsqrtA)
  have hcov_eq : covariance A S μ =
      ∫ ω, A ω * S ω ∂μ - (∫ ω, A ω ∂μ) * (∫ ω, S ω ∂μ) :=
    covariance_eq_sub hA hS
  have hge : (∫ ω, A ω ∂μ) * (∫ ω, S ω ∂μ) - |covariance A S μ| ≤
      ∫ ω, A ω * S ω ∂μ := by
    have hrew : ∫ ω, A ω * S ω ∂μ =
        covariance A S μ + (∫ ω, A ω ∂μ) * (∫ ω, S ω ∂μ) := by
      linarith [hcov_eq]
    have hneg : -|covariance A S μ| ≤ covariance A S μ := (abs_le.mp le_rfl).1
    linarith [hrew, hneg]
  calc
    (∫ ω, S ω ∂μ) * (∫ ω, A ω ∂μ) - √(variance S μ) =
        (∫ ω, A ω ∂μ) * (∫ ω, S ω ∂μ) - √(variance S μ) := by ring
    _ ≤ (∫ ω, A ω ∂μ) * (∫ ω, S ω ∂μ) - |covariance A S μ| := by
        linarith [hcov']
    _ ≤ ∫ ω, A ω * S ω ∂μ := hge

/-- Combining upper/lower bounds: exchange LHS ≥ (1/2)P - δ when `E[S] ≥ 1/2` and
`Var S ≤ δ²`. -/
lemma stein_exchange_ge_half_prob
    (hX : ∀ j, MemLp (X j) 2 μ) (hXmeas : ∀ j, Measurable (X j))
    (h_indep : iIndepFun X μ) (h_mean : ∀ j, ∫ ω, X j ω ∂μ = 0)
    (hvar : ∑ j, variance (X j) μ = 1)
    (i : ι) {a b δ : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b)
    (hES : (1 : ℝ) / 2 ≤ ∫ ω, kernelMassSum δ X ω ∂μ)
    (hVS : variance (kernelMassSum δ X) μ ≤ δ ^ 2) :
    (1 : ℝ) / 2 *
        (μ.real {ω | a ≤ leaveOneOut X i ω ∧ leaveOneOut X i ω ≤ b}) - δ ≤
      ∫ ω, leaveOneOut X i ω * concRamp a b δ (leaveOneOut X i ω) ∂μ -
        ∫ ω, X i ω * concRamp a b δ (leaveOneOut X i ω - X i ω) ∂μ := by
  set p := μ.real {ω | a ≤ leaveOneOut X i ω ∧ leaveOneOut X i ω ≤ b}
  set S := kernelMassSum δ X
  set A := leaveOneOutInterval X i a b
  have hAS :
      ∫ ω, A ω * S ω ∂μ ≤
        ∫ ω, leaveOneOut X i ω * concRamp a b δ (leaveOneOut X i ω) ∂μ -
          ∫ ω, X i ω * concRamp a b δ (leaveOneOut X i ω - X i ω) ∂μ := by
    simpa [A, S] using
      stein_exchange_ge_indicator_kernelMass hX hXmeas h_indep h_mean i hδ hab
  have hCS := integral_indicator_kernelMass_ge hX hXmeas i a b hδ
  have hP : ∫ ω, A ω ∂μ = p := integral_leaveOneOutInterval hXmeas i a b
  have hsqrtV : √(variance S μ) ≤ δ :=
    (sqrt_le_iff).2 ⟨hδ, hVS⟩
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hES_p : (1 : ℝ) / 2 * p ≤ (∫ ω, S ω ∂μ) * (∫ ω, A ω ∂μ) := by
    rw [hP]
    exact mul_le_mul_of_nonneg_right hES hp0
  have hmid : (∫ ω, S ω ∂μ) * (∫ ω, A ω ∂μ) - √(variance S μ) ≤ ∫ ω, A ω * S ω ∂μ :=
    hCS
  have hstep1 : (1 : ℝ) / 2 * p - δ ≤
      (∫ ω, S ω ∂μ) * (∫ ω, A ω ∂μ) - √(variance S μ) := by
    linarith [hES_p, hsqrtV]
  linarith [hstep1, hmid, hAS]

/-- Leave-one-out concentration (CGS Lemma 3.1 form):
`P(a ≤ W⁽ⁱ⁾ ≤ b) ≤ √2 (b - a) + 2(√2 + 1) γ` with `γ = ∑ E|Xⱼ|³`. -/
lemma concentration_leaveOneOut
    (hX : ∀ j, MemLp (X j) 2 μ) (hXmeas : ∀ j, Measurable (X j))
    (h_indep : iIndepFun X μ) (h_mean : ∀ j, ∫ ω, X j ω ∂μ = 0)
    (hvar : ∑ j, variance (X j) μ = 1)
    (h3 : ∀ j, Integrable (fun ω => |X j ω| ^ 3) μ)
    (i : ι) {a b : ℝ} (hab : a ≤ b) :
    μ.real {ω | a ≤ leaveOneOut X i ω ∧ leaveOneOut X i ω ≤ b} ≤
      √2 * (b - a) + 2 * (√2 + 1) * thirdMomentSum (X := X) μ := by
  set γ := thirdMomentSum (X := X) μ
  have hγ0 : 0 ≤ γ := thirdMomentSum_nonneg h3
  set p := μ.real {ω | a ≤ leaveOneOut X i ω ∧ leaveOneOut X i ω ≤ b}
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := by
    change (μ {ω | a ≤ leaveOneOut X i ω ∧ leaveOneOut X i ω ≤ b}).toReal ≤ 1
    have hμ : μ {ω | a ≤ leaveOneOut X i ω ∧ leaveOneOut X i ω ≤ b} ≤ 1 := prob_le_one
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2 hμ
  by_cases htriv : 1 ≤ 2 * (√2 + 1) * γ
  · have : p ≤ 2 * (√2 + 1) * γ := le_trans hp1 htriv
    have hba : 0 ≤ √2 * (b - a) :=
      mul_nonneg (sqrt_nonneg _) (sub_nonneg.mpr hab)
    linarith
  · -- Main: γ > 0 from total variance 1
    have hγpos : 0 < γ := by
      by_contra hne
      push_neg at hne
      have hγeq : γ = 0 := le_antisymm hne hγ0
      have hterm : ∀ j, ∫ ω, |X j ω| ^ 3 ∂μ = 0 := by
        intro j
        have hsum0 : ∑ j : ι, ∫ ω, |X j ω| ^ 3 ∂μ = 0 := by
          simpa [γ, thirdMomentSum] using hγeq
        have hnn : ∀ j ∈ Finset.univ, 0 ≤ ∫ ω, |X j ω| ^ 3 ∂μ := fun j _ =>
          integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _
        exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum0 j (Finset.mem_univ j)
      have hvar0 : ∀ j, variance (X j) μ = 0 := by
        intro j
        have hnn : 0 ≤ᵐ[μ] fun ω => |X j ω| ^ 3 :=
          Eventually.of_forall fun _ => pow_nonneg (abs_nonneg _) _
        have hae : (fun ω => |X j ω| ^ 3) =ᵐ[μ] 0 :=
          (integral_eq_zero_iff_of_nonneg_ae hnn (h3 j)).1 (hterm j)
        have hX0 : X j =ᵐ[μ] 0 := by
          filter_upwards [hae] with ω hω
          have hpow : |X j ω| ^ 3 = 0 := by simpa using hω
          have habs : |X j ω| = 0 := (pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).1 hpow
          exact abs_eq_zero.mp habs
        rw [variance_congr hX0, variance_zero]
      have : ∑ j, variance (X j) μ = 0 := Finset.sum_eq_zero fun j _ => hvar0 j
      linarith [hvar]
    set δ : ℝ := γ
    have hδ : 0 ≤ δ := hγ0
    have hδpos : 0 < δ := hγpos
    have hES_raw := integral_kernelMassSum_ge hX hXmeas h_mean hvar h3 hδpos
    have hES : (1 : ℝ) / 2 ≤ ∫ ω, kernelMassSum δ X ω ∂μ := by
      have hfrac : thirdMomentSum (X := X) μ / (4 * δ) = (1 : ℝ) / 4 := by
        change γ / (4 * γ) = 1 / 4
        have hne : γ ≠ 0 := hγpos.ne'
        field_simp [hne]
      have hrew : 1 - thirdMomentSum (X := X) μ / (4 * δ) = (3 : ℝ) / 4 := by
        rw [hfrac]; ring
      have h34 : (3 : ℝ) / 4 ≤ ∫ ω, kernelMassSum δ X ω ∂μ := by
        rwa [hrew] at hES_raw
      linarith
    have hVS := variance_kernelMassSum_le hX hXmeas h_indep h_mean hδ hvar
    have hlow := stein_exchange_ge_half_prob hX hXmeas h_indep h_mean hvar i hδ hab hES hVS
    have hup := abs_stein_exchange_le hX hXmeas h_indep h_mean hvar i hδ hab
    set LHS :=
      ∫ ω, leaveOneOut X i ω * concRamp a b δ (leaveOneOut X i ω) ∂μ -
        ∫ ω, X i ω * concRamp a b δ (leaveOneOut X i ω - X i ω) ∂μ
    have hlow' : (1 : ℝ) / 2 * p - δ ≤ LHS := hlow
    have hup' : |LHS| ≤ √2 * ((b - a) / 2 + δ) := hup
    have hL_le : LHS ≤ √2 * ((b - a) / 2 + δ) := (le_abs_self LHS).trans hup'
    have hhalf : (1 : ℝ) / 2 * p ≤ √2 * ((b - a) / 2 + δ) + δ := by linarith
    have hp_bound : p ≤ √2 * (b - a) + 2 * (√2 + 1) * δ := by
      have h1 : p ≤ 2 * (√2 * ((b - a) / 2 + δ) + δ) := by
        have := mul_le_mul_of_nonneg_left hhalf (by norm_num : (0 : ℝ) ≤ 2)
        linarith
      have h2 : 2 * (√2 * ((b - a) / 2 + δ) + δ) =
          √2 * (b - a) + 2 * (√2 + 1) * δ := by ring
      linarith
    simpa [δ, γ] using hp_bound

end ProbabilityTheory
