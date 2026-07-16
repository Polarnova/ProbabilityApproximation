/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.ChenShao.UniformBerryEsseen
import ProbabilityApproximation.ChenShao.TruncationComparison
import ProbabilityApproximation.ChenShao.TruncatedUniform
import ProbabilityApproximation.ChenShao.FourthMoment

/-!
# Analytic leaves for nonuniform Berry–Esseen

This module supplies the Stein-solution decay and the easy, large-moment, and large-truncation
branches reused by the one-sided-truncation proof.  The completed release theorem is assembled in
`NonuniformRelease.lean` and exported as `nonuniformBerryEsseen` (SPEC §4.3).

## Results

* **Lemma 5.1**: `E|f'_x(W)| ≤ 64/(1+x)²` (`x≥2`); `≤ 256/(1+x)²` (`x≥1`)
* `|E[W f_x]| ≤ 2/x`, Stein identity, Stein decay
* Easy / large-γ / large-δ → nonuniform form (`C = 10⁶`)
  via `abs_cdf_sub_le_nonuniform_of_easy_large_or_delta`
* `deltaTrunc` / α,β; R3 & R4 majorants; residual `30γ`

## Scope boundary

The complementary hard-small-error branch is discharged downstream by the Bennett--Hoeffding,
one-sided truncation, residual decomposition, and atom-safe reflection chain.  The present module
does not duplicate that assembly.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal

noncomputable section

namespace ProbabilityTheory

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ι → Ω → ℝ}

/-! ### Nonuniform truncated moment sum -/

def nonuniformTruncMomentSum (X : ι → Ω → ℝ) (μ : Measure Ω) (r : ℝ) : ℝ :=
  ∑ i : ι,
    ((∫ ω in {ω | r < |X i ω|}, (X i ω) ^ 2 ∂μ) / r ^ 2 +
      (∫ ω in {ω | |X i ω| ≤ r}, |X i ω| ^ 3 ∂μ) / r ^ 3)

lemma nonuniformTruncMomentSum_nonneg
    (hX : ∀ i, Measurable (X i)) {r : ℝ} (hr : 0 < r) :
    0 ≤ nonuniformTruncMomentSum (X := X) μ r := by
  refine Finset.sum_nonneg fun i _ => add_nonneg ?_ ?_
  · exact div_nonneg
      (setIntegral_nonneg (measurableSet_lt measurable_const (hX i).abs)
        fun _ _ => sq_nonneg _)
      (sq_nonneg r)
  · exact div_nonneg
      (setIntegral_nonneg (measurableSet_le (hX i).abs measurable_const)
        fun _ _ => pow_nonneg (abs_nonneg _) _)
      (pow_nonneg hr.le 3)

lemma nonuniformTruncMomentSum_le_thirdMomentSum_div
    (hX : ∀ i, Measurable (X i))
    (h3 : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ)
    (h2 : ∀ i, MemLp (X i) 2 μ)
    {r : ℝ} (hr : 0 < r) :
    nonuniformTruncMomentSum (X := X) μ r ≤ thirdMomentSum (X := X) μ / r ^ 3 := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hr3 : 0 < r ^ 3 := pow_pos hr 3
  have hterm (i : ι) :
      (∫ ω in {ω | r < |X i ω|}, (X i ω) ^ 2 ∂μ) / r ^ 2 +
          (∫ ω in {ω | |X i ω| ≤ r}, |X i ω| ^ 3 ∂μ) / r ^ 3 ≤
        (∫ ω, |X i ω| ^ 3 ∂μ) / r ^ 3 := by
    set s1 : Set Ω := {ω | r < |X i ω|}
    set s2 : Set Ω := {ω | |X i ω| ≤ r}
    have hs1 : MeasurableSet s1 := measurableSet_lt measurable_const (hX i).abs
    have hs2 : MeasurableSet s2 := measurableSet_le (hX i).abs measurable_const
    have hA : IntegrableOn (fun ω => (X i ω) ^ 2) s1 μ := (h2 i).integrable_sq.integrableOn
    have hB : IntegrableOn (fun ω => |X i ω| ^ 3) s1 μ := (h3 i).integrableOn
    have hC : IntegrableOn (fun ω => |X i ω| ^ 3) s2 μ := (h3 i).integrableOn
    have htail :
        (∫ ω in s1, (X i ω) ^ 2 ∂μ) / r ^ 2 ≤
          (∫ ω in s1, |X i ω| ^ 3 ∂μ) / r ^ 3 := by
      have hpt : ∫ ω in s1, (X i ω) ^ 2 ∂μ ≤ (1 / r) * ∫ ω in s1, |X i ω| ^ 3 ∂μ := by
        have hrhs : IntegrableOn (fun ω => |X i ω| ^ 3 / r) s1 μ := hB.div_const r
        refine (setIntegral_mono_on hA hrhs hs1 fun ω hω => ?_).trans_eq ?_
        · have hy := sq_div_sq_le_abs_cube_div_cube hr hω
          have hy' : (X i ω) ^ 2 * r ^ 3 ≤ |X i ω| ^ 3 * r ^ 2 :=
            (div_le_div_iff₀ hr2 hr3).mp hy
          have hmul : (X i ω) ^ 2 * r ≤ |X i ω| ^ 3 := by
            calc
              (X i ω) ^ 2 * r = ((X i ω) ^ 2 * r ^ 3) / r ^ 2 := by field_simp [hr.ne']
              _ ≤ (|X i ω| ^ 3 * r ^ 2) / r ^ 2 :=
                    div_le_div_of_nonneg_right hy' (sq_nonneg r)
              _ = |X i ω| ^ 3 := by field_simp [hr2.ne']
          have : (X i ω) ^ 2 ≤ |X i ω| ^ 3 / r := (le_div_iff₀ hr).mpr hmul
          simpa [div_eq_mul_inv, mul_comm] using this
        · rw [show (fun ω => |X i ω| ^ 3 / r) = fun ω => (1 / r) * |X i ω| ^ 3 by
            funext; ring, integral_const_mul]
      calc
        (∫ ω in s1, (X i ω) ^ 2 ∂μ) / r ^ 2 ≤
            ((1 / r) * ∫ ω in s1, |X i ω| ^ 3 ∂μ) / r ^ 2 :=
          div_le_div_of_nonneg_right hpt (sq_nonneg r)
        _ = (∫ ω in s1, |X i ω| ^ 3 ∂μ) / r ^ 3 := by field_simp [hr.ne']
    have hpart :
        ∫ ω in s1, |X i ω| ^ 3 ∂μ + ∫ ω in s2, |X i ω| ^ 3 ∂μ =
          ∫ ω, |X i ω| ^ 3 ∂μ := by
      have hU : s1 ∪ s2 = univ := by
        ext ω
        simp only [s1, s2, mem_union, mem_setOf_eq, mem_univ, iff_true]
        exact (lt_or_ge r |X i ω|).elim Or.inl Or.inr
      have hdisj : Disjoint s1 s2 := by
        refine disjoint_left.2 fun ω (h1 : ω ∈ s1) (h2 : ω ∈ s2) => ?_
        exact (not_le_of_gt (show r < |X i ω| from h1)) (show |X i ω| ≤ r from h2)
      have hsum := setIntegral_union hdisj hs2 hB hC
      rw [hU, setIntegral_univ] at hsum
      exact hsum.symm
    calc
      (∫ ω in s1, (X i ω) ^ 2 ∂μ) / r ^ 2 +
            (∫ ω in s2, |X i ω| ^ 3 ∂μ) / r ^ 3 ≤
          (∫ ω in s1, |X i ω| ^ 3 ∂μ) / r ^ 3 +
            (∫ ω in s2, |X i ω| ^ 3 ∂μ) / r ^ 3 :=
        add_le_add htail le_rfl
      _ = (∫ ω in s1, |X i ω| ^ 3 ∂μ + ∫ ω in s2, |X i ω| ^ 3 ∂μ) / r ^ 3 := by
            field_simp [hr3.ne']
      _ = (∫ ω, |X i ω| ^ 3 ∂μ) / r ^ 3 := by rw [hpart]
  calc
    nonuniformTruncMomentSum (X := X) μ r =
        ∑ i, ((∫ ω in {ω | r < |X i ω|}, (X i ω) ^ 2 ∂μ) / r ^ 2 +
          (∫ ω in {ω | |X i ω| ≤ r}, |X i ω| ^ 3 ∂μ) / r ^ 3) := rfl
    _ ≤ ∑ i, (∫ ω, |X i ω| ^ 3 ∂μ) / r ^ 3 :=
          Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) / r ^ 3 := by simp only [Finset.sum_div]
    _ = thirdMomentSum (X := X) μ / r ^ 3 := rfl

/-! ### Constants and large-δ branch -/

def nonuniformBerryEsseenConstant : ℝ := 1000000

lemma nonuniformBerryEsseenConstant_pos : 0 < nonuniformBerryEsseenConstant := by
  norm_num [nonuniformBerryEsseenConstant]

lemma abs_cdf_sub_le_of_large_nonuniform
    (hX : ∀ i, Measurable (X i)) (x : ℝ)
    (hlarge : (1 : ℝ) / nonuniformBerryEsseenConstant ≤
      nonuniformTruncMomentSum (X := X) μ (1 + |x|)) :
    |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤
      nonuniformBerryEsseenConstant *
        nonuniformTruncMomentSum (X := X) μ (1 + |x|) := by
  haveI : IsProbabilityMeasure (μ.map fun ω ↦ ∑ i, X i ω) :=
    isProbabilityMeasure_map_sumX (μ := μ) (X := X) fun i => (hX i).aemeasurable
  have h1 : |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤ 1 :=
    abs_cdf_sub_le_one _ _ x
  have hC : (0 : ℝ) ≤ nonuniformBerryEsseenConstant :=
    nonuniformBerryEsseenConstant_pos.le
  have hge : (1 : ℝ) ≤ nonuniformBerryEsseenConstant *
      nonuniformTruncMomentSum (X := X) μ (1 + |x|) := by
    have : nonuniformBerryEsseenConstant * (1 / nonuniformBerryEsseenConstant) = 1 := by
      field_simp [nonuniformBerryEsseenConstant]
    calc
      (1 : ℝ) = nonuniformBerryEsseenConstant * (1 / nonuniformBerryEsseenConstant) :=
        this.symm
      _ ≤ nonuniformBerryEsseenConstant *
            nonuniformTruncMomentSum (X := X) μ (1 + |x|) :=
          mul_le_mul_of_nonneg_left hlarge hC
  exact h1.trans hge

/-! ### Truncation operators -/

def truncAt (Y : Ω → ℝ) (r : ℝ) : Ω → ℝ :=
  fun ω => if |Y ω| ≤ r then Y ω else 0

lemma measurable_truncAt {Y : Ω → ℝ} (hY : Measurable Y) (r : ℝ) :
    Measurable (truncAt Y r) :=
  Measurable.ite (measurableSet_le hY.abs measurable_const) hY measurable_const

lemma abs_truncAt_le {Y : Ω → ℝ} {r : ℝ} (hr : 0 ≤ r) (ω : Ω) :
    |truncAt Y r ω| ≤ r := by
  unfold truncAt; split_ifs with h <;> simp [h, hr]

lemma integrable_truncAt {Y : Ω → ℝ} (hY : Measurable Y) {r : ℝ} (hr : 0 ≤ r) :
    Integrable (truncAt Y r) μ :=
  Integrable.of_bound (measurable_truncAt hY r).aestronglyMeasurable r
    (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using abs_truncAt_le hr ω)

lemma memLp_truncAt {Y : Ω → ℝ} (hY : Measurable Y) {r : ℝ} (hr : 0 ≤ r) :
    MemLp (truncAt Y r) 2 μ :=
  MemLp.of_bound (measurable_truncAt hY r).aestronglyMeasurable r
    (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using abs_truncAt_le hr ω)

def centeredTrunc (Y : Ω → ℝ) (r : ℝ) (μ : Measure Ω) : Ω → ℝ :=
  fun ω => truncAt Y r ω - ∫ ω', truncAt Y r ω' ∂μ

lemma measurable_centeredTrunc {Y : Ω → ℝ} (hY : Measurable Y) (r : ℝ) (μ : Measure Ω) :
    Measurable (centeredTrunc Y r μ) :=
  (measurable_truncAt hY r).sub measurable_const

lemma integral_centeredTrunc {Y : Ω → ℝ} (hY : Measurable Y) {r : ℝ} (hr : 0 ≤ r) :
    ∫ ω, centeredTrunc Y r μ ω ∂μ = 0 := by
  simp only [centeredTrunc]
  rw [integral_sub (integrable_truncAt (μ := μ) hY hr) (integrable_const _)]
  simp

lemma memLp_centeredTrunc {Y : Ω → ℝ} (hY : Measurable Y) {r : ℝ} (hr : 0 ≤ r) :
    MemLp (centeredTrunc Y r μ) 2 μ :=
  (memLp_truncAt (μ := μ) hY hr).sub (memLp_const _)

lemma abs_centeredTrunc_le {Y : Ω → ℝ} {r : ℝ} (hr : 0 ≤ r) (ω : Ω) :
    |centeredTrunc Y r μ ω| ≤ 2 * r := by
  simp only [centeredTrunc]
  have h1 := abs_truncAt_le (Y := Y) hr ω
  have h2 : |∫ ω', truncAt Y r ω' ∂μ| ≤ r := by
    refine (abs_integral_le_integral_abs (f := truncAt Y r) (μ := μ)).trans ?_
    refine (integral_mono_of_nonneg
      (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const r)
      (Eventually.of_forall fun ω' => abs_truncAt_le hr ω')).trans_eq (by simp)
  calc
    |truncAt Y r ω - ∫ ω', truncAt Y r ω' ∂μ| ≤
        |truncAt Y r ω| + |∫ ω', truncAt Y r ω' ∂μ| := abs_sub _ _
    _ ≤ r + r := add_le_add h1 h2
    _ = 2 * r := by ring

lemma integrable_abs_centeredTrunc_pow_three
    {Y : Ω → ℝ} (hY : Measurable Y) {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun ω => |centeredTrunc Y r μ ω| ^ 3) μ := by
  refine Integrable.of_bound
    ((measurable_centeredTrunc hY r μ).abs.pow_const 3).aestronglyMeasurable
    ((2 * r) ^ 3)
    (Eventually.of_forall fun ω => ?_)
  have hle := abs_centeredTrunc_le (μ := μ) (Y := Y) hr ω
  have hnn : 0 ≤ |centeredTrunc Y r μ ω| ^ 3 := pow_nonneg (abs_nonneg _) _
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact pow_le_pow_left₀ (abs_nonneg _) hle 3

/-! ### Partial third-moment nonuniform -/

lemma nonuniform_thirdMoment_of_bounded_x
    [DecidableEq ι]
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (x : ℝ) (hx : 1 + |x| ^ 3 ≤ 30) :
    |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤
      900 * thirdMomentSum (X := X) μ / (1 + |x| ^ 3) := by
  have hγ0 : 0 ≤ thirdMomentSum (X := X) μ := thirdMomentSum_nonneg h3
  have hden : 0 < 1 + |x| ^ 3 := by positivity
  have hBE := uniformBerryEsseen_thirdMoment hX hXmeas h_indep h_mean hvar h3 x
  have hrew :
      thirdMomentBerryEsseenConstant * thirdMomentSum (X := X) μ =
        30 * thirdMomentSum (X := X) μ := by
    simp [thirdMomentBerryEsseenConstant]
  rw [hrew] at hBE
  have hmul :
      30 * thirdMomentSum (X := X) μ ≤
        900 * thirdMomentSum (X := X) μ / (1 + |x| ^ 3) := by
    rw [le_div_iff₀ hden]
    nlinarith [hγ0, hx]
  exact hBE.trans hmul



/-! ### MemLp 3 helpers and sum moments -/

lemma memLp2_of_memLp3 {Y : Ω → ℝ} (hY : MemLp Y 3 μ) : MemLp Y 2 μ :=
  hY.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 3)

lemma integrable_abs_pow_three_of_memLp3 {Y : Ω → ℝ} (hY : MemLp Y 3 μ) :
    Integrable (fun ω => |Y ω| ^ 3) μ := by
  simpa [Real.norm_eq_abs] using hY.integrable_norm_pow (by decide : (3 : ℕ) ≠ 0)

lemma memLp2_of_memLp3_family (hX : ∀ i, MemLp (X i) 3 μ) :
    ∀ i, MemLp (X i) 2 μ := fun i => memLp2_of_memLp3 (hX i)

lemma integrable_abs_pow_three_family (hX : ∀ i, MemLp (X i) 3 μ) :
    ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ :=
  fun i => integrable_abs_pow_three_of_memLp3 (hX i)

variable [DecidableEq ι]

lemma integral_sumX_eq_zero
    (hX : ∀ k, MemLp (X k) 2 μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0) :
    ∫ ω, sumX X ω ∂μ = 0 := by
  simp only [sumX]
  rw [integral_finsetSum _ fun i _ => (hX i).integrable one_le_two]
  exact Finset.sum_eq_zero fun i _ => h_mean i

lemma integral_sq_sumX_eq_one
    (hX : ∀ k, MemLp (X k) 2 μ) (h_indep : iIndepFun X μ)
    (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0) (hvar : ∑ k, variance (X k) μ = 1) :
    ∫ ω, (sumX X ω) ^ 2 ∂μ = 1 := by
  -- Reuse coordinate form ∑ E X_i² = 1 and independence of centered summands:
  -- E W² = Var W = ∑ Var X_i = 1.
  have hcoord := sum_integral_sq_eq_one (X := X) (μ := μ) hX h_mean hvar
  have hmem : MemLp (sumX X) 2 μ := by
    change MemLp (fun ω => ∑ i, X i ω) 2 μ
    exact memLp_finsetSum (s := Finset.univ) (fun i _ => hX i)
  have h0 := integral_sumX_eq_zero hX h_mean
  -- Var(∑ X_i) = 1, and sumX is pointwise equal to the function sum
  have hfun : (∑ i : ι, X i) = sumX X := by
    funext ω; simp [sumX, Finset.sum_apply]
  have hvarW : variance (sumX X) μ = 1 := by
    rw [← hfun]
    exact variance_sumX_eq_one hX h_indep hvar
  have hveq : variance (sumX X) μ = ∫ ω, (sumX X ω) ^ 2 ∂μ :=
    variance_eq_integral_sq hmem h0
  linarith [hvarW, hveq]

/-- Large-γ nonuniform branch. -/
lemma abs_cdf_sub_le_of_large_thirdMoment_div
    (hX : ∀ i, Measurable (X i)) (x : ℝ) {γ C : ℝ}
    (hC : 0 < C) (_hγ : 0 ≤ γ)
    (hlarge : (1 + |x| ^ 3) / C ≤ γ) :
    |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤
      C * γ / (1 + |x| ^ 3) := by
  haveI : IsProbabilityMeasure (μ.map fun ω ↦ ∑ i, X i ω) :=
    isProbabilityMeasure_map_sumX (μ := μ) (X := X) fun i => (hX i).aemeasurable
  have habs : |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤ 1 :=
    abs_cdf_sub_le_one _ _ x
  have hden : 0 < 1 + |x| ^ 3 := by positivity
  have hge : (1 : ℝ) ≤ C * γ / (1 + |x| ^ 3) := by
    rw [le_div_iff₀ hden]
    calc
      (1 : ℝ) * (1 + |x| ^ 3) = 1 + |x| ^ 3 := one_mul _
      _ = C * ((1 + |x| ^ 3) / C) := by field_simp [hC.ne']
      _ ≤ C * γ := mul_le_mul_of_nonneg_left hlarge hC.le
  exact habs.trans hge

/-- Release constant. -/
def nonuniformThirdMomentBerryEsseenConstant : ℝ := 10000

lemma nonuniformThirdMomentBerryEsseenConstant_pos :
    0 < nonuniformThirdMomentBerryEsseenConstant := by
  norm_num [nonuniformThirdMomentBerryEsseenConstant]

/-- Nonuniform bound for nonnegative thresholds covering the easy zones and the
moderate-threshold zone where the uniform estimate scales. -/
lemma nonuniform_thirdMoment_nonneg_x_easy
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (x : ℝ) (hx : 0 ≤ x)
    (heasy : 1 + x ^ 3 ≤ nonuniformThirdMomentBerryEsseenConstant / 30) :
    |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤
      nonuniformThirdMomentBerryEsseenConstant *
        thirdMomentSum (X := X) μ / (1 + x ^ 3) := by
  set γ := thirdMomentSum (X := X) μ
  set C := nonuniformThirdMomentBerryEsseenConstant
  have hγ0 : 0 ≤ γ := thirdMomentSum_nonneg h3
  have hC0 : 0 < C := nonuniformThirdMomentBerryEsseenConstant_pos
  have hden : 0 < 1 + x ^ 3 := by positivity
  by_cases hlarge : (1 + x ^ 3) / C ≤ γ
  · have : (1 + |x| ^ 3) / C ≤ γ := by simpa [abs_of_nonneg hx] using hlarge
    simpa [γ, C, abs_of_nonneg hx] using
      abs_cdf_sub_le_of_large_thirdMoment_div hXmeas x hC0 hγ0 this
  · have hBE := uniformBerryEsseen_thirdMoment hX hXmeas h_indep h_mean hvar h3 x
    have hrew : thirdMomentBerryEsseenConstant * γ = 30 * γ := by
      simp [thirdMomentBerryEsseenConstant, γ]
    rw [hrew] at hBE
    have hmul : 30 * γ ≤ C * γ / (1 + x ^ 3) := by
      rw [le_div_iff₀ hden]
      have h30C : 30 * (1 + x ^ 3) ≤ C := by
        have h1 : 30 * (1 + x ^ 3) ≤ 30 * (C / 30) :=
          mul_le_mul_of_nonneg_left heasy (by norm_num)
        have h2 : 30 * (C / 30) = C := by field_simp [hC0.ne']
        rwa [h2] at h1
      nlinarith [hγ0, h30C]
    exact hBE.trans hmul

/-! ### Chebyshev for the normalized sum -/

lemma measureReal_abs_sumX_ge_le
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |sumX X ω|} ≤ 1 / t ^ 2 := by
  have hmem : MemLp (sumX X) 2 μ := by
    change MemLp (fun ω => ∑ i, X i ω) 2 μ
    exact memLp_finsetSum (s := Finset.univ) (fun i _ => hX i)
  have hsq := integral_sq_sumX_eq_one hX h_indep h_mean hvar
  have hmeas : MeasurableSet {ω | t ≤ |sumX X ω|} :=
    measurableSet_le measurable_const (measurable_sumX hXmeas).abs
  have hint : Integrable (fun ω => (sumX X ω) ^ 2) μ := hmem.integrable_sq
  have hpt : ∀ ω ∈ {ω | t ≤ |sumX X ω|}, t ^ 2 ≤ (sumX X ω) ^ 2 := by
    intro ω hω
    have : t ≤ |sumX X ω| := hω
    calc
      t ^ 2 ≤ |sumX X ω| ^ 2 := pow_le_pow_left₀ ht.le this 2
      _ = (sumX X ω) ^ 2 := sq_abs _
  have hIntc : IntegrableOn (fun _ : Ω => t ^ 2) {ω | t ≤ |sumX X ω|} μ :=
    (integrable_const _).integrableOn
  have hge := setIntegral_mono_on hIntc hint.integrableOn hmeas hpt
  have hleft : ∫ ω in {ω | t ≤ |sumX X ω|}, (t ^ 2 : ℝ) ∂μ =
      t ^ 2 * μ.real {ω | t ≤ |sumX X ω|} := by
    rw [integral_const]
    simp [Measure.real, smul_eq_mul, mul_comm]
  have hmono : ∫ ω in {ω | t ≤ |sumX X ω|}, (sumX X ω) ^ 2 ∂μ ≤
      ∫ ω, (sumX X ω) ^ 2 ∂μ :=
    setIntegral_le_integral hint (Eventually.of_forall fun _ => sq_nonneg _)
  have hle : t ^ 2 * μ.real {ω | t ≤ |sumX X ω|} ≤ 1 := by
    calc
      t ^ 2 * μ.real {ω | t ≤ |sumX X ω|} =
          ∫ ω in {ω | t ≤ |sumX X ω|}, (t ^ 2 : ℝ) ∂μ := hleft.symm
      _ ≤ ∫ ω in {ω | t ≤ |sumX X ω|}, (sumX X ω) ^ 2 ∂μ := hge
      _ ≤ ∫ ω, (sumX X ω) ^ 2 ∂μ := hmono
      _ = 1 := hsq
  exact (le_div_iff₀ (sq_pos_of_pos ht)).mpr (by rwa [mul_comm] at hle)


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

/-! ### Lemma 5.1 infrastructure -/

def lemma51Constant : ℝ := 64

lemma lemma51Constant_pos : 0 < lemma51Constant := by norm_num [lemma51Constant]

/-- Bound `|1 + w √(2π) e^{w²/2} Φ(w)| ≤ 2` for `w ≤ 0`. -/
lemma abs_one_add_left_mills_le_two {w : ℝ} (hw : w ≤ 0) :
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
      -- Φ(w) = 1-Φ(-w) ≤ pdf(-w)/(-w)
      have hΦle0 : Φw ≤ gaussianPDFReal 0 1 (-w) / (-w) := by
        have hrew : Φw = 1 - cdf (gaussianReal 0 1) (-w) := by
          -- hΦeq: Φ(-w) = 1 - Φ(w) ⇒ Φ(w) = 1 - Φ(-w)
          simp only [Φw]
          linarith [hΦeq]
        rw [hrew]; exact hMills
      have hΦle : Φw ≤ ((√(2 * π))⁻¹ * exp (-w ^ 2 / 2)) / (-w) := by
        -- gaussianPDFReal 0 1 (-w) = (√(2π))⁻¹ exp(-w²/2)
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
  -- hmul: a * |...| ≤ a * 2, goal: a * |...| ≤ 2 * a
  linarith

lemma steinSolutionDeriv_nonneg_of_nonneg_le
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

/-- Easy + large-γ zones for every real threshold. -/
lemma nonuniform_thirdMoment_easy_or_large
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (x : ℝ)
    (hh : 1 + |x| ^ 3 ≤ nonuniformThirdMomentBerryEsseenConstant / 30 ∨
      (1 + |x| ^ 3) / nonuniformThirdMomentBerryEsseenConstant ≤
        thirdMomentSum (X := X) μ) :
    |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤
      nonuniformThirdMomentBerryEsseenConstant *
        thirdMomentSum (X := X) μ / (1 + |x| ^ 3) := by
  set γ := thirdMomentSum (X := X) μ
  set C := nonuniformThirdMomentBerryEsseenConstant
  have hγ0 : 0 ≤ γ := thirdMomentSum_nonneg h3
  have hC0 : 0 < C := nonuniformThirdMomentBerryEsseenConstant_pos
  have hden : 0 < 1 + |x| ^ 3 := by positivity
  rcases hh with heasy | hlarge
  · have hBE := uniformBerryEsseen_thirdMoment hX hXmeas h_indep h_mean hvar h3 x
    have hrew : thirdMomentBerryEsseenConstant * γ = 30 * γ := by
      simp [thirdMomentBerryEsseenConstant, γ]
    rw [hrew] at hBE
    have hmul : 30 * γ ≤ C * γ / (1 + |x| ^ 3) := by
      rw [le_div_iff₀ hden]
      have h30C : 30 * (1 + |x| ^ 3) ≤ C := by
        have h1 : 30 * (1 + |x| ^ 3) ≤ 30 * (C / 30) :=
          mul_le_mul_of_nonneg_left heasy (by norm_num)
        have h2 : 30 * (C / 30) = C := by field_simp [hC0.ne']
        rwa [h2] at h1
      nlinarith [hγ0, h30C]
    exact hBE.trans hmul
  · simpa [γ, C] using
      abs_cdf_sub_le_of_large_thirdMoment_div hXmeas x hC0 hγ0 hlarge

/-! ### Lemma 5.1: `E|f'_x(W)| ≤ C/(1+x)²` -/

lemma integrable_abs_steinSolutionDeriv_sumX
    (hXmeas : ∀ k, Measurable (X k)) (x : ℝ) :
    Integrable (fun ω => |steinSolutionDeriv x (sumX X ω)|) μ :=
  Integrable.of_bound
    (((measurable_steinSolutionDeriv x).comp
      (measurable_sumX hXmeas)).abs).aestronglyMeasurable
    (2 : ℝ)
    (Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using
        abs_steinSolutionDeriv_le_two x (sumX X ω))

/-- `exp(-t) ≤ 1/t` for `t > 0`, via `exp t ≥ t+1 > t`. -/
lemma exp_neg_le_one_div {t : ℝ} (ht : 0 < t) : exp (-t) ≤ 1 / t := by
  have hge : t + 1 ≤ exp t := Real.add_one_le_exp t
  have ht1 : t < exp t := lt_of_lt_of_le (lt_add_of_pos_right t zero_lt_one) hge
  rw [Real.exp_neg, one_div]
  exact (inv_le_inv₀ (exp_pos t) ht).2 ht1.le

/-- Majorant value `g(x) ≤ 32/(1+x)²` for `x ≥ 2`. -/
lemma steinDeriv_region_majorant_le {x : ℝ} (hx : 2 ≤ x) :
    (1 - cdf (gaussianReal 0 1) x) *
        (1 + √(2 * π) * (x / 2) * exp (x ^ 2 / 8)) ≤
      32 / (1 + x) ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have h1m := one_sub_cdf_gaussian_le_pdf_div hx0
  have hφ : gaussianPDFReal 0 1 x =
      (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) := by
    simp [gaussianPDFReal, NNReal.coe_one]
  have h1m' : 1 - cdf (gaussianReal 0 1) x ≤
      ((√(2 * π))⁻¹ * exp (-x ^ 2 / 2)) / x := by rwa [hφ] at h1m
  have hne : (√(2 * π) : ℝ) ≠ 0 := sqrt_ne_zero'.2 (by positivity)
  have hsqrt2 : (2 : ℝ) ≤ √(2 * π) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith [Real.two_le_pi]
  have hinv : (√(2 * π))⁻¹ ≤ (1 : ℝ) / 2 :=
    ((inv_le_inv₀ (by positivity) (by norm_num)).2 hsqrt2).trans_eq (by norm_num)
  -- Expansion of mills product
  have he : exp (-x ^ 2 / 2) * exp (x ^ 2 / 8) =
      exp (-(3 : ℝ) * x ^ 2 / 8) := by
    rw [← exp_add]; congr 1; ring
  have hexpand :
      (((√(2 * π))⁻¹ * exp (-x ^ 2 / 2)) / x) *
          (1 + √(2 * π) * (x / 2) * exp (x ^ 2 / 8)) =
        ((√(2 * π))⁻¹ * exp (-x ^ 2 / 2)) / x +
          (1 / 2) * exp (-(3 : ℝ) * x ^ 2 / 8) := by
    have hst :
        ((√(2 * π))⁻¹ * exp (-x ^ 2 / 2) / x) *
            (√(2 * π) * (x / 2) * exp (x ^ 2 / 8)) =
          (1 / 2) * (exp (-x ^ 2 / 2) * exp (x ^ 2 / 8)) := by
      have hinv : (√(2 * π))⁻¹ * √(2 * π) = 1 := inv_mul_cancel₀ hne
      have hxx : (x / 2) / x = (1 : ℝ) / 2 := by field_simp [hx0.ne']
      calc
        ((√(2 * π))⁻¹ * exp (-x ^ 2 / 2) / x) *
              (√(2 * π) * (x / 2) * exp (x ^ 2 / 8)) =
            ((√(2 * π))⁻¹ * √(2 * π)) * (exp (-x ^ 2 / 2) * exp (x ^ 2 / 8)) *
              ((x / 2) / x) := by ring
        _ = 1 * (exp (-x ^ 2 / 2) * exp (x ^ 2 / 8)) * (1 / 2) := by
              rw [hinv, hxx]
        _ = (1 / 2) * (exp (-x ^ 2 / 2) * exp (x ^ 2 / 8)) := by ring
    calc
      (((√(2 * π))⁻¹ * exp (-x ^ 2 / 2)) / x) *
            (1 + √(2 * π) * (x / 2) * exp (x ^ 2 / 8)) =
          ((√(2 * π))⁻¹ * exp (-x ^ 2 / 2)) / x +
            ((√(2 * π))⁻¹ * exp (-x ^ 2 / 2) / x) *
              (√(2 * π) * (x / 2) * exp (x ^ 2 / 8)) := by ring
      _ = ((√(2 * π))⁻¹ * exp (-x ^ 2 / 2)) / x +
            (1 / 2) * (exp (-x ^ 2 / 2) * exp (x ^ 2 / 8)) := by rw [hst]
      _ = ((√(2 * π))⁻¹ * exp (-x ^ 2 / 2)) / x +
            (1 / 2) * exp (-(3 : ℝ) * x ^ 2 / 8) := by rw [he]
  -- Term 1 via exp(-t) ≤ 1/t with t = x²/2
  have ht1 : ((√(2 * π))⁻¹ * exp (-x ^ 2 / 2)) / x ≤ 16 / (1 + x) ^ 2 := by
    have hexp_le : exp (-x ^ 2 / 2) ≤ 2 / x ^ 2 := by
      have h := exp_neg_le_one_div (by positivity : (0 : ℝ) < x ^ 2 / 2)
      -- h: exp(-(x²/2)) ≤ 1/(x²/2)
      have hrew : (1 : ℝ) / (x ^ 2 / 2) = 2 / x ^ 2 := by field_simp
      calc
        exp (-x ^ 2 / 2) = exp (-(x ^ 2 / 2)) := by ring_nf
        _ ≤ 1 / (x ^ 2 / 2) := h
        _ = 2 / x ^ 2 := hrew
    have h1 : (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) ≤ (1 / 2 : ℝ) * (2 / x ^ 2) :=
      mul_le_mul hinv hexp_le (exp_nonneg _) (by norm_num)
    have h1' : (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) ≤ 1 / x ^ 2 := by
      have : (1 / 2 : ℝ) * (2 / x ^ 2) = 1 / x ^ 2 := by ring
      rwa [this] at h1
    have h3 : ((√(2 * π))⁻¹ * exp (-x ^ 2 / 2)) / x ≤ (1 / x ^ 2) / x :=
      div_le_div_of_nonneg_right h1' hx0.le
    have h4 : (1 : ℝ) / x ^ 2 / x = 1 / (x ^ 3) := by
      field_simp [pow_three]
    have h5 : (1 : ℝ) / x ^ 3 ≤ 16 / (1 + x) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg x, hx]
    calc
      ((√(2 * π))⁻¹ * exp (-x ^ 2 / 2)) / x ≤ (1 / x ^ 2) / x := h3
      _ = 1 / x ^ 3 := h4
      _ ≤ 16 / (1 + x) ^ 2 := h5
  -- Term 2 via exp(-u) ≤ 1/u with u = 3x²/8
  have ht2 : (1 / 2 : ℝ) * exp (-((3 : ℝ) * x ^ 2 / 8)) ≤ 16 / (1 + x) ^ 2 := by
    have hu : (0 : ℝ) < (3 : ℝ) * x ^ 2 / 8 := by positivity
    have hexp_u := exp_neg_le_one_div hu
    have h1 : (1 / 2 : ℝ) * exp (-((3 : ℝ) * x ^ 2 / 8)) ≤
        (1 / 2) * (1 / ((3 : ℝ) * x ^ 2 / 8)) :=
      mul_le_mul_of_nonneg_left hexp_u (by norm_num)
    have h2 : (1 / 2 : ℝ) * (1 / ((3 : ℝ) * x ^ 2 / 8)) = 4 / (3 * x ^ 2) := by
      field_simp
      ring
    have h3 : (4 : ℝ) / (3 * x ^ 2) ≤ 16 / (1 + x) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg x, hx]
    calc
      (1 / 2 : ℝ) * exp (-((3 : ℝ) * x ^ 2 / 8)) ≤
          (1 / 2) * (1 / ((3 : ℝ) * x ^ 2 / 8)) := h1
      _ = 4 / (3 * x ^ 2) := h2
      _ ≤ 16 / (1 + x) ^ 2 := h3
  have hprod :=
    mul_le_mul_of_nonneg_right h1m'
      (by positivity : 0 ≤ 1 + √(2 * π) * (x / 2) * exp (x ^ 2 / 8))
  calc
    (1 - cdf (gaussianReal 0 1) x) *
          (1 + √(2 * π) * (x / 2) * exp (x ^ 2 / 8)) ≤
        (((√(2 * π))⁻¹ * exp (-x ^ 2 / 2)) / x) *
          (1 + √(2 * π) * (x / 2) * exp (x ^ 2 / 8)) := hprod
    _ = ((√(2 * π))⁻¹ * exp (-x ^ 2 / 2)) / x +
          (1 / 2) * exp (-((3 : ℝ) * x ^ 2 / 8)) := by
            convert hexpand using 2
            ring_nf
    _ ≤ 16 / (1 + x) ^ 2 + 16 / (1 + x) ^ 2 := add_le_add ht1 ht2
    _ = 32 / (1 + x) ^ 2 := by ring

/-- Lemma 5.1: for `x ≥ 2` and unit-variance centered sum, `E|f'_x(W)| ≤ 64/(1+x)²`. -/
lemma integral_abs_steinSolutionDeriv_sumX_le
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    {x : ℝ} (hx : 2 ≤ x) :
    ∫ ω, |steinSolutionDeriv x (sumX X ω)| ∂μ ≤
      lemma51Constant / (1 + x) ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx2 : 0 < x / 2 := half_pos hx0
  have hint := integrable_abs_steinSolutionDeriv_sumX (μ := μ) hXmeas x
  set g : ℝ :=
    (1 - cdf (gaussianReal 0 1) x) *
      (1 + √(2 * π) * (x / 2) * exp (x ^ 2 / 8))
  have hg0 : 0 ≤ g := by
    dsimp [g]
    exact mul_nonneg (sub_nonneg.mpr (cdf_le_one _ _)) (by positivity)
  have hmaj : g ≤ 32 / (1 + x) ^ 2 := by
    dsimp [g]; exact steinDeriv_region_majorant_le hx
  set S : Set Ω := {ω | x / 2 < |sumX X ω|}
  have hmeasS : MeasurableSet S :=
    measurableSet_lt measurable_const (measurable_sumX hXmeas).abs
  -- Pointwise |f'| ≤ g + 2 * 1_S
  have hpt (ω : Ω) :
      |steinSolutionDeriv x (sumX X ω)| ≤
        g + 2 * S.indicator (fun _ => (1 : ℝ)) ω := by
    by_cases h : |sumX X ω| ≤ x / 2
    · have hmaj_pt := abs_steinSolutionDeriv_le_majorant_of_abs_le_half hx h
      have : S.indicator (fun _ => (1 : ℝ)) ω = 0 := by
        simp only [S, Set.indicator, Set.mem_setOf_eq]
        exact if_neg (not_lt.mpr h)
      rw [this, mul_zero, add_zero]
      simpa [g] using hmaj_pt
    · have h' : x / 2 < |sumX X ω| := lt_of_not_ge h
      have h2 := abs_steinSolutionDeriv_le_two x (sumX X ω)
      have : S.indicator (fun _ => (1 : ℝ)) ω = 1 := by
        simp only [S, Set.indicator, Set.mem_setOf_eq]
        exact if_pos h'
      rw [this, mul_one]
      linarith [hg0]
  have hInt_ind : Integrable (S.indicator fun _ => (1 : ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hmeasS
  have hInt_rhs :
      Integrable (fun ω => g + 2 * S.indicator (fun _ => (1 : ℝ)) ω) μ :=
    (integrable_const g).add (hInt_ind.const_mul 2)
  have hmono := integral_mono hint hInt_rhs hpt
  have hP : μ.real S ≤ 4 / x ^ 2 := by
    have hsub : S ⊆ {ω | x / 2 ≤ |sumX X ω|} := by
      intro ω hω
      exact le_of_lt (show x / 2 < |sumX X ω| from hω)
    have hch := measureReal_abs_sumX_ge_le hX hXmeas h_indep h_mean hvar hx2
    have hrew : 1 / (x / 2) ^ 2 = (4 : ℝ) / x ^ 2 := by field_simp [hx0.ne']; ring
    exact (measureReal_mono hsub).trans (by rwa [← hrew])
  have hrhs :
      ∫ ω, g + 2 * S.indicator (fun _ => (1 : ℝ)) ω ∂μ ≤ g + 8 / x ^ 2 := by
    have hadd := integral_add (integrable_const g) (hInt_ind.const_mul 2)
    rw [hadd]
    have hg_int : ∫ _ : Ω, g ∂μ = g := by
      rw [integral_const, smul_eq_mul, Measure.real, measure_univ, ENNReal.toReal_one,
        one_mul]
    have hind_eq : ∫ ω, S.indicator (fun _ => (1 : ℝ)) ω ∂μ = μ.real S := by
      rw [integral_indicator hmeasS, integral_const]
      simp [smul_eq_mul, Measure.real]
    rw [hg_int, integral_const_mul, hind_eq]
    have h2P : 2 * μ.real S ≤ 8 / x ^ 2 := by
      calc
        2 * μ.real S ≤ 2 * (4 / x ^ 2) := mul_le_mul_of_nonneg_left hP (by norm_num)
        _ = 8 / x ^ 2 := by ring
    linarith
  have h8 : (8 : ℝ) / x ^ 2 ≤ 32 / (1 + x) ^ 2 := by
    have hxpos : (0 : ℝ) < 1 + x := by linarith [hx0]
    rw [div_le_div_iff₀ (sq_pos_of_pos hx0) (sq_pos_of_pos hxpos)]
    -- 8(1+x)² ≤ 32 x² ⇔ (1+x)² ≤ 4 x²
    nlinarith [sq_nonneg (x - 1), hx]
  calc
    ∫ ω, |steinSolutionDeriv x (sumX X ω)| ∂μ ≤
        ∫ ω, g + 2 * S.indicator (fun _ => (1 : ℝ)) ω ∂μ := hmono
    _ ≤ g + 8 / x ^ 2 := hrhs
    _ ≤ 32 / (1 + x) ^ 2 + 32 / (1 + x) ^ 2 := add_le_add hmaj h8
    _ = 64 / (1 + x) ^ 2 := by ring
    _ = lemma51Constant / (1 + x) ^ 2 := by rw [lemma51Constant]


/-! ### Integrated Stein bound for large positive thresholds -/

/-- For `x ≥ 1`, `|E[W f_x(W)]| ≤ 2/x`. -/
lemma abs_integral_Wf_le_two_div
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    {x : ℝ} (hx : 1 ≤ x) :
    |∫ ω, sumX X ω * steinSolution x (sumX X ω) ∂μ| ≤ 2 / x := by
  have hmem : MemLp (sumX X) 2 μ := by
    change MemLp (fun ω => ∑ i, X i ω) 2 μ
    exact memLp_finsetSum (s := Finset.univ) (fun i _ => hX i)
  have hsq := integral_sq_sumX_eq_one hX h_indep h_mean hvar
  have hint := integrable_sumX_mul_steinSolution hX hXmeas x
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hle_pt (ω : Ω) :
      |sumX X ω * steinSolution x (sumX X ω)| ≤ (2 / x) * |sumX X ω| := by
    have hf := abs_steinSolution_le_two_div (x := x) (w := sumX X ω) hx
    rw [abs_mul]
    calc
      |sumX X ω| * |steinSolution x (sumX X ω)| ≤ |sumX X ω| * (2 / x) :=
        mul_le_mul_of_nonneg_left hf (abs_nonneg _)
      _ = (2 / x) * |sumX X ω| := mul_comm _ _
  have hmono :
      ∫ ω, |sumX X ω * steinSolution x (sumX X ω)| ∂μ ≤
        (2 / x) * ∫ ω, |sumX X ω| ∂μ := by
    have hInt_abs := hint.abs
    have hInt_maj : Integrable (fun ω => (2 / x) * |sumX X ω|) μ :=
      ((hmem.integrable one_le_two).abs).const_mul (2 / x)
    have h := integral_mono hInt_abs hInt_maj fun ω => hle_pt ω
    rwa [integral_const_mul] at h
  have hE : ∫ ω, |sumX X ω| ∂μ ≤ 1 := by
    have h := integral_abs_le_sqrt_integral_sq hmem
    calc
      ∫ ω, |sumX X ω| ∂μ ≤ √(∫ ω, (sumX X ω) ^ 2 ∂μ) := h
      _ = √(1 : ℝ) := by rw [hsq]
      _ = 1 := Real.sqrt_one
  calc
    |∫ ω, sumX X ω * steinSolution x (sumX X ω) ∂μ| ≤
        ∫ ω, |sumX X ω * steinSolution x (sumX X ω)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ (2 / x) * ∫ ω, |sumX X ω| ∂μ := hmono
    _ ≤ (2 / x) * 1 := mul_le_mul_of_nonneg_left hE (by positivity)
    _ = 2 / x := mul_one _

/-- Stein equation integrated form: `F(x) − Φ(x) = E[f'_x(W) − W f_x(W)]`. -/
lemma cdf_sub_eq_integral_steinSolutionDeriv_sub_Wf
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (x : ℝ) :
    cdf (μ.map (sumX X)) x - cdf (gaussianReal 0 1) x =
      ∫ ω, steinSolutionDeriv x (sumX X ω) ∂μ -
        ∫ ω, sumX X ω * steinSolution x (sumX X ω) ∂μ := by
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
      · filter_upwards with ω; split_ifs <;> simp
    have h2 : Integrable (fun _ : Ω => cdf (gaussianReal 0 1) x) μ :=
      integrable_const _
    have heq : ∫ ω, steinIntegrand x (sumX X ω) ∂μ =
        ∫ ω, (if sumX X ω ≤ x then (1 : ℝ) else 0) ∂μ -
          cdf (gaussianReal 0 1) x := by
      have hfun :
          (fun ω => steinIntegrand x (sumX X ω)) =
            fun ω => (if sumX X ω ≤ x then (1 : ℝ) else 0) -
              cdf (gaussianReal 0 1) x := by
        funext ω; rfl
      rw [hfun, integral_sub h1 h2, integral_const]
      simp [smul_eq_mul, measure_univ, ENNReal.toReal_one]
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
        funext ω; simp [Set.indicator]]
      rw [integral_indicator hset, integral_const, smul_eq_mul, mul_one]
      -- LHS = (μ.restrict s).real univ = μ.real s; RHS = (μ.map).real (Iic)
      simp only [Measure.real, Measure.restrict_apply_univ, hmap_apply]
    -- hmap: cdf = map.real Iic; heq: ∫ steinIntegrand = ∫ 1_{≤x} - Φ; hind: ∫ 1 = map.real
    linarith [hmap, heq, hind]
  rw [hFeq, hident]

/-- For `x ≥ 2`: `|F−Φ| ≤ 64/(1+x)² + 2/x` via Lemma 5.1 and `|f|≤2/x`. -/
lemma abs_cdf_sub_le_of_stein_decay
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    {x : ℝ} (hx : 2 ≤ x) :
    |cdf (μ.map (sumX X)) x - cdf (gaussianReal 0 1) x| ≤
      lemma51Constant / (1 + x) ^ 2 + 2 / x := by
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx
  have hWf := abs_integral_Wf_le_two_div hX hXmeas h_indep h_mean hvar hx1
  have hf' := integral_abs_steinSolutionDeriv_sumX_le hX hXmeas h_indep h_mean hvar hx
  have heq := cdf_sub_eq_integral_steinSolutionDeriv_sub_Wf hX hXmeas x
  rw [heq]
  calc
    |∫ ω, steinSolutionDeriv x (sumX X ω) ∂μ -
          ∫ ω, sumX X ω * steinSolution x (sumX X ω) ∂μ| ≤
        |∫ ω, steinSolutionDeriv x (sumX X ω) ∂μ| +
          |∫ ω, sumX X ω * steinSolution x (sumX X ω) ∂μ| :=
      abs_sub _ _
    _ ≤ ∫ ω, |steinSolutionDeriv x (sumX X ω)| ∂μ +
          |∫ ω, sumX X ω * steinSolution x (sumX X ω) ∂μ| := by
            gcongr; exact abs_integral_le_integral_abs
    _ ≤ lemma51Constant / (1 + x) ^ 2 + 2 / x := add_le_add hf' hWf

/-! ### Lemma 5.1 for `x ≥ 1` (reduce to `x ≥ 2` or bound by 2) -/

/-- Lemma 5.1 for `x ≥ 1`: `E|f'_x(W)| ≤ 256/(1+x)²`. -/
lemma integral_abs_steinSolutionDeriv_sumX_le_of_one_le
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    {x : ℝ} (hx : 1 ≤ x) :
    ∫ ω, |steinSolutionDeriv x (sumX X ω)| ∂μ ≤ 256 / (1 + x) ^ 2 := by
  by_cases hx2 : 2 ≤ x
  · have h := integral_abs_steinSolutionDeriv_sumX_le hX hXmeas h_indep h_mean hvar hx2
    have hle : lemma51Constant / (1 + x) ^ 2 ≤ 256 / (1 + x) ^ 2 := by
      have hden : 0 < (1 + x) ^ 2 := by positivity
      exact div_le_div_of_nonneg_right (by norm_num [lemma51Constant]) hden.le
    exact h.trans hle
  · push_neg at hx2
    -- On [1, 2): |f'| ≤ 2 and 2 ≤ 256/(1+x)² since (1+x)² ≤ 9 < 128
    have hint := integrable_abs_steinSolutionDeriv_sumX (μ := μ) hXmeas x
    have hbound : ∫ ω, |steinSolutionDeriv x (sumX X ω)| ∂μ ≤ 2 := by
      have hpt : ∀ ω, |steinSolutionDeriv x (sumX X ω)| ≤ 2 := fun ω =>
        abs_steinSolutionDeriv_le_two x (sumX X ω)
      have hInt2 : Integrable (fun _ : Ω => (2 : ℝ)) μ := integrable_const 2
      exact (integral_mono hint hInt2 hpt).trans_eq (by simp)
    have hden : 0 < (1 + x) ^ 2 := by positivity
    have hxlt : x < 2 := hx2
    have h1x : 1 + x < 3 := by linarith
    have hsq : (1 + x) ^ 2 < 9 := by
      nlinarith [sq_nonneg (1 + x), hx]
    have h256 : (2 : ℝ) ≤ 256 / (1 + x) ^ 2 := by
      rw [le_div_iff₀ hden]
      -- 2 (1+x)² ≤ 256 ⇔ (1+x)² ≤ 128
      nlinarith [hsq]
    exact hbound.trans h256

/-! ### Large-δ branch via third-moment tails -/

/-- Truncated-moment δ at level `r > 0`: `α/r² + β/r³ ≤ γ/r³` form already in
`nonuniformTruncMomentSum_le_thirdMomentSum_div`. -/
lemma nonuniform_delta_le_third_div
    (hX : ∀ i, Measurable (X i))
    (h3 : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ)
    (h2 : ∀ i, MemLp (X i) 2 μ)
    {r : ℝ} (hr : 0 < r) :
    nonuniformTruncMomentSum (X := X) μ r ≤ thirdMomentSum (X := X) μ / r ^ 3 :=
  nonuniformTruncMomentSum_le_thirdMomentSum_div hX h3 h2 hr

/-- Large truncated-moment branch: if `δ_r ≥ 1/C` then `|F−Φ| ≤ C δ_r`. -/
lemma abs_cdf_sub_le_of_large_delta
    (hX : ∀ i, Measurable (X i)) (x : ℝ) {r C : ℝ}
    (hC : 0 < C) (_hr : 0 < r)
    (hlarge : (1 : ℝ) / C ≤ nonuniformTruncMomentSum (X := X) μ r) :
    |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤
      C * nonuniformTruncMomentSum (X := X) μ r := by
  haveI : IsProbabilityMeasure (μ.map fun ω ↦ ∑ i, X i ω) :=
    isProbabilityMeasure_map_sumX (μ := μ) (X := X) fun i => (hX i).aemeasurable
  have h1 : |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤ 1 :=
    abs_cdf_sub_le_one _ _ x
  have hge : (1 : ℝ) ≤ C * nonuniformTruncMomentSum (X := X) μ r := by
    have : C * (1 / C) = 1 := by field_simp [hC.ne']
    calc
      (1 : ℝ) = C * (1 / C) := this.symm
      _ ≤ C * nonuniformTruncMomentSum (X := X) μ r :=
        mul_le_mul_of_nonneg_left hlarge hC.le
  exact h1.trans hge

/-- Large-δ ⇒ nonuniform third-moment bound (via δ ≤ γ/r³ and r = 1+|x|). -/
lemma abs_cdf_sub_le_of_large_delta_third
    (hX : ∀ i, Measurable (X i))
    (h3 : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ)
    (h2 : ∀ i, MemLp (X i) 2 μ)
    (x : ℝ) {C : ℝ} (hC : 0 < C)
    (hlarge : (1 : ℝ) / C ≤
      nonuniformTruncMomentSum (X := X) μ (1 + |x|)) :
    |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤
      C * thirdMomentSum (X := X) μ / (1 + |x|) ^ 3 := by
  have hr : (0 : ℝ) < 1 + |x| := by positivity
  have hδ := abs_cdf_sub_le_of_large_delta hX x hC hr hlarge
  have hle := nonuniform_delta_le_third_div hX h3 h2 hr
  have hγ0 : 0 ≤ thirdMomentSum (X := X) μ := thirdMomentSum_nonneg h3
  have hC0 : 0 ≤ C := hC.le
  have hδ0 : 0 ≤ nonuniformTruncMomentSum (X := X) μ (1 + |x|) :=
    nonuniformTruncMomentSum_nonneg hX hr
  calc
    |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤
        C * nonuniformTruncMomentSum (X := X) μ (1 + |x|) := hδ
    _ ≤ C * (thirdMomentSum (X := X) μ / (1 + |x|) ^ 3) := by gcongr
    _ = C * thirdMomentSum (X := X) μ / (1 + |x|) ^ 3 := by ring

/-- Convert `(1+|x|)³` denominator to `1+|x|³`. -/
lemma abs_cdf_sub_le_third_div_one_add_abs
    (x : ℝ) {C γ : ℝ} (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (h : |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤
      C * γ / (1 + |x|) ^ 3) :
    |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤
      C * γ / (1 + |x| ^ 3) :=
  h.trans (div_one_add_abs_pow_three_le x C γ hC hγ)


/-! ### δ-notation and Lemma 5.1 absolute form -/

def alphaTrunc (X : ι → Ω → ℝ) (μ : Measure Ω) (y : ℝ) : ℝ :=
  ∑ i, ∫ ω in {ω | 1 + y < |X i ω|}, (X i ω) ^ 2 ∂μ

def betaTrunc (X : ι → Ω → ℝ) (μ : Measure Ω) (y : ℝ) : ℝ :=
  ∑ i, ∫ ω in {ω | |X i ω| ≤ 1 + y}, |X i ω| ^ 3 ∂μ

def deltaTrunc (X : ι → Ω → ℝ) (μ : Measure Ω) (y : ℝ) : ℝ :=
  alphaTrunc (X := X) μ y / (1 + y) ^ 2 + betaTrunc (X := X) μ y / (1 + y) ^ 3

lemma deltaTrunc_eq_nonuniform (y : ℝ) :
    deltaTrunc (X := X) μ y = nonuniformTruncMomentSum (X := X) μ (1 + y) := by
  set r := 1 + y
  simp only [deltaTrunc, alphaTrunc, betaTrunc, nonuniformTruncMomentSum, r]
  -- (∑ a_i)/r² + (∑ b_i)/r³ = ∑ (a_i/r² + b_i/r³)
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]

lemma deltaTrunc_le_third_div
    (hX : ∀ i, Measurable (X i))
    (h3 : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ)
    (h2 : ∀ i, MemLp (X i) 2 μ)
    {y : ℝ} (hy : 0 ≤ y) :
    deltaTrunc (X := X) μ y ≤ thirdMomentSum (X := X) μ / (1 + y) ^ 3 := by
  rw [deltaTrunc_eq_nonuniform]
  exact nonuniformTruncMomentSum_le_thirdMomentSum_div hX h3 h2 (by positivity)

lemma deltaTrunc_nonneg (hX : ∀ i, Measurable (X i)) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ deltaTrunc (X := X) μ y := by
  rw [deltaTrunc_eq_nonuniform]
  exact nonuniformTruncMomentSum_nonneg hX (by positivity)

lemma abs_integral_steinSolutionDeriv_le
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    {x : ℝ} (hx : 1 ≤ x) :
    |∫ ω, steinSolutionDeriv x (sumX X ω) ∂μ| ≤ 256 / (1 + x) ^ 2 :=
  (abs_integral_le_integral_abs).trans
    (integral_abs_steinSolutionDeriv_sumX_le_of_one_le hX hXmeas h_indep h_mean hvar hx)

/-- Tail first moments: `∑ E[|X| 1_{|X|>r}] ≤ γ/r²`. -/
lemma sum_setIntegral_abs_tail_le
    (hXmeas : ∀ i, Measurable (X i))
    (h3 : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ)
    {r : ℝ} (hr : 0 < r) :
    ∑ i, ∫ ω in {ω | r < |X i ω|}, |X i ω| ∂μ ≤
      thirdMomentSum (X := X) μ / r ^ 2 := by
  have hterm (i : ι) :
      ∫ ω in {ω | r < |X i ω|}, |X i ω| ∂μ ≤
        (∫ ω, |X i ω| ^ 3 ∂μ) / r ^ 2 := by
    set s : Set Ω := {ω | r < |X i ω|}
    have hs : MeasurableSet s := measurableSet_lt measurable_const (hXmeas i).abs
    have hAbs : Integrable (fun ω => |X i ω|) μ := by
      have hmaj : Integrable (fun ω => (1 : ℝ) + |X i ω| ^ 3) μ :=
        (integrable_const 1).add (h3 i)
      refine hmaj.mono' (hXmeas i).abs.aestronglyMeasurable ?_
      filter_upwards with ω
      simp only [Real.norm_eq_abs, abs_abs]
      nlinarith [sq_nonneg (|X i ω| - 1), abs_nonneg (X i ω)]
    have hA : IntegrableOn (fun ω => |X i ω|) s μ := hAbs.integrableOn
    have hB : IntegrableOn (fun ω => |X i ω| ^ 3 / r ^ 2) s μ :=
      ((h3 i).div_const (r ^ 2)).integrableOn
    have hpt : ∀ ω ∈ s, |X i ω| ≤ |X i ω| ^ 3 / r ^ 2 := by
      intro ω hω
      have hrX : r < |X i ω| := hω
      have : |X i ω| * r ^ 2 ≤ |X i ω| ^ 3 := by
        have hpow : r ^ 2 ≤ |X i ω| ^ 2 :=
          pow_le_pow_left₀ hr.le hrX.le 2
        calc
          |X i ω| * r ^ 2 ≤ |X i ω| * |X i ω| ^ 2 := by gcongr
          _ = |X i ω| ^ 3 := by ring
      exact (le_div_iff₀ (sq_pos_of_pos hr)).mpr this
    have hmono := setIntegral_mono_on hA hB hs hpt
    have hrhs : ∫ ω in s, |X i ω| ^ 3 / r ^ 2 ∂μ =
        (∫ ω in s, |X i ω| ^ 3 ∂μ) / r ^ 2 := by
      have heq : (fun ω => |X i ω| ^ 3 / r ^ 2) =
          fun ω => (r ^ 2)⁻¹ * |X i ω| ^ 3 := by
        ext ω; ring
      rw [heq, integral_const_mul, div_eq_inv_mul]
    have hsub : ∫ ω in s, |X i ω| ^ 3 ∂μ ≤ ∫ ω, |X i ω| ^ 3 ∂μ :=
      setIntegral_le_integral (h3 i)
        (Eventually.of_forall fun _ => pow_nonneg (abs_nonneg _) _)
    calc
      ∫ ω in s, |X i ω| ∂μ ≤ ∫ ω in s, |X i ω| ^ 3 / r ^ 2 ∂μ := hmono
      _ = (∫ ω in s, |X i ω| ^ 3 ∂μ) / r ^ 2 := hrhs
      _ ≤ (∫ ω, |X i ω| ^ 3 ∂μ) / r ^ 2 :=
            div_le_div_of_nonneg_right hsub (sq_nonneg r)
  calc
    ∑ i, ∫ ω in {ω | r < |X i ω|}, |X i ω| ∂μ ≤
        ∑ i, (∫ ω, |X i ω| ^ 3 ∂μ) / r ^ 2 :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) / r ^ 2 := by simp [Finset.sum_div]
    _ = thirdMomentSum (X := X) μ / r ^ 2 := rfl

/-- Pointwise R4 kernel: `|ξ(f(w+ξ)-f(w))| ≤ (4/x)|ξ|` for `x ≥ 1`. -/
lemma abs_X_mul_stein_sub_le_four_div {x ξ w : ℝ} (hx : 1 ≤ x) :
    |ξ * (steinSolution x (w + ξ) - steinSolution x w)| ≤ (4 / x) * |ξ| := by
  have h1 := abs_steinSolution_le_two_div (x := x) (w := w + ξ) hx
  have h2 := abs_steinSolution_le_two_div (x := x) (w := w) hx
  have hsub : |steinSolution x (w + ξ) - steinSolution x w| ≤ 4 / x := by
    calc
      |_ - _| ≤ |steinSolution x (w + ξ)| + |steinSolution x w| := abs_sub _ _
      _ ≤ 2 / x + 2 / x := add_le_add h1 h2
      _ = 4 / x := by ring
  calc
    |ξ * (steinSolution x (w + ξ) - steinSolution x w)| =
        |ξ| * |steinSolution x (w + ξ) - steinSolution x w| := abs_mul _ _
    _ ≤ |ξ| * (4 / x) := mul_le_mul_of_nonneg_left hsub (abs_nonneg _)
    _ = (4 / x) * |ξ| := mul_comm _ _

/-- R3-style: `|α E[f'_x(W)]| ≤ |α| · 256/(1+x)²`. -/
lemma abs_alpha_mul_Efderiv_le
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    {x α : ℝ} (hx : 1 ≤ x) :
    |α * ∫ ω, steinSolutionDeriv x (sumX X ω) ∂μ| ≤ |α| * 256 / (1 + x) ^ 2 := by
  have h := abs_integral_steinSolutionDeriv_le hX hXmeas h_indep h_mean hvar hx
  calc
    |α * ∫ ω, steinSolutionDeriv x (sumX X ω) ∂μ| =
        |α| * |∫ ω, steinSolutionDeriv x (sumX X ω) ∂μ| := abs_mul _ _
    _ ≤ |α| * (256 / (1 + x) ^ 2) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = |α| * 256 / (1 + x) ^ 2 := by ring

/-- Combined residual (uniform): `|F−Φ| ≤ 30γ`. -/
lemma abs_cdf_sub_le_thirty_gamma
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (x : ℝ) :
    |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤
      30 * thirdMomentSum (X := X) μ := by
  have h := uniformBerryEsseen_thirdMoment hX hXmeas h_indep h_mean hvar h3 x
  have hrew : thirdMomentBerryEsseenConstant * thirdMomentSum (X := X) μ =
      30 * thirdMomentSum (X := X) μ := by
    simp [thirdMomentBerryEsseenConstant]
  rwa [hrew] at h

/-- Easy, large-`γ`, or large-truncation-error cases with constant `C = 10^6` for all `x`.
The complementary hard-small-error region is supplied by the downstream one-sided-truncation
residual chain. -/
lemma abs_cdf_sub_le_nonuniform_of_easy_large_or_delta
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (x : ℝ)
    (hcase : 1 + |x| ^ 3 ≤ nonuniformBerryEsseenConstant / 30 ∨
      (1 + |x| ^ 3) / nonuniformBerryEsseenConstant ≤ thirdMomentSum (X := X) μ ∨
      (1 : ℝ) / nonuniformBerryEsseenConstant ≤
        nonuniformTruncMomentSum (X := X) μ (1 + |x|)) :
    |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤
      nonuniformBerryEsseenConstant *
        thirdMomentSum (X := X) μ / (1 + |x| ^ 3) := by
  set γ := thirdMomentSum (X := X) μ
  set C := nonuniformBerryEsseenConstant
  have hγ0 : 0 ≤ γ := thirdMomentSum_nonneg h3
  have hC0 : 0 < C := nonuniformBerryEsseenConstant_pos
  have hden : 0 < 1 + |x| ^ 3 := by positivity
  rcases hcase with heasy | hrest
  · have hBE := abs_cdf_sub_le_thirty_gamma hX hXmeas h_indep h_mean hvar h3 x
    have hmul : 30 * γ ≤ C * γ / (1 + |x| ^ 3) := by
      rw [le_div_iff₀ hden]
      have h30C : 30 * (1 + |x| ^ 3) ≤ C := by
        have h1 : 30 * (1 + |x| ^ 3) ≤ 30 * (C / 30) :=
          mul_le_mul_of_nonneg_left heasy (by norm_num)
        have h2 : 30 * (C / 30) = C := by field_simp [hC0.ne']
        rwa [h2] at h1
      nlinarith [hγ0, h30C]
    exact hBE.trans hmul
  · rcases hrest with hlarge | hδ
    · simpa [γ, C] using
        abs_cdf_sub_le_of_large_thirdMoment_div hXmeas x hC0 hγ0 hlarge
    · have h := abs_cdf_sub_le_of_large_delta_third (X := X) (μ := μ)
        hXmeas h3 hX x hC0 hδ
      exact abs_cdf_sub_le_third_div_one_add_abs (μ := μ) (X := X) x hC0.le hγ0 h


/-!
## Prop 3.4 leaves + flagship theorem
-/

open Filter

/-- `E Y² ≤ E X²` for centered truncations. -/
lemma integral_sq_centeredTrunc_le_integral_sq
    {Y : Ω → ℝ} (hYmeas : Measurable Y) (hY2 : MemLp Y 2 μ) {r : ℝ} (hr : 0 ≤ r) :
    ∫ ω, (centeredTrunc Y r μ ω) ^ 2 ∂μ ≤ ∫ ω, (Y ω) ^ 2 ∂μ := by
  set t := truncAt Y r
  have hmem : MemLp t 2 μ := memLp_truncAt (μ := μ) hYmeas hr
  have h0t : ∫ ω, centeredTrunc Y r μ ω ∂μ = 0 :=
    integral_centeredTrunc (μ := μ) hYmeas hr
  have hmemc : MemLp (centeredTrunc Y r μ) 2 μ := memLp_centeredTrunc (μ := μ) hYmeas hr
  have hveq : variance (centeredTrunc Y r μ) μ =
      ∫ ω, (centeredTrunc Y r μ ω) ^ 2 ∂μ :=
    variance_eq_integral_sq hmemc h0t
  have hshift : variance (centeredTrunc Y r μ) μ = variance t μ := by
    have hEq : centeredTrunc Y r μ = fun ω => t ω + (-∫ ω', t ω' ∂μ) := by
      funext ω; simp only [centeredTrunc, t, sub_eq_add_neg]
    rw [hEq]
    exact variance_add_const (μ := μ) hmem.aestronglyMeasurable _
  have hvar_le : variance t μ ≤ ∫ ω, (t ω) ^ 2 ∂μ := by
    rw [variance_eq_sub hmem]
    exact sub_le_self _ (sq_nonneg _)
  have ht_le : ∫ ω, (t ω) ^ 2 ∂μ ≤ ∫ ω, (Y ω) ^ 2 ∂μ := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
      hY2.integrable_sq (Eventually.of_forall fun ω => ?_)
    dsimp [t, truncAt]
    split_ifs
    · exact le_rfl
    · simpa using sq_nonneg (Y ω)
  calc
    ∫ ω, (centeredTrunc Y r μ ω) ^ 2 ∂μ = variance (centeredTrunc Y r μ) μ := hveq.symm
    _ = variance t μ := hshift
    _ ≤ ∫ ω, (t ω) ^ 2 ∂μ := hvar_le
    _ ≤ ∫ ω, (Y ω) ^ 2 ∂μ := ht_le

/-- Case A core: `E(∑ centeredTrunc)⁴ ≤ 3 + 4 r²`. -/
lemma integral_sum_centeredTrunc_pow_four_le_three_add
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    {r : ℝ} (hr : 0 ≤ r) :
    ∫ ω, (∑ i : ι, centeredTrunc (X i) r μ ω) ^ 4 ∂μ ≤ 3 + 4 * r ^ 2 := by
  let Y : ι → Ω → ℝ := fun i => centeredTrunc (X i) r μ
  have hYmeas : ∀ i, Measurable (Y i) := fun i =>
    measurable_centeredTrunc (hXmeas i) r μ
  have hY0 : ∀ i, ∫ ω, Y i ω ∂μ = 0 := fun i =>
    integral_centeredTrunc (μ := μ) (hXmeas i) hr
  have hYind : iIndepFun Y μ := by
    let g : ι → ℝ → ℝ := fun i y =>
      (if |y| ≤ r then y else 0) - ∫ ω', truncAt (X i) r ω' ∂μ
    have hg : ∀ i, Measurable (g i) := fun i =>
      (Measurable.ite (measurableSet_le measurable_id.abs measurable_const)
        measurable_id measurable_const).sub measurable_const
    convert (h_indep.comp (g := g) hg) using 1
    funext i ω; rfl
  have hros :=
    integral_finsetSum_pow_four_le (μ := μ) (X := Y) hYmeas hYind hY0
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr)
      (fun i ω => abs_centeredTrunc_le (μ := μ) (Y := X i) hr ω) Finset.univ
  have hsum2 : ∑ i, ∫ ω, (Y i ω) ^ 2 ∂μ ≤ 1 := by
    have hle (i : ι) :
        ∫ ω, (Y i ω) ^ 2 ∂μ ≤ ∫ ω, (X i ω) ^ 2 ∂μ :=
      integral_sq_centeredTrunc_le_integral_sq (hXmeas i) (hX i) hr
    have hsum :
        (∑ i, ∫ ω, (Y i ω) ^ 2 ∂μ) ≤ ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ :=
      Finset.sum_le_sum fun i _ => hle i
    have hXsq : ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ = 1 :=
      sum_integral_sq_eq_one (X := X) (μ := μ) hX h_mean hvar
    linarith
  have hsum4 : ∑ i, ∫ ω, (Y i ω) ^ 4 ∂μ ≤ 4 * r ^ 2 := by
    have hterm (i : ι) :
        ∫ ω, (Y i ω) ^ 4 ∂μ ≤ 4 * r ^ 2 * ∫ ω, (Y i ω) ^ 2 ∂μ := by
      have hbd : ∀ ω, |Y i ω| ≤ 2 * r := fun ω =>
        abs_centeredTrunc_le (μ := μ) (Y := X i) hr ω
      have h4 := integrable_pow_four_of_bound (μ := μ) (hYmeas i)
        (mul_nonneg (by norm_num) hr) hbd
      have h2 : Integrable (fun ω => (Y i ω) ^ 2) μ := by
        refine Integrable.of_bound ((hYmeas i).pow_const 2).aestronglyMeasurable
          ((2 * r) ^ 2) ?_
        filter_upwards with ω
        have hnn : 0 ≤ (Y i ω) ^ 2 := sq_nonneg _
        rw [Real.norm_eq_abs, abs_of_nonneg hnn, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbd ω) 2
      have hpt : ∀ ω, (Y i ω) ^ 4 ≤ 4 * r ^ 2 * (Y i ω) ^ 2 := fun ω => by
        have hsqle : (Y i ω) ^ 2 ≤ 4 * r ^ 2 := by
          have h := pow_le_pow_left₀ (abs_nonneg _) (hbd ω) 2
          rwa [sq_abs, show (2 * r) ^ 2 = 4 * r ^ 2 by ring] at h
        nlinarith [sq_nonneg (Y i ω)]
      have hmono := integral_mono h4 (h2.const_mul (4 * r ^ 2)) hpt
      rwa [integral_const_mul] at hmono
    calc
      ∑ i, ∫ ω, (Y i ω) ^ 4 ∂μ ≤
          ∑ i, 4 * r ^ 2 * ∫ ω, (Y i ω) ^ 2 ∂μ :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = 4 * r ^ 2 * ∑ i, ∫ ω, (Y i ω) ^ 2 ∂μ := by
            simp only [Finset.mul_sum]
      _ ≤ 4 * r ^ 2 * 1 := by gcongr
      _ = 4 * r ^ 2 := by ring
  have h3sq : 3 * (∑ i, ∫ ω, (Y i ω) ^ 2 ∂μ) ^ 2 ≤ 3 := by
    have hnn : 0 ≤ ∑ i, ∫ ω, (Y i ω) ^ 2 ∂μ :=
      Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
    nlinarith [hsum2]
  have hros' :
      ∫ ω, (∑ i : ι, Y i ω) ^ 4 ∂μ ≤
        3 * (∑ i, ∫ ω, (Y i ω) ^ 2 ∂μ) ^ 2 +
          ∑ i, ∫ ω, (Y i ω) ^ 4 ∂μ := by
    convert hros using 1 <;> simp only [Y, Finset.sum_apply]
  linarith [hros', h3sq, hsum4]

/-- Prop 3.4 Case A: Markov fourth-moment bound. -/
lemma measureReal_abs_sum_centeredTrunc_ge_le
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) :
    μ.real {ω | t ≤ |∑ i, centeredTrunc (X i) r μ ω|} ≤
      (3 + 4 * r ^ 2) / t ^ 4 := by
  set Z : Ω → ℝ := fun ω => ∑ i, centeredTrunc (X i) r μ ω
  have hZmeas : Measurable Z :=
    Finset.measurable_fun_sum _ fun i _ => measurable_centeredTrunc (hXmeas i) r μ
  have hET4 :=
    integral_sum_centeredTrunc_pow_four_le_three_add hX hXmeas h_indep h_mean hvar hr
  have hbd : ∀ ω, |Z ω| ≤ (Fintype.card ι : ℝ) * (2 * r) := fun ω => by
    calc
      |Z ω| ≤ ∑ i, |centeredTrunc (X i) r μ ω| := by
        simpa [Z] using
          Finset.abs_sum_le_sum_abs (fun i => centeredTrunc (X i) r μ ω) (Finset.univ)
      _ ≤ ∑ _i : ι, (2 * r) :=
          Finset.sum_le_sum fun i _ =>
            abs_centeredTrunc_le (μ := μ) (Y := X i) hr ω
      _ = (Fintype.card ι : ℝ) * (2 * r) := by
            simp [Finset.sum_const, nsmul_eq_mul]
  have h4 : Integrable (fun ω => (Z ω) ^ 4) μ :=
    integrable_pow_four_of_bound (μ := μ) hZmeas
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) hr)) hbd
  have hmeas : MeasurableSet {ω | t ≤ |Z ω|} :=
    measurableSet_le measurable_const hZmeas.abs
  have hpt : ∀ ω ∈ {ω | t ≤ |Z ω|}, t ^ 4 ≤ (Z ω) ^ 4 := fun ω hω => by
    have h1 : t ^ 4 ≤ |Z ω| ^ 4 := pow_le_pow_left₀ ht.le hω 4
    have heq : |Z ω| ^ 4 = (Z ω) ^ 4 := by
      have h : |Z ω| ^ 2 = (Z ω) ^ 2 := sq_abs _
      calc
        |Z ω| ^ 4 = (|Z ω| ^ 2) ^ 2 := by ring
        _ = ((Z ω) ^ 2) ^ 2 := by rw [h]
        _ = (Z ω) ^ 4 := by ring
    rwa [heq] at h1
  have hge :=
    setIntegral_mono_on (integrable_const (t ^ 4)).integrableOn h4.integrableOn hmeas hpt
  have hleft :
      ∫ ω in {ω | t ≤ |Z ω|}, (t ^ 4 : ℝ) ∂μ =
        t ^ 4 * μ.real {ω | t ≤ |Z ω|} := by
    rw [integral_const]
    simp [smul_eq_mul, Measure.real, mul_comm]
  have hmono :
      ∫ ω in {ω | t ≤ |Z ω|}, (Z ω) ^ 4 ∂μ ≤ ∫ ω, (Z ω) ^ 4 ∂μ :=
    setIntegral_le_integral h4
      (Eventually.of_forall fun ω => by positivity)
  have hle : t ^ 4 * μ.real {ω | t ≤ |Z ω|} ≤ 3 + 4 * r ^ 2 := by
    calc
      t ^ 4 * μ.real {ω | t ≤ |Z ω|} =
          ∫ ω in {ω | t ≤ |Z ω|}, (t ^ 4 : ℝ) ∂μ := hleft.symm
      _ ≤ ∫ ω in {ω | t ≤ |Z ω|}, (Z ω) ^ 4 ∂μ := hge
      _ ≤ ∫ ω, (Z ω) ^ 4 ∂μ := hmono
      _ ≤ 3 + 4 * r ^ 2 := by simpa [Z] using hET4
  exact (le_div_iff₀ (pow_pos ht 4)).mpr (by rwa [mul_comm] at hle)

/-- Prop 3.4 Case B: leave-one-out concentration on the original family. -/
lemma concentration_leaveOneOut_caseB
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (i : ι) {a b : ℝ} (hab : a ≤ b) :
    μ.real {ω | a ≤ leaveOneOut X i ω ∧ leaveOneOut X i ω ≤ b} ≤
      √2 * (b - a) + 2 * (√2 + 1) * thirdMomentSum (X := X) μ :=
  concentration_leaveOneOut hX hXmeas h_indep h_mean hvar h3 i hab

end ProbabilityTheory
