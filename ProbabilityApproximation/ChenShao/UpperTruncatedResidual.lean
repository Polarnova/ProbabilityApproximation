/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.ChenShao.NonuniformBerryEsseen
import ProbabilityApproximation.ChenShao.UpperTruncatedStein

/-!
# Residual decomposition for the one-sided truncated sum

This module records the exact algebraic `R₁ + R₂ + R₃` decomposition underlying Chen--Shao
(2005), equation (6.16).  The missing second-moment mass of the truncated coordinates is kept
explicit and bounded by the original sum of absolute third moments.
-/

open MeasureTheory ProbabilityTheory Real

noncomputable section

namespace ProbabilityTheory

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ι → Ω → ℝ}

/-- Second-moment mass removed by one-sided truncation. -/
def upperTruncatedMissingSecondMoment (X : ι → Ω → ℝ) (μ : Measure Ω) : ℝ :=
  1 - ∑ i, ∫ ω, upperTruncatedFamily X i ω ^ 2 ∂μ

private lemma sq_sub_sq_upperTruncateOne_nonneg (x : ℝ) :
    0 ≤ x ^ 2 - upperTruncateOne x ^ 2 := by
  exact sub_nonneg.mpr (sq_upperTruncateOne_le_sq x)

private lemma sq_sub_sq_upperTruncateOne_le_abs_cube (x : ℝ) :
    x ^ 2 - upperTruncateOne x ^ 2 ≤ |x| ^ 3 := by
  by_cases hx : x ≤ 1
  · simp [upperTruncateOne, hx]
  · have hx1 : 1 < x := lt_of_not_ge hx
    have hx0 : 0 ≤ x := le_trans zero_le_one hx1.le
    simp only [upperTruncateOne, if_neg hx]
    rw [abs_of_nonneg hx0]
    nlinarith [sq_nonneg x]

lemma upperTruncatedMissingSecondMoment_nonneg
    (hXmeas : ∀ i, Measurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1) :
    0 ≤ upperTruncatedMissingSecondMoment X μ := by
  unfold upperTruncatedMissingSecondMoment
  exact sub_nonneg.mpr
    (sum_integral_sq_upperTruncatedFamily_le hXmeas hX2 h_mean hvar)

lemma upperTruncatedMissingSecondMoment_le_thirdMomentSum
    (hXmeas : ∀ i, Measurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1)
    (h3 : ∀ i, Integrable (fun ω ↦ |X i ω| ^ 3) μ) :
    upperTruncatedMissingSecondMoment X μ ≤ thirdMomentSum X μ := by
  have hsumX : ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ = 1 :=
    sum_integral_sq_eq_one hX2 h_mean hvar
  have hcoordinate (i : ι) :
      (∫ ω, (X i ω) ^ 2 ∂μ) -
          ∫ ω, upperTruncatedFamily X i ω ^ 2 ∂μ ≤
        ∫ ω, |X i ω| ^ 3 ∂μ := by
    have hbar2 : Integrable (fun ω ↦ upperTruncatedFamily X i ω ^ 2) μ :=
      (memLp_upperTruncatedFamily hXmeas hX2 i).integrable_sq
    have hdiff : Integrable
        (fun ω ↦ (X i ω) ^ 2 - upperTruncatedFamily X i ω ^ 2) μ :=
      (hX2 i).integrable_sq.sub hbar2
    rw [← integral_sub (hX2 i).integrable_sq hbar2]
    exact integral_mono hdiff (h3 i) fun ω ↦ by
      simpa only [upperTruncatedFamily, Function.comp_apply] using
        sq_sub_sq_upperTruncateOne_le_abs_cube (X i ω)
  unfold upperTruncatedMissingSecondMoment thirdMomentSum
  rw [← hsumX, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ ↦ hcoordinate i

/-- The kernel-exchange term in the truncated Stein identity. -/
def upperTruncatedKernelDerivativeTerm [DecidableEq ι]
    (X : ι → Ω → ℝ) (μ : Measure Ω)
    (z : ℝ) : ℝ :=
  ∑ i : ι, ∫ ω, (∫ t : ℝ,
    kernelDensityFwd (upperTruncatedFamily X i ω) t *
      steinSolutionDeriv z (leaveOneOut (upperTruncatedFamily X) i ω + t)) ∂μ

/-- The noncentered mean correction in the truncated Stein identity. -/
def upperTruncatedMeanCorrection [DecidableEq ι]
    (X : ι → Ω → ℝ) (μ : Measure Ω)
    (z : ℝ) : ℝ :=
  ∑ i : ι, (∫ ω, upperTruncatedFamily X i ω ∂μ) *
    ∫ ω, steinSolution z (leaveOneOut (upperTruncatedFamily X) i ω) ∂μ

/-- `R₁`: the second-moment mass removed by truncation, multiplied by `E f'_z(W̄)`. -/
def upperTruncatedR1 (X : ι → Ω → ℝ) (μ : Measure Ω) (z : ℝ) : ℝ :=
  upperTruncatedMissingSecondMoment X μ *
    ∫ ω, steinSolutionDeriv z (upperTruncatedSum X ω) ∂μ

/-- `R₂`: the difference between the retained kernel mass applied at the full truncated sum and
the leave-one-out kernel exchange. -/
def upperTruncatedR2 [DecidableEq ι]
    (X : ι → Ω → ℝ) (μ : Measure Ω) (z : ℝ) : ℝ :=
  (1 - upperTruncatedMissingSecondMoment X μ) *
      ∫ ω, steinSolutionDeriv z (upperTruncatedSum X ω) ∂μ -
    upperTruncatedKernelDerivativeTerm X μ z

/-- `R₃`: the sign-adjusted noncentered mean correction. -/
def upperTruncatedR3 [DecidableEq ι]
    (X : ι → Ω → ℝ) (μ : Measure Ω) (z : ℝ) : ℝ :=
  -upperTruncatedMeanCorrection X μ z

/-- Exact Chen--Shao (2005), (6.16), residual identity. -/
theorem cdf_upperTruncatedSum_sub_gaussian_eq_R1_add_R2_add_R3
    [DecidableEq ι]
    (hXmeas : ∀ i, Measurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (h_indep : iIndepFun X μ)
    (z : ℝ) :
    cdf (μ.map (upperTruncatedSum X)) z - cdf (gaussianReal 0 1) z =
      upperTruncatedR1 X μ z + upperTruncatedR2 X μ z +
        upperTruncatedR3 X μ z := by
  have hcdf := cdf_sub_eq_integral_steinSolutionDeriv_sub_Wf
    (X := upperTruncatedFamily X) (μ := μ)
    (memLp_upperTruncatedFamily hXmeas hX2)
    (measurable_upperTruncatedFamily hXmeas) z
  have hstein := stein_identity_upperTruncatedSum hX2 hXmeas h_indep z
  change cdf (μ.map (upperTruncatedSum X)) z - cdf (gaussianReal 0 1) z =
      (∫ ω, steinSolutionDeriv z (upperTruncatedSum X ω) ∂μ) -
        ∫ ω, upperTruncatedSum X ω * steinSolution z (upperTruncatedSum X ω) ∂μ at hcdf
  rw [hcdf, hstein]
  simp only [upperTruncatedR1, upperTruncatedR2, upperTruncatedR3,
    upperTruncatedKernelDerivativeTerm, upperTruncatedMeanCorrection]
  ring

end ProbabilityTheory
