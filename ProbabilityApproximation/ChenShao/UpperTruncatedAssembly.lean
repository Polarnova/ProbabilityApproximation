/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.ChenShao.UpperTruncatedExpectedKernel
import ProbabilityApproximation.ChenShao.UpperTruncatedSteinBounds

/-!
# Assembly of the one-sided truncated central estimate

This module combines the exact Chen--Shao residual identity with the exponential estimates for
`R₁` and `R₃`.  It isolates `R₂`, and then its indicator and Stein-product pieces, as the only
remaining analytic inputs.
-/

open MeasureTheory ProbabilityTheory Real

noncomputable section

namespace ProbabilityTheory

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ι → Ω → ℝ}

/-- The exact residual identity reduces the central estimate to an exponential bound for `R₂`.
The constant `16` is the sum of the two proved constants for `R₁` and `R₃`. -/
theorem abs_cdf_upperTruncatedSum_sub_gaussian_le_of_R2
    (hXmeas : ∀ i, Measurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (h_indep : iIndepFun X μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1)
    (h3 : ∀ i, Integrable (fun ω ↦ |X i ω| ^ 3) μ)
    {B z : ℝ} (hz : 2 ≤ z)
    (hR2 : |upperTruncatedR2 X μ z| ≤
      B * exp (-z / 2) * thirdMomentSum X μ) :
    |cdf (μ.map (upperTruncatedSum X)) z - cdf (gaussianReal 0 1) z| ≤
      (16 + B) * exp (-z / 2) * thirdMomentSum X μ := by
  have hR1 := abs_upperTruncatedR1_le
    hXmeas hX2 h_indep h_mean hvar h3 hz
  have hR3 := abs_upperTruncatedR3_le
    hXmeas hX2 h_indep h_mean hvar h3 hz
  rw [cdf_upperTruncatedSum_sub_gaussian_eq_R1_add_R2_add_R3
    hXmeas hX2 h_indep z]
  calc
    |upperTruncatedR1 X μ z + upperTruncatedR2 X μ z +
        upperTruncatedR3 X μ z| ≤
        |upperTruncatedR1 X μ z| + |upperTruncatedR2 X μ z| +
          |upperTruncatedR3 X μ z| := by
            exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 8 * exp (-z / 2) * thirdMomentSum X μ +
          (B * exp (-z / 2) * thirdMomentSum X μ) +
          8 * exp (-z / 2) * thirdMomentSum X μ := by gcongr
    _ = (16 + B) * exp (-z / 2) * thirdMomentSum X μ := by ring

/-- Bounds for the two canonical pieces of `R₂` combine with `R₁` and `R₃` to give the
central exponential estimate. -/
theorem abs_cdf_upperTruncatedSum_sub_gaussian_le_of_R21_R22
    (hXmeas : ∀ i, Measurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (h_indep : iIndepFun X μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1)
    (h3 : ∀ i, Integrable (fun ω ↦ |X i ω| ^ 3) μ)
    {B₁ B₂ z : ℝ} (hz : 2 ≤ z)
    (hR21 : |upperTruncatedR21 X μ z| ≤
      B₁ * exp (-z / 2) * thirdMomentSum X μ)
    (hR22 : |upperTruncatedR22 X μ z| ≤
      B₂ * exp (-z / 2) * thirdMomentSum X μ) :
    |cdf (μ.map (upperTruncatedSum X)) z - cdf (gaussianReal 0 1) z| ≤
      (16 + (B₁ + B₂)) * exp (-z / 2) * thirdMomentSum X μ := by
  apply abs_cdf_upperTruncatedSum_sub_gaussian_le_of_R2
    hXmeas hX2 h_indep h_mean hvar h3 hz
  rw [upperTruncatedR2_eq_R21_add_R22 hX2 hXmeas h_indep z]
  calc
    |upperTruncatedR21 X μ z + upperTruncatedR22 X μ z| ≤
        |upperTruncatedR21 X μ z| + |upperTruncatedR22 X μ z| := abs_add_le _ _
    _ ≤ B₁ * exp (-z / 2) * thirdMomentSum X μ +
          B₂ * exp (-z / 2) * thirdMomentSum X μ := add_le_add hR21 hR22
    _ = (B₁ + B₂) * exp (-z / 2) * thirdMomentSum X μ := by ring

end ProbabilityTheory
