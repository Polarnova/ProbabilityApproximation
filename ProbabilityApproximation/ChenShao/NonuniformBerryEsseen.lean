/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.ChenShao.UpperTruncatedAssembly
import ProbabilityApproximation.ChenShao.UpperTruncatedIndicator
import ProbabilityApproximation.ChenShao.UpperTruncatedProduct
import ProbabilityApproximation.ChenShao.NonuniformReduction

/-!
# Nonuniform Berry--Esseen theorem

The one-sided truncated estimate combines the Stein residual identity with the bounds for `R₁`,
`R₃`, `R₂,₁`, and `R₂,₂` from Chen--Shao (2005), Section 6. Truncation comparison, a
bounded-threshold uniform estimate, a large-third-moment estimate, and reflection extend the
central estimate to every real threshold.
-/

open MeasureTheory ProbabilityTheory Real

noncomputable section

namespace ProbabilityTheory

universe uι uΩ

/-- Explicit constant in the central exponential estimate for the one-sided truncated sum. -/
def upperTruncatedNonuniformConstant : ℝ :=
  184 + (3 / 2 : ℝ) * steinProductIncrementConstant

lemma upperTruncatedNonuniformConstant_nonneg :
    0 ≤ upperTruncatedNonuniformConstant := by
  dsimp [upperTruncatedNonuniformConstant]
  nlinarith [steinProductIncrementConstant_pos.le]

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ι → Ω → ℝ}

/-- Chen--Shao's one-sided truncated central estimate.  The four contributions are
`8` (`R₁`), `8` (`R₃`), `168` (`R₂,₁`), and
`(3 / 2) * steinProductIncrementConstant` (`R₂,₂`). -/
theorem abs_cdf_upperTruncatedSum_sub_gaussian_le_exp_thirdMomentSum
    (hXmeas : ∀ i, Measurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (h_indep : iIndepFun X μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1)
    (h3 : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ)
    {z : ℝ} (hz : 2 ≤ z) :
    |cdf (μ.map (upperTruncatedSum X)) z - cdf (gaussianReal 0 1) z| ≤
      upperTruncatedNonuniformConstant * exp (-z / 2) * thirdMomentSum X μ := by
  classical
  have hR21 := abs_upperTruncatedR21_le_exp_thirdMomentSum
    hXmeas h_indep hX2 h_mean hvar h3 z
  have hR22 := abs_upperTruncatedR22_le_exp_thirdMomentSum
    hXmeas hX2 h_indep h_mean hvar h3 hz
  have hmain := abs_cdf_upperTruncatedSum_sub_gaussian_le_of_R21_R22
    hXmeas hX2 h_indep h_mean hvar h3 hz hR21 hR22
  convert hmain using 1
  simp only [upperTruncatedNonuniformConstant]
  ring

/-- The finite-third-moment nonuniform Berry--Esseen theorem for independent centered finite
families with unit total variance. This Bikelis-type consequence of the Chen--Shao nonuniform
bound follows from their one-sided truncated estimate by truncation and reflection. -/
theorem nonuniformBerryEsseen :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ι : Type uι} {Ω : Type uΩ} [Fintype ι] [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ι → Ω → ℝ),
        (∀ i, Measurable (X i)) →
        iIndepFun X μ →
        (∀ i, ∫ ω, X i ω ∂μ = 0) →
        (∀ i, MemLp (X i) 3 μ) →
        (∑ i, variance (X i) μ) = 1 →
        ∀ x : ℝ,
          |cdf (μ.map (fun ω ↦ ∑ i, X i ω)) x -
              cdf (gaussianReal 0 1) x| ≤
            C * (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) / (1 + |x| ^ 3) := by
  apply exists_nonuniformBerryEsseen_of_upperTruncated_decay
    upperTruncatedNonuniformConstant upperTruncatedNonuniformConstant_nonneg
  intro ι Ω instι instΩ μ instμ X hXmeas hX3 h_indep h_mean hvar z hz _
  have hX2 : ∀ i, MemLp (X i) 2 μ := fun i =>
    (hX3 i).mono_exponent (by norm_num)
  have h3 : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ := fun i => by
    simpa only [Real.norm_eq_abs] using
      (hX3 i).integrable_norm_pow (by decide : (3 : ℕ) ≠ 0)
  exact abs_cdf_upperTruncatedSum_sub_gaussian_le_exp_thirdMomentSum
    hXmeas hX2 h_indep h_mean hvar h3 hz

end ProbabilityTheory
