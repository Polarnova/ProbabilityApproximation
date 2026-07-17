/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.ChenShao.NonuniformLargeGamma
import ProbabilityApproximation.ChenShao.NonuniformAssembly
import ProbabilityApproximation.ChenShao.UpperTruncation
import ProbabilityApproximation.ChenShao.UniformBerryEsseen

/-!
# Reduction of the scalar release theorem to the truncated central estimate

This module combines the bounded-threshold uniform estimate, the large-third-moment tail branch,
and the comparison with the one-sided truncated sum.  Its composition theorem takes the central
Chen--Shao estimate for the truncated sum at `z ≥ 2` and total third moment at most one as an
explicit input; `NonuniformBerryEsseen.lean` supplies that input.
-/

open MeasureTheory ProbabilityTheory Real

noncomputable section

namespace ProbabilityTheory

universe uι uΩ

/-- Explicit release constant obtained from a truncated exponential-decay estimate with constant
`A`. -/
def nonuniformReductionConstant (A : ℝ) : ℝ := 270 + 54 * A

lemma nonuniformReductionConstant_pos {A : ℝ} (hA : 0 ≤ A) :
    0 < nonuniformReductionConstant A := by
  simp only [nonuniformReductionConstant]
  positivity

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ι → Ω → ℝ}

/-- A central exponential-decay estimate for the one-sided truncated sum implies the public cubic
estimate for the original sum at every nonnegative threshold. -/
theorem nonuniformBerryEsseen_nonnegative_of_upperTruncated_decay
    (hXmeas : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ)
    (h_indep : iIndepFun X μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1)
    {A : ℝ} (hA : 0 ≤ A)
    (hcentral : ∀ z : ℝ, 2 ≤ z → thirdMomentSum X μ ≤ 1 →
      |cdf (μ.map (upperTruncatedSum X)) z - cdf (gaussianReal 0 1) z| ≤
        A * exp (-z / 2) * thirdMomentSum X μ) :
    ∀ z : ℝ, 0 ≤ z →
      |cdf (μ.map (sumX X)) z - cdf (gaussianReal 0 1) z| ≤
        nonuniformReductionConstant A * thirdMomentSum X μ / (1 + z ^ 3) := by
  classical
  intro z hz
  have hX2 : ∀ i, MemLp (X i) 2 μ := fun i ↦
    (hX3 i).mono_exponent (by norm_num)
  have hXabs3 : ∀ i, Integrable (fun ω ↦ |X i ω| ^ 3) μ := fun i ↦ by
    simpa [Real.norm_eq_abs] using
      (hX3 i).integrable_norm_pow (by decide : (3 : ℕ) ≠ 0)
  let γ := thirdMomentSum X μ
  let C := nonuniformReductionConstant A
  have hγ0 : 0 ≤ γ := thirdMomentSum_nonneg hXabs3
  have hC0 : 0 < C := nonuniformReductionConstant_pos hA
  have hden : 0 < 1 + z ^ 3 := by positivity
  by_cases hzlarge : 2 ≤ z
  · by_cases hγsmall : γ ≤ 1
    · have hcomparison := abs_cdf_sumX_sub_gaussian_le_upperTruncated_add
        hXmeas hX3 h_indep h_mean hvar hγsmall hzlarge
      have htruncated := hcentral z hzlarge hγsmall
      have hexponential := exp_neg_half_le_div_one_add_cube hzlarge
      have hcentralCubic :
          A * exp (-z / 2) * γ ≤ 54 * A * γ / (1 + z ^ 3) := by
        calc
          A * exp (-z / 2) * γ = (A * γ) * exp (-z / 2) := by ring
          _ ≤ (A * γ) * (54 / (1 + z ^ 3)) :=
            mul_le_mul_of_nonneg_left hexponential (mul_nonneg hA hγ0)
          _ = 54 * A * γ / (1 + z ^ 3) := by ring
      have h45 :
          45 * γ / (1 + z ^ 3) ≤ C * γ / (1 + z ^ 3) -
              54 * A * γ / (1 + z ^ 3) := by
        simp only [C, nonuniformReductionConstant]
        have hden0 : 0 ≤ 1 + z ^ 3 := hden.le
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        nlinarith [mul_nonneg hγ0 (inv_nonneg.mpr hden0)]
      calc
        |cdf (μ.map (sumX X)) z - cdf (gaussianReal 0 1) z| ≤
            |cdf (μ.map (upperTruncatedSum X)) z - cdf (gaussianReal 0 1) z| +
              45 * γ / (1 + z ^ 3) := by
                simpa only [γ, thirdMomentSum] using hcomparison
        _ ≤ A * exp (-z / 2) * γ + 45 * γ / (1 + z ^ 3) := by gcongr
        _ ≤ 54 * A * γ / (1 + z ^ 3) + 45 * γ / (1 + z ^ 3) := by gcongr
        _ ≤ C * γ / (1 + z ^ 3) := by linarith
    · have hγlarge : 1 ≤ γ := le_of_not_ge hγsmall
      have hlarge := abs_cdf_sumX_sub_gaussian_le_of_one_le_thirdMoment
        hXmeas hX3 h_indep h_mean hvar hγlarge hzlarge
      have h62C : (62 : ℝ) ≤ C := by
        simp only [C, nonuniformReductionConstant]
        nlinarith
      exact hlarge.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right h62C hγ0) hden.le)
  · have hzlt : z < 2 := lt_of_not_ge hzlarge
    have hBE := uniformBerryEsseen_thirdMoment hX2 hXmeas h_indep h_mean hvar hXabs3 z
    change |cdf (μ.map (sumX X)) z - cdf (gaussianReal 0 1) z| ≤
      thirdMomentBerryEsseenConstant * thirdMomentSum X μ at hBE
    have hBE30 :
        |cdf (μ.map (sumX X)) z - cdf (gaussianReal 0 1) z| ≤ 30 * γ := by
      simpa only [thirdMomentBerryEsseenConstant, γ] using hBE
    have hzCube : z ^ 3 ≤ 8 := by nlinarith [sq_nonneg z]
    have h30den : 30 * (1 + z ^ 3) ≤ C := by
      simp only [C, nonuniformReductionConstant]
      nlinarith
    have hscale : 30 * γ ≤ C * γ / (1 + z ^ 3) := by
      rw [le_div_iff₀ hden]
      calc
        30 * γ * (1 + z ^ 3) = (30 * (1 + z ^ 3)) * γ := by ring
        _ ≤ C * γ := mul_le_mul_of_nonneg_right h30den hγ0
    exact hBE30.trans hscale

/-- A universal central estimate for one-sided truncated sums composes with the reduction into the
frozen scalar release theorem. -/
theorem exists_nonuniformBerryEsseen_of_upperTruncated_decay
    (A : ℝ) (hA : 0 ≤ A)
    (hcentral :
      ∀ {ι : Type uι} {Ω : Type uΩ} [Fintype ι] [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ι → Ω → ℝ),
        (∀ i, Measurable (X i)) →
        (∀ i, MemLp (X i) 3 μ) →
        iIndepFun X μ →
        (∀ i, ∫ ω, X i ω ∂μ = 0) →
        (∑ i, variance (X i) μ) = 1 →
        ∀ z : ℝ, 2 ≤ z → thirdMomentSum X μ ≤ 1 →
          |cdf (μ.map (upperTruncatedSum X)) z - cdf (gaussianReal 0 1) z| ≤
            A * exp (-z / 2) * thirdMomentSum X μ) :
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
  refine ⟨nonuniformReductionConstant A, nonuniformReductionConstant_pos hA, ?_⟩
  have hnonnegative :
      ∀ {ι : Type uι} {Ω : Type uΩ} [Fintype ι] [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ι → Ω → ℝ),
        (∀ i, Measurable (X i)) →
        iIndepFun X μ →
        (∀ i, ∫ ω, X i ω ∂μ = 0) →
        (∀ i, MemLp (X i) 3 μ) →
        (∑ i, variance (X i) μ) = 1 →
        ∀ x : ℝ, 0 ≤ x →
          |cdf (μ.map (sumX X)) x - cdf (gaussianReal 0 1) x| ≤
            nonuniformReductionConstant A * thirdMomentSum X μ / (1 + x ^ 3) := by
    intro ι Ω instι instΩ μ instμ X hX h_indep h_mean hmem hvar
    exact nonuniformBerryEsseen_nonnegative_of_upperTruncated_decay
      hX hmem h_indep h_mean hvar hA
      (hcentral (ι := ι) (Ω := Ω) μ X hX hmem h_indep h_mean hvar)
  have hall :
      ∀ {ι : Type uι} {Ω : Type uΩ} [Fintype ι] [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ι → Ω → ℝ),
        (∀ i, Measurable (X i)) →
        iIndepFun X μ →
        (∀ i, ∫ ω, X i ω ∂μ = 0) →
        (∀ i, MemLp (X i) 3 μ) →
        (∑ i, variance (X i) μ) = 1 →
        ∀ x : ℝ,
          |cdf (μ.map (sumX X)) x - cdf (gaussianReal 0 1) x| ≤
            nonuniformReductionConstant A * thirdMomentSum X μ / (1 + |x| ^ 3) :=
    nonuniformBerryEsseen_all_thresholds_of_nonnegative
      (nonuniformReductionConstant A) hnonnegative
  intro ι Ω instι instΩ μ instμ X hX h_indep h_mean hmem hvar x
  change |cdf (μ.map (sumX X)) x - cdf (gaussianReal 0 1) x| ≤
    nonuniformReductionConstant A * thirdMomentSum X μ / (1 + |x| ^ 3)
  exact hall μ X hX h_indep h_mean hmem hvar x

end ProbabilityTheory
