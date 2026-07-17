/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.ChenShao.ThirdMoment
import ProbabilityApproximation.ChenShao.Concentration
import ProbabilityApproximation.ChenShao.TruncationComparison
import ProbabilityApproximation.Stein.IndicatorSolution
import Mathlib.Tactic

/-!
# The large-third-moment branch of the nonuniform bound

Chen--Shao's final nonuniform argument separates the case in which the sum of absolute third
moments is at least one.  In that case a third-moment tail estimate for the normalized sum already
has the required cubic decay.
-/

open MeasureTheory ProbabilityTheory Real

noncomputable section

namespace ProbabilityTheory

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ι → Ω → ℝ}

private lemma one_sub_cdf_gaussian_le_exp_neg_half
    {z : ℝ} (hz : 2 ≤ z) :
    1 - cdf (gaussianReal 0 1) z ≤ exp (-z / 2) := by
  have hz0 : 0 < z := by linarith
  have hmills := one_sub_cdf_gaussian_le_pdf_div hz0
  have hpdf : gaussianPDFReal 0 1 z =
      (√(2 * π))⁻¹ * exp (-z ^ 2 / 2) := by
    simp [gaussianPDFReal, NNReal.coe_one]
  rw [hpdf] at hmills
  have hsqrt : (1 : ℝ) ≤ √(2 * π) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith [Real.two_le_pi]
  have hinvSqrt : (√(2 * π))⁻¹ ≤ 1 := by
    exact (inv_le_one₀ (by positivity)).2 hsqrt
  have hinvZ : z⁻¹ ≤ 1 := by
    exact (inv_le_one₀ hz0).2 (by linarith)
  have hexp : exp (-z ^ 2 / 2) ≤ exp (-z / 2) := by
    apply exp_le_exp.mpr
    nlinarith [sq_nonneg z]
  calc
    1 - cdf (gaussianReal 0 1) z ≤
        ((√(2 * π))⁻¹ * exp (-z ^ 2 / 2)) / z := hmills
    _ = (√(2 * π))⁻¹ * exp (-z ^ 2 / 2) * z⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ 1 * exp (-z / 2) * 1 := by gcongr
    _ = exp (-z / 2) := by ring

/-- If the sum of third moments is at least one, then the normalized sum already satisfies a
nonuniform CDF estimate by third-moment Markov and the Gaussian tail bound. -/
lemma abs_cdf_sumX_sub_gaussian_le_of_one_le_thirdMoment
    (hXmeas : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ)
    (h_indep : iIndepFun X μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1)
    (hgamma : 1 ≤ thirdMomentSum X μ)
    {z : ℝ} (hz : 2 ≤ z) :
    |cdf (μ.map (sumX X)) z - cdf (gaussianReal 0 1) z| ≤
      62 * thirdMomentSum X μ / (1 + z ^ 3) := by
  let γ := thirdMomentSum X μ
  have hγ0 : 0 ≤ γ := le_trans zero_le_one hgamma
  have hz0 : 0 < z := by linarith
  have hsumMeas : Measurable (sumX X) := measurable_sumX hXmeas
  letI : IsProbabilityMeasure (μ.map (sumX X)) :=
    Measure.isProbabilityMeasure_map hsumMeas.aemeasurable
  have hsum3 : MemLp (sumX X) 3 μ := by
    change MemLp (fun ω ↦ ∑ i, X i ω) 3 μ
    exact memLp_finsetSum (s := Finset.univ) fun i _ ↦ hX3 i
  have htailEq :
      1 - cdf (μ.map (sumX X)) z = μ.real {ω | z < sumX X ω} := by
    rw [cdf_eq_real, map_measureReal_apply hsumMeas measurableSet_Iic]
    change 1 - μ.real {ω | sumX X ω ≤ z} = μ.real {ω | z < sumX X ω}
    rw [show {ω | z < sumX X ω} = {ω | sumX X ω ≤ z}ᶜ by ext ω; simp]
    rw [probReal_compl_eq_one_sub
      (measurableSet_le hsumMeas measurable_const)]
  have htailSubset : {ω | z < sumX X ω} ⊆ {ω | z ≤ |sumX X ω|} := by
    intro ω hω
    exact hω.le.trans (le_abs_self (sumX X ω))
  have hmarkov := measureReal_abs_ge_le_integral_abs_pow_three
    hsumMeas hsum3 hz0
  have hmoment := integral_abs_sumX_pow_three_le hXmeas hX3 h_indep h_mean hvar
  have hmoment' :
      ∫ ω, |sumX X ω| ^ 3 ∂μ ≤ 3 + γ := by
    simpa only [γ, thirdMomentSum] using hmoment
  have htailMoment :
      1 - cdf (μ.map (sumX X)) z ≤ (3 + γ) / z ^ 3 := by
    rw [htailEq]
    calc
      μ.real {ω | z < sumX X ω} ≤ μ.real {ω | z ≤ |sumX X ω|} :=
        measureReal_mono htailSubset
      _ ≤ (∫ ω, |sumX X ω| ^ 3 ∂μ) / z ^ 3 := hmarkov
      _ ≤ (3 + γ) / z ^ 3 := by
        exact div_le_div_of_nonneg_right hmoment' (pow_nonneg hz0.le 3)
  have hzCube : 0 < z ^ 3 := pow_pos hz0 3
  have hzCubeOne : 1 ≤ z ^ 3 := by nlinarith [sq_nonneg z]
  have hden : 0 < 1 + z ^ 3 := by positivity
  have htail :
      1 - cdf (μ.map (sumX X)) z ≤ 8 * γ / (1 + z ^ 3) := by
    apply htailMoment.trans
    rw [div_le_div_iff₀ hzCube hden]
    have h3γ : 3 + γ ≤ 4 * γ := by linarith
    have hdenLe : 1 + z ^ 3 ≤ 2 * z ^ 3 := by linarith
    calc
      (3 + γ) * (1 + z ^ 3) ≤ (4 * γ) * (1 + z ^ 3) := by
        exact mul_le_mul_of_nonneg_right h3γ hden.le
      _ ≤ (4 * γ) * (2 * z ^ 3) := by
        exact mul_le_mul_of_nonneg_left hdenLe (mul_nonneg (by norm_num) hγ0)
      _ = 8 * γ * z ^ 3 := by ring
  have hgaussian :
      1 - cdf (gaussianReal 0 1) z ≤ 54 / (1 + z ^ 3) :=
    (one_sub_cdf_gaussian_le_exp_neg_half hz).trans
      (exp_neg_half_le_div_one_add_cube hz)
  have hFnonneg : 0 ≤ 1 - cdf (μ.map (sumX X)) z :=
    sub_nonneg.mpr (cdf_le_one _ _)
  have hGnonneg : 0 ≤ 1 - cdf (gaussianReal 0 1) z :=
    sub_nonneg.mpr (cdf_le_one _ _)
  calc
    |cdf (μ.map (sumX X)) z - cdf (gaussianReal 0 1) z| =
        |(1 - cdf (gaussianReal 0 1) z) - (1 - cdf (μ.map (sumX X)) z)| := by
          congr 1
          ring
    _ ≤ |1 - cdf (gaussianReal 0 1) z| +
          |1 - cdf (μ.map (sumX X)) z| := abs_sub _ _
    _ = (1 - cdf (gaussianReal 0 1) z) +
          (1 - cdf (μ.map (sumX X)) z) := by
          rw [abs_of_nonneg hGnonneg, abs_of_nonneg hFnonneg]
    _ ≤ 54 / (1 + z ^ 3) + 8 * γ / (1 + z ^ 3) := add_le_add hgaussian htail
    _ ≤ 54 * γ / (1 + z ^ 3) + 8 * γ / (1 + z ^ 3) := by
      have h54 : (54 : ℝ) ≤ 54 * γ := by nlinarith
      exact add_le_add (div_le_div_of_nonneg_right h54 hden.le) le_rfl
    _ = 62 * thirdMomentSum X μ / (1 + z ^ 3) := by
      simp only [γ]
      ring

end ProbabilityTheory
