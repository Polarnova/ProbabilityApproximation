/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.ChenShao.Concentration

/-!
# Reflection of a finite family of real random variables

This module supplies the coordinatewise reflection adapter used to apply a scalar CDF estimate to
both a normalized sum and its negative.
-/

open MeasureTheory ProbabilityTheory Real

noncomputable section

namespace ProbabilityTheory

/-- Coordinatewise negation of a family of real random variables. -/
def reflectedFamily {ι Ω : Type*} (X : ι → Ω → ℝ) : ι → Ω → ℝ :=
  fun i ω => -X i ω

variable {ι Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} {X : ι → Ω → ℝ}

/-- Coordinatewise reflection preserves measurability. -/
lemma measurable_reflectedFamily (hX : ∀ i, Measurable (X i)) :
    ∀ i, Measurable (reflectedFamily X i) :=
  fun i => by
    change Measurable (-X i)
    exact (hX i).neg

/-- Coordinatewise reflection preserves third-order `MemLp`. -/
lemma memLp_three_reflectedFamily (hX : ∀ i, MemLp (X i) 3 μ) :
    ∀ i, MemLp (reflectedFamily X i) 3 μ :=
  fun i => by
    change MemLp (-X i) 3 μ
    exact (hX i).neg

/-- Applying coordinatewise reflection preserves mutual independence. -/
lemma iIndepFun_reflectedFamily (hX : iIndepFun X μ) :
    iIndepFun (reflectedFamily X) μ := by
  change iIndepFun (fun i => (fun x : ℝ => -x) ∘ X i) μ
  exact hX.comp (fun _ => fun x : ℝ => -x) (fun _ => measurable_id.neg)

/-- Coordinatewise reflection preserves zero means. -/
lemma integral_reflectedFamily_eq_zero
    (hX : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    ∀ i, ∫ ω, reflectedFamily X i ω ∂μ = 0 :=
  fun i => by
    change ∫ ω, -X i ω ∂μ = 0
    rw [integral_neg, hX i, neg_zero]

variable [Fintype ι]

/-- Coordinatewise reflection preserves the unit sum-of-variances normalization. -/
lemma sum_variance_reflectedFamily_eq_one
    (hX : ∑ i, variance (X i) μ = 1) :
    ∑ i, variance (reflectedFamily X i) μ = 1 := by
  calc
    ∑ i, variance (reflectedFamily X i) μ = ∑ i, variance (X i) μ := by
      apply Finset.sum_congr rfl
      intro i _
      change variance (fun ω => -X i ω) μ = variance (X i) μ
      exact variance_fun_neg
    _ = 1 := hX

/-- Coordinatewise reflection leaves the sum of absolute third moments unchanged. -/
lemma thirdMomentSum_reflectedFamily :
    thirdMomentSum (reflectedFamily X) μ = thirdMomentSum X μ := by
  simp [thirdMomentSum, reflectedFamily]

/-- The law of the sum of the reflected family is the reflection of the law of the original sum. -/
lemma map_sumX_reflectedFamily
    (hX : ∀ i, Measurable (X i)) :
    μ.map (sumX (reflectedFamily X)) =
      (μ.map (sumX X)).map (fun z : ℝ => -z) := by
  rw [Measure.map_map (by fun_prop) (measurable_sumX hX)]
  congr 1
  funext ω
  simp [sumX, reflectedFamily]

end ProbabilityTheory
