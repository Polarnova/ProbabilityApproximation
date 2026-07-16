/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.ChenShao.CDFReflection
import ProbabilityApproximation.ChenShao.ReflectedFamily

/-!
# Assembly of scalar nonuniform bounds

This module lifts a nonuniform Berry--Esseen estimate proved at nonnegative thresholds to every
real threshold.  The passage to negative thresholds uses coordinatewise reflection together with
the atom-safe CDF limit from `CDFReflection`.
-/

open MeasureTheory ProbabilityTheory Real

noncomputable section

namespace ProbabilityTheory

universe uι uΩ

/-- A finite-third-moment nonuniform estimate for every normalized family at nonnegative
thresholds implies the same estimate at all real thresholds. -/
theorem nonuniformBerryEsseen_all_thresholds_of_nonnegative
    (C : ℝ)
    (h_nonnegative :
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
            C * thirdMomentSum X μ / (1 + x ^ 3)) :
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
          C * thirdMomentSum X μ / (1 + |x| ^ 3) := by
  intro ι Ω instι instΩ μ instμ X hX h_indep h_mean h_memLp h_variance
  let ν : Measure ℝ := μ.map (sumX X)
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_sumX hX).aemeasurable
  apply cdf_gaussian_error_le_of_nonneg_of_map_neg ν
  · intro x hx
    simpa only [ν] using
      h_nonnegative (ι := ι) (Ω := Ω) μ X hX h_indep h_mean h_memLp h_variance x hx
  · intro x hx
    have hreflected := h_nonnegative (ι := ι) (Ω := Ω) μ (reflectedFamily X)
      (measurable_reflectedFamily hX)
      (iIndepFun_reflectedFamily h_indep)
      (integral_reflectedFamily_eq_zero h_mean)
      (memLp_three_reflectedFamily h_memLp)
      (sum_variance_reflectedFamily_eq_one (X := X) h_variance) x hx
    rw [map_sumX_reflectedFamily hX, thirdMomentSum_reflectedFamily] at hreflected
    simpa only [ν] using hreflected

end ProbabilityTheory
