/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Reflection of nonuniform CDF bounds

This module extends CDF bounds proved on nonnegative thresholds to every real threshold.  At a
negative threshold, decreasing open half-lines approach the closed half-line defining the CDF.
Consequently the argument remains valid when the approximated distribution has atoms.
-/

open MeasureTheory Real Set Filter Topology
open scoped ENNReal

noncomputable section

namespace ProbabilityTheory

/-- For a negative threshold `x`, the strict complements of reflected CDF events converge from
above to `Iic x`.  This is the atom-safe replacement for the generally false identity
`F(x) = 1 - F_{-X}(-x)`. -/
lemma tendsto_one_sub_cdf_map_neg_of_neg
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {x : ℝ} (hx : x < 0) :
    Tendsto
      (fun n : ℕ =>
        1 - cdf (ν.map fun z : ℝ => -z)
          (-(x + (-x) * (1 / ((n : ℝ) + 1)))))
      atTop (𝓝 (cdf ν x)) := by
  letI : IsProbabilityMeasure (ν.map fun z : ℝ => -z) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let ε : ℕ → ℝ := fun n => (-x) * (1 / ((n : ℝ) + 1))
  let a : ℕ → ℝ := fun n => x + ε n
  let s : ℕ → Set ℝ := fun n => Iio (a n)
  have hε_pos (n : ℕ) : 0 < ε n := by
    exact mul_pos (neg_pos.mpr hx) (by positivity)
  have hε_tendsto : Tendsto ε atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => -x) atTop (𝓝 (-x)) := tendsto_const_nhds
    simpa [ε] using
      hconst.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ha_tendsto : Tendsto a atTop (𝓝 x) := by
    simpa [a] using tendsto_const_nhds.add hε_tendsto
  have hs_antitone : Antitone s := by
    intro n m hnm
    simpa only [s, a, ε, add_comm] using Iio_subset_Iio (add_le_add_left
      (mul_le_mul_of_nonneg_left (Nat.one_div_le_one_div hnm) (neg_nonneg.mpr hx.le)) x)
  have hs_iInter : ⋂ n, s n = Iic x := by
    ext z
    simp only [s, mem_iInter, mem_Iio, mem_Iic]
    constructor
    · intro hz
      exact ge_of_tendsto' ha_tendsto fun n => (hz n).le
    · intro hzx n
      exact lt_of_le_of_lt hzx (lt_add_of_pos_right x (hε_pos n))
  have hmeasure : Tendsto (fun n => ν (s n)) atTop (𝓝 (ν (Iic x))) := by
    have h := tendsto_measure_iInter_atTop (μ := ν)
      (fun n => measurableSet_Iio.nullMeasurableSet) hs_antitone
      ⟨0, measure_ne_top ν (s 0)⟩
    rw [hs_iInter] at h
    change Tendsto (ν ∘ s) atTop (𝓝 (ν (Iic x)))
    exact h
  have hmeasureReal :
      Tendsto (fun n => ν.real (s n)) atTop (𝓝 (ν.real (Iic x))) := by
    change Tendsto (ENNReal.toReal ∘ fun n => ν (s n)) atTop
      (𝓝 (ENNReal.toReal (ν (Iic x))))
    exact (ENNReal.tendsto_toReal (measure_ne_top ν (Iic x))).comp hmeasure
  have hcdf (n : ℕ) :
      1 - cdf (ν.map fun z : ℝ => -z) (-a n) = ν.real (s n) := by
    rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic]
    have hpreimage :
        (fun z : ℝ => -z) ⁻¹' Iic (-a n) = Ici (a n) := by
      ext z
      simp
    rw [hpreimage]
    rw [show Ici (a n) = (Iio (a n))ᶜ by simp]
    rw [probReal_compl_eq_one_sub measurableSet_Iio]
    simp only [sub_sub_cancel, s]
  have hseq :
      (fun n : ℕ =>
        1 - cdf (ν.map fun z : ℝ => -z)
          (-(x + (-x) * (1 / ((n : ℝ) + 1))))) =
        fun n => ν.real (s n) := by
    funext n
    simpa only [a, ε] using hcdf n
  rw [hseq, cdf_eq_real]
  exact hmeasureReal

/-- A nonuniform standard-Gaussian CDF estimate for a probability measure and its reflection on
nonnegative thresholds yields the corresponding estimate at every real threshold. -/
theorem cdf_gaussian_error_le_of_nonneg_of_map_neg
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {K : ℝ}
    (hν : ∀ x : ℝ, 0 ≤ x →
      |cdf ν x - cdf (gaussianReal 0 1) x| ≤ K / (1 + x ^ 3))
    (hneg : ∀ x : ℝ, 0 ≤ x →
      |cdf (ν.map fun z : ℝ => -z) x - cdf (gaussianReal 0 1) x| ≤
        K / (1 + x ^ 3)) :
    ∀ x : ℝ,
      |cdf ν x - cdf (gaussianReal 0 1) x| ≤ K / (1 + |x| ^ 3) := by
  intro x
  by_cases hx : 0 ≤ x
  · simpa [abs_of_nonneg hx] using hν x hx
  · have hxneg : x < 0 := lt_of_not_ge hx
    let r : ℕ → ℝ := fun n => -(x + (-x) * (1 / ((n : ℝ) + 1)))
    have hr_tendsto : Tendsto r atTop (𝓝 (-x)) := by
      have hzero : Tendsto (fun n : ℕ => (-x) * (1 / ((n : ℝ) + 1)))
          atTop (𝓝 0) := by
        have hconst : Tendsto (fun _ : ℕ => -x) atTop (𝓝 (-x)) := tendsto_const_nhds
        simpa using
          hconst.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa [r] using (tendsto_const_nhds.add hzero).neg
    have hr_nonneg (n : ℕ) : 0 ≤ r n := by
      have hdiv : 1 / ((n : ℝ) + 1) ≤ 1 := by
        simpa using (Nat.one_div_le_one_div (α := ℝ) (Nat.zero_le n))
      have hmul : (-x) * (1 / ((n : ℝ) + 1)) ≤ -x := by
        simpa using mul_le_mul_of_nonneg_left hdiv (neg_nonneg.mpr hxneg.le)
      dsimp [r]
      linarith
    have hν_limit :
        Tendsto (fun n => 1 - cdf (ν.map fun z : ℝ => -z) (r n))
          atTop (𝓝 (cdf ν x)) := by
      simpa [r] using tendsto_one_sub_cdf_map_neg_of_neg ν hxneg
    have hgaussian_limit :
        Tendsto (fun n => 1 - cdf (gaussianReal 0 1) (r n))
          atTop (𝓝 (cdf (gaussianReal 0 1) x)) := by
      simpa [r, gaussianReal_map_neg] using
        tendsto_one_sub_cdf_map_neg_of_neg (gaussianReal 0 1) hxneg
    have hlhs :
        Tendsto
          (fun n =>
            |cdf (ν.map fun z : ℝ => -z) (r n) - cdf (gaussianReal 0 1) (r n)|)
          atTop
          (𝓝 |cdf ν x - cdf (gaussianReal 0 1) x|) := by
      simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using
        (hν_limit.sub hgaussian_limit).abs
    have hrhs :
        Tendsto (fun n => K / (1 + (r n) ^ 3)) atTop
          (𝓝 (K / (1 + (-x) ^ 3))) := by
      exact tendsto_const_nhds.div (tendsto_const_nhds.add (hr_tendsto.pow 3))
        (by
          have hy : 0 < -x := neg_pos.mpr hxneg
          exact ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (pow_nonneg hy.le 3)))
    have hdiff := hlhs.sub hrhs
    have hle :
        |cdf ν x - cdf (gaussianReal 0 1) x| - K / (1 + (-x) ^ 3) ≤ 0 :=
      le_of_tendsto' hdiff fun n => sub_nonpos.mpr (hneg (r n) (hr_nonneg n))
    simpa [abs_of_neg hxneg] using sub_nonpos.mp hle

end ProbabilityTheory
