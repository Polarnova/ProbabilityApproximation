/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.ChenShao.UpperTruncation
import ProbabilityApproximation.ChenShao.UniformBerryEsseen

/-!
# Stein exchange for one-sided truncated sums

This module records the noncentered leave-one-out Stein identity needed for Chen--Shao (2005),
(6.16), and specializes it to the coordinatewise one-sided truncated family.
-/

open MeasureTheory ProbabilityTheory Real Filter

noncomputable section

namespace ProbabilityTheory

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {Y : ι → Ω → ℝ}

private lemma integrable_steinSolution_comp
    {V : Ω → ℝ} (hVmeas : Measurable V) (z : ℝ) :
    Integrable (fun ω => steinSolution z (V ω)) μ := by
  refine (integrable_const (μ := μ) (sqrt (2 * π) / 2)).mono' ?_ ?_
  · exact (continuous_steinSolution z).comp_aestronglyMeasurable hVmeas.aestronglyMeasurable
  · filter_upwards with ω
    simpa [Real.norm_eq_abs] using abs_steinSolution_le_sqrt_two_pi_div_two z (V ω)

private lemma integrable_mul_steinSolution_comp
    {U V : Ω → ℝ} (hU : MemLp U 2 μ) (hUmeas : Measurable U)
    (hVmeas : Measurable V) (z : ℝ) :
    Integrable (fun ω => U ω * steinSolution z (V ω)) μ := by
  have hUint := hU.integrable one_le_two
  refine (hUint.abs.const_mul (sqrt (2 * π) / 2)).mono' ?_ ?_
  · exact hUmeas.aestronglyMeasurable.mul
      ((continuous_steinSolution z).comp_aestronglyMeasurable hVmeas.aestronglyMeasurable)
  · filter_upwards with ω
    have hf := abs_steinSolution_le_sqrt_two_pi_div_two z (V ω)
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |U ω| * |steinSolution z (V ω)| ≤ |U ω| * (sqrt (2 * π) / 2) := by gcongr
      _ = (sqrt (2 * π) / 2) * |U ω| := mul_comm _ _

private lemma integral_coordinate_stein_eq_kernel_add_mean
    [DecidableEq ι]
    (hY : ∀ k, MemLp (Y k) 2 μ) (hYmeas : ∀ k, Measurable (Y k))
    (h_indep : iIndepFun Y μ) (i : ι) (z : ℝ) :
    ∫ ω, Y i ω * steinSolution z (sumX Y ω) ∂μ =
      (∫ ω, (∫ t : ℝ,
        kernelDensityFwd (Y i ω) t *
          steinSolutionDeriv z (leaveOneOut Y i ω + t)) ∂μ) +
      (∫ ω, Y i ω ∂μ) *
        ∫ ω, steinSolution z (leaveOneOut Y i ω) ∂μ := by
  have hsumMeas : Measurable (sumX Y) := measurable_sumX hYmeas
  have hlooMeas : Measurable (leaveOneOut Y i) := measurable_leaveOneOut hYmeas i
  have hfull : Integrable (fun ω => Y i ω * steinSolution z (sumX Y ω)) μ :=
    integrable_mul_steinSolution_comp (hY i) (hYmeas i) hsumMeas z
  have hbase : Integrable
      (fun ω => Y i ω * steinSolution z (leaveOneOut Y i ω)) μ :=
    integrable_mul_steinSolution_comp (hY i) (hYmeas i) hlooMeas z
  have hsteinBase : Integrable (fun ω => steinSolution z (leaveOneOut Y i ω)) μ :=
    integrable_steinSolution_comp hlooMeas z
  have hexchange (ω : Ω) :
      Y i ω * (steinSolution z (sumX Y ω) - steinSolution z (leaveOneOut Y i ω)) =
        ∫ t : ℝ, kernelDensityFwd (Y i ω) t *
          steinSolutionDeriv z (leaveOneOut Y i ω + t) := by
    have hsum : sumX Y ω = leaveOneOut Y i ω + Y i ω := leaveOneOut_add i ω
    rw [hsum]
    exact mul_steinSolution_add_eq_integral_kernelFwd z (leaveOneOut Y i ω) (Y i ω)
  have hdiff : Integrable
      (fun ω => Y i ω *
        (steinSolution z (sumX Y ω) - steinSolution z (leaveOneOut Y i ω))) μ := by
    have heq :
        (fun ω => Y i ω *
          (steinSolution z (sumX Y ω) - steinSolution z (leaveOneOut Y i ω))) =
          fun ω => Y i ω * steinSolution z (sumX Y ω) -
            Y i ω * steinSolution z (leaveOneOut Y i ω) := by
      funext ω
      ring
    rw [heq]
    exact hfull.sub hbase
  have hkernel : Integrable
      (fun ω => ∫ t : ℝ, kernelDensityFwd (Y i ω) t *
        steinSolutionDeriv z (leaveOneOut Y i ω + t)) μ :=
    hdiff.congr (Eventually.of_forall hexchange)
  have hfactor :
      ∫ ω, Y i ω * steinSolution z (leaveOneOut Y i ω) ∂μ =
        (∫ ω, Y i ω ∂μ) *
          ∫ ω, steinSolution z (leaveOneOut Y i ω) ∂μ := by
    have hInd :
        IndepFun (Y i) (fun ω => steinSolution z (leaveOneOut Y i ω)) μ := by
      simpa [Function.comp_def] using
        (indepFun_leaveOneOut (X := Y) (μ := μ) hYmeas h_indep i).symm.comp
          (φ := id) (ψ := steinSolution z) measurable_id
          (continuous_steinSolution z).measurable
    exact hInd.integral_fun_mul_eq_mul_integral
      (hYmeas i).aestronglyMeasurable
      hsteinBase.aestronglyMeasurable
  calc
    ∫ ω, Y i ω * steinSolution z (sumX Y ω) ∂μ =
        ∫ ω, ((∫ t : ℝ, kernelDensityFwd (Y i ω) t *
          steinSolutionDeriv z (leaveOneOut Y i ω + t)) +
            Y i ω * steinSolution z (leaveOneOut Y i ω)) ∂μ := by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      calc
        Y i ω * steinSolution z (sumX Y ω) =
            Y i ω * (steinSolution z (sumX Y ω) -
              steinSolution z (leaveOneOut Y i ω)) +
              Y i ω * steinSolution z (leaveOneOut Y i ω) := by ring
        _ = (∫ t : ℝ, kernelDensityFwd (Y i ω) t *
              steinSolutionDeriv z (leaveOneOut Y i ω + t)) +
              Y i ω * steinSolution z (leaveOneOut Y i ω) := by rw [hexchange]
    _ = (∫ ω, (∫ t : ℝ, kernelDensityFwd (Y i ω) t *
          steinSolutionDeriv z (leaveOneOut Y i ω + t)) ∂μ) +
          ∫ ω, Y i ω * steinSolution z (leaveOneOut Y i ω) ∂μ :=
      integral_add hkernel hbase
    _ = (∫ ω, (∫ t : ℝ, kernelDensityFwd (Y i ω) t *
          steinSolutionDeriv z (leaveOneOut Y i ω + t)) ∂μ) +
          (∫ ω, Y i ω ∂μ) *
            ∫ ω, steinSolution z (leaveOneOut Y i ω) ∂μ := by rw [hfactor]

/-- Noncentered leave-one-out Stein exchange.  The second sum is the mean correction that vanishes
for centered coordinates but must be retained for one-sided truncations. -/
theorem stein_identity_sum_leaveOneOut_noncentered
    [DecidableEq ι]
    (hY : ∀ k, MemLp (Y k) 2 μ) (hYmeas : ∀ k, Measurable (Y k))
    (h_indep : iIndepFun Y μ) (z : ℝ) :
    ∫ ω, sumX Y ω * steinSolution z (sumX Y ω) ∂μ =
      (∑ i : ι, ∫ ω, (∫ t : ℝ,
        kernelDensityFwd (Y i ω) t *
          steinSolutionDeriv z (leaveOneOut Y i ω + t)) ∂μ) +
      ∑ i : ι, (∫ ω, Y i ω ∂μ) *
        ∫ ω, steinSolution z (leaveOneOut Y i ω) ∂μ := by
  have hterm (i : ι) :
      Integrable (fun ω => Y i ω * steinSolution z (sumX Y ω)) μ :=
    integrable_mul_steinSolution_comp (hY i) (hYmeas i) (measurable_sumX hYmeas) z
  calc
    ∫ ω, sumX Y ω * steinSolution z (sumX Y ω) ∂μ =
        ∑ i : ι, ∫ ω, Y i ω * steinSolution z (sumX Y ω) ∂μ := by
      have hfun :
          (fun ω => sumX Y ω * steinSolution z (sumX Y ω)) =
            fun ω => ∑ i : ι, Y i ω * steinSolution z (sumX Y ω) := by
        funext ω
        simp only [sumX, Finset.sum_mul]
      rw [hfun, integral_finsetSum _ fun i _ => hterm i]
    _ = ∑ i : ι,
        ((∫ ω, (∫ t : ℝ, kernelDensityFwd (Y i ω) t *
          steinSolutionDeriv z (leaveOneOut Y i ω + t)) ∂μ) +
          (∫ ω, Y i ω ∂μ) *
            ∫ ω, steinSolution z (leaveOneOut Y i ω) ∂μ) :=
      Finset.sum_congr rfl fun i _ =>
        integral_coordinate_stein_eq_kernel_add_mean hY hYmeas h_indep i z
    _ = (∑ i : ι, ∫ ω, (∫ t : ℝ,
        kernelDensityFwd (Y i ω) t *
          steinSolutionDeriv z (leaveOneOut Y i ω + t)) ∂μ) +
        ∑ i : ι, (∫ ω, Y i ω ∂μ) *
          ∫ ω, steinSolution z (leaveOneOut Y i ω) ∂μ :=
      Finset.sum_add_distrib

/-- Chen--Shao (2005), (6.16): the noncentered Stein exchange for the one-sided truncated family. -/
theorem stein_identity_upperTruncatedSum
    [DecidableEq ι] {X : ι → Ω → ℝ}
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (z : ℝ) :
    ∫ ω, upperTruncatedSum X ω * steinSolution z (upperTruncatedSum X ω) ∂μ =
      (∑ i : ι, ∫ ω, (∫ t : ℝ,
        kernelDensityFwd (upperTruncatedFamily X i ω) t *
          steinSolutionDeriv z
            (leaveOneOut (upperTruncatedFamily X) i ω + t)) ∂μ) +
      ∑ i : ι, (∫ ω, upperTruncatedFamily X i ω ∂μ) *
        ∫ ω, steinSolution z (leaveOneOut (upperTruncatedFamily X) i ω) ∂μ := by
  simpa only [upperTruncatedSum] using
    stein_identity_sum_leaveOneOut_noncentered
      (memLp_upperTruncatedFamily hXmeas hX)
      (measurable_upperTruncatedFamily hXmeas)
      (iIndepFun_upperTruncatedFamily h_indep) z

end ProbabilityTheory
