/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.ChenShao.UpperTruncatedResidual

/-!
# Expected-kernel form of the upper-truncated residual

This module converts the algebraic upper-truncated residual into the deterministic
expected-kernel form used after Chen--Shao (2005), equation (6.16).  It then splits the
derivative residual exactly into its indicator and Stein-product components.  No numerical
estimate is made here.
-/

open MeasureTheory ProbabilityTheory Real Filter

noncomputable section

namespace ProbabilityTheory

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ι → Ω → ℝ}

/-- The expected forward kernel of the one-sided truncated coordinate `X̄ᵢ`. -/
def upperTruncatedExpectedKernel
    (X : ι → Ω → ℝ) (μ : Measure Ω) (i : ι) (t : ℝ) : ℝ :=
  expectedKernelFwd (X := upperTruncatedFamily X) (μ := μ) i t

lemma upperTruncatedExpectedKernel_nonneg [DecidableEq ι] (i : ι) (t : ℝ) :
    0 ≤ upperTruncatedExpectedKernel X μ i t :=
  expectedKernelFwd_nonneg i t

lemma integral_upperTruncatedExpectedKernel
    [DecidableEq ι]
    (hX2 : ∀ i, MemLp (X i) 2 μ) (hXmeas : ∀ i, Measurable (X i)) (i : ι) :
    ∫ t : ℝ, upperTruncatedExpectedKernel X μ i t =
      ∫ ω, upperTruncatedFamily X i ω ^ 2 ∂μ := by
  exact integral_expectedKernelFwd i
    (memLp_upperTruncatedFamily hXmeas hX2 i)
    (measurable_upperTruncatedFamily hXmeas i)

lemma integrable_upperTruncatedExpectedKernel
    [DecidableEq ι]
    (hX2 : ∀ i, MemLp (X i) 2 μ) (hXmeas : ∀ i, Measurable (X i)) (i : ι) :
    Integrable (upperTruncatedExpectedKernel X μ i) := by
  exact integrable_expectedKernelFwd i
    (memLp_upperTruncatedFamily hXmeas hX2 i)
    (measurable_upperTruncatedFamily hXmeas i)

private lemma integrable_upperTruncatedKernelDerivative_uncurry
    [DecidableEq ι]
    (hX2 : ∀ i, MemLp (X i) 2 μ) (hXmeas : ∀ i, Measurable (X i))
    (z : ℝ) (i : ι) :
    Integrable (fun p : Ω × ℝ =>
      kernelDensityFwd (upperTruncatedFamily X i p.1) p.2 *
        steinSolutionDeriv z
          (leaveOneOut (upperTruncatedFamily X) i p.1 + p.2)) (μ.prod volume) := by
  let Y := upperTruncatedFamily X
  have hY2 : ∀ j, MemLp (Y j) 2 μ := memLp_upperTruncatedFamily hXmeas hX2
  have hYmeas : ∀ j, Measurable (Y j) := measurable_upperTruncatedFamily hXmeas
  have hK := integrable_uncurry_kernelDensityFwd i (hY2 i) (hYmeas i)
  have hsm : AEStronglyMeasurable (fun p : Ω × ℝ =>
      kernelDensityFwd (Y i p.1) p.2 *
        steinSolutionDeriv z (leaveOneOut Y i p.1 + p.2)) (μ.prod volume) :=
    ((measurable_kernelDensityFwd_pair i (hYmeas i)).mul
      ((measurable_steinSolutionDeriv z).comp
        (((measurable_leaveOneOut hYmeas i).comp measurable_fst).add
          measurable_snd))).aestronglyMeasurable
  refine (hK.const_mul 2).mono' hsm ?_
  filter_upwards with p
  have hK0 := kernelDensityFwd_nonneg (Y i p.1) p.2
  have hderiv := abs_steinSolutionDeriv_le_two z (leaveOneOut Y i p.1 + p.2)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK0]
  calc
    kernelDensityFwd (Y i p.1) p.2 *
          |steinSolutionDeriv z (leaveOneOut Y i p.1 + p.2)| ≤
        kernelDensityFwd (Y i p.1) p.2 * 2 :=
      mul_le_mul_of_nonneg_left hderiv hK0
    _ = 2 * kernelDensityFwd (Y i p.1) p.2 := by ring

private lemma integral_upperTruncatedDeriv_mul_kernel_eq_mul
    [DecidableEq ι]
    (hX2 : ∀ i, MemLp (X i) 2 μ) (hXmeas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ) (z : ℝ) (i : ι) (t : ℝ) :
    ∫ ω, steinSolutionDeriv z
          (leaveOneOut (upperTruncatedFamily X) i ω + t) *
        kernelDensityFwd (upperTruncatedFamily X i ω) t ∂μ =
      (∫ ω, steinSolutionDeriv z
        (leaveOneOut (upperTruncatedFamily X) i ω + t) ∂μ) *
        upperTruncatedExpectedKernel X μ i t := by
  let Y := upperTruncatedFamily X
  have hY2 : ∀ j, MemLp (Y j) 2 μ := memLp_upperTruncatedFamily hXmeas hX2
  have hYmeas : ∀ j, Measurable (Y j) := measurable_upperTruncatedFamily hXmeas
  have hYindep : iIndepFun Y μ := iIndepFun_upperTruncatedFamily h_indep
  have hInd := indepFun_leaveOneOut (X := Y) (μ := μ) hYmeas hYindep i
  have hg : Measurable fun w : ℝ => steinSolutionDeriv z (w + t) :=
    (measurable_steinSolutionDeriv z).comp (measurable_id.add_const t)
  have hK : Measurable fun ξ : ℝ => kernelDensityFwd ξ t :=
    measurable_kernelDensityFwd_left t
  have hindep :
      IndepFun (fun ω => steinSolutionDeriv z (leaveOneOut Y i ω + t))
        (fun ω => kernelDensityFwd (Y i ω) t) μ :=
    hInd.comp hg hK
  have hIntg : Integrable
      (fun ω => steinSolutionDeriv z (leaveOneOut Y i ω + t)) μ := by
    refine (integrable_const (μ := μ) (2 : ℝ)).mono' ?_ ?_
    · exact (hg.comp (measurable_leaveOneOut hYmeas i)).aestronglyMeasurable
    · filter_upwards with ω
      simpa [Real.norm_eq_abs] using
        abs_steinSolutionDeriv_le_two z (leaveOneOut Y i ω + t)
  have hIntK := integrable_kernelDensityFwd_eval i (hY2 i) (hYmeas i) t
  have hfactor := hindep.integral_mul_eq_mul_integral
    hIntg.aestronglyMeasurable hIntK.aestronglyMeasurable
  simpa [Y, upperTruncatedExpectedKernel, expectedKernelFwd] using hfactor

/-- Fubini and leave-one-out independence turn the random kernel exchange into a deterministic
expected-kernel integral. -/
theorem upperTruncatedKernelDerivativeTerm_eq_sum_integral_expectedKernel
    [DecidableEq ι]
    (hX2 : ∀ i, MemLp (X i) 2 μ) (hXmeas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ) (z : ℝ) :
    upperTruncatedKernelDerivativeTerm X μ z =
      ∑ i : ι, ∫ t : ℝ,
        (∫ ω, steinSolutionDeriv z
          (leaveOneOut (upperTruncatedFamily X) i ω + t) ∂μ) *
          upperTruncatedExpectedKernel X μ i t := by
  unfold upperTruncatedKernelDerivativeTerm
  refine Finset.sum_congr rfl fun i _ => ?_
  let g : Ω × ℝ → ℝ := fun p =>
    kernelDensityFwd (upperTruncatedFamily X i p.1) p.2 *
      steinSolutionDeriv z
        (leaveOneOut (upperTruncatedFamily X) i p.1 + p.2)
  have hInt : Integrable g (μ.prod volume) :=
    integrable_upperTruncatedKernelDerivative_uncurry hX2 hXmeas z i
  calc
    ∫ ω, (∫ t : ℝ,
        kernelDensityFwd (upperTruncatedFamily X i ω) t *
          steinSolutionDeriv z
            (leaveOneOut (upperTruncatedFamily X) i ω + t)) ∂μ =
        ∫ p, g p ∂(μ.prod volume) := integral_integral hInt
    _ = ∫ t : ℝ, ∫ ω, g (ω, t) ∂μ := integral_prod_symm g hInt
    _ = ∫ t : ℝ,
        (∫ ω, steinSolutionDeriv z
          (leaveOneOut (upperTruncatedFamily X) i ω + t) ∂μ) *
          upperTruncatedExpectedKernel X μ i t := by
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      calc
        ∫ ω, g (ω, t) ∂μ =
            ∫ ω, steinSolutionDeriv z
                (leaveOneOut (upperTruncatedFamily X) i ω + t) *
              kernelDensityFwd (upperTruncatedFamily X i ω) t ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          dsimp [g]
          ring
        _ = (∫ ω, steinSolutionDeriv z
              (leaveOneOut (upperTruncatedFamily X) i ω + t) ∂μ) *
            upperTruncatedExpectedKernel X μ i t :=
          integral_upperTruncatedDeriv_mul_kernel_eq_mul
            hX2 hXmeas h_indep z i t

/-- The retained truncated second-moment mass is exactly the total expected-kernel mass. -/
theorem one_sub_upperTruncatedMissingSecondMoment_eq_sum_integral_expectedKernel
    [DecidableEq ι]
    (hX2 : ∀ i, MemLp (X i) 2 μ) (hXmeas : ∀ i, Measurable (X i)) :
    1 - upperTruncatedMissingSecondMoment X μ =
      ∑ i : ι, ∫ t : ℝ, upperTruncatedExpectedKernel X μ i t := by
  calc
    1 - upperTruncatedMissingSecondMoment X μ =
        ∑ i : ι, ∫ ω, upperTruncatedFamily X i ω ^ 2 ∂μ := by
      simp only [upperTruncatedMissingSecondMoment]
      ring
    _ = ∑ i : ι, ∫ t : ℝ, upperTruncatedExpectedKernel X μ i t :=
      Finset.sum_congr rfl fun i _ =>
        (integral_upperTruncatedExpectedKernel hX2 hXmeas i).symm

private lemma integrable_upperTruncatedDerivExpectedKernel
    [DecidableEq ι]
    (hX2 : ∀ i, MemLp (X i) 2 μ) (hXmeas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ) (z : ℝ) (i : ι) :
    Integrable (fun t : ℝ =>
      (∫ ω, steinSolutionDeriv z
        (leaveOneOut (upperTruncatedFamily X) i ω + t) ∂μ) *
        upperTruncatedExpectedKernel X μ i t) := by
  let g : Ω × ℝ → ℝ := fun p =>
    kernelDensityFwd (upperTruncatedFamily X i p.1) p.2 *
      steinSolutionDeriv z
        (leaveOneOut (upperTruncatedFamily X) i p.1 + p.2)
  have hInt : Integrable g (μ.prod volume) :=
    integrable_upperTruncatedKernelDerivative_uncurry hX2 hXmeas z i
  have hright := hInt.integral_prod_right
  have heq :
      (fun t : ℝ => ∫ ω, g (ω, t) ∂μ) =
        fun t : ℝ =>
          (∫ ω, steinSolutionDeriv z
            (leaveOneOut (upperTruncatedFamily X) i ω + t) ∂μ) *
            upperTruncatedExpectedKernel X μ i t := by
    funext t
    calc
      ∫ ω, g (ω, t) ∂μ =
          ∫ ω, steinSolutionDeriv z
              (leaveOneOut (upperTruncatedFamily X) i ω + t) *
            kernelDensityFwd (upperTruncatedFamily X i ω) t ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        dsimp [g]
        ring
      _ = (∫ ω, steinSolutionDeriv z
            (leaveOneOut (upperTruncatedFamily X) i ω + t) ∂μ) *
          upperTruncatedExpectedKernel X μ i t :=
        integral_upperTruncatedDeriv_mul_kernel_eq_mul
          hX2 hXmeas h_indep z i t
  simpa only [heq] using hright

/-- Deterministic expected-kernel form of `R₂`. -/
theorem upperTruncatedR2_eq_sum_integral_expectedKernel
    [DecidableEq ι]
    (hX2 : ∀ i, MemLp (X i) 2 μ) (hXmeas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ) (z : ℝ) :
    upperTruncatedR2 X μ z =
      ∑ i : ι, ∫ t : ℝ,
        ((∫ ω, steinSolutionDeriv z (upperTruncatedSum X ω) ∂μ) -
          ∫ ω, steinSolutionDeriv z
            (leaveOneOut (upperTruncatedFamily X) i ω + t) ∂μ) *
          upperTruncatedExpectedKernel X μ i t := by
  let F : ℝ := ∫ ω, steinSolutionDeriv z (upperTruncatedSum X ω) ∂μ
  have hmass := one_sub_upperTruncatedMissingSecondMoment_eq_sum_integral_expectedKernel
    (X := X) hX2 hXmeas
  have hkernel := upperTruncatedKernelDerivativeTerm_eq_sum_integral_expectedKernel
    (X := X) hX2 hXmeas h_indep z
  have hfull :
      (1 - upperTruncatedMissingSecondMoment X μ) * F =
        ∑ i : ι, ∫ t : ℝ, F * upperTruncatedExpectedKernel X μ i t := by
    rw [hmass, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
    ring
  rw [upperTruncatedR2, hkernel]
  change (1 - upperTruncatedMissingSecondMoment X μ) * F -
      ∑ i : ι, ∫ t : ℝ,
        (∫ ω, steinSolutionDeriv z
          (leaveOneOut (upperTruncatedFamily X) i ω + t) ∂μ) *
          upperTruncatedExpectedKernel X μ i t = _
  rw [hfull, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hFint : Integrable
      (fun t : ℝ => F * upperTruncatedExpectedKernel X μ i t) :=
    (integrable_upperTruncatedExpectedKernel hX2 hXmeas i).const_mul F
  have hGint := integrable_upperTruncatedDerivExpectedKernel
    hX2 hXmeas h_indep z i
  rw [← integral_sub hFint hGint]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp [F]
  ring

/-- `R₂,₁`: the indicator jump in the expected-kernel representation of `R₂`. -/
def upperTruncatedR21 [DecidableEq ι]
    (X : ι → Ω → ℝ) (μ : Measure Ω) (z : ℝ) : ℝ :=
  ∑ i : ι, ∫ t : ℝ,
    ((∫ ω, (if upperTruncatedSum X ω ≤ z then (1 : ℝ) else 0) ∂μ) -
      ∫ ω, (if leaveOneOut (upperTruncatedFamily X) i ω + t ≤ z
        then (1 : ℝ) else 0) ∂μ) *
      upperTruncatedExpectedKernel X μ i t

/-- `R₂,₂`: the increment of `w ↦ w f_z(w)` in the expected-kernel representation of `R₂`. -/
def upperTruncatedR22 [DecidableEq ι]
    (X : ι → Ω → ℝ) (μ : Measure Ω) (z : ℝ) : ℝ :=
  ∑ i : ι, ∫ t : ℝ,
    ((∫ ω, upperTruncatedSum X ω *
        steinSolution z (upperTruncatedSum X ω) ∂μ) -
      ∫ ω, (leaveOneOut (upperTruncatedFamily X) i ω + t) *
        steinSolution z
          (leaveOneOut (upperTruncatedFamily X) i ω + t) ∂μ) *
      upperTruncatedExpectedKernel X μ i t

private lemma integrable_steinIntegrand_comp
    {V : Ω → ℝ} (hVmeas : Measurable V) (z : ℝ) :
    Integrable (fun ω => steinIntegrand z (V ω)) μ := by
  refine (integrable_const (μ := μ) (1 : ℝ)).mono' ?_ ?_
  · exact ((measurable_steinIntegrand z).comp hVmeas).aestronglyMeasurable
  · filter_upwards with ω
    simpa [Real.norm_eq_abs] using steinIntegrand_abs_le z (V ω)

private lemma integrable_indicator_comp
    {V : Ω → ℝ} (hVmeas : Measurable V) (z : ℝ) :
    Integrable (fun ω => if V ω ≤ z then (1 : ℝ) else 0) μ := by
  refine (integrable_const (μ := μ) (1 : ℝ)).mono' ?_ ?_
  · exact (Measurable.ite
      (measurableSet_le hVmeas measurable_const)
      measurable_const measurable_const).aestronglyMeasurable
  · filter_upwards with ω
    split_ifs <;> simp

private lemma integral_steinSolutionDeriv_comp_eq_product_add_steinIntegrand
    {V : Ω → ℝ} (hVmeas : Measurable V) (z : ℝ) :
    ∫ ω, steinSolutionDeriv z (V ω) ∂μ =
      (∫ ω, V ω * steinSolution z (V ω) ∂μ) +
        ∫ ω, steinIntegrand z (V ω) ∂μ := by
  have hproduct : Integrable (fun ω => V ω * steinSolution z (V ω)) μ := by
    refine (integrable_const (μ := μ) (1 : ℝ)).mono' ?_ ?_
    · exact hVmeas.mul
        ((continuous_steinSolution z).measurable.comp hVmeas) |>.aestronglyMeasurable
    · filter_upwards with ω
      simpa [Real.norm_eq_abs, abs_mul] using abs_mul_steinSolution_le_one z (V ω)
  have hstein := integrable_steinIntegrand_comp (μ := μ) hVmeas z
  have hfun :
      (fun ω => steinSolutionDeriv z (V ω)) =
        fun ω => V ω * steinSolution z (V ω) + steinIntegrand z (V ω) := by
    funext ω
    exact steinSolutionDeriv_eq z (V ω)
  rw [hfun, integral_add hproduct hstein]

private lemma upperTruncatedDerivExpectation_sub_eq_indicator_add_product
    [DecidableEq ι]
    (hXmeas : ∀ i, Measurable (X i)) (z : ℝ) (i : ι) (t : ℝ) :
    (∫ ω, steinSolutionDeriv z (upperTruncatedSum X ω) ∂μ) -
        ∫ ω, steinSolutionDeriv z
          (leaveOneOut (upperTruncatedFamily X) i ω + t) ∂μ =
      ((∫ ω, (if upperTruncatedSum X ω ≤ z then (1 : ℝ) else 0) ∂μ) -
        ∫ ω, (if leaveOneOut (upperTruncatedFamily X) i ω + t ≤ z
          then (1 : ℝ) else 0) ∂μ) +
      ((∫ ω, upperTruncatedSum X ω *
          steinSolution z (upperTruncatedSum X ω) ∂μ) -
        ∫ ω, (leaveOneOut (upperTruncatedFamily X) i ω + t) *
          steinSolution z
            (leaveOneOut (upperTruncatedFamily X) i ω + t) ∂μ) := by
  have hYmeas := measurable_upperTruncatedFamily hXmeas
  have hfullMeas : Measurable (upperTruncatedSum X) := by
    simpa only [upperTruncatedSum] using measurable_sumX hYmeas
  have hleaveMeas : Measurable
      (fun ω => leaveOneOut (upperTruncatedFamily X) i ω + t) :=
    (measurable_leaveOneOut hYmeas i).add_const t
  have hfull := integral_steinSolutionDeriv_comp_eq_product_add_steinIntegrand
    (μ := μ) (V := upperTruncatedSum X) hfullMeas z
  have hleave := integral_steinSolutionDeriv_comp_eq_product_add_steinIntegrand
    (μ := μ) (V := fun ω => leaveOneOut (upperTruncatedFamily X) i ω + t)
      hleaveMeas z
  have hsteinFull := integrable_steinIntegrand_comp (μ := μ) hfullMeas z
  have hsteinLeave := integrable_steinIntegrand_comp (μ := μ) hleaveMeas z
  have hindicatorFull := integrable_indicator_comp (μ := μ) hfullMeas z
  have hindicatorLeave := integrable_indicator_comp (μ := μ) hleaveMeas z
  have hsteinDiff :
      (∫ ω, steinIntegrand z (upperTruncatedSum X ω) ∂μ) -
          ∫ ω, steinIntegrand z
            (leaveOneOut (upperTruncatedFamily X) i ω + t) ∂μ =
        (∫ ω, (if upperTruncatedSum X ω ≤ z then (1 : ℝ) else 0) ∂μ) -
          ∫ ω, (if leaveOneOut (upperTruncatedFamily X) i ω + t ≤ z
            then (1 : ℝ) else 0) ∂μ := by
    rw [← integral_sub hsteinFull hsteinLeave,
      ← integral_sub hindicatorFull hindicatorLeave]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    unfold steinIntegrand
    ring
  rw [hfull, hleave]
  linear_combination hsteinDiff

private lemma integrable_upperTruncatedLeaveOneOutIndicatorExpectedKernel
    [DecidableEq ι]
    (hX2 : ∀ i, MemLp (X i) 2 μ) (hXmeas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ) (z : ℝ) (i : ι) :
    Integrable (fun t : ℝ =>
      (∫ ω, (if leaveOneOut (upperTruncatedFamily X) i ω + t ≤ z
        then (1 : ℝ) else 0) ∂μ) *
        upperTruncatedExpectedKernel X μ i t) := by
  let Y := upperTruncatedFamily X
  have hY2 : ∀ j, MemLp (Y j) 2 μ := memLp_upperTruncatedFamily hXmeas hX2
  have hYmeas : ∀ j, Measurable (Y j) := measurable_upperTruncatedFamily hXmeas
  have hYindep : iIndepFun Y μ := iIndepFun_upperTruncatedFamily h_indep
  let g : Ω × ℝ → ℝ := fun p =>
    kernelDensityFwd (Y i p.1) p.2 *
      (if leaveOneOut Y i p.1 + p.2 ≤ z then (1 : ℝ) else 0)
  have hInt : Integrable g (μ.prod volume) :=
    integrable_uncurry_kernel_mul_indicator hY2 hYmeas z i
  have hright := hInt.integral_prod_right
  have heq :
      (fun t : ℝ => ∫ ω, g (ω, t) ∂μ) =
        fun t : ℝ =>
          (∫ ω, (if leaveOneOut Y i ω + t ≤ z then (1 : ℝ) else 0) ∂μ) *
            expectedKernelFwd (X := Y) (μ := μ) i t := by
    funext t
    have hrawCdf :
        (∫ ω, (if leaveOneOut Y i ω + t ≤ z then (1 : ℝ) else 0) ∂μ) =
          leaveOneOutCdf (X := Y) (μ := μ) i (z - t) := by
      have hfun :
          (fun ω => if leaveOneOut Y i ω + t ≤ z then (1 : ℝ) else 0) =
            fun ω => if leaveOneOut Y i ω ≤ z - t then (1 : ℝ) else 0 := by
        funext ω
        by_cases h : leaveOneOut Y i ω + t ≤ z
        · have h' : leaveOneOut Y i ω ≤ z - t := by linarith
          simp [h, h']
        · have h' : ¬leaveOneOut Y i ω ≤ z - t := by linarith
          simp [h, h']
      rw [hfun, integral_leaveOneOut_indicator_eq_cdf hYmeas i]
    calc
      ∫ ω, g (ω, t) ∂μ =
          ∫ ω, (if leaveOneOut Y i ω + t ≤ z then (1 : ℝ) else 0) *
            kernelDensityFwd (Y i ω) t ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        dsimp [g]
        ring
      _ = leaveOneOutCdf (X := Y) (μ := μ) i (z - t) *
          expectedKernelFwd (X := Y) (μ := μ) i t :=
        integral_indicator_mul_kernel_eq_mul hY2 hYmeas hYindep z i t
      _ = (∫ ω, (if leaveOneOut Y i ω + t ≤ z then (1 : ℝ) else 0) ∂μ) *
          expectedKernelFwd (X := Y) (μ := μ) i t := by rw [hrawCdf]
  change Integrable (fun t : ℝ =>
    (∫ ω, (if leaveOneOut Y i ω + t ≤ z then (1 : ℝ) else 0) ∂μ) *
      expectedKernelFwd (X := Y) (μ := μ) i t)
  simpa only [heq] using hright

private lemma integrable_upperTruncatedLeaveOneOutSteinProductExpectedKernel
    [DecidableEq ι]
    (hX2 : ∀ i, MemLp (X i) 2 μ) (hXmeas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ) (z : ℝ) (i : ι) :
    Integrable (fun t : ℝ =>
      (∫ ω, (leaveOneOut (upperTruncatedFamily X) i ω + t) *
        steinSolution z
          (leaveOneOut (upperTruncatedFamily X) i ω + t) ∂μ) *
        upperTruncatedExpectedKernel X μ i t) := by
  let Y := upperTruncatedFamily X
  have hY2 : ∀ j, MemLp (Y j) 2 μ := memLp_upperTruncatedFamily hXmeas hX2
  have hYmeas : ∀ j, Measurable (Y j) := measurable_upperTruncatedFamily hXmeas
  have hYindep : iIndepFun Y μ := iIndepFun_upperTruncatedFamily h_indep
  let g : Ω × ℝ → ℝ := fun p =>
    kernelDensityFwd (Y i p.1) p.2 *
      ((leaveOneOut Y i p.1 + p.2) *
        steinSolution z (leaveOneOut Y i p.1 + p.2))
  have hInt : Integrable g (μ.prod volume) :=
    integrable_uncurry_kernel_mul_steinProduct hY2 hYmeas z i
  have hright := hInt.integral_prod_right
  have heq :
      (fun t : ℝ => ∫ ω, g (ω, t) ∂μ) =
        fun t : ℝ =>
          (∫ ω, (leaveOneOut Y i ω + t) *
            steinSolution z (leaveOneOut Y i ω + t) ∂μ) *
            expectedKernelFwd (X := Y) (μ := μ) i t := by
    funext t
    calc
      ∫ ω, g (ω, t) ∂μ =
          ∫ ω, ((leaveOneOut Y i ω + t) *
            steinSolution z (leaveOneOut Y i ω + t)) *
              kernelDensityFwd (Y i ω) t ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        dsimp [g]
        ring
      _ = (∫ ω, (leaveOneOut Y i ω + t) *
            steinSolution z (leaveOneOut Y i ω + t) ∂μ) *
          expectedKernelFwd (X := Y) (μ := μ) i t :=
        integral_stein_mul_kernel_eq_mul hY2 hYmeas hYindep z i t
  change Integrable (fun t : ℝ =>
    (∫ ω, (leaveOneOut Y i ω + t) *
      steinSolution z (leaveOneOut Y i ω + t) ∂μ) *
        expectedKernelFwd (X := Y) (μ := μ) i t)
  simpa only [heq] using hright

private lemma integrable_upperTruncatedIndicatorResidualIntegrand
    [DecidableEq ι]
    (hX2 : ∀ i, MemLp (X i) 2 μ) (hXmeas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ) (z : ℝ) (i : ι) :
    Integrable (fun t : ℝ =>
      ((∫ ω, (if upperTruncatedSum X ω ≤ z then (1 : ℝ) else 0) ∂μ) -
        ∫ ω, (if leaveOneOut (upperTruncatedFamily X) i ω + t ≤ z
          then (1 : ℝ) else 0) ∂μ) *
        upperTruncatedExpectedKernel X μ i t) := by
  let A : ℝ := ∫ ω, (if upperTruncatedSum X ω ≤ z then (1 : ℝ) else 0) ∂μ
  have hA : Integrable (fun t : ℝ => A * upperTruncatedExpectedKernel X μ i t) :=
    (integrable_upperTruncatedExpectedKernel hX2 hXmeas i).const_mul A
  have hB := integrable_upperTruncatedLeaveOneOutIndicatorExpectedKernel
    hX2 hXmeas h_indep z i
  have heq :
      (fun t : ℝ =>
        ((∫ ω, (if upperTruncatedSum X ω ≤ z then (1 : ℝ) else 0) ∂μ) -
          ∫ ω, (if leaveOneOut (upperTruncatedFamily X) i ω + t ≤ z
            then (1 : ℝ) else 0) ∂μ) *
          upperTruncatedExpectedKernel X μ i t) =
        fun t : ℝ => A * upperTruncatedExpectedKernel X μ i t -
          (∫ ω, (if leaveOneOut (upperTruncatedFamily X) i ω + t ≤ z
            then (1 : ℝ) else 0) ∂μ) *
          upperTruncatedExpectedKernel X μ i t := by
    funext t
    dsimp [A]
    ring
  rw [heq]
  exact hA.sub hB

private lemma integrable_upperTruncatedSteinProductResidualIntegrand
    [DecidableEq ι]
    (hX2 : ∀ i, MemLp (X i) 2 μ) (hXmeas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ) (z : ℝ) (i : ι) :
    Integrable (fun t : ℝ =>
      ((∫ ω, upperTruncatedSum X ω *
          steinSolution z (upperTruncatedSum X ω) ∂μ) -
        ∫ ω, (leaveOneOut (upperTruncatedFamily X) i ω + t) *
          steinSolution z
            (leaveOneOut (upperTruncatedFamily X) i ω + t) ∂μ) *
        upperTruncatedExpectedKernel X μ i t) := by
  let A : ℝ := ∫ ω, upperTruncatedSum X ω *
    steinSolution z (upperTruncatedSum X ω) ∂μ
  have hA : Integrable (fun t : ℝ => A * upperTruncatedExpectedKernel X μ i t) :=
    (integrable_upperTruncatedExpectedKernel hX2 hXmeas i).const_mul A
  have hB := integrable_upperTruncatedLeaveOneOutSteinProductExpectedKernel
    hX2 hXmeas h_indep z i
  have heq :
      (fun t : ℝ =>
        ((∫ ω, upperTruncatedSum X ω *
            steinSolution z (upperTruncatedSum X ω) ∂μ) -
          ∫ ω, (leaveOneOut (upperTruncatedFamily X) i ω + t) *
            steinSolution z
              (leaveOneOut (upperTruncatedFamily X) i ω + t) ∂μ) *
          upperTruncatedExpectedKernel X μ i t) =
        fun t : ℝ => A * upperTruncatedExpectedKernel X μ i t -
          (∫ ω, (leaveOneOut (upperTruncatedFamily X) i ω + t) *
            steinSolution z
              (leaveOneOut (upperTruncatedFamily X) i ω + t) ∂μ) *
          upperTruncatedExpectedKernel X μ i t := by
    funext t
    dsimp [A]
    ring
  rw [heq]
  exact hA.sub hB

/-- Exact Chen--Shao split `R₂ = R₂,₁ + R₂,₂`, with the Gaussian-CDF constant canceled between
the two derivative expectations. -/
theorem upperTruncatedR2_eq_R21_add_R22
    [DecidableEq ι]
    (hX2 : ∀ i, MemLp (X i) 2 μ) (hXmeas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ) (z : ℝ) :
    upperTruncatedR2 X μ z =
      upperTruncatedR21 X μ z + upperTruncatedR22 X μ z := by
  rw [upperTruncatedR2_eq_sum_integral_expectedKernel hX2 hXmeas h_indep z]
  unfold upperTruncatedR21 upperTruncatedR22
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hindicator := integrable_upperTruncatedIndicatorResidualIntegrand
    hX2 hXmeas h_indep z i
  have hproduct := integrable_upperTruncatedSteinProductResidualIntegrand
    hX2 hXmeas h_indep z i
  rw [← integral_add hindicator hproduct]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [upperTruncatedDerivExpectation_sub_eq_indicator_add_product hXmeas z i t]
  ring

end ProbabilityTheory
