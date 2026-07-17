/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.ChenShao.SteinProductDerivative
import ProbabilityApproximation.ChenShao.ExponentialConcentration
import ProbabilityApproximation.ChenShao.UpperTruncation

/-!
# Expected increments of the Stein product

This module completes the expectation step in Chen--Shao (2005), Lemma 6.5.  The unique-kink FTC
for `w f_z(w)` is combined with the lower/upper partition for its derivative and a finite-interval
Fubini argument.  The generic theorem assumes an MGF bound at `2`; its one-sided-truncated
specialization obtains that bound from Bennett's inequality.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped intervalIntegral ENNReal

noncomputable section

namespace ProbabilityTheory

/-- Increment of the Stein product `w f_z(w)` between shifts `s` and `t`. -/
def steinProductIncrement {Ω : Type*} (z : ℝ) (W : Ω → ℝ) (s t : ℝ) (ω : Ω) : ℝ :=
  (W ω + t) * steinSolution z (W ω + t) -
    (W ω + s) * steinSolution z (W ω + s)

/-- Pointwise FTC representation of the Stein-product increment. -/
lemma steinProductIncrement_eq_intervalIntegral
    {Ω : Type*} (z : ℝ) (W : Ω → ℝ) (s t : ℝ) (ω : Ω) :
    steinProductIncrement z W s t ω =
      ∫ u in s..t, steinProductDeriv z (W ω + u) := by
  have hFTC := mul_steinSolution_sub_eq_integral_steinProductDeriv
    z (W ω + s) (W ω + t)
  have hshift :
      (∫ v in (W ω + s)..(W ω + t), steinProductDeriv z v) =
        ∫ u in s..t, steinProductDeriv z (W ω + u) := by
    have h := intervalIntegral.integral_comp_add_right
      (steinProductDeriv z) (W ω) (a := s) (b := t)
    simpa only [add_comm] using h.symm
  exact hFTC.trans hshift

lemma steinProductIncrement_nonneg_of_le
    {Ω : Type*} (z : ℝ) (W : Ω → ℝ) {s t : ℝ} (hst : s ≤ t) (ω : Ω) :
    0 ≤ steinProductIncrement z W s t ω := by
  rw [steinProductIncrement_eq_intervalIntegral]
  exact intervalIntegral.integral_nonneg hst fun u _ =>
    steinProductDeriv_nonneg z (W ω + u)

lemma steinProductIncrement_swap
    {Ω : Type*} (z : ℝ) (W : Ω → ℝ) (s t : ℝ) :
    steinProductIncrement z W s t = -steinProductIncrement z W t s := by
  funext ω
  simp only [steinProductIncrement, Pi.neg_apply]
  ring

/-- The low/high partition written as one product-MGF majorant. -/
lemma steinProductDeriv_add_le_mgf_majorant {z : ℝ} (hz : 2 ≤ z) (w u : ℝ) :
    steinProductDeriv z (w + u) ≤
      steinProductLowConstant * exp (-z / 2) +
        (√(2 * π) / 2 + 2) * (1 + z) * exp (-z) *
          exp (2 * u) * exp (2 * w) := by
  by_cases hlow : w + u ≤ z / 2
  · have h := steinProductDeriv_le_low_exp hz hlow
    have hhigh0 : 0 ≤
        (√(2 * π) / 2 + 2) * (1 + z) * exp (-z) *
          exp (2 * u) * exp (2 * w) := by
      have hz0 : 0 ≤ 1 + z := by linarith
      positivity
    linarith
  · have hhigh := steinProductDeriv_le_upper_mgf hz (lt_of_not_ge hlow)
    have hlow0 : 0 ≤ steinProductLowConstant * exp (-z / 2) :=
      mul_nonneg steinProductLowConstant_pos.le (exp_nonneg _)
    have hexp : exp (2 * (w + u)) = exp (2 * u) * exp (2 * w) := by
      rw [show 2 * (w + u) = 2 * u + 2 * w by ring, exp_add]
    rw [hexp] at hhigh
    linarith

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma measurable_steinProductIncrement {W : Ω → ℝ} (hW : Measurable W)
    (z s t : ℝ) : Measurable (steinProductIncrement z W s t) := by
  have hWt : Measurable fun ω => W ω + t := hW.add_const t
  have hWs : Measurable fun ω => W ω + s := hW.add_const s
  exact (hWt.mul ((continuous_steinSolution z).measurable.comp hWt)).sub
    (hWs.mul ((continuous_steinSolution z).measurable.comp hWs))

private def steinProductKernelMajorant (z : ℝ) (W : Ω → ℝ) (u : ℝ) (ω : Ω) : ℝ :=
  steinProductLowConstant * exp (-z / 2) +
    (√(2 * π) / 2 + 2) * (1 + z) * exp (-z) * exp (2 * u) * exp (2 * W ω)

private lemma integrable_steinProductKernelMajorant
    {W : Ω → ℝ} (hExp : Integrable (fun ω => exp (2 * W ω)) μ)
    (z u : ℝ) : Integrable (steinProductKernelMajorant (Ω := Ω) z W u) μ := by
  exact (integrable_const _).add
    (hExp.const_mul
      ((√(2 * π) / 2 + 2) * (1 + z) * exp (-z) * exp (2 * u)))

private lemma integrable_steinProductDeriv_add
    {W : Ω → ℝ} (hW : Measurable W)
    (hExp : Integrable (fun ω => exp (2 * W ω)) μ)
    {z : ℝ} (hz : 2 ≤ z) (u : ℝ) :
    Integrable (fun ω => steinProductDeriv z (W ω + u)) μ := by
  refine (integrable_steinProductKernelMajorant (μ := μ) hExp z u).mono' ?_ ?_
  · exact (measurable_steinProductDeriv z).comp (hW.add_const u) |>.aestronglyMeasurable
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (steinProductDeriv_nonneg z (W ω + u))]
    exact steinProductDeriv_add_le_mgf_majorant hz (W ω) u

private lemma integrable_steinProductDeriv_add_prod
    {W : Ω → ℝ} (hW : Measurable W)
    (hExp : Integrable (fun ω => exp (2 * W ω)) μ)
    {z : ℝ} (hz : 2 ≤ z) (s t : ℝ) :
    Integrable
      (fun p : ℝ × Ω => steinProductDeriv z (W p.2 + p.1))
      ((volume.restrict (uIoc s t)).prod μ) := by
  let K : ℝ := (√(2 * π) / 2 + 2) * (1 + z) * exp (-z)
  have huInterval : IntervalIntegrable (fun u : ℝ => K * exp (2 * u)) volume s t := by
    have hcont : Continuous (fun u : ℝ => K * exp (2 * u)) := by fun_prop
    exact hcont.intervalIntegrable s t
  have hu : Integrable (fun u : ℝ => K * exp (2 * u))
      (volume.restrict (uIoc s t)) := intervalIntegrable_iff.mp huInterval
  have hhigh : Integrable
      (fun p : ℝ × Ω => K * exp (2 * p.1) * exp (2 * W p.2))
      ((volume.restrict (uIoc s t)).prod μ) := hu.mul_prod hExp
  have hmajor : Integrable
      (fun p : ℝ × Ω => steinProductKernelMajorant z W p.1 p.2)
      ((volume.restrict (uIoc s t)).prod μ) := by
    have hlowU : Integrable (fun _ : ℝ => steinProductLowConstant * exp (-z / 2))
        (volume.restrict (uIoc s t)) :=
      intervalIntegrable_iff.mp intervalIntegrable_const
    have hlowΩ : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const _
    have hlow : Integrable
        (fun _ : ℝ × Ω => steinProductLowConstant * exp (-z / 2))
        ((volume.restrict (uIoc s t)).prod μ) := by
      simpa only [mul_one] using hlowU.mul_prod hlowΩ
    have hadd := hlow.add hhigh
    exact hadd.congr (ae_of_all _ fun p => by
      simp only [Pi.add_apply, steinProductKernelMajorant, K])
  refine hmajor.mono' ?_ ?_
  · exact (measurable_steinProductDeriv z).comp
      ((hW.comp measurable_snd).add measurable_fst) |>.aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (steinProductDeriv_nonneg z (W p.2 + p.1))]
    exact steinProductDeriv_add_le_mgf_majorant hz (W p.2) p.1

lemma integrable_steinProductIncrement
    {W : Ω → ℝ} (hW : Measurable W)
    (hExp : Integrable (fun ω => exp (2 * W ω)) μ)
    {z s t : ℝ} (hz : 2 ≤ z) (hst : s ≤ t) :
    Integrable (steinProductIncrement z W s t) μ := by
  have hprod := integrable_steinProductDeriv_add_prod (μ := μ) hW hExp hz s t
  have hinner := hprod.integral_prod_right
  refine hinner.congr (ae_of_all μ fun ω => ?_)
  rw [steinProductIncrement_eq_intervalIntegral]
  simp only [intervalIntegral.integral_of_le hst, uIoc_of_le hst]

/-- Fubini form of the expected Stein-product increment. -/
lemma integral_steinProductIncrement_eq_intervalIntegral_integral
    {W : Ω → ℝ} (hW : Measurable W)
    (hExp : Integrable (fun ω => exp (2 * W ω)) μ)
    {z s t : ℝ} (hz : 2 ≤ z) :
    ∫ ω, steinProductIncrement z W s t ω ∂μ =
      ∫ u in s..t, ∫ ω, steinProductDeriv z (W ω + u) ∂μ := by
  have hprod := integrable_steinProductDeriv_add_prod (μ := μ) hW hExp hz s t
  have hswap := intervalIntegral_integral_swap (a := s) (b := t)
    (f := fun u ω => steinProductDeriv z (W ω + u)) hprod
  have hright :
      (∫ ω, (∫ u in s..t, steinProductDeriv z (W ω + u)) ∂μ) =
        ∫ ω, steinProductIncrement z W s t ω ∂μ := by
    exact integral_congr_ae (ae_of_all μ fun ω =>
      (steinProductIncrement_eq_intervalIntegral z W s t ω).symm)
  linarith [hswap, hright]

private lemma integral_steinProductDeriv_add_le_of_mgf
    {W : Ω → ℝ} (hW : Measurable W)
    (hExp : Integrable (fun ω => exp (2 * W ω)) μ)
    {M z : ℝ} (hM : mgf W μ 2 ≤ M) (hz : 2 ≤ z) (u : ℝ) :
    ∫ ω, steinProductDeriv z (W ω + u) ∂μ ≤
      steinProductLowConstant * exp (-z / 2) +
        (√(2 * π) / 2 + 2) * (1 + z) * exp (-z) * exp (2 * u) * M := by
  let K : ℝ := (√(2 * π) / 2 + 2) * (1 + z) * exp (-z) * exp (2 * u)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    have hz0 : 0 ≤ 1 + z := by linarith
    positivity
  have hg := integrable_steinProductDeriv_add (μ := μ) hW hExp hz u
  have hmajor := integrable_steinProductKernelMajorant (μ := μ) hExp z u
  have hmono :
      (∫ ω, steinProductDeriv z (W ω + u) ∂μ) ≤
        ∫ ω, steinProductKernelMajorant z W u ω ∂μ := by
    exact integral_mono hg hmajor fun ω => by
      exact steinProductDeriv_add_le_mgf_majorant hz (W ω) u
  have hmajorEq :
      (∫ ω, steinProductKernelMajorant z W u ω ∂μ) =
        steinProductLowConstant * exp (-z / 2) +
          K * ∫ ω, exp (2 * W ω) ∂μ := by
    have hconst : Integrable
        (fun _ : Ω => steinProductLowConstant * exp (-z / 2)) μ := integrable_const _
    have hscaled : Integrable (fun ω => K * exp (2 * W ω)) μ := hExp.const_mul K
    rw [show steinProductKernelMajorant z W u =
        fun ω => steinProductLowConstant * exp (-z / 2) + K * exp (2 * W ω) by
      funext ω
      simp only [steinProductKernelMajorant, K]]
    rw [integral_add hconst hscaled, integral_const, integral_const_mul]
    simp
  have hmgfEq : (∫ ω, exp (2 * W ω) ∂μ) = mgf W μ 2 := by
    rw [mgf]
  calc
    (∫ ω, steinProductDeriv z (W ω + u) ∂μ) ≤
        ∫ ω, steinProductKernelMajorant z W u ω ∂μ := hmono
    _ = steinProductLowConstant * exp (-z / 2) + K * mgf W μ 2 := by
      rw [hmajorEq, hmgfEq]
    _ ≤ steinProductLowConstant * exp (-z / 2) + K * M := by gcongr
    _ = steinProductLowConstant * exp (-z / 2) +
        (√(2 * π) / 2 + 2) * (1 + z) * exp (-z) * exp (2 * u) * M := by
      rfl

/-- Generic expectation form of Chen--Shao Lemma 6.5 under an MGF bound at `2`. -/
theorem integral_steinProductIncrement_le_of_mgf
    {W : Ω → ℝ} (hW : Measurable W)
    (hExp : Integrable (fun ω => exp (2 * W ω)) μ)
    {M z s t : ℝ} (hM : mgf W μ 2 ≤ M)
    (hz : 2 ≤ z) (hst : s < t) (ht : t ≤ 1) :
    ∫ ω, steinProductIncrement z W s t ω ∂μ ≤
      (t - s) *
        (steinProductLowConstant * exp (-z / 2) +
          (√(2 * π) / 2 + 2) * (1 + z) * exp (-z) * exp 2 * M) := by
  let F : ℝ → ℝ := fun u => ∫ ω, steinProductDeriv z (W ω + u) ∂μ
  let G : ℝ → ℝ := fun u =>
    steinProductLowConstant * exp (-z / 2) +
      (√(2 * π) / 2 + 2) * (1 + z) * exp (-z) * exp (2 * u) * M
  let C : ℝ := steinProductLowConstant * exp (-z / 2) +
    (√(2 * π) / 2 + 2) * (1 + z) * exp (-z) * exp 2 * M
  have hM0 : 0 ≤ M := (mgf_nonneg (X := W) (μ := μ) (t := (2 : ℝ))).trans hM
  have hK0 : 0 ≤ (√(2 * π) / 2 + 2) * (1 + z) * exp (-z) * M := by
    have hz0 : 0 ≤ 1 + z := by linarith
    positivity
  have hprod := integrable_steinProductDeriv_add_prod (μ := μ) hW hExp hz s t
  have hFint : IntervalIntegrable F volume s t := by
    rw [intervalIntegrable_iff]
    change Integrable F (volume.restrict (uIoc s t))
    simpa only [F] using hprod.integral_prod_left
  have hGint : IntervalIntegrable G volume s t := by
    have hcont : Continuous G := by
      dsimp [G]
      fun_prop
    exact hcont.intervalIntegrable s t
  have hCint : IntervalIntegrable (fun _ : ℝ => C) volume s t := intervalIntegrable_const
  have hFG : ∀ u, F u ≤ G u := fun u => by
    exact integral_steinProductDeriv_add_le_of_mgf (μ := μ) hW hExp hM hz u
  have hGC : ∀ u ∈ Icc s t, G u ≤ C := by
    intro u hu
    have hu1 : u ≤ 1 := le_trans hu.2 ht
    have hexp : exp (2 * u) ≤ exp 2 := exp_le_exp.mpr (by linarith)
    dsimp [G, C]
    gcongr
  have hFubini := integral_steinProductIncrement_eq_intervalIntegral_integral
    (μ := μ) (s := s) (t := t) hW hExp hz
  have hfirst : (∫ u in s..t, F u) ≤ ∫ u in s..t, G u :=
    intervalIntegral.integral_mono_on hst.le hFint hGint fun u _ => hFG u
  have hsecond : (∫ u in s..t, G u) ≤ ∫ u in s..t, C :=
    intervalIntegral.integral_mono_on hst.le hGint hCint hGC
  have hconst : (∫ _u in s..t, C) = C * (t - s) := by
    rw [intervalIntegral.integral_const]
    simp
    ring
  calc
    (∫ ω, steinProductIncrement z W s t ω ∂μ) =
        ∫ u in s..t, ∫ ω, steinProductDeriv z (W ω + u) ∂μ := hFubini
    _ = ∫ u in s..t, F u := rfl
    _ ≤ ∫ u in s..t, G u := hfirst
    _ ≤ ∫ _u in s..t, C := hsecond
    _ = C * (t - s) := hconst
    _ = (t - s) *
        (steinProductLowConstant * exp (-z / 2) +
          (√(2 * π) / 2 + 2) * (1 + z) * exp (-z) * exp 2 * M) := by
      dsimp [C]
      ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {X : ι → Ω → ℝ}

/-- Exponential integrability at `2` for a one-sided-truncated leave-one-out sum. -/
lemma integrable_exp_two_upperTruncated_leaveOneOut
    (hXmeas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ) (i : ι) :
    Integrable
      (fun ω => exp (2 * leaveOneOut (upperTruncatedFamily X) i ω)) μ := by
  let Y := upperTruncatedFamily X
  have hYmeas : ∀ j, Measurable (Y j) := measurable_upperTruncatedFamily hXmeas
  have hYindep : iIndepFun Y μ := iIndepFun_upperTruncatedFamily h_indep
  have hYle : ∀ j, ∀ᵐ ω ∂μ, Y j ω ≤ 1 := fun j =>
    ae_of_all μ fun ω => upperTruncateOne_le_one (X j ω)
  have hcoord : ∀ j ∈ Finset.univ.erase i,
      Integrable (fun ω => exp (2 * Y j ω)) μ := by
    intro j hj
    refine Integrable.of_bound
      (((hYmeas j).const_mul 2).exp.aestronglyMeasurable) (exp 2) ?_
    filter_upwards [hYle j] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_exp.mpr (mul_le_of_le_one_right (by norm_num) hω)
  simpa only [leaveOneOut, Finset.sum_apply, Y] using
    hYindep.integrable_exp_mul_sum hYmeas (t := (2 : ℝ)) hcoord

/-- Bennett's inequality at `t = 2` for a one-sided-truncated leave-one-out sum. -/
lemma mgf_upperTruncated_leaveOneOut_two_le_bennett
    (hXmeas : ∀ i, Measurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (h_indep : iIndepFun X μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1) (i : ι) :
    mgf (leaveOneOut (upperTruncatedFamily X) i) μ 2 ≤
      exp (exp 2 - 3) := by
  let Y := upperTruncatedFamily X
  have hYmeas : ∀ j, Measurable (Y j) := measurable_upperTruncatedFamily hXmeas
  have hYmem : ∀ j, MemLp (Y j) 2 μ := memLp_upperTruncatedFamily hXmeas hX2
  have hYindep : iIndepFun Y μ := iIndepFun_upperTruncatedFamily h_indep
  have hYmean : ∀ j, ∫ ω, Y j ω ∂μ ≤ 0 := fun j => by
    simpa only [Y, upperTruncatedFamily, Function.comp_apply] using
      integral_upperTruncateOne_comp_nonpos (hXmeas j) (hX2 j) (h_mean j)
  have hYle : ∀ j, ∀ᵐ ω ∂μ, Y j ω ≤ 1 := fun j =>
    ae_of_all μ fun ω => upperTruncateOne_le_one (X j ω)
  have hsecond : ∑ j ∈ Finset.univ.erase i, ∫ ω, (Y j ω) ^ 2 ∂μ ≤ 1 := by
    simpa only [Y, upperTruncatedFamily, Function.comp_apply] using
      sum_integral_sq_upperTruncateOne_erase_le_one hXmeas hX2 h_mean hvar i
  have hmgf := mgf_finsetSum_le_exp_bennett (μ := μ) (Finset.univ.erase i)
    hYmeas hYindep hYmem hYmean hYle hsecond
    (t := (2 : ℝ)) (α := (1 : ℝ)) (B2 := (1 : ℝ)) (by norm_num) (by norm_num)
  have hfun : leaveOneOut (upperTruncatedFamily X) i =
      ∑ j ∈ Finset.univ.erase i, Y j := by
    funext ω
    simp only [leaveOneOut, Finset.sum_apply, Y]
  rw [hfun]
  convert hmgf using 1
  ring_nf

/-- Explicit absolute constant for the truncated Stein-product increment estimate. -/
def steinProductIncrementConstant : ℝ :=
  steinProductLowConstant +
    3 * (√(2 * π) / 2 + 2) * exp 2 * exp (exp 2 - 3)

lemma steinProductIncrementConstant_pos : 0 < steinProductIncrementConstant := by
  dsimp [steinProductIncrementConstant]
  have hlow := steinProductLowConstant_pos
  positivity

private lemma one_add_mul_exp_neg_half_le_three {z : ℝ} (hz : 2 ≤ z) :
    (1 + z) * exp (-z / 2) ≤ 3 := by
  have hbase := Real.add_one_le_exp (z / 2)
  have hlinear : 1 + z ≤ 3 * exp (z / 2) := by
    nlinarith [exp_pos (z / 2)]
  have hmul := mul_le_mul_of_nonneg_right hlinear (exp_nonneg (-z / 2))
  calc
    (1 + z) * exp (-z / 2) ≤
        (3 * exp (z / 2)) * exp (-z / 2) := hmul
    _ = 3 := by
      rw [mul_assoc, ← exp_add, show z / 2 + -z / 2 = 0 by ring, exp_zero, mul_one]

/-- Chen--Shao Lemma 6.5 for a one-sided-truncated leave-one-out sum, with an
explicit absolute constant and the stronger interval-length factor. -/
theorem integral_steinProductIncrement_upperTruncated_le
    (hXmeas : ∀ i, Measurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (h_indep : iIndepFun X μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1) (i : ι)
    {z s t : ℝ} (hz : 2 ≤ z) (hst : s < t) (ht : t ≤ 1) :
    ∫ ω, steinProductIncrement z
        (leaveOneOut (upperTruncatedFamily X) i) s t ω ∂μ ≤
      steinProductIncrementConstant * exp (-z / 2) * (t - s) := by
  let W := leaveOneOut (upperTruncatedFamily X) i
  let A : ℝ := √(2 * π) / 2 + 2
  let M : ℝ := exp (exp 2 - 3)
  have hWmeas : Measurable W :=
    measurable_leaveOneOut (measurable_upperTruncatedFamily hXmeas) i
  have hExp : Integrable (fun ω => exp (2 * W ω)) μ :=
    integrable_exp_two_upperTruncated_leaveOneOut hXmeas h_indep i
  have hM : mgf W μ 2 ≤ M :=
    mgf_upperTruncated_leaveOneOut_two_le_bennett
      hXmeas hX2 h_indep h_mean hvar i
  have hgeneric := integral_steinProductIncrement_le_of_mgf
    (μ := μ) hWmeas hExp hM hz hst ht
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hM0 : 0 ≤ M := by
    dsimp [M]
    positivity
  have hdecay :
      (1 + z) * exp (-z) ≤ 3 * exp (-z / 2) := by
    have hfactor : exp (-z) = exp (-z / 2) * exp (-z / 2) := by
      rw [← exp_add]
      congr 1
      ring
    rw [hfactor, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (one_add_mul_exp_neg_half_le_three hz) (exp_nonneg _)
  have hbracket :
      steinProductLowConstant * exp (-z / 2) +
          A * (1 + z) * exp (-z) * exp 2 * M ≤
        steinProductIncrementConstant * exp (-z / 2) := by
    have hscaled := mul_le_mul_of_nonneg_right hdecay (mul_nonneg (exp_nonneg 2) hM0)
    have hscaled' := mul_le_mul_of_nonneg_left hscaled hA0
    dsimp [A, M, steinProductIncrementConstant] at hscaled' ⊢
    nlinarith [exp_nonneg (-z / 2), steinProductLowConstant_pos.le]
  have hlen : 0 ≤ t - s := sub_nonneg.mpr hst.le
  calc
    (∫ ω, steinProductIncrement z W s t ω ∂μ) ≤
        (t - s) *
          (steinProductLowConstant * exp (-z / 2) +
            A * (1 + z) * exp (-z) * exp 2 * M) := hgeneric
    _ ≤ (t - s) * (steinProductIncrementConstant * exp (-z / 2)) := by
      gcongr
    _ = steinProductIncrementConstant * exp (-z / 2) * (t - s) := by ring

/-- The interval-length estimate implies the symmetric shift-size form used downstream. -/
theorem integral_steinProductIncrement_upperTruncated_le_abs_add
    (hXmeas : ∀ i, Measurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (h_indep : iIndepFun X μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1) (i : ι)
    {z s t : ℝ} (hz : 2 ≤ z) (hst : s < t) (ht : t ≤ 1) :
    ∫ ω, steinProductIncrement z
        (leaveOneOut (upperTruncatedFamily X) i) s t ω ∂μ ≤
      steinProductIncrementConstant * exp (-z / 2) * (|s| + |t|) := by
  have hmain := integral_steinProductIncrement_upperTruncated_le
    hXmeas hX2 h_indep h_mean hvar i hz hst ht
  have hdist : t - s ≤ |s| + |t| := by
    calc
      t - s ≤ |t - s| := le_abs_self _
      _ ≤ |t| + |s| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le t (-s)
      _ = |s| + |t| := add_comm _ _
  have hcoef : 0 ≤ steinProductIncrementConstant * exp (-z / 2) :=
    mul_nonneg steinProductIncrementConstant_pos.le (exp_nonneg _)
  exact hmain.trans (mul_le_mul_of_nonneg_left hdist hcoef)

/-- Orientation-free absolute-value form of the truncated Stein-product increment estimate. -/
theorem abs_integral_steinProductIncrement_upperTruncated_le_abs_add
    (hXmeas : ∀ i, Measurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (h_indep : iIndepFun X μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1) (i : ι)
    {z s t : ℝ} (hz : 2 ≤ z) (hs : s ≤ 1) (ht : t ≤ 1) :
    |∫ ω, steinProductIncrement z
        (leaveOneOut (upperTruncatedFamily X) i) s t ω ∂μ| ≤
      steinProductIncrementConstant * exp (-z / 2) * (|s| + |t|) := by
  let W := leaveOneOut (upperTruncatedFamily X) i
  by_cases hst : s < t
  · have hnonneg : 0 ≤ ∫ ω, steinProductIncrement z W s t ω ∂μ :=
      integral_nonneg fun ω => steinProductIncrement_nonneg_of_le z W hst.le ω
    rw [abs_of_nonneg hnonneg]
    exact integral_steinProductIncrement_upperTruncated_le_abs_add
      hXmeas hX2 h_indep h_mean hvar i hz hst ht
  · by_cases hts : t < s
    · have hswap :
          (∫ ω, steinProductIncrement z W s t ω ∂μ) =
            -(∫ ω, steinProductIncrement z W t s ω ∂μ) := by
        rw [steinProductIncrement_swap]
        simpa only [Pi.neg_apply] using
          (integral_neg (μ := μ) (steinProductIncrement z W t s))
      rw [hswap, abs_neg]
      have hbound := integral_steinProductIncrement_upperTruncated_le_abs_add
        hXmeas hX2 h_indep h_mean hvar i hz hts hs
      have hnonneg : 0 ≤ ∫ ω, steinProductIncrement z W t s ω ∂μ :=
        integral_nonneg fun ω => steinProductIncrement_nonneg_of_le z W hts.le ω
      rw [abs_of_nonneg hnonneg]
      simpa only [add_comm] using hbound
    · have heq : s = t := le_antisymm (le_of_not_gt hts) (le_of_not_gt hst)
      subst t
      simp only [steinProductIncrement, sub_self, integral_zero, abs_zero]
      exact mul_nonneg
        (mul_nonneg steinProductIncrementConstant_pos.le (exp_nonneg _))
        (add_nonneg (abs_nonneg _) (abs_nonneg _))

end ProbabilityTheory
