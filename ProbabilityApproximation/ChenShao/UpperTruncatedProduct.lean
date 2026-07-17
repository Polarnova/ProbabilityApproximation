/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.ChenShao.UpperTruncatedExpectedKernel
import ProbabilityApproximation.ChenShao.UpperTruncatedIndicator
import ProbabilityApproximation.ChenShao.SteinProductIncrement

/-!
# Stein-product residual for the upper-truncated sum

This module proves the estimate corresponding to Chen--Shao (2005), equation (6.20).  Independence
first rewrites the Stein product of the full truncated sum as an iterated leave-one-out integral.
The orientation-free form of Lemma 6.5 then controls the two deterministic shifts.  The factor
`3 / 2` is the sum of the first absolute expected-kernel moment (`1 / 2`) and the product of the
coordinate first moment with the expected-kernel mass (`1`).
-/

open MeasureTheory ProbabilityTheory Real Filter

noncomputable section

namespace ProbabilityTheory

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ι → Ω → ℝ}

/-- Leave-one-out independence factors the Stein product of the full upper-truncated sum into an
outer coordinate integral and an inner leave-one-out integral. -/
theorem integral_upperTruncatedSteinProduct_eq_iterated_leaveOneOut
    (hXmeas : ∀ i, Measurable (X i)) (h_indep : iIndepFun X μ)
    (i : ι) (z : ℝ) :
    (∫ ω, upperTruncatedSum X ω * steinSolution z (upperTruncatedSum X ω) ∂μ) =
      ∫ ξ, (∫ ω, (leaveOneOut (upperTruncatedFamily X) i ω +
          upperTruncatedFamily X i ξ) *
        steinSolution z (leaveOneOut (upperTruncatedFamily X) i ω +
          upperTruncatedFamily X i ξ) ∂μ) ∂μ := by
  let Y := upperTruncatedFamily X
  let W := leaveOneOut Y i
  let f : ℝ × ℝ → ℝ := fun p =>
    (p.1 + p.2) * steinSolution z (p.1 + p.2)
  have hYmeas : ∀ j, Measurable (Y j) := measurable_upperTruncatedFamily hXmeas
  have hWmeas : Measurable W := measurable_leaveOneOut hYmeas i
  have hInd : IndepFun W (Y i) μ :=
    indepFun_leaveOneOut (X := Y) (μ := μ) hYmeas
      (iIndepFun_upperTruncatedFamily h_indep) i
  have hf_meas : Measurable f := by
    have hsum : Measurable (fun p : ℝ × ℝ => p.1 + p.2) :=
      measurable_fst.add measurable_snd
    exact hsum.mul ((continuous_steinSolution z).measurable.comp hsum)
  have hf_int : Integrable f ((μ.map W).prod (μ.map (Y i))) := by
    refine (integrable_const (μ := (μ.map W).prod (μ.map (Y i))) (1 : ℝ)).mono'
      hf_meas.aestronglyMeasurable ?_
    filter_upwards with p
    simpa only [f, Real.norm_eq_abs] using
      abs_mul_steinSolution_le_one z (p.1 + p.2)
  have hmap_eq := hInd.map_prod_eq_prod_map_map
    hWmeas.aemeasurable (hYmeas i).aemeasurable
  have hpair : AEMeasurable (fun ω => (W ω, Y i ω)) μ :=
    hWmeas.aemeasurable.prodMk (hYmeas i).aemeasurable
  have hleft :
      (∫ ω, upperTruncatedSum X ω * steinSolution z (upperTruncatedSum X ω) ∂μ) =
        ∫ p, f p ∂((μ.map W).prod (μ.map (Y i))) := by
    have hsum (ω : Ω) : upperTruncatedSum X ω = W ω + Y i ω := by
      simpa only [upperTruncatedSum, W, Y] using
        leaveOneOut_add (X := upperTruncatedFamily X) i ω
    calc
      (∫ ω, upperTruncatedSum X ω * steinSolution z (upperTruncatedSum X ω) ∂μ) =
          ∫ ω, f (W ω, Y i ω) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [f, hsum]
      _ = ∫ p, f p ∂(μ.map fun ω => (W ω, Y i ω)) :=
        (integral_map hpair hf_meas.aestronglyMeasurable).symm
      _ = ∫ p, f p ∂((μ.map W).prod (μ.map (Y i))) := by rw [hmap_eq]
  have hinner (ξ : ℝ) :
      (∫ w, f (w, ξ) ∂(μ.map W)) = ∫ ω, f (W ω, ξ) ∂μ := by
    exact integral_map hWmeas.aemeasurable
      ((hf_meas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  have houterMeas : AEStronglyMeasurable
      (fun ξ : ℝ => ∫ w, f (w, ξ) ∂(μ.map W)) (μ.map (Y i)) :=
    hf_meas.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
  have hright :
      (∫ p, f p ∂((μ.map W).prod (μ.map (Y i)))) =
        ∫ ξ, (∫ ω, f (W ω, Y i ξ) ∂μ) ∂μ := by
    calc
      (∫ p, f p ∂((μ.map W).prod (μ.map (Y i)))) =
          ∫ ξ, (∫ w, f (w, ξ) ∂(μ.map W)) ∂(μ.map (Y i)) :=
        integral_prod_symm f hf_int
      _ = ∫ ξ, (∫ w, f (w, Y i ξ) ∂(μ.map W)) ∂μ :=
        integral_map (hYmeas i).aemeasurable houterMeas
      _ = ∫ ξ, (∫ ω, f (W ω, Y i ξ) ∂μ) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        exact hinner (Y i ξ)
  rw [hleft, hright]

private lemma abs_upperTruncatedSteinProductExpectation_sub_leaveOneOut_le
    (hXmeas : ∀ i, Measurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (h_indep : iIndepFun X μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1)
    (i : ι) {z t : ℝ} (hz : 2 ≤ z) (ht : t ≤ 1) :
    |(∫ ω, upperTruncatedSum X ω *
          steinSolution z (upperTruncatedSum X ω) ∂μ) -
        ∫ ω, (leaveOneOut (upperTruncatedFamily X) i ω + t) *
          steinSolution z
            (leaveOneOut (upperTruncatedFamily X) i ω + t) ∂μ| ≤
      steinProductIncrementConstant * exp (-z / 2) *
        ((∫ ξ, |upperTruncatedFamily X i ξ| ∂μ) + |t|) := by
  let Y := upperTruncatedFamily X
  let W := leaveOneOut Y i
  let F : ℝ → ℝ := fun w => w * steinSolution z w
  let A : ℝ := ∫ ω, upperTruncatedSum X ω *
    steinSolution z (upperTruncatedSum X ω) ∂μ
  let B : ℝ := ∫ ω, F (W ω + t) ∂μ
  let C : ℝ := steinProductIncrementConstant * exp (-z / 2)
  have hYmeas : ∀ j, Measurable (Y j) := measurable_upperTruncatedFamily hXmeas
  have hY2 : ∀ j, MemLp (Y j) 2 μ := memLp_upperTruncatedFamily hXmeas hX2
  have hWmeas : Measurable W := measurable_leaveOneOut hYmeas i
  have hFmeas : Measurable F := by
    exact measurable_id.mul ((continuous_steinSolution z).measurable.comp measurable_id)
  have hpairMeas : Measurable (fun p : Ω × Ω => F (W p.1 + Y i p.2)) :=
    hFmeas.comp ((hWmeas.comp measurable_fst).add ((hYmeas i).comp measurable_snd))
  have hpairInt : Integrable (fun p : Ω × Ω => F (W p.1 + Y i p.2))
      (μ.prod μ) := by
    refine (integrable_const (μ := μ.prod μ) (1 : ℝ)).mono'
      hpairMeas.aestronglyMeasurable ?_
    filter_upwards with p
    simpa only [F, Real.norm_eq_abs] using
      abs_mul_steinSolution_le_one z (W p.1 + Y i p.2)
  have houterInt : Integrable
      (fun ξ => ∫ ω, F (W ω + Y i ξ) ∂μ) μ := by
    simpa only using hpairInt.integral_prod_right
  have hBInt : Integrable (fun _ : Ω => B) μ := integrable_const B
  have hfactor : A = ∫ ξ, (∫ ω, F (W ω + Y i ξ) ∂μ) ∂μ := by
    simpa only [A, F, W, Y] using
      integral_upperTruncatedSteinProduct_eq_iterated_leaveOneOut
        hXmeas h_indep i z
  have hdiff :
      A - B = ∫ ξ, ((∫ ω, F (W ω + Y i ξ) ∂μ) - B) ∂μ := by
    rw [hfactor, integral_sub houterInt hBInt]
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
      one_smul]
  have hFtInt (u : ℝ) : Integrable (fun ω => F (W ω + u)) μ := by
    refine (integrable_const (μ := μ) (1 : ℝ)).mono'
      (hFmeas.comp (hWmeas.add_const u)).aestronglyMeasurable ?_
    filter_upwards with ω
    simpa only [F, Real.norm_eq_abs] using
      abs_mul_steinSolution_le_one z (W ω + u)
  have hinner (ξ : Ω) :
      |(∫ ω, F (W ω + Y i ξ) ∂μ) - B| ≤ C * (|Y i ξ| + |t|) := by
    have heq :
        (∫ ω, F (W ω + Y i ξ) ∂μ) - B =
          -(∫ ω, steinProductIncrement z W (Y i ξ) t ω ∂μ) := by
      rw [← integral_sub (hFtInt (Y i ξ)) (hFtInt t), ← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [F, steinProductIncrement]
      ring
    rw [heq, abs_neg]
    simpa only [C, Y, W, upperTruncatedFamily, Function.comp_apply] using
      abs_integral_steinProductIncrement_upperTruncated_le_abs_add
        hXmeas hX2 h_indep h_mean hvar i hz
          (upperTruncateOne_le_one (X i ξ)) ht
  have hYabs : Integrable (fun ξ => |Y i ξ|) μ :=
    ((hY2 i).integrable one_le_two).abs
  have hC0 : 0 ≤ C := by
    exact mul_nonneg steinProductIncrementConstant_pos.le (exp_nonneg _)
  have hmajorInt : Integrable (fun ξ => C * (|Y i ξ| + |t|)) μ :=
    (hYabs.add (integrable_const |t|)).const_mul C
  have hdiffInt : Integrable
      (fun ξ => (∫ ω, F (W ω + Y i ξ) ∂μ) - B) μ :=
    houterInt.sub hBInt
  have habs :
      |A - B| ≤ ∫ ξ, C * (|Y i ξ| + |t|) ∂μ := by
    rw [hdiff]
    calc
      |∫ ξ, ((∫ ω, F (W ω + Y i ξ) ∂μ) - B) ∂μ| ≤
          ∫ ξ, |(∫ ω, F (W ω + Y i ξ) ∂μ) - B| ∂μ :=
        abs_integral_le_integral_abs
      _ ≤ ∫ ξ, C * (|Y i ξ| + |t|) ∂μ :=
        integral_mono hdiffInt.abs hmajorInt hinner
  refine habs.trans_eq ?_
  rw [show (fun ξ => C * (|Y i ξ| + |t|)) =
      fun ξ => C * |Y i ξ| + C * |t| by
        funext ξ
        ring,
    integral_add (hYabs.const_mul C) (integrable_const (C * |t|)),
    integral_const_mul]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  dsimp only [A, B, C, F, W, Y]
  ring

omit [Fintype ι] [DecidableEq ι] [IsProbabilityMeasure μ] in
private lemma upperTruncatedExpectedKernel_eq_zero_of_one_lt_product
    (i : ι) {t : ℝ} (ht : 1 < t) :
    upperTruncatedExpectedKernel X μ i t = 0 := by
  rw [upperTruncatedExpectedKernel, expectedKernelFwd]
  have hzero :
      (fun ω => kernelDensityFwd (upperTruncatedFamily X i ω) t) =ᵐ[μ]
        (0 : Ω → ℝ) := by
    filter_upwards with ω
    let y := upperTruncatedFamily X i ω
    change kernelDensityFwd y t = (0 : ℝ)
    have hy : y ≤ 1 := upperTruncateOne_le_one (X i ω)
    by_cases hy0 : 0 ≤ y
    · have ht_not : t ∉ Set.Icc 0 y := by
        simp only [Set.mem_Icc, not_and_or]
        exact Or.inr (not_le.mpr (by linarith))
      rw [kernelDensityFwd_eq_indicator_nonneg y hy0, Set.indicator_of_notMem ht_not]
    · have hyneg : y < 0 := lt_of_not_ge hy0
      have ht_not : t ∉ Set.Ioc y 0 := by
        simp only [Set.mem_Ioc, not_and_or]
        exact Or.inr (not_le.mpr (by linarith))
      rw [kernelDensityFwd_eq_indicator_neg y hyneg, Set.indicator_of_notMem ht_not]
  rw [integral_congr_ae hzero]
  simp

private lemma abs_upperTruncatedR22_coordinate_le
    (hXmeas : ∀ i, Measurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (h_indep : iIndepFun X μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1)
    (h3 : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ)
    (i : ι) {z : ℝ} (hz : 2 ≤ z) :
    |∫ t : ℝ,
      ((∫ ω, upperTruncatedSum X ω *
          steinSolution z (upperTruncatedSum X ω) ∂μ) -
        ∫ ω, (leaveOneOut (upperTruncatedFamily X) i ω + t) *
          steinSolution z
            (leaveOneOut (upperTruncatedFamily X) i ω + t) ∂μ) *
        upperTruncatedExpectedKernel X μ i t| ≤
      (steinProductIncrementConstant * exp (-z / 2)) *
        ((∫ ω, |upperTruncatedFamily X i ω| ∂μ) *
            (∫ t : ℝ, upperTruncatedExpectedKernel X μ i t) +
          ∫ t : ℝ, |t| * upperTruncatedExpectedKernel X μ i t) := by
  let Y := upperTruncatedFamily X
  let W := leaveOneOut Y i
  let F : ℝ → ℝ := fun w => w * steinSolution z w
  let A : ℝ := ∫ ω, upperTruncatedSum X ω *
    steinSolution z (upperTruncatedSum X ω) ∂μ
  let B : ℝ → ℝ := fun t => ∫ ω, F (W ω + t) ∂μ
  let K : ℝ → ℝ := upperTruncatedExpectedKernel X μ i
  let EY : ℝ := ∫ ω, |Y i ω| ∂μ
  let C : ℝ := steinProductIncrementConstant * exp (-z / 2)
  have hYmeas : ∀ j, Measurable (Y j) := measurable_upperTruncatedFamily hXmeas
  have hY2 : ∀ j, MemLp (Y j) 2 μ := memLp_upperTruncatedFamily hXmeas hX2
  have hY3 : Integrable (fun ω => |Y i ω| ^ 3) μ :=
    integrable_abs_cube_upperTruncatedFamily hXmeas h3 i
  have hWmeas : Measurable W := measurable_leaveOneOut hYmeas i
  have hFmeas : Measurable F :=
    measurable_id.mul ((continuous_steinSolution z).measurable.comp measurable_id)
  have hBstrong : StronglyMeasurable B := by
    have hg : StronglyMeasurable (fun p : ℝ × Ω => F (W p.2 + p.1)) :=
      (hFmeas.comp ((hWmeas.comp measurable_snd).add measurable_fst)).stronglyMeasurable
    simpa only [B] using hg.integral_prod_right'
  have hKint : Integrable K := by
    simpa only [K] using integrable_upperTruncatedExpectedKernel hX2 hXmeas i
  have hK0 (t : ℝ) : 0 ≤ K t := by
    simpa only [K] using upperTruncatedExpectedKernel_nonneg (X := X) (μ := μ) i t
  have hAbsK : Integrable (fun t : ℝ => |t| * K t) := by
    simpa only [K, upperTruncatedExpectedKernel] using
      integrable_abs_mul_expectedKernelFwd i (hY2 i) (hYmeas i) hY3
  have hC0 : 0 ≤ C :=
    mul_nonneg steinProductIncrementConstant_pos.le (exp_nonneg _)
  have hmajorInt : Integrable (fun t : ℝ => C * (EY + |t|) * K t) := by
    have heq :
        (fun t : ℝ => C * (EY + |t|) * K t) =
          fun t => (C * EY) * K t + C * (|t| * K t) := by
      funext t
      ring
    rw [heq]
    exact (hKint.const_mul (C * EY)).add (hAbsK.const_mul C)
  have hresMeas : AEStronglyMeasurable
      (fun t : ℝ => (A - B t) * K t) :=
    (aestronglyMeasurable_const.sub hBstrong.aestronglyMeasurable).mul
      hKint.aestronglyMeasurable
  have hpoint (t : ℝ) :
      |(A - B t) * K t| ≤ C * (EY + |t|) * K t := by
    by_cases ht : t ≤ 1
    · have hbase := abs_upperTruncatedSteinProductExpectation_sub_leaveOneOut_le
        hXmeas hX2 h_indep h_mean hvar i hz ht
      have hbase' : |A - B t| ≤ C * (EY + |t|) := by
        simpa only [A, B, C, EY, F, W, Y] using hbase
      rw [abs_mul, abs_of_nonneg (hK0 t)]
      exact mul_le_mul_of_nonneg_right hbase' (hK0 t)
    · have hKzero : K t = 0 := by
        simpa only [K] using
          upperTruncatedExpectedKernel_eq_zero_of_one_lt_product
            (X := X) (μ := μ) i (lt_of_not_ge ht)
      simp only [hKzero, mul_zero, abs_zero, le_refl]
  have hresInt : Integrable (fun t : ℝ => (A - B t) * K t) := by
    refine hmajorInt.mono' hresMeas ?_
    filter_upwards with t
    simpa only [Real.norm_eq_abs] using hpoint t
  have habs :
      |∫ t : ℝ, (A - B t) * K t| ≤
        ∫ t : ℝ, C * (EY + |t|) * K t := by
    calc
      |∫ t : ℝ, (A - B t) * K t| ≤
          ∫ t : ℝ, |(A - B t) * K t| := abs_integral_le_integral_abs
      _ ≤ ∫ t : ℝ, C * (EY + |t|) * K t :=
        integral_mono hresInt.abs hmajorInt hpoint
  refine habs.trans_eq ?_
  have heq :
      (fun t : ℝ => C * (EY + |t|) * K t) =
        fun t => (C * EY) * K t + C * (|t| * K t) := by
    funext t
    ring
  rw [heq, integral_add (hKint.const_mul (C * EY)) (hAbsK.const_mul C),
    integral_const_mul, integral_const_mul]
  dsimp only [A, B, C, EY, F, W, Y, K]
  ring

/-- Chen--Shao (2005), equation (6.20): the Stein-product component of `R₂` decays
exponentially.  The explicit factor `3 / 2` records the two exact expected-kernel moment
contributions rather than absorbing them into an unspecified constant. -/
theorem abs_upperTruncatedR22_le_exp_thirdMomentSum
    (hXmeas : ∀ i, Measurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (h_indep : iIndepFun X μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1)
    (h3 : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ)
    {z : ℝ} (hz : 2 ≤ z) :
    |upperTruncatedR22 X μ z| ≤
      (3 / 2 : ℝ) * steinProductIncrementConstant * exp (-z / 2) *
        thirdMomentSum X μ := by
  let C : ℝ := steinProductIncrementConstant * exp (-z / 2)
  let S₁ : ℝ := ∑ i : ι,
    (∫ ω, |upperTruncatedFamily X i ω| ∂μ) *
      (∫ t : ℝ, upperTruncatedExpectedKernel X μ i t)
  let S₂ : ℝ := ∑ i : ι,
    ∫ t : ℝ, |t| * upperTruncatedExpectedKernel X μ i t
  have hC0 : 0 ≤ C :=
    mul_nonneg steinProductIncrementConstant_pos.le (exp_nonneg _)
  have hS₁ : S₁ ≤ thirdMomentSum X μ := by
    simpa only [S₁] using
      sum_integral_abs_upperTruncatedFamily_mul_integral_upperTruncatedExpectedKernel_le
        hX2 hXmeas h3
  have hS₂ : S₂ ≤ (1 / 2 : ℝ) * thirdMomentSum X μ := by
    simpa only [S₂] using
      sum_integral_abs_mul_upperTruncatedExpectedKernel_le hX2 hXmeas h3
  unfold upperTruncatedR22
  calc
    |∑ i : ι, ∫ t : ℝ,
        ((∫ ω, upperTruncatedSum X ω *
            steinSolution z (upperTruncatedSum X ω) ∂μ) -
          ∫ ω, (leaveOneOut (upperTruncatedFamily X) i ω + t) *
            steinSolution z
              (leaveOneOut (upperTruncatedFamily X) i ω + t) ∂μ) *
          upperTruncatedExpectedKernel X μ i t| ≤
        ∑ i : ι, |∫ t : ℝ,
          ((∫ ω, upperTruncatedSum X ω *
              steinSolution z (upperTruncatedSum X ω) ∂μ) -
            ∫ ω, (leaveOneOut (upperTruncatedFamily X) i ω + t) *
              steinSolution z
                (leaveOneOut (upperTruncatedFamily X) i ω + t) ∂μ) *
            upperTruncatedExpectedKernel X μ i t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : ι, C *
        ((∫ ω, |upperTruncatedFamily X i ω| ∂μ) *
            (∫ t : ℝ, upperTruncatedExpectedKernel X μ i t) +
          ∫ t : ℝ, |t| * upperTruncatedExpectedKernel X μ i t) :=
      Finset.sum_le_sum fun i _ => by
        simpa only [C] using
          abs_upperTruncatedR22_coordinate_le
            hXmeas hX2 h_indep h_mean hvar h3 i hz
    _ = C * (S₁ + S₂) := by
      dsimp only [S₁, S₂]
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ C * (thirdMomentSum X μ +
        (1 / 2 : ℝ) * thirdMomentSum X μ) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hS₁ hS₂) hC0
    _ = (3 / 2 : ℝ) * steinProductIncrementConstant * exp (-z / 2) *
        thirdMomentSum X μ := by
      dsimp only [C]
      ring

end ProbabilityTheory
