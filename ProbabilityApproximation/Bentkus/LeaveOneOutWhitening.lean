/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.Bentkus.InductionBranches
import ProbabilityApproximation.Bentkus.Whitening

/-!
# Leave-one-out whitening bounds for Bentkus's induction

This module formalizes the spectral branch at the beginning of Bentkus (2004), Section 3,
printed pages 403--404.  If every summand has second norm moment below `1 / 4`, then the
leave-one-out covariance is bounded below by `3 / 4` times the identity.  It is therefore
positive definite, and its inverse square root has operator norm at most `2`.  The resulting
factor `8` on third moments is the form consumed by the rotation and smoothing estimates.
-/

open MeasureTheory InnerProductSpace Matrix
open scoped RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

/-- The variance of a centered random vector in direction `x` is at most
`‖x‖² E ‖X‖²`. -/
lemma covarianceBilin_self_le_norm_sq_mul_integral_norm_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {X : Ω → EuclideanSpace ℝ (Fin d)}
    (hX2 : MemLp X 2 μ) (hX0 : ∫ ω, X ω ∂μ = 0)
    (x : EuclideanSpace ℝ (Fin d)) :
    covarianceBilin (μ.map X) x x ≤
      ‖x‖ ^ 2 * ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
  have hLaw : MemLp id 2 (μ.map X) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hX2.aemeasurable).2 (by
      simpa only [Function.comp_def, id_eq] using hX2)
  have hmean : ∫ z, z ∂(μ.map X) = 0 := by
    calc
      ∫ z, z ∂(μ.map X) = ∫ ω, X ω ∂μ := by
        simpa only [Function.comp_def, id_eq] using
          (integral_map hX2.aemeasurable aestronglyMeasurable_id)
      _ = 0 := hX0
  rw [covarianceBilin_apply hLaw]
  simp only [id_eq] at hmean ⊢
  rw [hmean]
  simp only [sub_zero]
  rw [integral_map hX2.aemeasurable (by fun_prop), ← integral_const_mul]
  apply integral_mono
  · exact (hX2.const_inner x).integrable_sq.congr
      (by filter_upwards with ω; rw [pow_two])
  · exact (hX2.integrable_norm_pow (by norm_num)).const_mul _
  · intro ω
    have hinner := abs_real_inner_le_norm x (X ω)
    have hsquare := (sq_le_sq₀ (abs_nonneg (inner ℝ x (X ω)))
      (mul_nonneg (norm_nonneg x) (norm_nonneg (X ω)))).2 hinner
    nlinarith [sq_abs (inner ℝ x (X ω))]

/-- Under identity total covariance, removing a summand whose second norm moment is below
`1 / 4` leaves a positive-definite covariance matrix. -/
lemma bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin n) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4) :
    (bentkusLeaveOneOutCovarianceMatrix μ X k).PosDef := by
  have hX2 : ∀ i, MemLp (X i) 2 μ :=
    fun i ↦ (hX3 i).mono_exponent (by norm_num)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (bentkusLeaveOneOutCovarianceMatrix_posSemidef μ X k).1 ?_
  intro x hx
  let xE : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 x
  have hxE : xE ≠ 0 := by
    change WithLp.toLp 2 x ≠ WithLp.toLp 2 0
    exact (WithLp.toLp_injective 2).ne hx
  have hcovXi := covarianceBilin_self_le_norm_sq_mul_integral_norm_sq
    (hX2 k) (hX0 k) xE
  have hleave := covarianceBilin_leaveOneOut_eq_inner_sub
    hX2 h_indep hidentity k xE xE
  have hnormpos : 0 < ‖xE‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hxE)
  have hcovpos : 0 < covarianceBilin (μ.map (bentkusLeaveOneOut X k)) xE xE := by
    rw [hleave]
    rw [real_inner_self_eq_norm_sq]
    nlinarith [mul_pos hnormpos (by norm_num : (0 : ℝ) < 3 / 4)]
  simpa only [xE, WithLp.ofLp_toLp, RCLike.star_def, starRingEnd_apply, star_trivial]
    using (show 0 < dotProduct x
      (Matrix.mulVec (bentkusLeaveOneOutCovarianceMatrix μ X k) x) by
        simpa only [xE, WithLp.ofLp_toLp] using
          (dotProduct_bentkusLeaveOneOutCovarianceMatrix_mulVec μ X k xE xE ▸ hcovpos))

/-- The inverse square root of a leave-one-out covariance with lower spectral bound `3 / 4`
expands Euclidean norms by at most a factor of `2`. -/
lemma norm_bentkusWhiteningCLM_leaveOneOut_apply_le_two
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin n) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖bentkusWhiteningCLM (bentkusLeaveOneOutCovarianceMatrix μ X k) x‖ ≤
      2 * ‖x‖ := by
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  let B := bentkusWhiteningCLM S
  have hX2 : ∀ i, MemLp (X i) 2 μ :=
    fun i ↦ (hX3 i).mono_exponent (by norm_num)
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  have hcovXi := covarianceBilin_self_le_norm_sq_mul_integral_norm_sq
    (hX2 k) (hX0 k) (B x)
  have hleave := covarianceBilin_leaveOneOut_eq_inner_sub
    hX2 h_indep hidentity k (B x) (B x)
  have hlower : (3 / 4 : ℝ) * ‖B x‖ ^ 2 ≤
      covarianceBilin (μ.map (bentkusLeaveOneOut X k)) (B x) (B x) := by
    have hmom : ‖B x‖ ^ 2 * (∫ ω, ‖X k ω‖ ^ 2 ∂μ) ≤
        ‖B x‖ ^ 2 * (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left (le_of_lt hk) (sq_nonneg ‖B x‖)
    rw [hleave, real_inner_self_eq_norm_sq]
    nlinarith [hcovXi, hmom]
  have hcov_eq :
      covarianceBilin (μ.map (bentkusLeaveOneOut X k)) (B x) (B x) =
        ‖x‖ ^ 2 := by
    rw [← dotProduct_bentkusLeaveOneOutCovarianceMatrix_mulVec μ X k]
    rw [← inner_toEuclideanCLM]
    change inner ℝ (B x) (toEuclideanCLM (𝕜 := ℝ) S (B x)) = ‖x‖ ^ 2
    calc
      inner ℝ (B x) (toEuclideanCLM (𝕜 := ℝ) S (B x)) =
          inner ℝ x (B.adjoint (toEuclideanCLM (𝕜 := ℝ) S (B x))) :=
        (B.adjoint_inner_right x (toEuclideanCLM (𝕜 := ℝ) S (B x))).symm
      _ = inner ℝ x (B (toEuclideanCLM (𝕜 := ℝ) S (B x))) := by
        rw [show B.adjoint = B by exact adjoint_bentkusWhiteningCLM S]
      _ = inner ℝ x x := by
        rw [show B (toEuclideanCLM (𝕜 := ℝ) S (B x)) = x by
          exact bentkusWhiteningCLM_covariance_comp d S hS x]
      _ = ‖x‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
  rw [hcov_eq] at hlower
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _))).mp
  nlinarith [sq_nonneg ‖B x‖, sq_nonneg ‖x‖]

/-- Cubing the leave-one-out whitening norm estimate produces the factor `8` used in the
third-moment remainder. -/
lemma norm_bentkusWhiteningCLM_leaveOneOut_apply_pow_three_le
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin n) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖bentkusWhiteningCLM (bentkusLeaveOneOutCovarianceMatrix μ X k) x‖ ^ 3 ≤
      8 * ‖x‖ ^ 3 := by
  calc
    ‖bentkusWhiteningCLM (bentkusLeaveOneOutCovarianceMatrix μ X k) x‖ ^ 3 ≤
        (2 * ‖x‖) ^ 3 :=
      pow_le_pow_left₀ (norm_nonneg _)
        (norm_bentkusWhiteningCLM_leaveOneOut_apply_le_two
          hX3 h_indep hX0 hidentity k hk x) 3
    _ = 8 * ‖x‖ ^ 3 := by ring

/-- Integrated third moments increase by at most a factor of `8` under leave-one-out
whitening.  The random vector being transformed may live on a different measure space. -/
lemma integral_norm_bentkusWhiteningCLM_leaveOneOut_pow_three_le
    {n d : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure Ω'}
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin n) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    {Z : Ω' → EuclideanSpace ℝ (Fin d)} (hZ3 : MemLp Z 3 ν) :
    (∫ ω, ‖bentkusWhiteningCLM
        (bentkusLeaveOneOutCovarianceMatrix μ X k) (Z ω)‖ ^ 3 ∂ν) ≤
      8 * ∫ ω, ‖Z ω‖ ^ 3 ∂ν := by
  rw [← integral_const_mul]
  apply integral_mono
  · exact (memLp_bentkusWhiteningCLM_comp
      (bentkusLeaveOneOutCovarianceMatrix μ X k) hZ3).integrable_norm_pow (by norm_num)
  · exact (hZ3.integrable_norm_pow (by norm_num)).const_mul 8
  · intro ω
    exact norm_bentkusWhiteningCLM_leaveOneOut_apply_pow_three_le
      hX3 h_indep hX0 hidentity k hk (Z ω)

end ProbabilityTheory
