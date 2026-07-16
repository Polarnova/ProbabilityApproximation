/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.Bentkus.Rotation
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Moment comparison for Gaussian companions

Bentkus (2004), pp. 407--409, repeatedly reduces mixed Taylor remainders to second and third
absolute moments.  The estimate preceding (3.30) uses
`E ‖X‖² ‖Y‖ ≤ (E ‖X‖²)^(3/2) ≤ E ‖X‖³`; the discussion following (3.35) uses
`E ‖Y‖³ ≪ E ‖X‖³` and `E ‖Y‖² = E ‖X‖²`; and (3.39)--(3.40) invoke the same moment
comparisons for polynomial mixtures of `‖X‖` and `‖Y‖`.

This module supplies the dimension-free comparison hidden by Bentkus's `≪`.  For a centered
summand `X` and its centered Gaussian companion `Y` with the same covariance, we prove

`E ‖Y‖³ ≤ 27 E ‖X‖³`.

The constant `27` is deliberately conservative.  It follows from the dimension-free Gaussian
fourth-moment estimate `E ‖Y‖⁴ ≤ 3 (E ‖Y‖²)²`, monotonicity of probability-space `Lᵖ` norms,
and exact matching of second moments.  No positive-definiteness, density, or nonsingularity
assumption is used for an individual covariance matrix.
-/

open MeasureTheory Matrix
open scoped ENNReal NNReal MatrixOrder RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

/-- The fourth moment of a centered real Gaussian. -/
lemma integral_pow_four_gaussianReal_zero (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  change (∫ x : ℝ, (id ^ 4) x ∂gaussianReal 0 v) = _
  rw [← iteratedDeriv_mgf_zero (by simp) 4]
  change iteratedDeriv 4 (mgf (fun x : ℝ ↦ x) (gaussianReal 0 v)) 0 = _
  rw [mgf_fun_id_gaussianReal]
  simp only [zero_mul, zero_add, iteratedDeriv_succ]
  let a : ℝ := v
  let f₀ : ℝ → ℝ := fun t ↦ Real.exp (a * t ^ 2 / 2)
  let f₁ : ℝ → ℝ := fun t ↦ (a * t) * Real.exp (a * t ^ 2 / 2)
  let f₂ : ℝ → ℝ := fun t ↦ (a + a ^ 2 * t ^ 2) * Real.exp (a * t ^ 2 / 2)
  let f₃ : ℝ → ℝ :=
    fun t ↦ (3 * a ^ 2 * t + a ^ 3 * t ^ 3) * Real.exp (a * t ^ 2 / 2)
  have h₁ : deriv f₀ = f₁ := by
    funext t
    simp only [f₀, f₁]
    rw [_root_.deriv_exp (by fun_prop)]
    rw [deriv_div_const, deriv_fun_mul (by fun_prop) (by fun_prop),
      deriv_const', zero_mul, zero_add, deriv_fun_pow differentiableAt_id, deriv_id'']
    ring
  have h₂ : deriv f₁ = f₂ := by
    funext t
    simp only [f₁, f₂]
    rw [deriv_fun_mul (by fun_prop) (by fun_prop), _root_.deriv_exp (by fun_prop)]
    have hinner : deriv (fun t : ℝ ↦ a * t ^ 2 / 2) t = a * t := by
      rw [deriv_div_const, deriv_fun_mul (by fun_prop) (by fun_prop),
        deriv_const', zero_mul, zero_add, deriv_fun_pow differentiableAt_id, deriv_id'']
      ring
    rw [hinner]
    have hlin : deriv (fun t : ℝ ↦ a * t) t = a := by
      rw [deriv_fun_mul (by fun_prop) (by fun_prop), deriv_const', deriv_id'']
      ring
    rw [hlin]
    ring
  have h₃ : deriv f₂ = f₃ := by
    funext t
    simp only [f₂, f₃]
    rw [deriv_fun_mul (by fun_prop) (by fun_prop), _root_.deriv_exp (by fun_prop)]
    have hinner : deriv (fun t : ℝ ↦ a * t ^ 2 / 2) t = a * t := by
      rw [deriv_div_const, deriv_fun_mul (by fun_prop) (by fun_prop),
        deriv_const', zero_mul, zero_add, deriv_fun_pow differentiableAt_id, deriv_id'']
      ring
    rw [hinner]
    have hpoly : deriv (fun t : ℝ ↦ a + a ^ 2 * t ^ 2) t = 2 * a ^ 2 * t := by
      rw [deriv_fun_add (by fun_prop) (by fun_prop), deriv_const', zero_add,
        deriv_fun_mul (by fun_prop) (by fun_prop), deriv_const', zero_mul, zero_add,
        deriv_fun_pow differentiableAt_id, deriv_id'']
      ring
    rw [hpoly]
    ring
  change deriv (deriv (deriv (deriv f₀))) 0 = _
  rw [h₁, h₂, h₃]
  simp only [f₃]
  rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
  norm_num [a]
  rw [deriv_fun_add (by fun_prop) (by fun_prop),
    deriv_fun_mul (by fun_prop) (by fun_prop), deriv_const', zero_mul, zero_add,
    deriv_fun_mul (by fun_prop) (by fun_prop), deriv_const', deriv_id'',
    deriv_fun_pow differentiableAt_id]
  norm_num

/-- Every coordinate of a centered multivariate Gaussian has the standard fourth moment. -/
lemma integral_eval_pow_four_multivariateGaussian {d : ℕ}
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosSemidef) (i : Fin d) :
    (∫ x : EuclideanSpace ℝ (Fin d), (x i) ^ 4 ∂multivariateGaussian 0 S) =
      3 * (S i i) ^ 2 := by
  let h := measurePreserving_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ (Fin d))) (i := i) hS
  have hmap : (multivariateGaussian 0 S).map (fun x ↦ x i) =
      gaussianReal 0 (S i i).toNNReal := by
    simpa using h.map_eq
  calc
    (∫ x : EuclideanSpace ℝ (Fin d), (x i) ^ 4 ∂multivariateGaussian 0 S) =
        ∫ t : ℝ, t ^ 4 ∂gaussianReal 0 (S i i).toNNReal := by
      rw [← hmap, integral_map h.measurable.aemeasurable (by fun_prop)]
    _ = 3 * ((S i i).toNNReal : ℝ) ^ 2 := integral_pow_four_gaussianReal_zero _
    _ = 3 * (S i i) ^ 2 := by
      rw [Real.coe_toNNReal (S i i) hS.diag_nonneg]

private lemma memLp_eval_sq_multivariateGaussian {d : ℕ}
    {S : Matrix (Fin d) (Fin d) ℝ} (i : Fin d) :
    MemLp (fun x : EuclideanSpace ℝ (Fin d) ↦ (x i) ^ 2) (ENNReal.ofReal 2)
      (multivariateGaussian 0 S) := by
  let ν := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S
  have hId4 : MemLp id 4 ν := IsGaussian.memLp_id ν 4 (by simp)
  have hi4 : MemLp (fun x : EuclideanSpace ℝ (Fin d) ↦ x i) 4 ν := by
    simpa only [id_eq] using hId4.eval_piLp i
  letI : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 (ENNReal.ofReal 2) := by
    apply ENNReal.HolderTriple.of_toReal
    norm_num
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  refine MemLp.ae_eq ?_ (hi4.mul hi4)
  filter_upwards with x
  change x i * x i = x i ^ 2
  rw [pow_two]

private lemma integrable_eval_sq_mul_eval_sq_multivariateGaussian {d : ℕ}
    {S : Matrix (Fin d) (Fin d) ℝ} (i j : Fin d) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) ↦ (x i) ^ 2 * (x j) ^ 2)
      (multivariateGaussian 0 S) := by
  have hi2 := memLp_eval_sq_multivariateGaussian (S := S) i
  have hj2 := memLp_eval_sq_multivariateGaussian (S := S) j
  letI : ENNReal.HolderTriple (ENNReal.ofReal 2) (ENNReal.ofReal 2) 1 := by
    apply ENNReal.HolderTriple.of_toReal
    norm_num
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  refine Integrable.congr (hi2.integrable_mul hj2) ?_
  filter_upwards with x
  rfl

/-- A dimension-free mixed coordinate fourth-moment estimate. -/
lemma integral_eval_sq_mul_eval_sq_multivariateGaussian_le {d : ℕ}
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosSemidef) (i j : Fin d) :
    (∫ x : EuclideanSpace ℝ (Fin d), (x i) ^ 2 * (x j) ^ 2
      ∂multivariateGaussian 0 S) ≤ 3 * (S i i) * (S j j) := by
  let ν := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S
  have hi2 := memLp_eval_sq_multivariateGaussian (S := S) i
  have hj2 := memLp_eval_sq_multivariateGaussian (S := S) j
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (μ := ν) (f := fun x : EuclideanSpace ℝ (Fin d) ↦ (x i) ^ 2)
    (g := fun x : EuclideanSpace ℝ (Fin d) ↦ (x j) ^ 2)
    (ae_of_all _ fun x ↦ sq_nonneg (x i)) (ae_of_all _ fun x ↦ sq_nonneg (x j)) hi2 hj2
  simp only [one_div, Real.rpow_two] at hholder
  have hpowi : (∫ x : EuclideanSpace ℝ (Fin d), ((x i) ^ 2) ^ (2 : ℕ)
      ∂multivariateGaussian 0 S) = 3 * (S i i) ^ 2 := by
    calc
      (∫ x : EuclideanSpace ℝ (Fin d), ((x i) ^ 2) ^ (2 : ℕ)
          ∂multivariateGaussian 0 S) =
          ∫ x : EuclideanSpace ℝ (Fin d), (x i) ^ 4 ∂multivariateGaussian 0 S := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = 3 * (S i i) ^ 2 := integral_eval_pow_four_multivariateGaussian hS i
  have hpowj : (∫ x : EuclideanSpace ℝ (Fin d), ((x j) ^ 2) ^ (2 : ℕ)
      ∂multivariateGaussian 0 S) = 3 * (S j j) ^ 2 := by
    calc
      (∫ x : EuclideanSpace ℝ (Fin d), ((x j) ^ 2) ^ (2 : ℕ)
          ∂multivariateGaussian 0 S) =
          ∫ x : EuclideanSpace ℝ (Fin d), (x j) ^ 4 ∂multivariateGaussian 0 S := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = 3 * (S j j) ^ 2 := integral_eval_pow_four_multivariateGaussian hS j
  dsimp only [ν] at hholder
  calc
    (∫ x : EuclideanSpace ℝ (Fin d), (x i) ^ 2 * (x j) ^ 2
      ∂multivariateGaussian 0 S) ≤
        (∫ x : EuclideanSpace ℝ (Fin d), ((x i) ^ 2) ^ (2 : ℕ)
          ∂multivariateGaussian 0 S) ^ (2 : ℝ)⁻¹ *
        (∫ x : EuclideanSpace ℝ (Fin d), ((x j) ^ 2) ^ (2 : ℕ)
          ∂multivariateGaussian 0 S) ^ (2 : ℝ)⁻¹ := hholder
    _ = (3 * (S i i) ^ 2) ^ (2 : ℝ)⁻¹ *
        (3 * (S j j) ^ 2) ^ (2 : ℝ)⁻¹ := by rw [hpowi, hpowj]
    _ = 3 * (S i i) * (S j j) := by
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by ring]
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
        Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
        abs_of_nonneg hS.diag_nonneg, abs_of_nonneg hS.diag_nonneg]
      have hsqrt : Real.sqrt 3 * Real.sqrt 3 = 3 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      calc
        Real.sqrt 3 * S i i * (Real.sqrt 3 * S j j) =
            (Real.sqrt 3 * Real.sqrt 3) * (S i i * S j j) := by ring
        _ = 3 * S i i * S j j := by rw [hsqrt]; ring

/-- The second norm moment of a centered multivariate Gaussian is the trace of its covariance. -/
lemma integral_norm_sq_multivariateGaussian {d : ℕ}
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosSemidef) :
    (∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ 2 ∂multivariateGaussian 0 S) =
      ∑ i : Fin d, S i i := by
  have hcoord (i : Fin d) :
      (∫ x : EuclideanSpace ℝ (Fin d), (x i) ^ 2 ∂multivariateGaussian 0 S) = S i i := by
    have hInt : Integrable
        (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (multivariateGaussian 0 S) := IsGaussian.integrable_id
    have hmean : (∫ x : EuclideanSpace ℝ (Fin d), x i ∂multivariateGaussian 0 S) = 0 := by
      calc
        (∫ x : EuclideanSpace ℝ (Fin d), x i ∂multivariateGaussian 0 S) =
            (∫ x : EuclideanSpace ℝ (Fin d), x ∂multivariateGaussian 0 S) i := by
              simpa only [id_eq] using (eval_integral_piLp hInt.eval_piLp i).symm
        _ = 0 := by rw [integral_id_multivariateGaussian]; rfl
    rw [← variance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin d))) hS i,
      variance_eq_integral (by fun_prop), hmean]
    simp
  rw [show (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ 2) =
      fun x ↦ ∑ i : Fin d, (x i) ^ 2 by
        funext x
        exact EuclideanSpace.real_norm_sq_eq (n := Fin d) x]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun i _ ↦ hcoord i
  · intro i _
    exact (IsGaussian.memLp_id (multivariateGaussian 0 S) 2 (by simp)).eval_piLp i
      |>.integrable_norm_pow (by norm_num)
      |>.congr (by filter_upwards with x; simp [Real.norm_eq_abs, sq_abs])

/-- The Gaussian fourth norm moment is at most three times the square of its second moment. -/
lemma integral_norm_pow_four_multivariateGaussian_le {d : ℕ}
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosSemidef) :
    (∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ 4 ∂multivariateGaussian 0 S) ≤
      3 * (∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ 2 ∂multivariateGaussian 0 S) ^ 2 := by
  have hpoint : ∀ x : EuclideanSpace ℝ (Fin d),
      ‖x‖ ^ 4 = ∑ i : Fin d, ∑ j : Fin d, (x i) ^ 2 * (x j) ^ 2 := by
    intro x
    rw [show ‖x‖ ^ 4 = (‖x‖ ^ 2) ^ 2 by ring,
      EuclideanSpace.real_norm_sq_eq, pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  calc
    (∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ 4 ∂multivariateGaussian 0 S) =
        ∫ x : EuclideanSpace ℝ (Fin d),
          ∑ i : Fin d, ∑ j : Fin d, (x i) ^ 2 * (x j) ^ 2
            ∂multivariateGaussian 0 S := by
      apply integral_congr_ae
      filter_upwards with x
      exact hpoint x
    _ = ∑ i : Fin d, ∑ j : Fin d,
        ∫ x : EuclideanSpace ℝ (Fin d), (x i) ^ 2 * (x j) ^ 2
          ∂multivariateGaussian 0 S := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum]
        exact fun j _ ↦ integrable_eval_sq_mul_eval_sq_multivariateGaussian (S := S) i j
      · intro i _
        exact integrable_finsetSum _ fun j _ ↦
          integrable_eval_sq_mul_eval_sq_multivariateGaussian (S := S) i j
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, 3 * S i i * S j j := by
      exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
        integral_eval_sq_mul_eval_sq_multivariateGaussian_le hS i j
    _ = 3 * (∑ i : Fin d, S i i) ^ 2 := by
      simp_rw [mul_assoc, ← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring
    _ = 3 * (∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ 2
        ∂multivariateGaussian 0 S) ^ 2 := by rw [integral_norm_sq_multivariateGaussian hS]

/-- Monotonicity of the real-valued `Lᵖ` norm on a probability space. -/
lemma lpNorm_mono_exponent_of_isProbabilityMeasure
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → E} {p q : ℝ≥0∞}
    (hfq : MemLp f q μ) (hpq : p ≤ q) : lpNorm f p μ ≤ lpNorm f q μ := by
  have hfp := hfq.mono_exponent hpq
  rw [← toReal_eLpNorm hfp.aestronglyMeasurable,
    ← toReal_eLpNorm hfq.aestronglyMeasurable]
  exact ENNReal.toReal_mono hfq.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le hpq hfq.1)

/-- The square of the real `L²` norm is the second norm moment. -/
lemma lpNorm_two_sq_eq_integral_norm_sq
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} {f : Ω → E} (hf : MemLp f 2 μ) :
    lpNorm f 2 μ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (p := _) (by norm_num) (by simp)
    hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  have hrpow : (∫ x : Ω, ‖f x‖ ^ (2 : ℝ) ∂μ) = ∫ x : Ω, ‖f x‖ ^ (2 : ℕ) ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    exact Real.rpow_natCast _ 2
  rw [hrpow]
  exact Real.rpow_inv_natCast_pow (n := 2)
    (x := ∫ x : Ω, ‖f x‖ ^ 2 ∂μ)
    (integral_nonneg fun x ↦ pow_nonneg (norm_nonneg _) _) (by norm_num)

/-- The cube of the real `L³` norm is the third norm moment. -/
lemma lpNorm_three_cube_eq_integral_norm_pow_three
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} {f : Ω → E} (hf : MemLp f 3 μ) :
    lpNorm f 3 μ ^ 3 = ∫ x, ‖f x‖ ^ 3 ∂μ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (p := _) (by norm_num) (by simp)
    hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  have hrpow : (∫ x : Ω, ‖f x‖ ^ (3 : ℝ) ∂μ) = ∫ x : Ω, ‖f x‖ ^ (3 : ℕ) ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    exact Real.rpow_natCast _ 3
  rw [hrpow]
  exact Real.rpow_inv_natCast_pow (n := 3)
    (x := ∫ x : Ω, ‖f x‖ ^ 3 ∂μ)
    (integral_nonneg fun x ↦ pow_nonneg (norm_nonneg _) _) (by norm_num)

private lemma lpNorm_four_pow_four_eq_integral_norm_pow_four
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} {f : Ω → E} (hf : MemLp f 4 μ) :
    lpNorm f 4 μ ^ 4 = ∫ x, ‖f x‖ ^ 4 ∂μ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (p := _) (by norm_num) (by simp)
    hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  have hrpow : (∫ x : Ω, ‖f x‖ ^ (4 : ℝ) ∂μ) = ∫ x : Ω, ‖f x‖ ^ (4 : ℕ) ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    exact Real.rpow_natCast _ 4
  rw [hrpow]
  exact Real.rpow_inv_natCast_pow (n := 4)
    (x := ∫ x : Ω, ‖f x‖ ^ 4 ∂μ)
    (integral_nonneg fun x ↦ pow_nonneg (norm_nonneg _) _) (by norm_num)

/-- A centered Euclidean random vector's second norm moment is the trace of its covariance
matrix. -/
lemma integral_norm_sq_eq_trace_covarianceMatrix
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ (Fin d)}
    (hX : MemLp X 2 μ) (hX0 : ∫ ω, X ω ∂μ = 0) :
    (∫ ω, ‖X ω‖ ^ 2 ∂μ) = ∑ i : Fin d, covarianceMatrix (μ.map X) i i := by
  have hcoord (i : Fin d) :
      (∫ ω, (X ω i) ^ 2 ∂μ) = covarianceMatrix (μ.map X) i i := by
    calc
      (∫ ω, (X ω i) ^ 2 ∂μ) = ∫ ω, X ω i * X ω i ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        rw [pow_two]
      _ =
          covarianceBilin (μ.map X)
            (EuclideanSpace.basisFun (Fin d) ℝ i)
            (EuclideanSpace.basisFun (Fin d) ℝ i) :=
        integral_coordinate_mul_eq_covarianceBilin hX hX0 i i
      _ = (EuclideanSpace.basisFun (Fin d) ℝ i) ⬝ᵥ
          covarianceMatrix (μ.map X) *ᵥ
            (EuclideanSpace.basisFun (Fin d) ℝ i) :=
        (dotProduct_covarianceMatrix_mulVec (μ.map X)
          (EuclideanSpace.basisFun (Fin d) ℝ i)
          (EuclideanSpace.basisFun (Fin d) ℝ i)).symm
      _ = covarianceMatrix (μ.map X) i i := by simp
  rw [show (fun ω ↦ ‖X ω‖ ^ 2) = fun ω ↦ ∑ i : Fin d, (X ω i) ^ 2 by
      funext ω
      exact EuclideanSpace.real_norm_sq_eq (n := Fin d) (X ω)]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun i _ ↦ hcoord i
  · intro i _
    exact (hX.eval_piLp i).integrable_norm_pow (by norm_num) |>.congr
      (by filter_upwards with ω; simp [Real.norm_eq_abs, sq_abs])

/-- The explicit absolute constant used for the Gaussian-companion third-moment comparison. -/
def gaussianCompanionThirdMomentConstant : ℝ := 27

lemma gaussianCompanionThirdMomentConstant_pos : 0 < gaussianCompanionThirdMomentConstant := by
  norm_num [gaussianCompanionThirdMomentConstant]

/-- A centered Gaussian with the covariance of `X` has a dimension-free third norm moment bounded
by an absolute multiple of the third norm moment of `X`.  The covariance may be singular. -/
theorem integral_norm_pow_three_multivariateGaussian_covarianceMatrix_le
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ (Fin d)}
    (hX3 : MemLp X 3 μ) (hX0 : ∫ ω, X ω ∂μ = 0) :
    (∫ y : EuclideanSpace ℝ (Fin d), ‖y‖ ^ 3
        ∂multivariateGaussian 0 (covarianceMatrix (μ.map X))) ≤
      gaussianCompanionThirdMomentConstant * ∫ ω, ‖X ω‖ ^ 3 ∂μ := by
  let S := covarianceMatrix (μ.map X)
  let ν := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S
  have hS : S.PosSemidef := covarianceMatrix_posSemidef (μ.map X)
  have hX2 : MemLp X 2 μ := hX3.mono_exponent (by norm_num)
  have hY4 : MemLp id 4 ν := IsGaussian.memLp_id ν 4 (by simp)
  have hY3 : MemLp id 3 ν := hY4.mono_exponent (by norm_num)
  have hY2 : MemLp id 2 ν := hY4.mono_exponent (by norm_num)
  have hsecond : lpNorm id 2 ν = lpNorm X 2 μ := by
    have hsquares : lpNorm id 2 ν ^ 2 = lpNorm X 2 μ ^ 2 := by
      rw [lpNorm_two_sq_eq_integral_norm_sq hY2,
        lpNorm_two_sq_eq_integral_norm_sq hX2]
      simpa only [id_eq, ν, S] using
        (integral_norm_sq_multivariateGaussian hS).trans
          (integral_norm_sq_eq_trace_covarianceMatrix hX2 hX0).symm
    nlinarith [lpNorm_nonneg (f := id) (p := (2 : ℝ≥0∞)) (μ := ν),
      lpNorm_nonneg (f := X) (p := (2 : ℝ≥0∞)) (μ := μ)]
  have hfour : lpNorm id 4 ν ^ 4 ≤ 3 * lpNorm id 2 ν ^ 4 := by
    rw [lpNorm_four_pow_four_eq_integral_norm_pow_four hY4]
    calc
      (∫ x, ‖id x‖ ^ 4 ∂ν) ≤ 3 * (∫ x, ‖id x‖ ^ 2 ∂ν) ^ 2 := by
        simpa only [id_eq, ν] using integral_norm_pow_four_multivariateGaussian_le hS
      _ = 3 * lpNorm id 2 ν ^ 4 := by
        rw [← lpNorm_two_sq_eq_integral_norm_sq hY2]
        ring
  have hY4Y2 : lpNorm id 4 ν ≤ 3 * lpNorm id 2 ν := by
    have hnonneg4 : 0 ≤ lpNorm id 4 ν := lpNorm_nonneg
    have hnonneg2 : 0 ≤ 3 * lpNorm id 2 ν := mul_nonneg (by norm_num) lpNorm_nonneg
    apply (pow_le_pow_iff_left₀ hnonneg4 hnonneg2 (by norm_num : (4 : ℕ) ≠ 0)).mp
    calc
      lpNorm id 4 ν ^ 4 ≤ 3 * lpNorm id 2 ν ^ 4 := hfour
      _ ≤ (3 * lpNorm id 2 ν) ^ 4 := by
        have hpow : 0 ≤ lpNorm id 2 ν ^ 4 := pow_nonneg lpNorm_nonneg _
        nlinarith
  have hY3Y4 : lpNorm id 3 ν ≤ lpNorm id 4 ν :=
    lpNorm_mono_exponent_of_isProbabilityMeasure hY4 (by norm_num)
  have hX2X3 : lpNorm X 2 μ ≤ lpNorm X 3 μ :=
    lpNorm_mono_exponent_of_isProbabilityMeasure hX3 (by norm_num)
  have hlp : lpNorm id 3 ν ≤ 3 * lpNorm X 3 μ := by
    calc
      lpNorm id 3 ν ≤ lpNorm id 4 ν := hY3Y4
      _ ≤ 3 * lpNorm id 2 ν := hY4Y2
      _ = 3 * lpNorm X 2 μ := by rw [hsecond]
      _ ≤ 3 * lpNorm X 3 μ := by gcongr
  change (∫ y, ‖id y‖ ^ 3 ∂ν) ≤
    gaussianCompanionThirdMomentConstant * ∫ ω, ‖X ω‖ ^ 3 ∂μ
  rw [← lpNorm_three_cube_eq_integral_norm_pow_three hY3,
    ← lpNorm_three_cube_eq_integral_norm_pow_three hX3]
  calc
    lpNorm id 3 ν ^ 3 ≤ (3 * lpNorm X 3 μ) ^ 3 :=
      pow_le_pow_left₀ lpNorm_nonneg hlp 3
    _ = gaussianCompanionThirdMomentConstant * lpNorm X 3 μ ^ 3 := by
      norm_num [gaussianCompanionThirdMomentConstant]
      ring

private lemma integral_norm_pow_comp_measurePreserving
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [NormedAddCommGroup E] [BorelSpace E]
    {μ : Measure Ω} {ν : Measure E} {f : Ω → E}
    (hf : MeasurePreserving f μ ν) (k : ℕ) :
    (∫ ω, ‖f ω‖ ^ k ∂μ) = ∫ x, ‖x‖ ^ k ∂ν := by
  calc
    (∫ ω, ‖f ω‖ ^ k ∂μ) = ∫ x, ‖x‖ ^ k ∂(μ.map f) := by
      exact (integral_map hf.measurable.aemeasurable
        ((by fun_prop : Measurable (fun x : E ↦ ‖x‖ ^ k)).aestronglyMeasurable)).symm
    _ = ∫ x, ‖x‖ ^ k ∂ν := by rw [hf.map_eq]

private lemma integral_norm_pow_replacementOriginal_eq
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i)) (i : Fin n) (k : ℕ) :
    (∫ ω, ‖replacementOriginal (d := d) i ω‖ ^ k
        ∂(bentkusReplacementMeasure μ X)) = ∫ ω, ‖X i ω‖ ^ k ∂μ := by
  calc
    (∫ ω, ‖replacementOriginal (d := d) i ω‖ ^ k
        ∂(bentkusReplacementMeasure μ X)) =
        ∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ k ∂(μ.map (X i)) :=
      integral_norm_pow_comp_measurePreserving
        (measurePreserving_replacementOriginal hXm i) k
    _ = ∫ ω, ‖X i ω‖ ^ k ∂μ := by
      exact integral_map (hXm i).aemeasurable
        ((by fun_prop : Measurable
          (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ k)).aestronglyMeasurable)

/-- Exact second-norm-moment matching for one original coordinate and its Gaussian companion on
the canonical replacement space. -/
lemma integral_norm_sq_replacementGaussian_eq_replacementOriginal
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i)) (hX2 : ∀ i, MemLp (X i) 2 μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0) (i : Fin n) :
    (∫ ω, ‖replacementGaussian (d := d) i ω‖ ^ 2
        ∂(bentkusReplacementMeasure μ X)) =
      ∫ ω, ‖replacementOriginal (d := d) i ω‖ ^ 2
        ∂(bentkusReplacementMeasure μ X) := by
  let S := summandCovarianceMatrix μ X i
  calc
    (∫ ω, ‖replacementGaussian (d := d) i ω‖ ^ 2
        ∂(bentkusReplacementMeasure μ X)) =
        ∫ y : EuclideanSpace ℝ (Fin d), ‖y‖ ^ 2 ∂multivariateGaussian 0 S := by
      simpa only [S] using integral_norm_pow_comp_measurePreserving
        (measurePreserving_replacementGaussian hXm i) 2
    _ = ∑ j : Fin d, covarianceMatrix (μ.map (X i)) j j := by
      simpa only [S, summandCovarianceMatrix] using
        integral_norm_sq_multivariateGaussian
          (covarianceMatrix_posSemidef (μ.map (X i)))
    _ = ∫ ω, ‖X i ω‖ ^ 2 ∂μ :=
      (integral_norm_sq_eq_trace_covarianceMatrix (hX2 i) (hX0 i)).symm
    _ = ∫ ω, ‖replacementOriginal (d := d) i ω‖ ^ 2
        ∂(bentkusReplacementMeasure μ X) := by
      symm
      exact integral_norm_pow_replacementOriginal_eq hXm i 2

/-- Bentkus's dimension-free Gaussian-companion comparison, realized on the canonical replacement
space.  This is the explicit-constant form of the `E ‖Y‖³ ≪ E ‖X‖³` estimate used on p. 408
after equation (3.35). -/
theorem integral_norm_pow_three_replacementGaussian_le
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i)) (hX3 : ∀ i, MemLp (X i) 3 μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0) (i : Fin n) :
    (∫ ω, ‖replacementGaussian (d := d) i ω‖ ^ 3
        ∂(bentkusReplacementMeasure μ X)) ≤
      gaussianCompanionThirdMomentConstant *
        ∫ ω, ‖replacementOriginal (d := d) i ω‖ ^ 3
          ∂(bentkusReplacementMeasure μ X) := by
  have hbase := integral_norm_pow_three_multivariateGaussian_covarianceMatrix_le
    (μ := μ) (X := X i) (hX3 i) (hX0 i)
  calc
    (∫ ω, ‖replacementGaussian (d := d) i ω‖ ^ 3
        ∂(bentkusReplacementMeasure μ X)) =
        ∫ y : EuclideanSpace ℝ (Fin d), ‖y‖ ^ 3
          ∂multivariateGaussian 0 (covarianceMatrix (μ.map (X i))) := by
      simpa only [summandCovarianceMatrix] using integral_norm_pow_comp_measurePreserving
        (measurePreserving_replacementGaussian hXm i) 3
    _ ≤ gaussianCompanionThirdMomentConstant * ∫ ω, ‖X i ω‖ ^ 3 ∂μ := hbase
    _ = gaussianCompanionThirdMomentConstant *
        ∫ ω, ‖replacementOriginal (d := d) i ω‖ ^ 3
          ∂(bentkusReplacementMeasure μ X) := by
      rw [integral_norm_pow_replacementOriginal_eq hXm i 3]

/-- The mixed Hölder estimate used immediately before Bentkus (3.30), on the canonical
replacement space: `E (‖X‖² ‖Y‖) ≤ E ‖X‖³`. -/
lemma integral_norm_sq_replacementOriginal_mul_norm_replacementGaussian_le
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i)) (hX3 : ∀ i, MemLp (X i) 3 μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0) (i : Fin n) :
    (∫ ω, ‖replacementOriginal (d := d) i ω‖ ^ 2 *
        ‖replacementGaussian (d := d) i ω‖
      ∂(bentkusReplacementMeasure μ X)) ≤
      ∫ ω, ‖replacementOriginal (d := d) i ω‖ ^ 3
        ∂(bentkusReplacementMeasure μ X) := by
  let ρ := bentkusReplacementMeasure μ X
  let O := replacementOriginal (d := d) i
  let G := replacementGaussian (d := d) i
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hO3 : MemLp O 3 ρ := memLp_replacementOriginal hXm hX3 i
  have hG3 : MemLp G 3 ρ := memLp_three_replacementGaussian hXm i
  have hO2 : MemLp O 2 ρ := hO3.mono_exponent (by norm_num)
  have hG2 : MemLp G 2 ρ := hG3.mono_exponent (by norm_num)
  have hG1 : MemLp G 1 ρ := hG3.mono_exponent (by norm_num)
  have hsecond : lpNorm O 2 ρ = lpNorm G 2 ρ := by
    have hsquares : lpNorm O 2 ρ ^ 2 = lpNorm G 2 ρ ^ 2 := by
      rw [lpNorm_two_sq_eq_integral_norm_sq hO2,
        lpNorm_two_sq_eq_integral_norm_sq hG2]
      simpa only [O, G, ρ] using
        (integral_norm_sq_replacementGaussian_eq_replacementOriginal
          hXm (fun j ↦ (hX3 j).mono_exponent (by norm_num)) hX0 i).symm
    nlinarith [lpNorm_nonneg (f := O) (p := (2 : ℝ≥0∞)) (μ := ρ),
      lpNorm_nonneg (f := G) (p := (2 : ℝ≥0∞)) (μ := ρ)]
  have hG1O3 : lpNorm G 1 ρ ≤ lpNorm O 3 ρ := by
    calc
      lpNorm G 1 ρ ≤ lpNorm G 2 ρ :=
        lpNorm_mono_exponent_of_isProbabilityMeasure hG2 (by norm_num)
      _ = lpNorm O 2 ρ := hsecond.symm
      _ ≤ lpNorm O 3 ρ :=
        lpNorm_mono_exponent_of_isProbabilityMeasure hO3 (by norm_num)
  have hO2O3 : lpNorm O 2 ρ ≤ lpNorm O 3 ρ :=
    lpNorm_mono_exponent_of_isProbabilityMeasure hO3 (by norm_num)
  have hind : (fun ω ↦ ‖O ω‖ ^ 2) ⟂ᵢ[ρ] (fun ω ↦ ‖G ω‖) := by
    change ((fun z : EuclideanSpace ℝ (Fin d) ↦ ‖z‖ ^ 2) ∘ O) ⟂ᵢ[ρ]
      ((fun z : EuclideanSpace ℝ (Fin d) ↦ ‖z‖) ∘ G)
    exact (indepFun_replacementOriginal_replacementGaussian hXm i i).comp
      (by fun_prop) (by fun_prop)
  have hG1nonneg : 0 ≤ lpNorm G 1 ρ := lpNorm_nonneg
  have hO2nonneg : 0 ≤ lpNorm O 2 ρ := lpNorm_nonneg
  calc
    (∫ ω, ‖replacementOriginal (d := d) i ω‖ ^ 2 *
        ‖replacementGaussian (d := d) i ω‖ ∂(bentkusReplacementMeasure μ X)) =
        (∫ ω, ‖O ω‖ ^ 2 ∂ρ) * ∫ ω, ‖G ω‖ ∂ρ := by
      simpa only [O, G, ρ] using hind.integral_fun_mul_eq_mul_integral
        (hO2.aestronglyMeasurable.norm.pow 2) hG1.aestronglyMeasurable.norm
    _ = lpNorm O 2 ρ ^ 2 * lpNorm G 1 ρ := by
      rw [lpNorm_two_sq_eq_integral_norm_sq hO2,
        lpNorm_one_eq_integral_norm hG1.aestronglyMeasurable]
    _ ≤ lpNorm O 3 ρ ^ 2 * lpNorm O 3 ρ := by gcongr
    _ = lpNorm O 3 ρ ^ 3 := by ring
    _ = ∫ ω, ‖replacementOriginal (d := d) i ω‖ ^ 3
        ∂(bentkusReplacementMeasure μ X) := by
      simpa only [O, ρ] using lpNorm_three_cube_eq_integral_norm_pow_three hO3

/-- The companion-side mixed moment used after Bentkus (3.35): covariance matching and Hölder give
`E ‖Y‖² · E ‖X‖ ≤ E ‖X‖³`. -/
lemma integral_norm_sq_replacementGaussian_mul_integral_norm_replacementOriginal_le
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i)) (hX3 : ∀ i, MemLp (X i) 3 μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0) (i : Fin n) :
    (∫ ω, ‖replacementGaussian (d := d) i ω‖ ^ 2
        ∂(bentkusReplacementMeasure μ X)) *
      (∫ ω, ‖replacementOriginal (d := d) i ω‖
        ∂(bentkusReplacementMeasure μ X)) ≤
      ∫ ω, ‖replacementOriginal (d := d) i ω‖ ^ 3
        ∂(bentkusReplacementMeasure μ X) := by
  let ρ := bentkusReplacementMeasure μ X
  let O := replacementOriginal (d := d) i
  let G := replacementGaussian (d := d) i
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hO3 : MemLp O 3 ρ := memLp_replacementOriginal hXm hX3 i
  have hG3 : MemLp G 3 ρ := memLp_three_replacementGaussian hXm i
  have hO2 : MemLp O 2 ρ := hO3.mono_exponent (by norm_num)
  have hG2 : MemLp G 2 ρ := hG3.mono_exponent (by norm_num)
  have hO1 : MemLp O 1 ρ := hO3.mono_exponent (by norm_num)
  have hsecond : lpNorm G 2 ρ = lpNorm O 2 ρ := by
    have hsquares : lpNorm G 2 ρ ^ 2 = lpNorm O 2 ρ ^ 2 := by
      rw [lpNorm_two_sq_eq_integral_norm_sq hG2,
        lpNorm_two_sq_eq_integral_norm_sq hO2]
      simpa only [O, G, ρ] using
        integral_norm_sq_replacementGaussian_eq_replacementOriginal
          hXm (fun j ↦ (hX3 j).mono_exponent (by norm_num)) hX0 i
    nlinarith [lpNorm_nonneg (f := G) (p := (2 : ℝ≥0∞)) (μ := ρ),
      lpNorm_nonneg (f := O) (p := (2 : ℝ≥0∞)) (μ := ρ)]
  have hO1O3 : lpNorm O 1 ρ ≤ lpNorm O 3 ρ :=
    lpNorm_mono_exponent_of_isProbabilityMeasure hO3 (by norm_num)
  have hO2O3 : lpNorm O 2 ρ ≤ lpNorm O 3 ρ :=
    lpNorm_mono_exponent_of_isProbabilityMeasure hO3 (by norm_num)
  calc
    (∫ ω, ‖replacementGaussian (d := d) i ω‖ ^ 2
        ∂(bentkusReplacementMeasure μ X)) *
      (∫ ω, ‖replacementOriginal (d := d) i ω‖
        ∂(bentkusReplacementMeasure μ X)) =
        lpNorm G 2 ρ ^ 2 * lpNorm O 1 ρ := by
      rw [lpNorm_two_sq_eq_integral_norm_sq hG2,
        lpNorm_one_eq_integral_norm hO1.aestronglyMeasurable]
    _ = lpNorm O 2 ρ ^ 2 * lpNorm O 1 ρ := by rw [hsecond]
    _ ≤ lpNorm O 3 ρ ^ 2 * lpNorm O 3 ρ := by
      have hO1nonneg : 0 ≤ lpNorm O 1 ρ := lpNorm_nonneg
      have hO2nonneg : 0 ≤ lpNorm O 2 ρ := lpNorm_nonneg
      gcongr
    _ = lpNorm O 3 ρ ^ 3 := by ring
    _ = ∫ ω, ‖replacementOriginal (d := d) i ω‖ ^ 3
        ∂(bentkusReplacementMeasure μ X) := by
      simpa only [O, ρ] using lpNorm_three_cube_eq_integral_norm_pow_three hO3

/-- The combined moment estimate stated in the discussion following Bentkus (3.35), with the
implicit absolute constant made explicit. -/
lemma integral_norm_pow_three_replacementGaussian_add_mixed_le
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i)) (hX3 : ∀ i, MemLp (X i) 3 μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0) (i : Fin n) :
    (∫ ω, ‖replacementGaussian (d := d) i ω‖ ^ 3
        ∂(bentkusReplacementMeasure μ X)) +
      (∫ ω, ‖replacementGaussian (d := d) i ω‖ ^ 2
        ∂(bentkusReplacementMeasure μ X)) *
      (∫ ω, ‖replacementOriginal (d := d) i ω‖
        ∂(bentkusReplacementMeasure μ X)) ≤
      (gaussianCompanionThirdMomentConstant + 1) *
        ∫ ω, ‖replacementOriginal (d := d) i ω‖ ^ 3
          ∂(bentkusReplacementMeasure μ X) := by
  calc
    (∫ ω, ‖replacementGaussian (d := d) i ω‖ ^ 3
        ∂(bentkusReplacementMeasure μ X)) +
      (∫ ω, ‖replacementGaussian (d := d) i ω‖ ^ 2
        ∂(bentkusReplacementMeasure μ X)) *
      (∫ ω, ‖replacementOriginal (d := d) i ω‖
        ∂(bentkusReplacementMeasure μ X)) ≤
      gaussianCompanionThirdMomentConstant *
          (∫ ω, ‖replacementOriginal (d := d) i ω‖ ^ 3
            ∂(bentkusReplacementMeasure μ X)) +
        ∫ ω, ‖replacementOriginal (d := d) i ω‖ ^ 3
          ∂(bentkusReplacementMeasure μ X) :=
      add_le_add (integral_norm_pow_three_replacementGaussian_le hXm hX3 hX0 i)
        (integral_norm_sq_replacementGaussian_mul_integral_norm_replacementOriginal_le
          hXm hX3 hX0 i)
    _ = (gaussianCompanionThirdMomentConstant + 1) *
        ∫ ω, ‖replacementOriginal (d := d) i ω‖ ^ 3
          ∂(bentkusReplacementMeasure μ X) := by ring

end ProbabilityTheory
