/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Angle integrals in Bentkus's Gaussian replacement argument

This module records the elementary trigonometric integrations used when Bentkus splits the
replacement rotation at an angle `γ`.  In particular, the large-angle remainder has density
`cos α / sin² α`, whose exact integral is the reciprocal-sine endpoint difference.
-/

open Set MeasureTheory

noncomputable section

namespace ProbabilityTheory

/-- The reciprocal-sine derivative is interval integrable away from the zero of sine. -/
theorem intervalIntegrable_cos_div_sin_sq {γ : ℝ} (hγ : 0 < γ)
    (hγpi : γ ≤ Real.pi / 2) :
    IntervalIntegrable (fun α ↦ Real.cos α / Real.sin α ^ 2)
      volume γ (Real.pi / 2) := by
  have hhalfpi : Real.pi / 2 < Real.pi := by
    linarith [Real.pi_pos]
  have hsinne : ∀ x ∈ Icc γ (Real.pi / 2), Real.sin x ≠ 0 := by
    intro x hx
    exact (Real.sin_pos_of_pos_of_lt_pi (hγ.trans_le hx.1)
      (hx.2.trans_lt hhalfpi)).ne'
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hγpi]
  exact Real.continuous_cos.continuousOn.div
    (Real.continuous_sin.continuousOn.pow 2)
    (fun x hx ↦ pow_ne_zero 2 (hsinne x hx))

/-- The exact large-angle integral in Bentkus (2004), equations (3.13)--(3.14). -/
theorem intervalIntegral_cos_div_sin_sq {γ : ℝ} (hγ : 0 < γ)
    (hγpi : γ ≤ Real.pi / 2) :
    (∫ α in γ..Real.pi / 2, Real.cos α / Real.sin α ^ 2) =
      (Real.sin γ)⁻¹ - 1 := by
  have hhalfpi : Real.pi / 2 < Real.pi := by linarith [Real.pi_pos]
  have hsinne : ∀ x ∈ Icc γ (Real.pi / 2), Real.sin x ≠ 0 := by
    intro x hx
    exact (Real.sin_pos_of_pos_of_lt_pi (hγ.trans_le hx.1)
      (hx.2.trans_lt hhalfpi)).ne'
  let F : ℝ → ℝ := -Real.sin⁻¹
  have hcont : ContinuousOn F (Icc γ (Real.pi / 2)) :=
    (Real.continuous_sin.continuousOn.inv₀ hsinne).neg
  have hderiv : ∀ x ∈ Ioo γ (Real.pi / 2),
      HasDerivAt F (Real.cos x / Real.sin x ^ 2) x := by
    intro x hx
    have hxIcc : x ∈ Icc γ (Real.pi / 2) := ⟨hx.1.le, hx.2.le⟩
    have h := ((Real.hasDerivAt_sin x).inv (hsinne x hxIcc)).neg
    change HasDerivAt (-Real.sin⁻¹) (Real.cos x / Real.sin x ^ 2) x
    have heq : Real.cos x / Real.sin x ^ 2 =
        -(-Real.cos x / Real.sin x ^ 2) := by ring
    rw [heq]
    exact h
  have hint : IntervalIntegrable (fun x : ℝ ↦ Real.cos x / Real.sin x ^ 2)
      volume γ (Real.pi / 2) :=
    intervalIntegrable_cos_div_sin_sq hγ hγpi
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hγpi hcont hderiv hint
  dsimp only [F] at hfund
  simpa [Real.sin_pi_div_two, sub_eq_add_neg, add_comm] using hfund

/-- The large-angle integral is at most the reciprocal of its lower-end sine. -/
theorem intervalIntegral_cos_div_sin_sq_le_inv {γ : ℝ} (hγ : 0 < γ)
    (hγpi : γ ≤ Real.pi / 2) :
    (∫ α in γ..Real.pi / 2, Real.cos α / Real.sin α ^ 2) ≤
      (Real.sin γ)⁻¹ := by
  rw [intervalIntegral_cos_div_sin_sq hγ hγpi]
  linarith

/-- With Bentkus's choice `γ = arcsin ε`, the exact large-angle integral is `ε⁻¹ - 1`. -/
theorem intervalIntegral_cos_div_sin_sq_arcsin {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    (∫ α in Real.arcsin ε..Real.pi / 2,
        Real.cos α / Real.sin α ^ 2) = ε⁻¹ - 1 := by
  rw [intervalIntegral_cos_div_sin_sq (Real.arcsin_pos.mpr hε)
    (Real.arcsin_le_pi_div_two ε), Real.sin_arcsin (by linarith) hε1]

/-- The small-angle cosine mass becomes exactly `ε` at `γ = arcsin ε`. -/
theorem intervalIntegral_cos_zero_arcsin {ε : ℝ} (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    (∫ α in (0 : ℝ)..Real.arcsin ε, Real.cos α) = ε := by
  rw [integral_cos, Real.sin_arcsin (by linarith) hε1, Real.sin_zero, sub_zero]

/-- The Gaussian-reference part of Bentkus's angle split has length at most two. -/
theorem pi_div_two_sub_arcsin_le_two {ε : ℝ} (hε : 0 ≤ ε) :
    Real.pi / 2 - Real.arcsin ε ≤ 2 := by
  have hasin : 0 ≤ Real.arcsin ε := Real.arcsin_nonneg.mpr hε
  nlinarith [Real.pi_lt_four]

/-- Exact three-piece decomposition at an intermediate angle: the initial actual contribution,
the later actual-minus-reference contribution, and the later reference contribution. -/
theorem intervalIntegral_eq_small_add_difference_add_reference
    {F R : ℝ → ℝ} {γ b : ℝ}
    (hF0γ : IntervalIntegrable F volume 0 γ)
    (hFγb : IntervalIntegrable F volume γ b)
    (hRγb : IntervalIntegrable R volume γ b) :
    (∫ α in (0 : ℝ)..b, F α) =
      (∫ α in (0 : ℝ)..γ, F α) +
        (∫ α in γ..b, F α - R α) +
        ∫ α in γ..b, R α := by
  rw [← intervalIntegral.integral_add_adjacent_intervals hF0γ hFγb,
    intervalIntegral.integral_sub hFγb hRγb]
  ring

/-- Integrating a Bentkus large-angle envelope from `arcsin ε` costs at most one factor
of `ε⁻¹`. -/
theorem bentkus_largeAngle_integral_le_of_cos_div_sin_sq_envelope
    {ε K : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hK : 0 ≤ K)
    {F : ℝ → ℝ}
    (hF : ∀ α ∈ Set.Ioc (Real.arcsin ε) (Real.pi / 2),
      |F α| ≤ K * (Real.cos α / Real.sin α ^ 2)) :
    |∫ α in Real.arcsin ε..Real.pi / 2, F α| ≤ K / ε := by
  have horder : Real.arcsin ε ≤ Real.pi / 2 :=
    Real.arcsin_le_pi_div_two ε
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ α in Real.arcsin ε..Real.pi / 2, F α‖ ≤
        ∫ α in Real.arcsin ε..Real.pi / 2,
          K * (Real.cos α / Real.sin α ^ 2) := by
      apply intervalIntegral.norm_integral_le_of_norm_le horder
      · filter_upwards with α
        intro hα
        simpa only [Real.norm_eq_abs] using hF α hα
      · exact (intervalIntegrable_cos_div_sin_sq
          (Real.arcsin_pos.mpr hε) horder).const_mul K
    _ = K * (ε⁻¹ - 1) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral_cos_div_sin_sq_arcsin hε hε1]
    _ ≤ K / ε := by
      rw [div_eq_mul_inv]
      nlinarith

end ProbabilityTheory
