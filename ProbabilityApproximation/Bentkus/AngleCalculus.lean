/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Angle integrals in Bentkus's Gaussian replacement argument

This module records the elementary trigonometric integrations used when Bentkus splits the
replacement rotation at an angle `γ`.  In particular, the large-angle remainder has density
`cos α / sin² α`, whose exact integral is the reciprocal-sine endpoint difference.
-/

open Set MeasureTheory

noncomputable section

namespace ProbabilityTheory

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
      volume γ (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hγpi]
    exact Real.continuous_cos.continuousOn.div
      (Real.continuous_sin.continuousOn.pow 2)
      (fun x hx ↦ pow_ne_zero 2 (hsinne x hx))
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

end ProbabilityTheory
