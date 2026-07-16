/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import Mathlib.Analysis.MeanInequalities

/-!
# Parameter closure for Bentkus's induction

This module isolates the final scalar calculation on Bentkus (2004), printed page 404,
equations (3.9)--(3.10).  The smoothing scale is `β * sqrt C`.  The two branches below say that
this scale is either below one, where the Taylor estimate applies, or at least one, where the
trivial probability bound is already sufficient.
-/

noncomputable section

namespace ProbabilityTheory

/-- The parameter choice `ε = β * sqrt C` closes Bentkus's induction once the absolute constant
dominates the coefficient in the Taylor estimate. -/
lemma bentkus_parameter_closure {K C d β Δ : ℝ}
    (hC : 1 ≤ C) (hKC : K * (2 * Real.sqrt C + 1) ≤ C)
    (hd : 1 ≤ d) (hβ : 0 < β) (hΔ1 : Δ ≤ 1)
    (hmain : β * Real.sqrt C < 1 →
      Δ ≤ K * d ^ (1 / 4 : ℝ) *
        (β * Real.sqrt C + β + C * β ^ 2 / (β * Real.sqrt C))) :
    Δ ≤ C * d ^ (1 / 4 : ℝ) * β := by
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hsqrtpos : 0 < Real.sqrt C := Real.sqrt_pos.2 (lt_of_lt_of_le (by norm_num) hC)
  have hdq : 1 ≤ d ^ (1 / 4 : ℝ) := Real.one_le_rpow hd (by norm_num)
  have hquot : C * β ^ 2 / (β * Real.sqrt C) = β * Real.sqrt C := by
    field_simp [ne_of_gt hβ, ne_of_gt hsqrtpos]
    nlinarith [Real.sq_sqrt hC0]
  by_cases hsmall : β * Real.sqrt C < 1
  · have h := hmain hsmall
    rw [hquot] at h
    have hscale := mul_le_mul_of_nonneg_right hKC
      (mul_nonneg (le_trans (by norm_num) hdq) hβ.le)
    calc
      Δ ≤ K * d ^ (1 / 4 : ℝ) *
          (β * Real.sqrt C + β + β * Real.sqrt C) := h
      _ = (K * (2 * Real.sqrt C + 1)) * (d ^ (1 / 4 : ℝ) * β) := by ring
      _ ≤ C * (d ^ (1 / 4 : ℝ) * β) := hscale
      _ = C * d ^ (1 / 4 : ℝ) * β := by ring
  · have hlarge : 1 ≤ β * Real.sqrt C := le_of_not_gt hsmall
    have hsqrtC : Real.sqrt C ≤ C := by
      nlinarith [Real.sq_sqrt hC0]
    have hfirst : β * Real.sqrt C ≤ β * C :=
      mul_le_mul_of_nonneg_left hsqrtC hβ.le
    have hsecond : β * C ≤ (β * C) * d ^ (1 / 4 : ℝ) := by
      have := mul_le_mul_of_nonneg_left hdq (mul_nonneg hβ.le hC0)
      simpa using this
    calc
      Δ ≤ 1 := hΔ1
      _ ≤ β * Real.sqrt C := hlarge
      _ ≤ β * C := hfirst
      _ ≤ (β * C) * d ^ (1 / 4 : ℝ) := hsecond
      _ = C * d ^ (1 / 4 : ℝ) * β := by ring

end ProbabilityTheory
