/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Truncated-moment comparison (SPEC §4.3)

Elementary real inequalities used to derive the finite-third-moment nonuniform
Berry–Esseen corollary from the truncated Chen–Shao theorem.
-/

open Real

namespace ProbabilityTheory

/-- On `{r < |y|}` with `r > 0`, one has `y² / r² ≤ |y|³ / r³`. -/
lemma sq_div_sq_le_abs_cube_div_cube {y r : ℝ} (hr : 0 < r) (hy : r < |y|) :
    y ^ 2 / r ^ 2 ≤ |y| ^ 3 / r ^ 3 := by
  have hr0 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hr1 : 0 < r ^ 3 := pow_pos hr 3
  rw [div_le_div_iff₀ hr0 hr1]
  have hy0 : 0 ≤ |y| := abs_nonneg _
  have hrnn : 0 ≤ r := hr.le
  calc
    y ^ 2 * r ^ 3 = |y| ^ 2 * r ^ 3 := by rw [sq_abs]
    _ = |y| ^ 2 * r ^ 2 * r := by ring
    _ ≤ |y| ^ 2 * r ^ 2 * |y| := by gcongr
    _ = |y| ^ 3 * r ^ 2 := by ring

/-- `(1 + |x|)³ ≥ 1 + |x|³`. -/
lemma one_add_abs_pow_three_ge (x : ℝ) : 1 + |x| ^ 3 ≤ (1 + |x|) ^ 3 := by
  have h : 0 ≤ |x| := abs_nonneg _
  nlinarith [sq_nonneg (|x|), mul_nonneg h h, mul_nonneg h (sq_nonneg |x|)]

/-- Pointwise: truncated second/third moment pieces sum to at most `|y|³ / r³`. -/
lemma trunc_moment_le_abs_cube_div {y r : ℝ} (hr : 0 < r) :
    (if r < |y| then y ^ 2 / r ^ 2 else 0) +
      (if |y| ≤ r then |y| ^ 3 / r ^ 3 else 0) ≤ |y| ^ 3 / r ^ 3 := by
  by_cases h : r < |y|
  · have hnot : ¬ |y| ≤ r := not_le.mpr h
    simp only [if_pos h, if_neg hnot, add_zero]
    exact sq_div_sq_le_abs_cube_div_cube hr h
  · have hle : |y| ≤ r := le_of_not_gt h
    simp only [if_neg h, if_pos hle, zero_add, le_refl]

/-- Denominator comparison for the third-moment corollary. -/
lemma div_one_add_abs_pow_three_le (x C β : ℝ) (hC : 0 ≤ C) (hβ : 0 ≤ β) :
    C * β / (1 + |x|) ^ 3 ≤ C * β / (1 + |x| ^ 3) := by
  have hden : 0 < 1 + |x| ^ 3 := by positivity
  have hle := one_add_abs_pow_three_ge x
  exact div_le_div_of_nonneg_left (mul_nonneg hC hβ) hden hle

/-- A coarse explicit conversion from the exponential decay in Chen--Shao (2005), Theorem 6.4,
to the cubic denominator of the public nonuniform Berry--Esseen theorem. -/
lemma exp_neg_half_le_div_one_add_cube {x : ℝ} (hx : 2 ≤ x) :
    Real.exp (-x / 2) ≤ 54 / (1 + x ^ 3) := by
  have hx0 : 0 < x := by linarith
  have hxhalf : 0 < x / 2 := by linarith
  have hseries := Real.pow_div_factorial_le_exp (x / 2) hxhalf.le 3
  norm_num [Nat.factorial] at hseries
  have hpoly : 0 < (x / 2) ^ 3 / 6 := by positivity
  have hinv : (Real.exp (x / 2))⁻¹ ≤ ((x / 2) ^ 3 / 6)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos _) hpoly).2 hseries
  have hfirst : Real.exp (-x / 2) ≤ 48 / x ^ 3 := by
    calc
      Real.exp (-x / 2) = (Real.exp (x / 2))⁻¹ := by
        rw [show -x / 2 = -(x / 2) by ring, Real.exp_neg]
      _ ≤ ((x / 2) ^ 3 / 6)⁻¹ := hinv
      _ = 48 / x ^ 3 := by field_simp [hx0.ne']; ring
  have hx0' : 0 ≤ x := hx0.le
  have hxSq : (4 : ℝ) ≤ x ^ 2 := by nlinarith
  have hxCube : (8 : ℝ) ≤ x ^ 3 := by
    calc
      (8 : ℝ) ≤ 4 * x := by linarith
      _ ≤ x ^ 2 * x := mul_le_mul_of_nonneg_right hxSq hx0'
      _ = x ^ 3 := by ring
  have hsecond : 48 / x ^ 3 ≤ 54 / (1 + x ^ 3) := by
    rw [div_le_div_iff₀ (by positivity : 0 < x ^ 3) (by positivity : 0 < 1 + x ^ 3)]
    nlinarith
  exact hfirst.trans hsecond

end ProbabilityTheory
