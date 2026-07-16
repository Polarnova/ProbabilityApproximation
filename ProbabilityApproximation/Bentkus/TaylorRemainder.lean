/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Taylor remainders with Lipschitz derivative

This module gives the first-order integral Taylor estimates used in Bentkus (2004),
equation (3.28).  A continuously differentiable scalar function whose Fréchet derivative is
`L`-Lipschitz has the sharp quadratic remainder `L / 2`.  The two-shift form keeps the derivative
at the unshifted base point and is arranged for moment cancellation.
-/

open Set MeasureTheory
open scoped NNReal

noncomputable section

namespace ProbabilityTheory

/-- First-order Taylor's theorem with the `L / 2` quadratic remainder for a scalar function with
globally Lipschitz Fréchet derivative. -/
lemma abs_firstOrderTaylorRemainder_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) {L : ℝ≥0}
    (hLip : LipschitzWith L (fderiv ℝ f)) (x h : E) :
    |f (x + h) - f x - (fderiv ℝ f x) h| ≤ (L : ℝ) / 2 * ‖h‖ ^ 2 := by
  have hformula :
      f (x + h) = f x + ∫ t in (0 : ℝ)..1, (fderiv ℝ f (x + t • h)) h := by
    simpa using
      (map_add_eq_sum_add_integral_iteratedFDeriv
        (n := 0) (f := f) (x := x) (y := h) (fun _ _ ↦ hf.contDiffAt))
  have hcont : Continuous (fun t : ℝ ↦ (fderiv ℝ f (x + t • h)) h) := by
    fun_prop
  have hremainder :
      f (x + h) - f x - (fderiv ℝ f x) h =
        ∫ t in (0 : ℝ)..1,
          ((fderiv ℝ f (x + t • h)) - fderiv ℝ f x) h := by
    rw [hformula]
    simp only [add_sub_cancel_left]
    have hconst : (fderiv ℝ f x) h =
        ∫ _t in (0 : ℝ)..1, (fderiv ℝ f x) h := by simp
    have hInt : IntervalIntegrable
        (fun t : ℝ ↦ (fderiv ℝ f (x + t • h)) h) volume 0 1 :=
      hcont.intervalIntegrable 0 1
    have hConst : IntervalIntegrable (fun _t : ℝ ↦ (fderiv ℝ f x) h) volume 0 1 :=
      intervalIntegrable_const
    rw [hconst]
    rw [← intervalIntegral.integral_sub hInt hConst]
    apply intervalIntegral.integral_congr
    intro t _
    simp
  rw [hremainder, ← Real.norm_eq_abs]
  calc
    ‖∫ t in (0 : ℝ)..1,
        ((fderiv ℝ f (x + t • h)) - fderiv ℝ f x) h‖ ≤
        ∫ t in (0 : ℝ)..1, (L : ℝ) * t * ‖h‖ ^ 2 := by
      apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      · filter_upwards with t
        intro ht
        calc
          ‖((fderiv ℝ f (x + t • h)) - fderiv ℝ f x) h‖ ≤
              ‖(fderiv ℝ f (x + t • h)) - fderiv ℝ f x‖ * ‖h‖ :=
            ContinuousLinearMap.le_opNorm _ _
          _ = dist (fderiv ℝ f (x + t • h)) (fderiv ℝ f x) * ‖h‖ := by
            rw [dist_eq_norm]
          _ ≤ ((L : ℝ) * dist (x + t • h) x) * ‖h‖ := by
            gcongr
            exact hLip.dist_le_mul (x + t • h) x
          _ = (L : ℝ) * t * ‖h‖ ^ 2 := by
            rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg ht.1.le]
            ring
      · exact (by fun_prop : Continuous (fun t : ℝ ↦ (L : ℝ) * t * ‖h‖ ^ 2)
          ).intervalIntegrable 0 1
    _ = (L : ℝ) / 2 * ‖h‖ ^ 2 := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
      have ht : (∫ t in (0 : ℝ)..1, t) = 1 / 2 := by
        rw [integral_id]
        norm_num
      rw [ht]
      ring

/-- Two-shift Taylor remainder with the derivative frozen at the original base point.  This is
the cancellation-friendly form of Bentkus's expansion (3.28). -/
lemma norm_twoShiftTaylorRemainder_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) {L : ℝ≥0}
    (hLip : LipschitzWith L (fderiv ℝ f)) (x v w : E) :
    ‖(f (x + v + w) - f (x + v)) - (fderiv ℝ f x) w‖ ≤
      (L : ℝ) * ‖w‖ * (‖v‖ + ‖w‖ / 2) := by
  have hrem :
      ‖f ((x + v) + w) - f (x + v) - (fderiv ℝ f (x + v)) w‖ ≤
        (L : ℝ) / 2 * ‖w‖ ^ 2 := by
    simpa only [Real.norm_eq_abs] using
      abs_firstOrderTaylorRemainder_le f hf hLip (x + v) w
  have hder :
      ‖((fderiv ℝ f (x + v)) - fderiv ℝ f x) w‖ ≤
        (L : ℝ) * ‖v‖ * ‖w‖ := by
    calc
      ‖((fderiv ℝ f (x + v)) - fderiv ℝ f x) w‖ ≤
          ‖fderiv ℝ f (x + v) - fderiv ℝ f x‖ * ‖w‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = dist (fderiv ℝ f (x + v)) (fderiv ℝ f x) * ‖w‖ := by
        rw [dist_eq_norm]
      _ ≤ ((L : ℝ) * dist (x + v) x) * ‖w‖ := by
        gcongr
        exact hLip.dist_le_mul (x + v) x
      _ = (L : ℝ) * ‖v‖ * ‖w‖ := by
        rw [dist_eq_norm, add_sub_cancel_left]
  have hsplit :
      (f (x + v + w) - f (x + v)) - (fderiv ℝ f x) w =
        (f ((x + v) + w) - f (x + v) - (fderiv ℝ f (x + v)) w) +
          ((fderiv ℝ f (x + v) - fderiv ℝ f x) w) := by
    simp only [sub_apply]
    ring
  rw [hsplit]
  calc
    ‖(f ((x + v) + w) - f (x + v) - (fderiv ℝ f (x + v)) w) +
        ((fderiv ℝ f (x + v) - fderiv ℝ f x) w)‖ ≤
        ‖f ((x + v) + w) - f (x + v) - (fderiv ℝ f (x + v)) w‖ +
          ‖((fderiv ℝ f (x + v) - fderiv ℝ f x) w)‖ := norm_add_le _ _
    _ ≤ (L : ℝ) / 2 * ‖w‖ ^ 2 + (L : ℝ) * ‖v‖ * ‖w‖ :=
      add_le_add hrem hder
    _ = (L : ℝ) * ‖w‖ * (‖v‖ + ‖w‖ / 2) := by ring

end ProbabilityTheory
