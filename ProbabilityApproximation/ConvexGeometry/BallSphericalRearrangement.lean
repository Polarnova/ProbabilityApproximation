/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.ConvexGeometry.BallSphereMoments
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The spherical rearrangement step in Ball's perimeter argument

This module formalizes the specialization `G(t) = t` of Lemma 3 in Keith Ball,
*The reverse isoperimetric problem for Gaussian measure*, Discrete & Computational Geometry
**10** (1993), 411--420, printed pp. 414--415.  This is exactly the form used in the proof of
Theorem 4: among two unit directions, the spherical average of an increasing function of the
first absolute coordinate times the second absolute coordinate is smallest when the directions
are orthogonal.

The proof averages a common plane rotation.  On each resulting circle, the claim is a
one-dimensional Chebyshev inequality for two antitone functions.  This avoids introducing a
spherical disintegration theorem that is not otherwise needed by the library.
-/

open Set Metric MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

/-- The paired absolute-cosine kernel produced by averaging a plane rotation and its reflection. -/
private def ballCircleKernel (α t : ℝ) : ℝ :=
  |Real.cos (t - α)| + |Real.cos (t + α)|

/-- The paired kernel relative to the orthogonal configuration. -/
private def ballCircleKernelDifference (α t : ℝ) : ℝ :=
  ballCircleKernel α t - 2 * Real.sin t

private lemma continuous_ballCircleKernel (α : ℝ) :
    Continuous (ballCircleKernel α) := by
  unfold ballCircleKernel
  fun_prop

private lemma continuous_ballCircleKernelDifference (α : ℝ) :
    Continuous (ballCircleKernelDifference α) := by
  unfold ballCircleKernelDifference
  exact (continuous_ballCircleKernel α).sub (continuous_const.mul Real.continuous_sin)

private lemma periodic_abs_cos :
    Function.Periodic (fun t : ℝ ↦ |Real.cos t|) Real.pi := by
  intro t
  change |Real.cos (t + Real.pi)| = |Real.cos t|
  rw [Real.cos_add_pi, abs_neg]

private lemma integral_abs_cos_full_period (s : ℝ) :
    (∫ t in s..s + Real.pi, |Real.cos t|) = 2 := by
  rw [periodic_abs_cos.intervalIntegral_add_eq s (-(Real.pi / 2))]
  have hpi : -(Real.pi / 2) + Real.pi = Real.pi / 2 := by ring
  rw [hpi]
  have hcos : (∫ t in (0 : ℝ)..Real.pi / 2, |Real.cos t|) = 1 := by
    calc
      (∫ t in (0 : ℝ)..Real.pi / 2, |Real.cos t|) =
          ∫ t in (0 : ℝ)..Real.pi / 2, Real.cos t := by
            apply intervalIntegral.integral_congr
            intro t ht
            have ht' : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
              simpa [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using ht
            dsimp only
            rw [abs_of_nonneg]
            exact Real.cos_nonneg_of_mem_Icc
              ⟨by linarith [ht'.1, Real.pi_pos], ht'.2⟩
      _ = 1 := by simp
  have hcont : Continuous fun t : ℝ ↦ |Real.cos t| := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hneg : (∫ t in -(Real.pi / 2)..(0 : ℝ), |Real.cos t|) = 1 := by
    calc
      (∫ t in -(Real.pi / 2)..(0 : ℝ), |Real.cos t|) =
          ∫ t in (0 : ℝ)..Real.pi / 2, |Real.cos (-t)| := by
            simpa using
              (intervalIntegral.integral_comp_neg
                (f := fun t : ℝ ↦ |Real.cos t|)
                (a := (0 : ℝ)) (b := Real.pi / 2)).symm
      _ = 1 := by simpa using hcos
  rw [hneg, hcos]
  norm_num

private lemma integral_ballCircleKernel (α : ℝ) :
    (∫ t in (0 : ℝ)..Real.pi / 2, ballCircleKernel α t) = 2 := by
  let g : ℝ → ℝ := fun t ↦ |Real.cos t|
  have hg : Continuous g := by
    dsimp only [g]
    fun_prop
  calc
    (∫ t in (0 : ℝ)..Real.pi / 2, ballCircleKernel α t) =
        (∫ t in (0 : ℝ)..Real.pi / 2, g (t - α)) +
          ∫ t in (0 : ℝ)..Real.pi / 2, g (t + α) := by
            unfold ballCircleKernel
            change (∫ t in (0 : ℝ)..Real.pi / 2, g (t - α) + g (t + α)) = _
            have hleft : IntervalIntegrable (fun t : ℝ ↦ g (t - α)) volume 0
                (Real.pi / 2) :=
              (hg.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
            have hright : IntervalIntegrable (fun t : ℝ ↦ g (t + α)) volume 0
                (Real.pi / 2) :=
              (hg.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
            rw [intervalIntegral.integral_add hleft hright]
    _ = (∫ t in -α..Real.pi / 2 - α, g t) +
          ∫ t in α..Real.pi / 2 + α, g t := by
            rw [intervalIntegral.integral_comp_sub_right,
              intervalIntegral.integral_comp_add_right]
            ring_nf
    _ = (∫ t in α - Real.pi / 2..α, g t) +
          ∫ t in α..Real.pi / 2 + α, g t := by
            congr 1
            calc
              (∫ t in -α..Real.pi / 2 - α, g t) =
                  ∫ t in α - Real.pi / 2..α, g (-t) := by
                    simpa only [neg_sub, neg_neg] using
                      (intervalIntegral.integral_comp_neg
                        (f := g) (a := α - Real.pi / 2) (b := α)).symm
              _ = ∫ t in α - Real.pi / 2..α, g t := by
                    apply intervalIntegral.integral_congr
                    intro t _ht
                    simp [g, Real.cos_neg]
    _ = ∫ t in α - Real.pi / 2..Real.pi / 2 + α, g t := by
          rw [intervalIntegral.integral_add_adjacent_intervals
            (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
    _ = 2 := by
          have hend :
              α - Real.pi / 2 + Real.pi = Real.pi / 2 + α := by ring
          rw [← hend]
          exact integral_abs_cos_full_period (α - Real.pi / 2)

private lemma integral_ballCircleKernelDifference (α : ℝ) :
    (∫ t in (0 : ℝ)..Real.pi / 2, ballCircleKernelDifference α t) = 0 := by
  unfold ballCircleKernelDifference
  have hkernel : IntervalIntegrable (ballCircleKernel α) volume 0 (Real.pi / 2) :=
    (continuous_ballCircleKernel α).intervalIntegrable _ _
  have hsin : IntervalIntegrable (fun t : ℝ ↦ 2 * Real.sin t) volume 0
      (Real.pi / 2) :=
    (continuous_const.mul Real.continuous_sin).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hkernel hsin]
  rw [integral_ballCircleKernel]
  simp

private lemma ballCircleKernelDifference_eq_left {α t : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2 - α)) :
    ballCircleKernelDifference α t =
      2 * Real.cos α * Real.cos t - 2 * Real.sin t := by
  have hsub : t - α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hα.1, hα.2, ht.1, ht.2, Real.pi_pos]
  have hadd : t + α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hα.1, hα.2, ht.1, ht.2, Real.pi_pos]
  unfold ballCircleKernelDifference ballCircleKernel
  rw [abs_of_nonneg (Real.cos_nonneg_of_mem_Icc hsub),
    abs_of_nonneg (Real.cos_nonneg_of_mem_Icc hadd),
    Real.cos_sub, Real.cos_add]
  ring

private lemma ballCircleKernelDifference_eq_right {α t : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (ht : t ∈ Set.Icc (Real.pi / 2 - α) (Real.pi / 2)) :
    ballCircleKernelDifference α t =
      2 * (Real.sin α - 1) * Real.sin t := by
  have hsub : t - α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hα.1, hα.2, ht.1, ht.2, Real.pi_pos]
  have haddLower : Real.pi / 2 ≤ t + α := by linarith [ht.1]
  have haddUpper : t + α ≤ Real.pi + Real.pi / 2 := by
    linarith [hα.2, ht.2, Real.pi_pos]
  unfold ballCircleKernelDifference ballCircleKernel
  rw [abs_of_nonneg (Real.cos_nonneg_of_mem_Icc hsub),
    abs_of_nonpos (Real.cos_nonpos_of_pi_div_two_le_of_le haddLower haddUpper),
    Real.cos_sub, Real.cos_add]
  ring

private lemma antitoneOn_ballCircleKernelDifference {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    AntitoneOn (ballCircleKernelDifference α)
      (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
  let a : ℝ := Real.pi / 2 - α
  have ha : a ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    dsimp only [a]
    constructor <;> linarith [hα.1, hα.2]
  have haLeft : a ∈ Set.Icc (0 : ℝ) a := ⟨ha.1, le_rfl⟩
  have haRight : a ∈ Set.Icc a (Real.pi / 2) := ⟨le_rfl, ha.2⟩
  have hcosα : 0 ≤ Real.cos α :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩
  have hsinα : Real.sin α ≤ 1 := Real.sin_le_one α
  have hleft : AntitoneOn (ballCircleKernelDifference α) (Set.Icc (0 : ℝ) a) := by
    intro x hx y hy hxy
    have hcos : Real.cos y ≤ Real.cos x :=
      Real.cos_le_cos_of_nonneg_of_le_pi hx.1
        (hy.2.trans (ha.2.trans (by linarith [Real.pi_pos]))) hxy
    have hsin : Real.sin x ≤ Real.sin y :=
      Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [hx.1, Real.pi_pos]) (hy.2.trans ha.2) hxy
    rw [ballCircleKernelDifference_eq_left hα hx,
      ballCircleKernelDifference_eq_left hα hy]
    have hmul := mul_le_mul_of_nonneg_left hcos hcosα
    linarith
  have hright : AntitoneOn (ballCircleKernelDifference α)
      (Set.Icc a (Real.pi / 2)) := by
    intro x hx y hy hxy
    have hsin : Real.sin x ≤ Real.sin y :=
      Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [ha.1, hx.1, Real.pi_pos]) hy.2 hxy
    rw [ballCircleKernelDifference_eq_right hα hx,
      ballCircleKernelDifference_eq_right hα hy]
    have hmul := mul_le_mul_of_nonpos_left hsin (sub_nonpos.mpr hsinα)
    linarith
  intro x hx y hy hxy
  by_cases hyLeft : y ≤ a
  · exact hleft ⟨hx.1, hxy.trans hyLeft⟩ ⟨hy.1, hyLeft⟩ hxy
  have hay : a ≤ y := (lt_of_not_ge hyLeft).le
  by_cases hxLeft : x ≤ a
  · exact (hright haRight ⟨hay, hy.2⟩ hay).trans
      (hleft ⟨hx.1, hxLeft⟩ haLeft hxLeft)
  · have hax : a ≤ x := (lt_of_not_ge hxLeft).le
    exact hright ⟨hax, hx.2⟩ ⟨hay, hy.2⟩ hxy

private lemma intervalIntegral_mul_nonneg_of_antitoneOn_of_integral_eq_zero
    {H D : ℝ → ℝ} (hH : Continuous H) (hD : Continuous D)
    (hHanti : AntitoneOn H (Set.Icc (0 : ℝ) (Real.pi / 2)))
    (hDanti : AntitoneOn D (Set.Icc (0 : ℝ) (Real.pi / 2)))
    (hDzero : (∫ t in (0 : ℝ)..Real.pi / 2, D t) = 0) :
    0 ≤ ∫ t in (0 : ℝ)..Real.pi / 2, H t * D t := by
  let L : ℝ := Real.pi / 2
  let IH : ℝ := ∫ t in (0 : ℝ)..L, H t
  let ID : ℝ := ∫ t in (0 : ℝ)..L, D t
  let IHD : ℝ := ∫ t in (0 : ℝ)..L, H t * D t
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  have hHint : IntervalIntegrable H volume 0 L := hH.intervalIntegrable _ _
  have hDint : IntervalIntegrable D volume 0 L := hD.intervalIntegrable _ _
  have hHDint : IntervalIntegrable (fun t ↦ H t * D t) volume 0 L :=
    (hH.mul hD).intervalIntegrable _ _
  have hinner (x : ℝ) :
      (∫ y in (0 : ℝ)..L, (H x - H y) * (D x - D y)) =
        L * (H x * D x) - H x * ID - D x * IH + IHD := by
    have hfirst : IntervalIntegrable
        (fun y : ℝ ↦ H x * D x - H x * D y) volume 0 L :=
      (continuous_const.sub (continuous_const.mul hD)).intervalIntegrable _ _
    have hsecond : IntervalIntegrable
        (fun y : ℝ ↦ H y * D x - H y * D y) volume 0 L :=
      ((hH.mul continuous_const).sub (hH.mul hD)).intervalIntegrable _ _
    have hconst : IntervalIntegrable (fun _y : ℝ ↦ H x * D x) volume 0 L :=
      continuous_const.intervalIntegrable _ _
    have hxD : IntervalIntegrable (fun y : ℝ ↦ H x * D y) volume 0 L :=
      (continuous_const.mul hD).intervalIntegrable _ _
    have hHDx : IntervalIntegrable (fun y : ℝ ↦ H y * D x) volume 0 L :=
      (hH.mul continuous_const).intervalIntegrable _ _
    calc
      (∫ y in (0 : ℝ)..L, (H x - H y) * (D x - D y)) =
          ∫ y in (0 : ℝ)..L,
            (H x * D x - H x * D y) - (H y * D x - H y * D y) := by
              apply intervalIntegral.integral_congr
              intro y _hy
              ring
      _ = (∫ y in (0 : ℝ)..L, H x * D x - H x * D y) -
          ∫ y in (0 : ℝ)..L, H y * D x - H y * D y := by
            rw [intervalIntegral.integral_sub hfirst hsecond]
      _ = ((∫ _y in (0 : ℝ)..L, H x * D x) -
            ∫ y in (0 : ℝ)..L, H x * D y) -
          ((∫ y in (0 : ℝ)..L, H y * D x) -
            ∫ y in (0 : ℝ)..L, H y * D y) := by
              rw [intervalIntegral.integral_sub hconst hxD,
                intervalIntegral.integral_sub hHDx hHDint]
      _ = L * (H x * D x) - H x * ID - D x * IH + IHD := by
            simp only [intervalIntegral.integral_const,
              intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
              sub_zero, smul_eq_mul]
            dsimp only [IH, ID, IHD]
            ring
  have hdouble_nonneg :
      0 ≤ ∫ x in (0 : ℝ)..L,
        ∫ y in (0 : ℝ)..L, (H x - H y) * (D x - D y) := by
    apply intervalIntegral.integral_nonneg hL
    intro x hx
    apply intervalIntegral.integral_nonneg hL
    intro y hy
    rcases le_total x y with hxy | hyx
    · exact mul_nonneg
        (sub_nonneg.mpr (hHanti (by simpa [L] using hx) (by simpa [L] using hy) hxy))
        (sub_nonneg.mpr (hDanti (by simpa [L] using hx) (by simpa [L] using hy) hxy))
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (hHanti (by simpa [L] using hy) (by simpa [L] using hx) hyx))
        (sub_nonpos.mpr (hDanti (by simpa [L] using hy) (by simpa [L] using hx) hyx))
  have hDzero' : ID = 0 := by
    dsimp only [ID, L]
    exact hDzero
  have houterIdentity :
      (∫ x in (0 : ℝ)..L,
        ∫ y in (0 : ℝ)..L, (H x - H y) * (D x - D y)) =
        2 * L * IHD := by
    calc
      (∫ x in (0 : ℝ)..L,
          ∫ y in (0 : ℝ)..L, (H x - H y) * (D x - D y)) =
          ∫ x in (0 : ℝ)..L,
            (L * (H x * D x) - H x * ID - D x * IH + IHD) := by
              apply intervalIntegral.integral_congr
              intro x _hx
              exact hinner x
      _ = ∫ x in (0 : ℝ)..L, L * (H x * D x) - D x * IH + IHD := by
            simp only [hDzero', mul_zero, sub_zero]
      _ = ((∫ x in (0 : ℝ)..L, L * (H x * D x)) -
            ∫ x in (0 : ℝ)..L, D x * IH) +
          ∫ _x in (0 : ℝ)..L, IHD := by
            have hfirst : IntervalIntegrable (fun x : ℝ ↦ L * (H x * D x)) volume 0 L :=
              (continuous_const.mul (hH.mul hD)).intervalIntegrable _ _
            have hsecond : IntervalIntegrable (fun x : ℝ ↦ D x * IH) volume 0 L :=
              (hD.mul continuous_const).intervalIntegrable _ _
            rw [intervalIntegral.integral_add (hfirst.sub hsecond)
              (continuous_const.intervalIntegrable _ _),
              intervalIntegral.integral_sub hfirst hsecond]
      _ = 2 * L * IHD := by
            simp only [intervalIntegral.integral_const_mul,
              intervalIntegral.integral_mul_const, intervalIntegral.integral_const,
              smul_eq_mul]
            rw [show (∫ x in (0 : ℝ)..L, D x) = 0 by
              simpa [L] using hDzero]
            dsimp only [IHD]
            ring
  rw [houterIdentity] at hdouble_nonneg
  have hcoef : 0 < 2 * L := by
    dsimp only [L]
    positivity
  have hIHD : 0 ≤ IHD := by nlinarith
  simpa [IHD, L] using hIHD

private theorem ball_circle_rearrangement {H : ℝ → ℝ}
    (hH : Continuous H)
    (hHanti : AntitoneOn H (Set.Icc (0 : ℝ) (Real.pi / 2)))
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    (∫ t in (0 : ℝ)..Real.pi / 2, H t * (2 * Real.sin t)) ≤
      ∫ t in (0 : ℝ)..Real.pi / 2, H t * ballCircleKernel α t := by
  have hnonneg := intervalIntegral_mul_nonneg_of_antitoneOn_of_integral_eq_zero
    hH (continuous_ballCircleKernelDifference α)
    hHanti (antitoneOn_ballCircleKernelDifference hα)
    (integral_ballCircleKernelDifference α)
  have hleft : IntervalIntegrable
      (fun t : ℝ ↦ H t * ballCircleKernel α t) volume 0 (Real.pi / 2) :=
    (hH.mul (continuous_ballCircleKernel α)).intervalIntegrable _ _
  have hright : IntervalIntegrable
      (fun t : ℝ ↦ H t * (2 * Real.sin t)) volume 0 (Real.pi / 2) :=
    (hH.mul (continuous_const.mul Real.continuous_sin)).intervalIntegrable _ _
  have hrearrange :
      (∫ t in (0 : ℝ)..Real.pi / 2,
        H t * ballCircleKernelDifference α t) =
        (∫ t in (0 : ℝ)..Real.pi / 2, H t * ballCircleKernel α t) -
          ∫ t in (0 : ℝ)..Real.pi / 2, H t * (2 * Real.sin t) := by
    calc
      (∫ t in (0 : ℝ)..Real.pi / 2,
          H t * ballCircleKernelDifference α t) =
          ∫ t in (0 : ℝ)..Real.pi / 2,
            H t * ballCircleKernel α t - H t * (2 * Real.sin t) := by
              apply intervalIntegral.integral_congr
              intro t _ht
              unfold ballCircleKernelDifference
              ring
      _ = _ := intervalIntegral.integral_sub hleft hright
  rw [hrearrange] at hnonneg
  linarith

/-- Rotation through angle `t` in the oriented plane generated by an orthonormal pair, acting as
the identity on its orthogonal complement. -/
private def ballPlaneRotationLinear {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (t : ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E +
    (Real.cos t - 1) • InnerProductSpace.rankOne ℝ u u +
    (-Real.sin t) • InnerProductSpace.rankOne ℝ u v +
    Real.sin t • InnerProductSpace.rankOne ℝ v u +
    (Real.cos t - 1) • InnerProductSpace.rankOne ℝ v v

private lemma ballPlaneRotationLinear_apply {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v x : E) (t : ℝ) :
    ballPlaneRotationLinear u v t x =
      x + ((Real.cos t - 1) * inner ℝ u x - Real.sin t * inner ℝ v x) • u +
        (Real.sin t * inner ℝ u x + (Real.cos t - 1) * inner ℝ v x) • v := by
  simp [ballPlaneRotationLinear, InnerProductSpace.rankOne_apply]
  module

private lemma inner_ballPlaneRotationLinear_map_map {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) (t : ℝ) (x y : E) :
    inner ℝ (ballPlaneRotationLinear u v t x)
      (ballPlaneRotationLinear u v t y) = inner ℝ x y := by
  have huu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, hu]
    norm_num
  have hvv : inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
  have hvu : inner ℝ v u = 0 := by
    rw [real_inner_comm, huv]
  rw [ballPlaneRotationLinear_apply, ballPlaneRotationLinear_apply]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [huu, hvv, huv, hvu]
  simp only [mul_zero, mul_one, add_zero]
  rw [real_inner_comm x u, real_inner_comm x v,
    real_inner_comm y u, real_inner_comm y v]
  ring_nf
  rw [show Real.cos t ^ 2 = 1 - Real.sin t ^ 2 by
    nlinarith [Real.sin_sq_add_cos_sq t]]
  ring

/-- The bundled Euclidean isometry implementing `ballPlaneRotationLinear`. -/
private noncomputable def ballPlaneRotation {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) (t : ℝ) : E ≃ₗᵢ[ℝ] E := by
  let f : E →ₗᵢ[ℝ] E :=
    (ballPlaneRotationLinear u v t).toLinearMap.isometryOfInner
      (inner_ballPlaneRotationLinear_map_map hu hv huv t)
  exact LinearIsometryEquiv.ofSurjective f
    (LinearMap.injective_iff_surjective.mp f.injective)

@[simp]
private lemma ballPlaneRotation_apply {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) (t : ℝ) (x : E) :
    ballPlaneRotation u v hu hv huv t x = ballPlaneRotationLinear u v t x := rfl

/-- The first coordinate of a vector after an ordinary planar rotation. -/
private def ballRotatingCoordinate (A B t : ℝ) : ℝ :=
  A * Real.cos t - B * Real.sin t

private lemma inner_ballPlaneRotation_right_first {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) (t : ℝ) (x : E) :
    inner ℝ (ballPlaneRotation u v hu hv huv t x) u =
      ballRotatingCoordinate (inner ℝ x u) (inner ℝ x v) t := by
  have huu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, hu]
    norm_num
  have hvu : inner ℝ v u = 0 := by rw [real_inner_comm, huv]
  rw [ballPlaneRotation_apply, ballPlaneRotationLinear_apply]
  simp only [inner_add_left, real_inner_smul_left, huu, hvu, mul_one, mul_zero, add_zero]
  unfold ballRotatingCoordinate
  rw [real_inner_comm x u, real_inner_comm x v]
  ring

private lemma inner_ballPlaneRotation_right_second {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) (t : ℝ) (x : E) :
    inner ℝ (ballPlaneRotation u v hu hv huv t x) v =
      Real.sin t * inner ℝ x u + Real.cos t * inner ℝ x v := by
  have hvv : inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
  rw [ballPlaneRotation_apply, ballPlaneRotationLinear_apply]
  simp only [inner_add_left, real_inner_smul_left, huv, hvv, mul_zero, mul_one,
    add_zero]
  rw [real_inner_comm x u, real_inner_comm x v]
  ring

private lemma inner_ballPlaneRotation_right_angle {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) (t α : ℝ) (x : E) :
    inner ℝ (ballPlaneRotation u v hu hv huv t x)
        (Real.cos α • u + Real.sin α • v) =
      ballRotatingCoordinate (inner ℝ x u) (inner ℝ x v) (t - α) := by
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    inner_ballPlaneRotation_right_first hu hv huv,
    inner_ballPlaneRotation_right_second hu hv huv]
  unfold ballRotatingCoordinate
  rw [Real.cos_sub, Real.sin_sub]
  ring

private lemma ballRotatingCoordinate_eq_norm_mul_cos_add_arg (A B t : ℝ) :
    ballRotatingCoordinate A B t =
      ‖(⟨A, B⟩ : ℂ)‖ * Real.cos (t + Complex.arg (⟨A, B⟩ : ℂ)) := by
  let z : ℂ := ⟨A, B⟩
  calc
    ballRotatingCoordinate A B t =
        (‖z‖ * Real.cos (Complex.arg z)) * Real.cos t -
          (‖z‖ * Real.sin (Complex.arg z)) * Real.sin t := by
            simp [ballRotatingCoordinate, z]
    _ = ‖z‖ * Real.cos (t + Complex.arg z) := by
          rw [Real.cos_add]
          ring

/-- The full half-turn correlation of two planar coordinates separated by angle `α`. -/
private def ballCircleCorrelation (F : ℝ → ℝ) (A B α : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..Real.pi,
    F |ballRotatingCoordinate A B t| *
      |ballRotatingCoordinate A B (t - α)|

private lemma ballCircleCorrelation_eq_kernel {F : ℝ → ℝ} (hF : Continuous F)
    (A B α : ℝ) :
    ballCircleCorrelation F A B α =
      ‖(⟨A, B⟩ : ℂ)‖ *
        ∫ t in (0 : ℝ)..Real.pi / 2,
          F (‖(⟨A, B⟩ : ℂ)‖ * Real.cos t) * ballCircleKernel α t := by
  let z : ℂ := ⟨A, B⟩
  let ρ : ℝ := ‖z‖
  let δ : ℝ := Complex.arg z
  let p : ℝ → ℝ := fun t ↦
    F (ρ * |Real.cos t|) * (ρ * |Real.cos (t - α)|)
  have hρ : 0 ≤ ρ := norm_nonneg z
  have hp : Continuous p := by
    dsimp only [p]
    fun_prop
  have hpperiod : Function.Periodic p Real.pi := by
    intro t
    dsimp only [p]
    rw [show t + Real.pi - α = (t - α) + Real.pi by ring,
      Real.cos_add_pi, Real.cos_add_pi, abs_neg, abs_neg]
  have hcoord (t : ℝ) :
      ballRotatingCoordinate A B t = ρ * Real.cos (t + δ) := by
    simpa [ρ, δ, z] using ballRotatingCoordinate_eq_norm_mul_cos_add_arg A B t
  have hshift : ballCircleCorrelation F A B α =
      ∫ t in (0 : ℝ)..Real.pi, p t := by
    calc
      ballCircleCorrelation F A B α =
          ∫ t in (0 : ℝ)..Real.pi, p (t + δ) := by
            unfold ballCircleCorrelation
            apply intervalIntegral.integral_congr
            intro t _ht
            dsimp only
            rw [hcoord t, hcoord (t - α)]
            dsimp only [p]
            rw [show t - α + δ = t + δ - α by ring]
            simp only [abs_mul, abs_of_nonneg hρ]
      _ = ∫ t in δ..Real.pi + δ, p t := by
            rw [intervalIntegral.integral_comp_add_right]
            ring_nf
      _ = ∫ t in (0 : ℝ)..Real.pi, p t := by
            convert hpperiod.intervalIntegral_add_eq δ 0 using 1 <;> ring
  rw [hshift]
  have hhalf : Real.pi - Real.pi / 2 = Real.pi / 2 := by ring
  calc
    (∫ t in (0 : ℝ)..Real.pi, p t) =
        (∫ t in (0 : ℝ)..Real.pi / 2, p t) +
          ∫ t in Real.pi / 2..Real.pi, p t :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hp.intervalIntegrable _ _) (hp.intervalIntegrable _ _)).symm
    _ = (∫ t in (0 : ℝ)..Real.pi / 2, p t) +
          ∫ t in (0 : ℝ)..Real.pi / 2, p (Real.pi - t) := by
            congr 1
            simpa [hhalf] using
              (intervalIntegral.integral_comp_sub_left
                (f := p) (a := (0 : ℝ)) (b := Real.pi / 2) Real.pi).symm
    _ = ∫ t in (0 : ℝ)..Real.pi / 2, p t + p (Real.pi - t) := by
          exact (intervalIntegral.integral_add
            (hp.intervalIntegrable _ _)
            ((hp.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _)).symm
    _ = ∫ t in (0 : ℝ)..Real.pi / 2,
          ρ * (F (ρ * Real.cos t) * ballCircleKernel α t) := by
            apply intervalIntegral.integral_congr
            intro t ht
            have ht' : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
              simpa [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using ht
            have hcost : 0 ≤ Real.cos t :=
              Real.cos_nonneg_of_mem_Icc
                ⟨by linarith [ht'.1, Real.pi_pos], ht'.2⟩
            dsimp only [p]
            rw [abs_of_nonneg hcost, Real.cos_pi_sub, abs_neg,
              show Real.pi - t - α = Real.pi - (t + α) by ring,
              Real.cos_pi_sub, abs_neg, abs_of_nonneg hcost]
            unfold ballCircleKernel
            ring
    _ = ρ * ∫ t in (0 : ℝ)..Real.pi / 2,
          F (ρ * Real.cos t) * ballCircleKernel α t := by
            rw [intervalIntegral.integral_const_mul]

private lemma ballCircleKernel_pi_div_two {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    ballCircleKernel (Real.pi / 2) t = 2 * Real.sin t := by
  have hsint : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht.1
      (ht.2.trans (by linarith [Real.pi_pos]))
  unfold ballCircleKernel
  rw [Real.cos_sub_pi_div_two, Real.cos_add_pi_div_two,
    abs_of_nonneg hsint, abs_neg, abs_of_nonneg hsint]
  ring

private theorem ballCircleCorrelation_orthogonal_le {F : ℝ → ℝ}
    (hF : Continuous F) (hFmono : MonotoneOn F (Set.Ici 0))
    (A B : ℝ) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    ballCircleCorrelation F A B (Real.pi / 2) ≤
      ballCircleCorrelation F A B α := by
  let ρ : ℝ := ‖(⟨A, B⟩ : ℂ)‖
  let H : ℝ → ℝ := fun t ↦ F (ρ * Real.cos t)
  have hρ : 0 ≤ ρ := norm_nonneg _
  have hH : Continuous H := by
    dsimp only [H]
    fun_prop
  have hHanti : AntitoneOn H (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    intro x hx y hy hxy
    have hcos : Real.cos y ≤ Real.cos x :=
      Real.cos_le_cos_of_nonneg_of_le_pi hx.1
        (hy.2.trans (by linarith [Real.pi_pos])) hxy
    have hcosx : 0 ≤ Real.cos x :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
    have hcosy : 0 ≤ Real.cos y :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hy.1, Real.pi_pos], hy.2⟩
    exact hFmono (mul_nonneg hρ hcosy) (mul_nonneg hρ hcosx)
      (mul_le_mul_of_nonneg_left hcos hρ)
  have hcircle := ball_circle_rearrangement hH hHanti hα
  have horth :
      (∫ t in (0 : ℝ)..Real.pi / 2, H t * (2 * Real.sin t)) =
        ∫ t in (0 : ℝ)..Real.pi / 2,
          H t * ballCircleKernel (Real.pi / 2) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
      simpa [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using ht
    dsimp only
    rw [ballCircleKernel_pi_div_two ht']
  rw [horth] at hcircle
  have hmul := mul_le_mul_of_nonneg_left hcircle hρ
  rw [← ballCircleCorrelation_eq_kernel hF A B (Real.pi / 2),
    ← ballCircleCorrelation_eq_kernel hF A B α] at hmul
  exact hmul

private lemma integrable_interval_prod_finiteSphereMeasure
    {d : ℕ} (μ : Measure (sphere (0 : EuclideanSpace ℝ (Fin d)) 1))
    [IsFiniteMeasure μ]
    {g : ℝ × sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ}
    (hg : Continuous g) :
    Integrable g
      ((volume.restrict (Set.uIoc (0 : ℝ) Real.pi)).prod
        μ) := by
  have hcompact : IsCompact
      (Set.Icc (0 : ℝ) Real.pi ×ˢ
        (Set.univ : Set (sphere (0 : EuclideanSpace ℝ (Fin d)) 1))) :=
    isCompact_Icc.prod isCompact_univ
  have hbig : IntegrableOn g
      (Set.Icc (0 : ℝ) Real.pi ×ˢ
        (Set.univ : Set (sphere (0 : EuclideanSpace ℝ (Fin d)) 1)))
      (volume.prod μ) :=
    hg.continuousOn.integrableOn_compact hcompact
  have hsmall : IntegrableOn g
      (Set.Ioc (0 : ℝ) Real.pi ×ˢ
        (Set.univ : Set (sphere (0 : EuclideanSpace ℝ (Fin d)) 1)))
      (volume.prod μ) :=
    hbig.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Set.Subset.rfl)
  change Integrable g
    ((volume.prod μ).restrict
      (Set.Ioc (0 : ℝ) Real.pi ×ˢ
        (Set.univ : Set (sphere (0 : EuclideanSpace ℝ (Fin d)) 1)))) at hsmall
  simpa [Set.uIoc_of_le Real.pi_pos.le,
    Measure.restrict_prod_eq_prod_univ] using hsmall

private lemma continuous_ballPlaneRotatedSphereIntegrand
    {d : ℕ} {u v w : EuclideanSpace ℝ (Fin d)}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    {F : ℝ → ℝ} (hF : Continuous F) :
    Continuous fun p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ↦
      F |inner ℝ (ballPlaneRotation u v hu hv huv p.1 (p.2 :
          EuclideanSpace ℝ (Fin d))) u| *
        |inner ℝ (ballPlaneRotation u v hu hv huv p.1 (p.2 :
          EuclideanSpace ℝ (Fin d))) w| := by
  simp_rw [ballPlaneRotation_apply, ballPlaneRotationLinear_apply]
  fun_prop

/-- **Ball's spherical rearrangement inequality for a finite rotation-invariant measure,
applied form (`G(t) = t`).**

Let `u,v` be orthogonal unit directions.  For every continuous function `F` that is
nondecreasing on the nonnegative real axis, the spherical correlation with the second direction
is smallest at the orthogonal angle.  This is the exact specialization of Ball (1993), Lemma 3,
used in the proof of his Gaussian perimeter theorem. -/
theorem ballSphericalRearrangement_absInner_of_measure
    {d : ℕ} (μ : Measure (sphere (0 : EuclideanSpace ℝ (Fin d)) 1))
    [IsFiniteMeasure μ]
    (hμ : ∀ e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      MeasurePreserving (linearIsometryEquivUnitSphere e) μ μ)
    {F : ℝ → ℝ}
    (hF : Continuous F) (hFmono : MonotoneOn F (Set.Ici 0))
    {u v : EuclideanSpace ℝ (Fin d)}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    (∫ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        F |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u| *
          |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v|
        ∂μ) ≤
      ∫ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        F |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u| *
          |inner ℝ (θ : EuclideanSpace ℝ (Fin d))
            (Real.cos α • u + Real.sin α • v)|
        ∂μ := by
  let w : EuclideanSpace ℝ (Fin d) := Real.cos α • u + Real.sin α • v
  let Iorth : ℝ :=
    ∫ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      F |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u| *
        |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v| ∂μ
  let Iangle : ℝ :=
    ∫ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      F |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u| *
        |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) w| ∂μ
  let gorth : ℝ × sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ := fun p ↦
    F |inner ℝ (ballPlaneRotation u v hu hv huv p.1
      (p.2 : EuclideanSpace ℝ (Fin d))) u| *
      |inner ℝ (ballPlaneRotation u v hu hv huv p.1
        (p.2 : EuclideanSpace ℝ (Fin d))) v|
  let gangle : ℝ × sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ := fun p ↦
    F |inner ℝ (ballPlaneRotation u v hu hv huv p.1
      (p.2 : EuclideanSpace ℝ (Fin d))) u| *
      |inner ℝ (ballPlaneRotation u v hu hv huv p.1
        (p.2 : EuclideanSpace ℝ (Fin d))) w|
  have hgorth : Continuous gorth := by
    dsimp only [gorth]
    exact continuous_ballPlaneRotatedSphereIntegrand hu hv huv hF
  have hgangle : Continuous gangle := by
    dsimp only [gangle]
    exact continuous_ballPlaneRotatedSphereIntegrand hu hv huv hF
  have hgorthProd : Integrable gorth
      ((volume.restrict (Set.uIoc (0 : ℝ) Real.pi)).prod μ) := by
    exact integrable_interval_prod_finiteSphereMeasure μ hgorth
  have hgangleProd : Integrable gangle
      ((volume.restrict (Set.uIoc (0 : ℝ) Real.pi)).prod μ) := by
    exact integrable_interval_prod_finiteSphereMeasure μ hgangle
  have hswapOrth :
      (∫ t in (0 : ℝ)..Real.pi, ∫ θ, gorth (t, θ) ∂μ) =
        ∫ θ, (∫ t in (0 : ℝ)..Real.pi, gorth (t, θ)) ∂μ :=
    intervalIntegral_integral_swap hgorthProd
  have hswapAngle :
      (∫ t in (0 : ℝ)..Real.pi, ∫ θ, gangle (t, θ) ∂μ) =
        ∫ θ, (∫ t in (0 : ℝ)..Real.pi, gangle (t, θ)) ∂μ :=
    intervalIntegral_integral_swap hgangleProd
  have hrotateOrth (t : ℝ) : (∫ θ, gorth (t, θ) ∂μ) = Iorth := by
    let e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
      ballPlaneRotation u v hu hv huv t
    have h :=
      (hμ e).integral_comp
        (linearIsometryEquivUnitSphere e).measurableEmbedding
        (fun θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ↦
          F |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u| *
            |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v|)
    simpa [gorth, Iorth, e] using h
  have hrotateAngle (t : ℝ) : (∫ θ, gangle (t, θ) ∂μ) = Iangle := by
    let e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
      ballPlaneRotation u v hu hv huv t
    have h :=
      (hμ e).integral_comp
        (linearIsometryEquivUnitSphere e).measurableEmbedding
        (fun θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ↦
          F |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u| *
            |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) w|)
    simpa [gangle, Iangle, e] using h
  have htime (θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
      (∫ t in (0 : ℝ)..Real.pi, gorth (t, θ)) ≤
        ∫ t in (0 : ℝ)..Real.pi, gangle (t, θ) := by
    let A : ℝ := inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u
    let B : ℝ := inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v
    have hcorr := ballCircleCorrelation_orthogonal_le hF hFmono A B hα
    have horthEq :
        (∫ t in (0 : ℝ)..Real.pi, gorth (t, θ)) =
          ballCircleCorrelation F A B (Real.pi / 2) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp only [gorth]
      rw [inner_ballPlaneRotation_right_first hu hv huv,
        inner_ballPlaneRotation_right_second hu hv huv]
      dsimp only [A, B]
      congr 2
      unfold ballRotatingCoordinate
      rw [Real.cos_sub, Real.sin_sub]
      simp
      ring
    have hangleEq :
        (∫ t in (0 : ℝ)..Real.pi, gangle (t, θ)) =
          ballCircleCorrelation F A B α := by
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp only [gangle, w]
      rw [inner_ballPlaneRotation_right_first hu hv huv,
        inner_ballPlaneRotation_right_angle hu hv huv]
    rw [horthEq, hangleEq]
    exact hcorr
  have htimeOrthContinuous : Continuous fun θ :
      sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ↦
        ∫ t in (0 : ℝ)..Real.pi, gorth (t, θ) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun θ t ↦ gorth (t, θ))
      (hgorth.comp (continuous_snd.prodMk continuous_fst)) 0 Real.pi
  have htimeAngleContinuous : Continuous fun θ :
      sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ↦
        ∫ t in (0 : ℝ)..Real.pi, gangle (t, θ) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun θ t ↦ gangle (t, θ))
      (hgangle.comp (continuous_snd.prodMk continuous_fst)) 0 Real.pi
  have htimeOrthIntegrable : Integrable
      (fun θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ↦
        ∫ t in (0 : ℝ)..Real.pi, gorth (t, θ)) μ := by
    simpa using htimeOrthContinuous.continuousOn.integrableOn_compact
      (μ := μ) isCompact_univ
  have htimeAngleIntegrable : Integrable
      (fun θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ↦
        ∫ t in (0 : ℝ)..Real.pi, gangle (t, θ)) μ := by
    simpa using htimeAngleContinuous.continuousOn.integrableOn_compact
      (μ := μ) isCompact_univ
  have htimeIntegral :
      (∫ θ, (∫ t in (0 : ℝ)..Real.pi, gorth (t, θ)) ∂μ) ≤
        ∫ θ, (∫ t in (0 : ℝ)..Real.pi, gangle (t, θ)) ∂μ :=
    integral_mono htimeOrthIntegrable htimeAngleIntegrable htime
  have hscaled : Real.pi * Iorth ≤ Real.pi * Iangle := by
    calc
      Real.pi * Iorth =
          ∫ t in (0 : ℝ)..Real.pi, ∫ θ, gorth (t, θ) ∂μ := by
            calc
              Real.pi * Iorth = ∫ _t in (0 : ℝ)..Real.pi, Iorth := by simp
              _ = _ := by
                apply intervalIntegral.integral_congr
                intro t _ht
                exact (hrotateOrth t).symm
      _ = ∫ θ, (∫ t in (0 : ℝ)..Real.pi, gorth (t, θ)) ∂μ := hswapOrth
      _ ≤ ∫ θ, (∫ t in (0 : ℝ)..Real.pi, gangle (t, θ)) ∂μ := htimeIntegral
      _ = ∫ t in (0 : ℝ)..Real.pi, ∫ θ, gangle (t, θ) ∂μ := hswapAngle.symm
      _ = Real.pi * Iangle := by
            calc
              (∫ t in (0 : ℝ)..Real.pi, ∫ θ, gangle (t, θ) ∂μ) =
                  ∫ _t in (0 : ℝ)..Real.pi, Iangle := by
                    apply intervalIntegral.integral_congr
                    intro t _ht
                    exact hrotateAngle t
              _ = Real.pi * Iangle := by simp
  have hresult : Iorth ≤ Iangle := by
    nlinarith [Real.pi_pos]
  simpa [Iorth, Iangle, w] using hresult

/-- **Ball's spherical rearrangement inequality, applied form (`G(t) = t`).**

This is the rotation-invariant probability specialization of
`ballSphericalRearrangement_absInner_of_measure`. -/
theorem ballSphericalRearrangement_absInner
    {d : ℕ} (hd : d ≠ 0) {F : ℝ → ℝ}
    (hF : Continuous F) (hFmono : MonotoneOn F (Set.Ici 0))
    {u v : EuclideanSpace ℝ (Fin d)}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    (∫ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        F |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u| *
          |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v|
        ∂(standardSphereProbability d hd).toMeasure) ≤
      ∫ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        F |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u| *
          |inner ℝ (θ : EuclideanSpace ℝ (Fin d))
            (Real.cos α • u + Real.sin α • v)|
        ∂(standardSphereProbability d hd).toMeasure := by
  apply ballSphericalRearrangement_absInner_of_measure
    (standardSphereProbability d hd).toMeasure
    (fun e ↦
      measurePreserving_linearIsometryEquivUnitSphere_standardSphereProbability hd e)
    hF hFmono hu hv huv hα

end ProbabilityTheory
