/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.ConvexGeometry.MetricProjection
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Differentiability of squared distance to a convex set

This file proves the Fréchet derivative of squared distance to a nonempty closed convex subset of
finite-dimensional Euclidean space. Away from the set, taking the square root gives the derivative
of distance itself. These formulas supply the differential input for the Bentkus smooth cutoff.
-/

open Set Topology
open scoped Pointwise

noncomputable section

namespace ProbabilityTheory

local instance {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

local instance {d : ℕ} :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.ofModule

/-- Squared distance differs from its first-order projection expansion by a quadratic remainder. -/
lemma squaredInfDist_remainder_bound {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hclosed : IsClosed s) (hne : s.Nonempty) (hconv : Convexity.IsConvexSet ℝ s)
    (x h : EuclideanSpace ℝ (Fin d)) :
    |Metric.infDist (x + h) s ^ 2 - Metric.infDist x s ^ 2 -
        2 * inner ℝ (x - metricProjection s hclosed hne x) h| ≤ 3 * ‖h‖ ^ 2 := by
  let p := metricProjection s hclosed hne x
  let q := metricProjection s hclosed hne (x + h)
  let r := x - p
  let rh := x + h - q
  change |Metric.infDist (x + h) s ^ 2 - Metric.infDist x s ^ 2 -
    2 * inner ℝ r h| ≤ 3 * ‖h‖ ^ 2
  have hp := metricProjection_isNearestPoint s hclosed hne x
  have hq := metricProjection_isNearestPoint s hclosed hne (x + h)
  have hdx : Metric.infDist x s = ‖r‖ := by
    rw [infDist_eq_dist_metricProjection s hclosed hne x, dist_eq_norm]
  have hdxh : Metric.infDist (x + h) s = ‖rh‖ := by
    rw [infDist_eq_dist_metricProjection s hclosed hne (x + h), dist_eq_norm]
  have hupperNorm : ‖rh‖ ≤ ‖r + h‖ := by
    have hmin := hq.2 p hp.1
    rw [dist_eq_norm, dist_eq_norm] at hmin
    have hleft : x + h - q = rh := rfl
    have hright : x + h - p = r + h := by
      dsimp [r]
      abel
    rwa [hleft, hright] at hmin
  have hlowerNorm : ‖r‖ ≤ ‖rh - h‖ := by
    have hmin := hp.2 q hq.1
    rw [dist_eq_norm, dist_eq_norm] at hmin
    have hleft : x - p = r := rfl
    have hright : x - q = rh - h := by
      dsimp [rh]
      abel
    rwa [hleft, hright] at hmin
  have hupperSq : ‖rh‖ ^ 2 ≤ ‖r + h‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hupperNorm
  have hlowerSq : ‖r‖ ^ 2 ≤ ‖rh - h‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hlowerNorm
  rw [norm_add_sq_real r h] at hupperSq
  rw [norm_sub_sq_real rh h] at hlowerSq
  have hres : ‖rh - r‖ ≤ ‖h‖ := by
    have hL := (metricProjection_residual_lipschitzWith hclosed hne hconv).norm_sub_le
      (x + h) x
    simpa only [NNReal.coe_one, one_mul, add_sub_cancel_left] using hL
  have hinnerAbs : |inner ℝ (rh - r) h| ≤ ‖h‖ ^ 2 := by
    calc
      |inner ℝ (rh - r) h| ≤ ‖rh - r‖ * ‖h‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖h‖ * ‖h‖ := mul_le_mul_of_nonneg_right hres (norm_nonneg _)
      _ = ‖h‖ ^ 2 := by ring
  have hinnerLow : -‖h‖ ^ 2 ≤ inner ℝ (rh - r) h := neg_le_of_abs_le hinnerAbs
  have hinnerEq : inner ℝ (rh - r) h = inner ℝ rh h - inner ℝ r h := by
    rw [inner_sub_left]
  rw [hdx, hdxh]
  apply abs_le.mpr
  constructor
  · rw [hinnerEq] at hinnerLow
    nlinarith
  · nlinarith

/-- The squared distance to a nonempty closed convex Euclidean set is Fréchet differentiable,
with gradient twice the residual from the metric projection. -/
lemma hasFDerivAt_squaredInfDist {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hclosed : IsClosed s) (hne : s.Nonempty) (hconv : Convexity.IsConvexSet ℝ s)
    (x : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun y ↦ Metric.infDist y s ^ 2)
      ((2 : ℝ) • ((innerSL ℝ) (x - metricProjection s hclosed hne x))) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hbig :
      (fun h ↦ Metric.infDist (x + h) s ^ 2 - Metric.infDist x s ^ 2 -
        ((2 : ℝ) • ((innerSL ℝ) (x - metricProjection s hclosed hne x))) h) =O[𝓝 0]
        (fun h : EuclideanSpace ℝ (Fin d) ↦ ‖h‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound 3
    filter_upwards with h
    simpa only [Real.norm_eq_abs, innerSL_apply_apply, smul_apply, smul_eq_mul,
      abs_of_nonneg (sq_nonneg ‖h‖)] using
      squaredInfDist_remainder_bound hclosed hne hconv x h
  exact hbig.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)

/-- Squared distance to a nonempty closed convex Euclidean set is differentiable everywhere. -/
lemma differentiable_squaredInfDist {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hclosed : IsClosed s) (hne : s.Nonempty) (hconv : Convexity.IsConvexSet ℝ s) :
    Differentiable ℝ (fun y ↦ Metric.infDist y s ^ 2) :=
  fun x ↦ (hasFDerivAt_squaredInfDist hclosed hne hconv x).differentiableAt

/-- Squared distance is continuous. -/
lemma continuous_squaredInfDist {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) :
    Continuous (fun y ↦ Metric.infDist y s ^ 2) :=
  (Metric.continuous_infDist_pt s).pow 2

/-- Squared distance is measurable. -/
lemma measurable_squaredInfDist {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) :
    Measurable (fun y ↦ Metric.infDist y s ^ 2) :=
  (continuous_squaredInfDist s).measurable

/-- Away from a nonempty closed convex set, distance is Fréchet differentiable in the normalized
metric-projection residual direction. -/
lemma hasFDerivAt_infDist_of_notMem {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hclosed : IsClosed s) (hne : s.Nonempty) (hconv : Convexity.IsConvexSet ℝ s)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∉ s) :
    HasFDerivAt (fun y ↦ Metric.infDist y s)
      ((Metric.infDist x s)⁻¹ •
        ((innerSL ℝ) (x - metricProjection s hclosed hne x))) x := by
  have hδpos : 0 < Metric.infDist x s := (hclosed.notMem_iff_infDist_pos hne).1 hx
  have hsq := (hasFDerivAt_squaredInfDist hclosed hne hconv x).sqrt
    (pow_ne_zero 2 hδpos.ne')
  have hfun : (fun y ↦ √(Metric.infDist y s ^ 2)) = fun y ↦ Metric.infDist y s := by
    funext y
    exact Real.sqrt_sq Metric.infDist_nonneg
  rw [hfun] at hsq
  apply hsq.congr_fderiv
  ext h
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [Real.sqrt_sq hδpos.le]
  field_simp

/-- Distance is differentiable at every point outside a nonempty closed convex set. -/
lemma differentiableAt_infDist_of_notMem {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))}
    (hclosed : IsClosed s) (hne : s.Nonempty) (hconv : Convexity.IsConvexSet ℝ s)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∉ s) :
    DifferentiableAt ℝ (fun y ↦ Metric.infDist y s) x :=
  (hasFDerivAt_infDist_of_notMem hclosed hne hconv hx).differentiableAt

/-- Outside the set, the Fréchet derivative of distance has operator norm one. -/
lemma norm_fderiv_infDist_of_notMem {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))}
    (hclosed : IsClosed s) (hne : s.Nonempty) (hconv : Convexity.IsConvexSet ℝ s)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∉ s) :
    ‖fderiv ℝ (fun y ↦ Metric.infDist y s) x‖ = 1 := by
  have hδpos : 0 < Metric.infDist x s := (hclosed.notMem_iff_infDist_pos hne).1 hx
  rw [(hasFDerivAt_infDist_of_notMem hclosed hne hconv hx).fderiv, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hδpos.le), innerSL_apply_norm]
  have hnorm : Metric.infDist x s = ‖x - metricProjection s hclosed hne x‖ := by
    rw [infDist_eq_dist_metricProjection s hclosed hne x, dist_eq_norm]
  rw [← hnorm, inv_mul_cancel₀ hδpos.ne']

end ProbabilityTheory
