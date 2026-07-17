/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.ConvexGeometry.ParallelSets
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Metric projection onto a closed convex Euclidean set

This file constructs the nearest-point projection onto a nonempty closed
`Convexity.IsConvexSet` subset of finite-dimensional Euclidean space. It proves the variational
inequality and the nonexpansive, continuous, and measurable properties needed by the Bentkus
distance cutoff.
-/

open Set
open scoped Pointwise

noncomputable section

namespace ProbabilityTheory

local instance instConvexSpaceRealEuclideanSpaceFin_metricProjection {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

local instance instIsModuleConvexSpaceRealEuclideanSpaceFin_metricProjection {d : ℕ} :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.ofModule

/-- `p` is a nearest point in `s` to `x`. -/
def IsNearestPoint {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d)))
    (x p : EuclideanSpace ℝ (Fin d)) : Prop :=
  p ∈ s ∧ ∀ z ∈ s, dist x p ≤ dist x z

/-- A nearest point in a convex Euclidean set satisfies the projection variational inequality. -/
lemma nearestPoint_variational {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {u v : EuclideanSpace ℝ (Fin d)}
    (hv : v ∈ s) (hmin : ∀ w ∈ s, dist u v ≤ dist u w) :
    ∀ w ∈ s, inner ℝ (u - v) (w - v) ≤ 0 := by
  intro w hw
  let p := inner ℝ (u - v) (w - v)
  let q := ‖w - v‖ ^ 2
  have htheta (θ : ℝ) (hθ₁ : 0 < θ) (hθ₂ : θ ≤ 1) : 2 * p ≤ θ * q := by
    have hseg : θ • w + (1 - θ) • v ∈ s := by
      rw [← Convexity.convexCombPair_eq_sum θ (1 - θ) hθ₁.le (sub_nonneg.2 hθ₂)
        (by ring) w v]
      exact hs.convexCombPair_mem hw hv hθ₁.le (sub_nonneg.2 hθ₂) (by ring)
    have hnorm : ‖u - v‖ ≤ ‖u - (θ • w + (1 - θ) • v)‖ := by
      simpa only [dist_eq_norm] using hmin _ hseg
    have hsq :
        ‖u - v‖ ^ 2 ≤
          ‖u - v‖ ^ 2 - 2 * θ * inner ℝ (u - v) (w - v) + θ * θ * ‖w - v‖ ^ 2 := by
      calc
        ‖u - v‖ ^ 2 ≤ ‖u - (θ • w + (1 - θ) • v)‖ ^ 2 := by
          exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm
        _ = ‖u - v - θ • (w - v)‖ ^ 2 := by
          congr 1
          rw [smul_sub, sub_smul, one_smul]
          abel_nf
        _ = ‖u - v‖ ^ 2 - 2 * θ * inner ℝ (u - v) (w - v) + θ * θ * ‖w - v‖ ^ 2 := by
          rw [norm_sub_sq_real, inner_smul_right, norm_smul]
          rw [Real.norm_of_nonneg hθ₁.le]
          ring
    change 2 * p ≤ θ * q
    dsimp [p, q]
    nlinarith
  by_cases hq : q = 0
  · have h := htheta 1 zero_lt_one le_rfl
    rw [hq] at h
    dsimp [p] at h ⊢
    linarith
  · have hqpos : 0 < q := lt_of_le_of_ne (sq_nonneg _) fun h ↦ hq h.symm
    by_contra hp
    rw [not_le] at hp
    let θ := min (1 : ℝ) (p / q)
    have hθpos : 0 < θ := lt_min zero_lt_one (div_pos hp hqpos)
    have hθle : θ ≤ 1 := min_le_left _ _
    have hθq : θ * q ≤ p := by
      calc
        θ * q ≤ (p / q) * q := mul_le_mul_of_nonneg_right (min_le_right _ _) hqpos.le
        _ = p := div_mul_cancel₀ _ hq
    have h := htheta θ hθpos hθle
    linarith

private lemma exists_isNearestPoint {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hclosed : IsClosed s) (hne : s.Nonempty) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ p, IsNearestPoint s x p := by
  obtain ⟨p, hp, hdist⟩ := hclosed.exists_infDist_eq_dist hne x
  refine ⟨p, hp, ?_⟩
  intro z hz
  rw [← hdist]
  exact Metric.infDist_le_dist_of_mem hz

/-- A nonempty closed convex Euclidean set has a unique nearest point to every point. -/
lemma existsUnique_isNearestPoint {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hclosed : IsClosed s) (hne : s.Nonempty) (hconv : Convexity.IsConvexSet ℝ s)
    (x : EuclideanSpace ℝ (Fin d)) : ∃! p, IsNearestPoint s x p := by
  obtain ⟨p, hp⟩ := exists_isNearestPoint hclosed hne x
  refine ⟨p, hp, ?_⟩
  intro q hq
  have hpv := nearestPoint_variational hconv hp.1 hp.2 q hq.1
  have hqv := nearestPoint_variational hconv hq.1 hq.2 p hp.1
  have hpv' : 0 ≤ inner ℝ (x - p) (p - q) := by
    rw [show q - p = -(p - q) by abel, inner_neg_right] at hpv
    linarith
  have hrel :
      inner ℝ (x - p) (p - q) = inner ℝ (x - q) (p - q) - ‖p - q‖ ^ 2 := by
    rw [show x - p = (x - q) - (p - q) by abel, inner_sub_left,
      real_inner_self_eq_norm_sq]
  have hsq : ‖p - q‖ ^ 2 ≤ 0 := by linarith
  have hnorm : ‖p - q‖ = 0 := (sq_nonpos_iff _).1 hsq
  exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm

/-- The selected nearest point in a nonempty closed Euclidean set. -/
noncomputable def metricProjection {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d)))
    (hclosed : IsClosed s) (hne : s.Nonempty) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  Classical.choose (exists_isNearestPoint hclosed hne x)

/-- The selected metric projection is a nearest point. -/
lemma metricProjection_isNearestPoint {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d)))
    (hclosed : IsClosed s) (hne : s.Nonempty) (x : EuclideanSpace ℝ (Fin d)) :
    IsNearestPoint s x (metricProjection s hclosed hne x) :=
  Classical.choose_spec (exists_isNearestPoint hclosed hne x)

/-- Distance to a closed nonempty set is attained at its selected metric projection. -/
lemma infDist_eq_dist_metricProjection {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d)))
    (hclosed : IsClosed s) (hne : s.Nonempty) (x : EuclideanSpace ℝ (Fin d)) :
    Metric.infDist x s = dist x (metricProjection s hclosed hne x) := by
  let p := metricProjection s hclosed hne x
  have hp := metricProjection_isNearestPoint s hclosed hne x
  obtain ⟨z, hz, hdist⟩ := hclosed.exists_infDist_eq_dist hne x
  apply le_antisymm
  · exact Metric.infDist_le_dist_of_mem hp.1
  · calc
      dist x p ≤ dist x z := hp.2 z hz
      _ = Metric.infDist x s := hdist.symm

/-- Distance to the selected projection is a continuous function of the source point. -/
lemma continuous_dist_metricProjection {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hclosed : IsClosed s) (hne : s.Nonempty) :
    Continuous (fun x ↦ dist x (metricProjection s hclosed hne x)) := by
  have hfun : (fun x ↦ dist x (metricProjection s hclosed hne x)) =
      fun x ↦ Metric.infDist x s := by
    funext x
    exact (infDist_eq_dist_metricProjection s hclosed hne x).symm
  rw [hfun]
  exact Metric.continuous_infDist_pt s

/-- Distance to the selected projection is measurable. -/
lemma measurable_dist_metricProjection {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hclosed : IsClosed s) (hne : s.Nonempty) :
    Measurable (fun x ↦ dist x (metricProjection s hclosed hne x)) :=
  (continuous_dist_metricProjection hclosed hne).measurable

/-- The selected projection onto a closed convex set satisfies the variational inequality. -/
lemma metricProjection_variational {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hclosed : IsClosed s) (hne : s.Nonempty) (hconv : Convexity.IsConvexSet ℝ s)
    (x : EuclideanSpace ℝ (Fin d)) {z : EuclideanSpace ℝ (Fin d)} (hz : z ∈ s) :
    inner ℝ (x - metricProjection s hclosed hne x)
      (z - metricProjection s hclosed hne x) ≤ 0 := by
  have hp := metricProjection_isNearestPoint s hclosed hne x
  exact nearestPoint_variational hconv hp.1 hp.2 z hz

/-- Projection fixes every point of the closed set. -/
lemma metricProjection_eq_self {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hclosed : IsClosed s) (hne : s.Nonempty) (hconv : Convexity.IsConvexSet ℝ s)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ s) :
    metricProjection s hclosed hne x = x := by
  have hunique := existsUnique_isNearestPoint hclosed hne hconv x
  have hself : IsNearestPoint s x x := ⟨hx, fun _ _ ↦ by simp⟩
  exact hunique.unique (metricProjection_isNearestPoint s hclosed hne x) hself

private lemma norm_sq_le_inner_of_variational {d : ℕ}
    {x y p q : EuclideanSpace ℝ (Fin d)}
    (hp : inner ℝ (x - p) (q - p) ≤ 0)
    (hq : inner ℝ (y - q) (p - q) ≤ 0) :
    ‖p - q‖ ^ 2 ≤ inner ℝ (x - y) (p - q) := by
  have hp' : 0 ≤ inner ℝ (x - p) (p - q) := by
    rw [show q - p = -(p - q) by abel, inner_neg_right] at hp
    linarith
  have hrel :
      inner ℝ (x - y) (p - q) =
        inner ℝ (x - p) (p - q) - inner ℝ (y - q) (p - q) + ‖p - q‖ ^ 2 := by
    rw [show x - y = (x - p) - (y - q) + (p - q) by abel,
      inner_add_left, inner_sub_left, real_inner_self_eq_norm_sq]
  linarith

private lemma dist_le_of_variational {d : ℕ}
    {x y p q : EuclideanSpace ℝ (Fin d)}
    (hp : inner ℝ (x - p) (q - p) ≤ 0)
    (hq : inner ℝ (y - q) (p - q) ≤ 0) :
    dist p q ≤ dist x y := by
  rw [dist_eq_norm, dist_eq_norm]
  have hsq := norm_sq_le_inner_of_variational hp hq
  have hmul : ‖p - q‖ * ‖p - q‖ ≤ ‖x - y‖ * ‖p - q‖ := by
    rw [← pow_two]
    exact hsq.trans (real_inner_le_norm _ _)
  by_cases hzero : ‖p - q‖ = 0
  · rw [hzero]
    exact norm_nonneg _
  · have hpos : 0 < ‖p - q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    exact le_of_mul_le_mul_right hmul hpos

/-- Metric projection satisfies the firm nonexpansiveness inequality. -/
lemma metricProjection_firmlyNonexpansive {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))}
    (hclosed : IsClosed s) (hne : s.Nonempty) (hconv : Convexity.IsConvexSet ℝ s)
    (x y : EuclideanSpace ℝ (Fin d)) :
    ‖metricProjection s hclosed hne x - metricProjection s hclosed hne y‖ ^ 2 ≤
      inner ℝ (x - y)
        (metricProjection s hclosed hne x - metricProjection s hclosed hne y) := by
  apply norm_sq_le_inner_of_variational
  · exact metricProjection_variational hclosed hne hconv x
      (metricProjection_isNearestPoint s hclosed hne y).1
  · exact metricProjection_variational hclosed hne hconv y
      (metricProjection_isNearestPoint s hclosed hne x).1

/-- Metric projection onto a closed convex Euclidean set is nonexpansive. -/
lemma metricProjection_nonexpansive {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hclosed : IsClosed s) (hne : s.Nonempty) (hconv : Convexity.IsConvexSet ℝ s)
    (x y : EuclideanSpace ℝ (Fin d)) :
    dist (metricProjection s hclosed hne x) (metricProjection s hclosed hne y) ≤ dist x y := by
  apply dist_le_of_variational
  · exact metricProjection_variational hclosed hne hconv x
      (metricProjection_isNearestPoint s hclosed hne y).1
  · exact metricProjection_variational hclosed hne hconv y
      (metricProjection_isNearestPoint s hclosed hne x).1

/-- Metric projection onto a closed convex Euclidean set is `1`-Lipschitz. -/
lemma metricProjection_lipschitzWith {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hclosed : IsClosed s) (hne : s.Nonempty) (hconv : Convexity.IsConvexSet ℝ s) :
    LipschitzWith 1 (metricProjection s hclosed hne) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa using metricProjection_nonexpansive hclosed hne hconv x y

/-- The residual from a point to its metric projection is also `1`-Lipschitz. -/
lemma metricProjection_residual_lipschitzWith {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))}
    (hclosed : IsClosed s) (hne : s.Nonempty) (hconv : Convexity.IsConvexSet ℝ s) :
    LipschitzWith 1 (fun x ↦ x - metricProjection s hclosed hne x) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [NNReal.coe_one, one_mul]
  rw [dist_eq_norm, dist_eq_norm]
  let px := metricProjection s hclosed hne x
  let py := metricProjection s hclosed hne y
  have hdiff : (x - px) - (y - py) = (x - y) - (px - py) := by abel
  rw [hdiff]
  have hfirm : ‖px - py‖ ^ 2 ≤ inner ℝ (x - y) (px - py) :=
    metricProjection_firmlyNonexpansive hclosed hne hconv x y
  have hinner : 0 ≤ inner ℝ (x - y) (px - py) :=
    (sq_nonneg ‖px - py‖).trans hfirm
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [norm_sub_sq_real]
  linarith

/-- Metric projection onto a closed convex Euclidean set is continuous. -/
lemma continuous_metricProjection {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hclosed : IsClosed s) (hne : s.Nonempty) (hconv : Convexity.IsConvexSet ℝ s) :
    Continuous (metricProjection s hclosed hne) :=
  (metricProjection_lipschitzWith hclosed hne hconv).continuous

/-- Metric projection onto a closed convex Euclidean set is measurable. -/
lemma measurable_metricProjection {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hclosed : IsClosed s) (hne : s.Nonempty) (hconv : Convexity.IsConvexSet ℝ s) :
    Measurable (metricProjection s hclosed hne) :=
  (continuous_metricProjection hclosed hne hconv).measurable

end ProbabilityTheory
