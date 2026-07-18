/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Geometry.Convex.Set
import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-!
# Convex Euclidean parallel sets

This file establishes the convexity, measurability, whole-space, and translation properties of
open and closed Euclidean thickenings used in the smoothing and whitening arguments for Bentkus's
convex-set theorem.
-/

open Set
open scoped Pointwise

noncomputable section

namespace ProbabilityTheory

local instance instConvexSpaceRealEuclideanSpaceFin_parallelSets {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

local instance instIsModuleConvexSpaceRealEuclideanSpaceFin_parallelSets {d : ℕ} :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.ofModule

/-- A pointwise sum of convex subsets of Euclidean space is convex. -/
lemma add_isConvexSet {d : ℕ} {s t : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) (ht : Convexity.IsConvexSet ℝ t) :
    Convexity.IsConvexSet ℝ (s + t) := by
  rw [← Set.add_image_prod]
  exact (hs.prod ht).image (Prod.isAffineMap_fst.add Prod.isAffineMap_snd)

/-- An open Euclidean ball centered at the origin is convex. -/
lemma ball_zero_isConvexSet {d : ℕ} (r : ℝ) :
    Convexity.IsConvexSet ℝ (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) := by
  refine Convexity.IsConvexSet.of_convexCombPair_mem ?_
  intro a b ha hb hab x hx y hy
  simp only [Metric.mem_ball, dist_zero_right] at hx hy ⊢
  rw [Convexity.convexCombPair_eq_sum]
  calc
    ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
    _ = a * ‖x‖ + b * ‖y‖ := by
      simp [norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ < r := by
      rcases ha.eq_or_lt with rfl | ha'
      · have hb1 : b = 1 := by linarith
        simpa [hb1] using hy
      rcases hb.eq_or_lt with rfl | hb'
      · have ha1 : a = 1 := by linarith
        simpa [ha1] using hx
      calc
        a * ‖x‖ + b * ‖y‖ < a * r + b * r :=
          add_lt_add (mul_lt_mul_of_pos_left hx ha') (mul_lt_mul_of_pos_left hy hb')
        _ = r := by rw [← add_mul, hab, one_mul]

/-- The open metric thickening of a convex Euclidean set is convex. -/
lemma thickening_isConvexSet {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) (r : ℝ) :
    Convexity.IsConvexSet ℝ (Metric.thickening r s) := by
  rw [← add_ball_zero]
  exact add_isConvexSet hs (ball_zero_isConvexSet r)

/-- A nonnegative-radius closed metric thickening of a convex Euclidean set is convex. -/
lemma cthickening_isConvexSet {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {r : ℝ} (hr : 0 ≤ r) :
    Convexity.IsConvexSet ℝ (Metric.cthickening r s) := by
  rw [Metric.cthickening_eq_iInter_thickening hr]
  exact Convexity.IsConvexSet.iInter₂ fun ε _ ↦ thickening_isConvexSet hs ε

/-- Open Euclidean thickenings are measurable. -/
lemma measurableSet_thickening {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) (r : ℝ) :
    MeasurableSet (Metric.thickening r s) :=
  Metric.isOpen_thickening.measurableSet

/-- Closed Euclidean thickenings are measurable. -/
lemma measurableSet_cthickening {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) (r : ℝ) :
    MeasurableSet (Metric.cthickening r s) :=
  Metric.isClosed_cthickening.measurableSet

/-- A positive-radius open thickening of the whole Euclidean space is the whole space. -/
lemma thickening_univ_of_pos {d : ℕ} {r : ℝ} (hr : 0 < r) :
    Metric.thickening r (Set.univ : Set (EuclideanSpace ℝ (Fin d))) = Set.univ :=
  Set.eq_univ_of_univ_subset (Metric.self_subset_thickening hr Set.univ)

/-- A closed thickening of the whole Euclidean space is the whole space. -/
lemma cthickening_univ {d : ℕ} (r : ℝ) :
    Metric.cthickening r (Set.univ : Set (EuclideanSpace ℝ (Fin d))) = Set.univ :=
  Set.eq_univ_of_univ_subset (Metric.self_subset_cthickening Set.univ)

/-- Translating a measurable Euclidean set preserves measurability. -/
lemma measurableSet_vadd {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : MeasurableSet s) (a : EuclideanSpace ℝ (Fin d)) : MeasurableSet (a +ᵥ s) := by
  rw [← Set.image_vadd]
  exact ((MeasurableEquiv.addLeft a).measurableSet_image).2 hs

/-- Translating a convex Euclidean set preserves convexity. -/
lemma vadd_isConvexSet {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) (a : EuclideanSpace ℝ (Fin d)) :
    Convexity.IsConvexSet ℝ (a +ᵥ s) := by
  rw [← Set.image_vadd]
  have hconst : Convexity.IsAffineMap ℝ (fun _ : EuclideanSpace ℝ (Fin d) ↦ a) := by
    constructor
    intro w
    simp
  simpa only [vadd_eq_add, Pi.add_apply, id_eq] using
    hs.image (hconst.add (Convexity.IsAffineMap.id (R := ℝ)))

/-- Open thickening commutes with Euclidean translation. -/
lemma thickening_vadd {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (r : ℝ)
    (s : Set (EuclideanSpace ℝ (Fin d))) :
    Metric.thickening r (a +ᵥ s) = a +ᵥ Metric.thickening r s := by
  ext x
  rw [mem_vadd_set_iff_neg_vadd_mem]
  change Metric.infEDist x (a +ᵥ s) < ENNReal.ofReal r ↔
    Metric.infEDist (-a +ᵥ x) s < ENNReal.ofReal r
  rw [← Metric.infEDist_vadd a (-a +ᵥ x) s]
  simp

/-- Closed thickening commutes with Euclidean translation. -/
lemma cthickening_vadd {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (r : ℝ)
    (s : Set (EuclideanSpace ℝ (Fin d))) :
    Metric.cthickening r (a +ᵥ s) = a +ᵥ Metric.cthickening r s := by
  ext x
  rw [mem_vadd_set_iff_neg_vadd_mem]
  change Metric.infEDist x (a +ᵥ s) ≤ ENNReal.ofReal r ↔
    Metric.infEDist (-a +ᵥ x) s ≤ ENNReal.ofReal r
  rw [← Metric.infEDist_vadd a (-a +ᵥ x) s]
  simp

end ProbabilityTheory
