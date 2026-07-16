/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Geometry.Convex.Set
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Supporting unit normals of convex bodies

This file isolates the separation-theoretic input to Ball's projection argument.  Every boundary
point of a closed, full-dimensional convex set admits a unit outward normal whose supporting
hyperplane contains that point.  The proof applies geometric Hahn--Banach separation and then the
finite-dimensional Fréchet--Riesz representation theorem.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

local instance instConvexSpaceSupportingNormal {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

local instance instIsModuleConvexSpaceSupportingNormal {d : ℕ} :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.ofModule

private lemma legacyConvex_of_isConvexSet {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : Convexity.IsConvexSet ℝ C) :
    Convex ℝ C := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  simpa [Convexity.convexCombPair_eq_sum] using
    hC.convexCombPair_mem hx hy ha hb hab

/-- Every boundary point of a closed convex set with nonempty ambient interior has a unit outward
supporting normal. -/
theorem exists_unit_supportingNormal {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))}
    (hC : Convexity.IsConvexSet ℝ C) (hclosed : IsClosed C)
    (hinterior : (interior C).Nonempty) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ frontier C) :
    ∃ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 ∧
      ∀ y ∈ C, inner ℝ (y - x) u ≤ 0 := by
  let E := EuclideanSpace ℝ (Fin d)
  have hxC : x ∈ C := hclosed.closure_subset hx.1
  have hxnot : x ∉ interior C := (mem_frontier_iff_notMem_interior hxC).mp hx
  obtain ⟨f, hfne, hf⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (legacyConvex_of_isConvexSet hC) hxnot hinterior
  let v : E := (InnerProductSpace.toDual ℝ E).symm f
  have hvne : v ≠ 0 := by
    intro hv
    apply hfne
    apply (InnerProductSpace.toDual ℝ E).symm.injective
    simp [v, hv]
  let u : E := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hvne)]
  refine ⟨u, hu, ?_⟩
  intro y hy
  have hfy : f y ≤ f x := hf y hy
  have hfdiff : f (y - x) ≤ 0 := by
    rw [map_sub]
    linarith
  have hvdiff : inner ℝ v (y - x) ≤ 0 := by
    simpa [v, InnerProductSpace.toDual_symm_apply] using hfdiff
  dsimp [u]
  rw [real_inner_smul_right]
  have hcomm : inner ℝ (y - x) v = inner ℝ v (y - x) := real_inner_comm _ _
  rw [hcomm]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg v)) hvdiff

end ProbabilityTheory
