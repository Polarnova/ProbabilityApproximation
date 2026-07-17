/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.ConvexGeometry.BallGraphJacobian
import ProbabilityApproximation.ConvexGeometry.SupportingNormal
import ProbabilityApproximation.ConvexGeometry.ScalarCoarea
import ProbabilityApproximation.ConvexGeometry.BallRadialMass
import Mathlib.Analysis.Convex.Measure
import Mathlib.Data.Set.Card

/-!
# Projection patches of a convex boundary

Ball's projection argument decomposes a convex boundary according to the sign of the scalar
product between a supporting unit normal and a projection direction.  On either strict-sign
patch, orthogonal projection is injective: two points in one projection fiber would force their
signed displacement to be simultaneously nonpositive and nonnegative.

This module packages that decomposition using the closed supporting-normal bundle.  Compactness
of the convex body makes every patch compact and hence measurable, providing the exact source
sets needed by the codimension-one area formula.
-/

open Set MeasureTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

local instance ballProjectionAreaConvexSpace {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

local instance ballProjectionAreaIsModuleConvexSpace {d : ℕ} :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.ofModule

private lemma legacyConvex_of_isConvexSet_ballProjectionArea {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : Convexity.IsConvexSet ℝ C) :
    Convex ℝ C := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  simpa [Convexity.convexCombPair_eq_sum] using
    hC.convexCombPair_mem hx hy ha hb hab

private lemma ray_affine_identity {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p z : E) (t a : ℝ) (hta : t * a + a = 1) :
    (t * a) • p + a • (z + t • (z - p)) = z := by
  calc
    (t * a) • p + a • (z + t • (z - p)) = (t * a + a) • z := by module
    _ = (1 : ℝ) • z := by rw [hta]
    _ = z := by simp

/-- Boundary points paired with outward supporting unit normals. -/
def supportingNormalPairs {d : ℕ} (C : Set (EuclideanSpace ℝ (Fin d))) :
    Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  {p | p.1 ∈ frontier C ∧ ‖p.2‖ = 1 ∧ ∀ y ∈ C, inner ℝ (y - p.1) p.2 ≤ 0}

@[simp]
theorem mem_supportingNormalPairs {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))}
    {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)} :
    p ∈ supportingNormalPairs C ↔
      p.1 ∈ frontier C ∧ ‖p.2‖ = 1 ∧ ∀ y ∈ C, inner ℝ (y - p.1) p.2 ≤ 0 :=
  Iff.rfl

theorem isClosed_supportingNormalPairs {d : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin d))) :
    IsClosed (supportingNormalPairs C) := by
  change IsClosed
    ({p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
        p.1 ∈ frontier C} ∩
      ({p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) | ‖p.2‖ = 1} ∩
        {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
          ∀ y ∈ C, inner ℝ (y - p.1) p.2 ≤ 0}))
  apply IsClosed.inter
  · exact isClosed_frontier.preimage continuous_fst
  apply IsClosed.inter
  · exact isClosed_eq (continuous_norm.comp continuous_snd) continuous_const
  · rw [show
      {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
        ∀ y ∈ C, inner ℝ (y - p.1) p.2 ≤ 0} =
        ⋂ y, ⋂ (_hy : y ∈ C),
          {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
            inner ℝ (y - p.1) p.2 ≤ 0} by
        ext p
        simp]
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro _hy
    have hcont : Continuous (fun p :
        EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        inner ℝ (y - p.1) p.2) :=
      (continuous_const.sub continuous_fst).inner continuous_snd
    exact isClosed_le hcont continuous_const

/-- Supporting-normal pairs of a compact set form a compact normal bundle. -/
theorem IsCompact.supportingNormalPairs {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : IsCompact C) :
    IsCompact (supportingNormalPairs C) := by
  have hfrontier : IsCompact (frontier C) :=
    hC.of_isClosed_subset isClosed_frontier
      (hC.isClosed.frontier_subset)
  have hsphere : IsCompact
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    isCompact_sphere _ _
  apply (hfrontier.prod hsphere).of_isClosed_subset
    (isClosed_supportingNormalPairs C)
  intro p hp
  exact ⟨hp.1, by simpa [mem_sphere_zero_iff_norm] using hp.2.1⟩

/-- Boundary points admitting a supporting normal whose component in direction `θ` is at
least `a`. -/
def positiveSupportingNormalPatch {d : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin d)))
    (θ : EuclideanSpace ℝ (Fin d)) (a : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  Prod.fst '' (supportingNormalPairs C ∩ {p | a ≤ inner ℝ θ p.2})

/-- Boundary points admitting a supporting normal whose component in direction `θ` is at
most `-a`. -/
def negativeSupportingNormalPatch {d : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin d)))
    (θ : EuclideanSpace ℝ (Fin d)) (a : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  Prod.fst '' (supportingNormalPairs C ∩ {p | inner ℝ θ p.2 ≤ -a})

theorem mem_positiveSupportingNormalPatch {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))}
    {θ x : EuclideanSpace ℝ (Fin d)} {a : ℝ} :
    x ∈ positiveSupportingNormalPatch C θ a ↔
      ∃ u, x ∈ frontier C ∧ ‖u‖ = 1 ∧
        (∀ y ∈ C, inner ℝ (y - x) u ≤ 0) ∧ a ≤ inner ℝ θ u := by
  simp only [positiveSupportingNormalPatch, mem_image, mem_inter_iff, mem_supportingNormalPairs,
    mem_setOf_eq, Prod.exists]
  constructor
  · rintro ⟨x', u, ⟨⟨hx', hu, hsupport⟩, ha⟩, rfl⟩
    exact ⟨u, hx', hu, hsupport, ha⟩
  · rintro ⟨u, hx, hu, hsupport, ha⟩
    exact ⟨x, u, ⟨⟨hx, hu, hsupport⟩, ha⟩, rfl⟩

theorem mem_negativeSupportingNormalPatch {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))}
    {θ x : EuclideanSpace ℝ (Fin d)} {a : ℝ} :
    x ∈ negativeSupportingNormalPatch C θ a ↔
      ∃ u, x ∈ frontier C ∧ ‖u‖ = 1 ∧
        (∀ y ∈ C, inner ℝ (y - x) u ≤ 0) ∧ inner ℝ θ u ≤ -a := by
  simp only [negativeSupportingNormalPatch, mem_image, mem_inter_iff,
    mem_supportingNormalPairs, mem_setOf_eq, Prod.exists]
  constructor
  · rintro ⟨x', u, ⟨⟨hx', hu, hsupport⟩, ha⟩, rfl⟩
    exact ⟨u, hx', hu, hsupport, ha⟩
  · rintro ⟨u, hx, hu, hsupport, ha⟩
    exact ⟨x, u, ⟨⟨hx, hu, hsupport⟩, ha⟩, rfl⟩

/-- Boundary points with at least one supporting normal transverse to `θ`. -/
def transverseSupportingNormalPoints {d : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin d)))
    (θ : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∃ u, x ∈ frontier C ∧ ‖u‖ = 1 ∧
    (∀ y ∈ C, inner ℝ (y - x) u ≤ 0) ∧ inner ℝ θ u ≠ 0}

/-- The transverse part of a convex boundary is a countable union of strict-sign compact
projection patches. -/
theorem transverseSupportingNormalPoints_eq_iUnion_patches {d : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin d)))
    (θ : EuclideanSpace ℝ (Fin d)) :
    transverseSupportingNormalPoints C θ =
      (⋃ n : ℕ, positiveSupportingNormalPatch C θ (1 / (n + 1 : ℝ))) ∪
        ⋃ n : ℕ, negativeSupportingNormalPatch C θ (1 / (n + 1 : ℝ)) := by
  ext x
  constructor
  · rintro ⟨u, hx, hu, hsupport, hne⟩
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.mpr hneg)
      apply Or.inr
      apply mem_iUnion.mpr
      refine ⟨n, mem_negativeSupportingNormalPatch.mpr
        ⟨u, hx, hu, hsupport, ?_⟩⟩
      linarith
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      apply Or.inl
      apply mem_iUnion.mpr
      exact ⟨n, mem_positiveSupportingNormalPatch.mpr
        ⟨u, hx, hu, hsupport, hn.le⟩⟩
  · rintro (hpos | hneg)
    · obtain ⟨n, hn⟩ := mem_iUnion.mp hpos
      obtain ⟨u, hx, hu, hsupport, hinner⟩ :=
        mem_positiveSupportingNormalPatch.mp hn
      refine ⟨u, hx, hu, hsupport, ?_⟩
      have hthreshold : 0 < (1 / (n + 1 : ℝ)) := by positivity
      exact ne_of_gt (hthreshold.trans_le hinner)
    · obtain ⟨n, hn⟩ := mem_iUnion.mp hneg
      obtain ⟨u, hx, hu, hsupport, hinner⟩ :=
        mem_negativeSupportingNormalPatch.mp hn
      refine ⟨u, hx, hu, hsupport, ?_⟩
      have hthreshold : 0 < (1 / (n + 1 : ℝ)) := by positivity
      exact ne_of_lt (hinner.trans_lt (neg_neg_of_pos hthreshold))

theorem IsCompact.positiveSupportingNormalPatch {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : IsCompact C)
    (θ : EuclideanSpace ℝ (Fin d)) (a : ℝ) :
    IsCompact (positiveSupportingNormalPatch C θ a) := by
  apply IsCompact.image_of_continuousOn
  · apply (IsCompact.supportingNormalPairs hC).inter_right
    exact isClosed_le continuous_const (continuous_const.inner continuous_snd)
  · exact continuous_fst.continuousOn

theorem IsCompact.negativeSupportingNormalPatch {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : IsCompact C)
    (θ : EuclideanSpace ℝ (Fin d)) (a : ℝ) :
    IsCompact (negativeSupportingNormalPatch C θ a) := by
  apply IsCompact.image_of_continuousOn
  · apply (IsCompact.supportingNormalPairs hC).inter_right
    exact isClosed_le (continuous_const.inner continuous_snd) continuous_const
  · exact continuous_fst.continuousOn

private lemma sub_mem_span_of_orthogonalProjectionOnto_eq {d : ℕ}
    {θ x y : EuclideanSpace ℝ (Fin d)}
    (hproj : ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto x =
      ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto y) :
    y - x ∈ ℝ ∙ θ := by
  have hker : y - x ∈ ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto.ker := by
    change ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto (y - x) = 0
    rw [map_sub, hproj, sub_self]
  rw [((ℝ ∙ θ)ᗮ).ker_orthogonalProjectionOnto,
    Submodule.orthogonal_orthogonal] at hker
  exact hker

/-- Every relative-interior point of the orthogonal projection of a full-dimensional convex set
has a lift in the ambient interior. -/
theorem interior_image_orthogonalProjectionOnto_subset_image_interior {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : Convexity.IsConvexSet ℝ C)
    (hinterior : (interior C).Nonempty) (θ : EuclideanSpace ℝ (Fin d)) :
    interior (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' C) ⊆
      ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' interior C := by
  let P := ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto
  have hconv : Convex ℝ C := legacyConvex_of_isConvexSet_ballProjectionArea hC
  obtain ⟨p, hp⟩ := hinterior
  intro z hz
  by_cases hzp : z = P p
  · exact ⟨p, hp, hzp.symm⟩
  have hznhds := mem_interior_iff_mem_nhds.mp hz
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hznhds
  let v : (ℝ ∙ θ)ᗮ := z - P p
  have hv0 : v ≠ 0 := sub_ne_zero.mpr hzp
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  let t : ℝ := ε / (2 * ‖v‖)
  have ht : 0 < t := by
    dsimp only [t]
    positivity
  let w : (ℝ ∙ θ)ᗮ := z + t • v
  have hdist : dist w z < ε := by
    have ht_mul : t * ‖v‖ = ε / 2 := by
      dsimp only [t]
      field_simp
    calc
      dist w z = ‖t • v‖ := by simp [w, dist_eq_norm]
      _ = t * ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      _ = ε / 2 := ht_mul
      _ < ε := by linarith
  obtain ⟨y, hy, hPy⟩ := hball hdist
  let a : ℝ := (1 + t)⁻¹
  have ha0 : 0 < a := by
    dsimp only [a]
    positivity
  have ha1 : a < 1 := by
    rw [inv_lt_one₀ (by linarith : 0 < 1 + t)]
    linarith
  let q : EuclideanSpace ℝ (Fin d) := AffineMap.lineMap p y a
  have hqinterior : q ∈ interior C := by
    apply hconv.openSegment_interior_self_subset_interior hp hy
    exact lineMap_mem_openSegment ℝ p y ⟨ha0, ha1⟩
  refine ⟨q, hqinterior, ?_⟩
  have ha : 1 - a = t * a := by
    dsimp only [a]
    field_simp
    ring
  have hta : t * a + a = 1 := by linarith [ha]
  change P q = z
  rw [show q = (1 - a) • p + a • y by
    simp [q, AffineMap.lineMap_apply_module]]
  rw [map_add, map_smul, map_smul, hPy, ha]
  simpa only [w, v] using ray_affine_identity (P p) z t a hta

/-- A nonzero supporting unit normal is strictly inward-pointing from a boundary point toward
every ambient-interior point. -/
theorem inner_sub_supportingNormal_lt_of_mem_interior {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))}
    {q x u : EuclideanSpace ℝ (Fin d)} (hq : q ∈ interior C)
    (hu : ‖u‖ = 1)
    (hsupport : ∀ y ∈ C, inner ℝ (y - x) u ≤ 0) :
    inner ℝ (q - x) u < 0 := by
  have hqnhds := mem_interior_iff_mem_nhds.mp hq
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hqnhds
  let y := q + (ε / 2) • u
  have hyball : y ∈ Metric.ball q ε := by
    rw [Metric.mem_ball, show dist y q = ‖(ε / 2) • u‖ by simp [y, dist_eq_norm]]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ε / 2), hu, mul_one]
    linarith
  have hs := hsupport y (hball hyball)
  have hyx : y - x = (q - x) + (ε / 2) • u := by
    dsimp only [y]
    module
  rw [hyx, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hu, one_pow, mul_one] at hs
  linarith

/-- A boundary point whose projection lies in the relative interior of the projected convex body
admits a supporting normal transverse to the projection direction. -/
theorem mem_transverseSupportingNormalPoints_of_projection_mem_interior {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : Convexity.IsConvexSet ℝ C)
    (hclosed : IsClosed C) (hinterior : (interior C).Nonempty)
    (θ : EuclideanSpace ℝ (Fin d)) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ frontier C)
    (hxproj : ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto x ∈
      interior (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' C)) :
    x ∈ transverseSupportingNormalPoints C θ := by
  obtain ⟨q, hqinterior, hqproj⟩ :=
    interior_image_orthogonalProjectionOnto_subset_image_interior
      hC hinterior θ hxproj
  obtain ⟨u, hu, hsupport⟩ :=
    exists_unit_supportingNormal hC hclosed hinterior hx
  have hstrict :=
    inner_sub_supportingNormal_lt_of_mem_interior hqinterior hu hsupport
  have htransverse : inner ℝ θ u ≠ 0 := by
    intro hzero
    have hproj :
        ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto x =
          ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto q := hqproj.symm
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
      (sub_mem_span_of_orthogonalProjectionOnto_eq hproj)
    have hinnerzero : inner ℝ (q - x) u = 0 := by
      rw [← ht, real_inner_smul_left, hzero, mul_zero]
    linarith
  exact ⟨u, hx, hu, hsupport, htransverse⟩

/-- Projection in direction `θ` is injective on every strictly positive supporting-normal
patch. -/
theorem injOn_orthogonalProjectionOnto_positiveSupportingNormalPatch {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hclosed : IsClosed C)
    (θ : EuclideanSpace ℝ (Fin d)) {a : ℝ} (ha : 0 < a) :
    InjOn ((ℝ ∙ θ)ᗮ.orthogonalProjectionOnto)
      (positiveSupportingNormalPatch C θ a) := by
  intro x hx y hy hproj
  obtain ⟨ux, hxfrontier, _hux, hsupportx, hax⟩ :=
    mem_positiveSupportingNormalPatch.mp hx
  obtain ⟨uy, hyfrontier, _huy, hsupporty, hay⟩ :=
    mem_positiveSupportingNormalPatch.mp hy
  have hxC : x ∈ C := hclosed.frontier_subset hxfrontier
  have hyC : y ∈ C := hclosed.frontier_subset hyfrontier
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
    (sub_mem_span_of_orthogonalProjectionOnto_eq hproj)
  have htx : t * inner ℝ θ ux ≤ 0 := by
    have h := hsupportx y hyC
    rw [← ht, real_inner_smul_left] at h
    exact h
  have hty : -t * inner ℝ θ uy ≤ 0 := by
    have h := hsupporty x hxC
    have hxy : x - y = (-t) • θ := by rw [← neg_sub, ← ht, neg_smul]
    rw [hxy, real_inner_smul_left] at h
    exact h
  have htxpos : 0 < inner ℝ θ ux := ha.trans_le hax
  have htypos : 0 < inner ℝ θ uy := ha.trans_le hay
  have ht_nonpos : t ≤ 0 := nonpos_of_mul_nonpos_left htx htxpos
  have ht_nonneg : 0 ≤ t := by
    have : -t ≤ 0 := nonpos_of_mul_nonpos_left hty htypos
    linarith
  have htzero : t = 0 := le_antisymm ht_nonpos ht_nonneg
  have hyx : y - x = 0 := by rw [← ht, htzero, zero_smul]
  exact (sub_eq_zero.mp hyx).symm

/-- Projection in direction `θ` is injective on every strictly negative supporting-normal
patch. -/
theorem injOn_orthogonalProjectionOnto_negativeSupportingNormalPatch {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hclosed : IsClosed C)
    (θ : EuclideanSpace ℝ (Fin d)) {a : ℝ} (ha : 0 < a) :
    InjOn ((ℝ ∙ θ)ᗮ.orthogonalProjectionOnto)
      (negativeSupportingNormalPatch C θ a) := by
  intro x hx y hy hproj
  obtain ⟨ux, hxfrontier, _hux, hsupportx, hax⟩ :=
    mem_negativeSupportingNormalPatch.mp hx
  obtain ⟨uy, hyfrontier, _huy, hsupporty, hay⟩ :=
    mem_negativeSupportingNormalPatch.mp hy
  have hxC : x ∈ C := hclosed.frontier_subset hxfrontier
  have hyC : y ∈ C := hclosed.frontier_subset hyfrontier
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
    (sub_mem_span_of_orthogonalProjectionOnto_eq hproj)
  have htx : t * inner ℝ θ ux ≤ 0 := by
    have h := hsupportx y hyC
    rw [← ht, real_inner_smul_left] at h
    exact h
  have hty : -t * inner ℝ θ uy ≤ 0 := by
    have h := hsupporty x hxC
    have hxy : x - y = (-t) • θ := by rw [← neg_sub, ← ht, neg_smul]
    rw [hxy, real_inner_smul_left] at h
    exact h
  have htxneg : inner ℝ θ ux < 0 := lt_of_le_of_lt hax (neg_lt_zero.mpr ha)
  have htyneg : inner ℝ θ uy < 0 := lt_of_le_of_lt hay (neg_lt_zero.mpr ha)
  have ht_nonneg : 0 ≤ t := nonneg_of_mul_nonpos_left htx htxneg
  have ht_nonpos : t ≤ 0 := by
    have : 0 ≤ -t := nonneg_of_mul_nonpos_left hty htyneg
    linarith
  have htzero : t = 0 := le_antisymm ht_nonpos ht_nonneg
  have hyx : y - x = 0 := by rw [← ht, htzero, zero_smul]
  exact (sub_eq_zero.mp hyx).symm

/-- On a positive normal patch, inverse orthogonal projection is Lipschitz.  The constant is a
deliberately simple bound; its role is to produce rectifiable graph charts, not the final Ball
constant. -/
theorem dist_le_one_add_inv_mul_dist_orthogonalProjectionOnto_of_mem_positivePatch {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hclosed : IsClosed C)
    {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1)
    {a : ℝ} (ha : 0 < a) {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ positiveSupportingNormalPatch C θ a)
    (hy : y ∈ positiveSupportingNormalPatch C θ a) :
    dist x y ≤ (1 + a⁻¹) *
      dist (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto x)
        (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto y) := by
  obtain ⟨ux, hxfrontier, hux, hsupportx, hax⟩ :=
    mem_positiveSupportingNormalPatch.mp hx
  obtain ⟨uy, hyfrontier, huy, hsupporty, hay⟩ :=
    mem_positiveSupportingNormalPatch.mp hy
  have hxC : x ∈ C := hclosed.frontier_subset hxfrontier
  have hyC : y ∈ C := hclosed.frontier_subset hyfrontier
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := (ℝ ∙ θ)ᗮ
  let w : EuclideanSpace ℝ (Fin d) := y - x
  let p : EuclideanSpace ℝ (Fin d) := K.starProjection w
  let t : ℝ := inner ℝ θ w
  have hw : p + t • θ = w := by
    simpa [K, p, t, Submodule.orthogonal_orthogonal,
      Submodule.starProjection_unit_singleton ℝ hθ] using
      (K.starProjection_add_starProjection_orthogonal w)
  have htcx : t * inner ℝ θ ux ≤ ‖p‖ := by
    have hs := hsupportx y hyC
    change inner ℝ w ux ≤ 0 at hs
    rw [← hw, inner_add_left, real_inner_smul_left] at hs
    have habs := abs_real_inner_le_norm p ux
    rw [hux, mul_one] at habs
    have hlower : -‖p‖ ≤ inner ℝ p ux := neg_le_of_abs_le habs
    linarith
  have htupper : t ≤ ‖p‖ / a := by
    by_cases ht : t ≤ 0
    · exact ht.trans (div_nonneg (norm_nonneg p) ha.le)
    · have htpos : 0 < t := lt_of_not_ge ht
      apply (le_div_iff₀ ha).2
      exact (mul_le_mul_of_nonneg_left hax htpos.le).trans htcx
  have htcy : -t * inner ℝ θ uy ≤ ‖p‖ := by
    have hs := hsupporty x hxC
    have hxy : -p + (-t) • θ = x - y := by
      calc
        -p + (-t) • θ = -(p + t • θ) := by module
        _ = -w := by rw [hw]
        _ = x - y := by simp [w]
    rw [← hxy, inner_add_left, real_inner_smul_left] at hs
    have habs := abs_real_inner_le_norm (-p) uy
    rw [norm_neg, huy, mul_one] at habs
    have hlower : -‖p‖ ≤ inner ℝ (-p) uy := neg_le_of_abs_le habs
    linarith
  have htlower : -t ≤ ‖p‖ / a := by
    by_cases ht : -t ≤ 0
    · exact ht.trans (div_nonneg (norm_nonneg p) ha.le)
    · have htpos : 0 < -t := lt_of_not_ge ht
      apply (le_div_iff₀ ha).2
      exact (mul_le_mul_of_nonneg_left hay htpos.le).trans htcy
  have habst : |t| ≤ ‖p‖ / a := abs_le.mpr ⟨by linarith, htupper⟩
  have hnorm : ‖w‖ ≤ (1 + a⁻¹) * ‖p‖ := by
    calc
      ‖w‖ = ‖p + t • θ‖ := by rw [hw]
      _ ≤ ‖p‖ + ‖t • θ‖ := norm_add_le _ _
      _ = ‖p‖ + |t| := by simp [norm_smul, Real.norm_eq_abs, hθ]
      _ ≤ ‖p‖ + ‖p‖ / a := by gcongr
      _ = (1 + a⁻¹) * ‖p‖ := by rw [div_eq_inv_mul]; ring
  have hpdist : ‖p‖ =
      dist (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto x)
        (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto y) := by
    simp [p, K, w, dist_eq_norm, map_sub, norm_sub_rev]
  calc
    dist x y = ‖w‖ := by simp [w, dist_eq_norm, norm_sub_rev]
    _ ≤ (1 + a⁻¹) * ‖p‖ := hnorm
    _ = (1 + a⁻¹) *
        dist (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto x)
          (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto y) := by rw [hpdist]

/-- The inverse-projection Lipschitz estimate on a negative normal patch. -/
theorem dist_le_one_add_inv_mul_dist_orthogonalProjectionOnto_of_mem_negativePatch {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hclosed : IsClosed C)
    {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1)
    {a : ℝ} (ha : 0 < a) {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ negativeSupportingNormalPatch C θ a)
    (hy : y ∈ negativeSupportingNormalPatch C θ a) :
    dist x y ≤ (1 + a⁻¹) *
      dist (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto x)
        (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto y) := by
  obtain ⟨ux, hxfrontier, hux, hsupportx, hax⟩ :=
    mem_negativeSupportingNormalPatch.mp hx
  obtain ⟨uy, hyfrontier, huy, hsupporty, hay⟩ :=
    mem_negativeSupportingNormalPatch.mp hy
  have hxC : x ∈ C := hclosed.frontier_subset hxfrontier
  have hyC : y ∈ C := hclosed.frontier_subset hyfrontier
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := (ℝ ∙ θ)ᗮ
  let w : EuclideanSpace ℝ (Fin d) := y - x
  let p : EuclideanSpace ℝ (Fin d) := K.starProjection w
  let t : ℝ := inner ℝ θ w
  have hw : p + t • θ = w := by
    simpa [K, p, t, Submodule.orthogonal_orthogonal,
      Submodule.starProjection_unit_singleton ℝ hθ] using
      (K.starProjection_add_starProjection_orthogonal w)
  have htcx : t * inner ℝ θ ux ≤ ‖p‖ := by
    have hs := hsupportx y hyC
    change inner ℝ w ux ≤ 0 at hs
    rw [← hw, inner_add_left, real_inner_smul_left] at hs
    have habs := abs_real_inner_le_norm p ux
    rw [hux, mul_one] at habs
    have hlower : -‖p‖ ≤ inner ℝ p ux := neg_le_of_abs_le habs
    linarith
  have htlower : -t ≤ ‖p‖ / a := by
    by_cases ht : -t ≤ 0
    · exact ht.trans (div_nonneg (norm_nonneg p) ha.le)
    · have htneg : t < 0 := by linarith
      apply (le_div_iff₀ ha).2
      calc
        (-t) * a = t * (-a) := by ring
        _ ≤ t * inner ℝ θ ux := mul_le_mul_of_nonpos_left hax htneg.le
        _ ≤ ‖p‖ := htcx
  have htcy : -t * inner ℝ θ uy ≤ ‖p‖ := by
    have hs := hsupporty x hxC
    have hxy : -p + (-t) • θ = x - y := by
      calc
        -p + (-t) • θ = -(p + t • θ) := by module
        _ = -w := by rw [hw]
        _ = x - y := by simp [w]
    rw [← hxy, inner_add_left, real_inner_smul_left] at hs
    have habs := abs_real_inner_le_norm (-p) uy
    rw [norm_neg, huy, mul_one] at habs
    have hlower : -‖p‖ ≤ inner ℝ (-p) uy := neg_le_of_abs_le habs
    linarith
  have htupper : t ≤ ‖p‖ / a := by
    by_cases ht : t ≤ 0
    · exact ht.trans (div_nonneg (norm_nonneg p) ha.le)
    · have htpos : 0 < t := lt_of_not_ge ht
      apply (le_div_iff₀ ha).2
      calc
        t * a = (-t) * (-a) := by ring
        _ ≤ (-t) * inner ℝ θ uy :=
          mul_le_mul_of_nonpos_left hay (neg_nonpos.mpr htpos.le)
        _ ≤ ‖p‖ := htcy
  have habst : |t| ≤ ‖p‖ / a := abs_le.mpr ⟨by linarith, htupper⟩
  have hnorm : ‖w‖ ≤ (1 + a⁻¹) * ‖p‖ := by
    calc
      ‖w‖ = ‖p + t • θ‖ := by rw [hw]
      _ ≤ ‖p‖ + ‖t • θ‖ := norm_add_le _ _
      _ = ‖p‖ + |t| := by simp [norm_smul, Real.norm_eq_abs, hθ]
      _ ≤ ‖p‖ + ‖p‖ / a := by gcongr
      _ = (1 + a⁻¹) * ‖p‖ := by rw [div_eq_inv_mul]; ring
  have hpdist : ‖p‖ =
      dist (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto x)
        (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto y) := by
    simp [p, K, w, dist_eq_norm, map_sub, norm_sub_rev]
  calc
    dist x y = ‖w‖ := by simp [w, dist_eq_norm, norm_sub_rev]
    _ ≤ (1 + a⁻¹) * ‖p‖ := hnorm
    _ = (1 + a⁻¹) *
        dist (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto x)
          (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto y) := by rw [hpdist]

/-- A total inverse to orthogonal projection on a specified source set.  Outside the projection
image it takes the harmless value zero; all geometric statements restrict it to the image. -/
def orthogonalProjectionPatchInverse {d : ℕ}
    (θ : EuclideanSpace ℝ (Fin d)) (s : Set (EuclideanSpace ℝ (Fin d)))
    (z : (ℝ ∙ θ)ᗮ) : EuclideanSpace ℝ (Fin d) := by
  classical
  exact if hz : z ∈ ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' s then hz.choose else 0

theorem orthogonalProjectionPatchInverse_mem {d : ℕ}
    {θ : EuclideanSpace ℝ (Fin d)} {s : Set (EuclideanSpace ℝ (Fin d))}
    {z : (ℝ ∙ θ)ᗮ}
    (hz : z ∈ ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' s) :
    orthogonalProjectionPatchInverse θ s z ∈ s := by
  rw [orthogonalProjectionPatchInverse, dif_pos hz]
  exact hz.choose_spec.1

theorem orthogonalProjectionOnto_patchInverse {d : ℕ}
    {θ : EuclideanSpace ℝ (Fin d)} {s : Set (EuclideanSpace ℝ (Fin d))}
    {z : (ℝ ∙ θ)ᗮ}
    (hz : z ∈ ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' s) :
    ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto
      (orthogonalProjectionPatchInverse θ s z) = z := by
  rw [orthogonalProjectionPatchInverse, dif_pos hz]
  exact hz.choose_spec.2

theorem orthogonalProjectionPatchInverse_apply_projection {d : ℕ}
    {θ : EuclideanSpace ℝ (Fin d)} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hinj : InjOn ((ℝ ∙ θ)ᗮ.orthogonalProjectionOnto) s)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ s) :
    orthogonalProjectionPatchInverse θ s
      (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto x) = x := by
  let z := ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto x
  have hz : z ∈ ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' s := ⟨x, hx, rfl⟩
  apply hinj (orthogonalProjectionPatchInverse_mem hz) hx
  exact orthogonalProjectionOnto_patchInverse hz

theorem image_orthogonalProjectionPatchInverse {d : ℕ}
    {θ : EuclideanSpace ℝ (Fin d)} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hinj : InjOn ((ℝ ∙ θ)ᗮ.orthogonalProjectionOnto) s) :
    orthogonalProjectionPatchInverse θ s ''
        (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' s) = s := by
  apply Set.Subset.antisymm
  · rintro x ⟨z, hz, rfl⟩
    exact orthogonalProjectionPatchInverse_mem hz
  · intro x hx
    refine ⟨((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto x, ⟨x, hx, rfl⟩, ?_⟩
    exact orthogonalProjectionPatchInverse_apply_projection hinj hx

/-- At every unique-differentiability point of a projection image, the derivative of the inverse
graph chart is a right inverse to orthogonal projection. -/
theorem fderivWithin_orthogonalProjectionPatchInverse_projection_comp {d : ℕ}
    {θ : EuclideanSpace ℝ (Fin d)} {s : Set (EuclideanSpace ℝ (Fin d))}
    {z : (ℝ ∙ θ)ᗮ}
    (hz : z ∈ ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' s)
    (hunique : UniqueDiffWithinAt ℝ
      (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' s) z)
    (hdiff : DifferentiableWithinAt ℝ (orthogonalProjectionPatchInverse θ s)
      (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' s) z) :
    ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto.toLinearMap.comp
        (fderivWithin ℝ (orthogonalProjectionPatchInverse θ s)
          (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' s) z).toLinearMap =
      LinearMap.id := by
  let P := ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto
  let S := P '' s
  let φ := orthogonalProjectionPatchInverse θ s
  have hcomp : HasFDerivWithinAt (fun y ↦ P (φ y))
      (P.comp (fderivWithin ℝ φ S z)) S z :=
    P.hasFDerivAt.comp_hasFDerivWithinAt z hdiff.hasFDerivWithinAt
  have heq : EqOn id (fun y ↦ P (φ y)) S := by
    intro y hy
    exact (orthogonalProjectionOnto_patchInverse hy).symm
  have hcompId : HasFDerivWithinAt id
      (P.comp (fderivWithin ℝ φ S z)) S z := hcomp.congr' heq hz
  have hid : HasFDerivWithinAt id (ContinuousLinearMap.id ℝ ((ℝ ∙ θ)ᗮ)) S z :=
    (hasFDerivAt_id z).hasFDerivWithinAt
  have hderiv := hunique.eq hcompId hid
  exact congr_arg ContinuousLinearMap.toLinearMap hderiv

/-- The inverse graph derivative has a unit normal whose projection factor exactly cancels its
surface Jacobian. -/
theorem exists_unit_normal_fderivWithin_patchInverse_normDet_mul_eq_one {d : ℕ}
    (hd : 2 ≤ d) {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1)
    {s : Set (EuclideanSpace ℝ (Fin d))} {z : (ℝ ∙ θ)ᗮ}
    (hz : z ∈ ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' s)
    (hunique : UniqueDiffWithinAt ℝ
      (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' s) z)
    (hdiff : DifferentiableWithinAt ℝ (orthogonalProjectionPatchInverse θ s)
      (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' s) z) :
    ∃ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 ∧
      (fderivWithin ℝ (orthogonalProjectionPatchInverse θ s)
        (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' s) z).toLinearMap.range =
          (ℝ ∙ u)ᗮ ∧
      |inner ℝ θ u| *
        (fderivWithin ℝ (orthogonalProjectionPatchInverse θ s)
          (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' s) z).toLinearMap.normDet = 1 := by
  apply exists_unit_normal_normDet_mul_eq_one_of_projection_comp_eq_id hd hθ
  exact fderivWithin_orthogonalProjectionPatchInverse_projection_comp hz hunique hdiff

/-- Projecting a codimension-one graph derivative in any unit direction multiplies its surface
Jacobian by the absolute component of a unit normal in that direction. -/
theorem normDet_orthogonalProjection_comp_eq_abs_inner_mul {d : ℕ}
    (hd : 2 ≤ d) {q θ u : EuclideanSpace ℝ (Fin d)}
    (hq : ‖q‖ = 1) (hθ : ‖θ‖ = 1)
    (L : (ℝ ∙ q)ᗮ →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (hu : ‖u‖ = 1) (hrange : L.range = (ℝ ∙ u)ᗮ) :
    (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto.toLinearMap.comp L).normDet =
      |inner ℝ θ u| * L.normDet := by
  let L' : (ℝ ∙ q)ᗮ →ₗ[ℝ] (ℝ ∙ u)ᗮ :=
    L.codRestrict ((ℝ ∙ u)ᗮ) (fun x ↦ by
      rw [← hrange]
      exact LinearMap.mem_range_self L x)
  have hq0 : q ≠ 0 := norm_ne_zero_iff.mp (by rw [hq]; exact one_ne_zero)
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; exact one_ne_zero)
  have hambient : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by
    simp [finrank_euclideanSpace]
  have hdomain : Module.finrank ℝ ((ℝ ∙ q)ᗮ) = d - 1 := by
    have hsum := (ℝ ∙ q).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton hq0, hambient] at hsum
    omega
  have hintermediate : Module.finrank ℝ ((ℝ ∙ u)ᗮ) = d - 1 := by
    have hsum := (ℝ ∙ u).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton hu0, hambient] at hsum
    omega
  have hfinrank : Module.finrank ℝ ((ℝ ∙ q)ᗮ) =
      Module.finrank ℝ ((ℝ ∙ u)ᗮ) := by
    rw [hdomain, hintermediate]
  have hnormDet := LinearMap.normDet_comp_of_finrank_eq L'
    (hyperplaneOrthogonalProjection u θ) hfinrank
  have hcomp :
      (hyperplaneOrthogonalProjection u θ).comp L' =
        ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto.toLinearMap.comp L := by
    rfl
  rw [hcomp, normDet_hyperplaneOrthogonalProjection hu hθ,
    LinearMap.normDet_codRestrict] at hnormDet
  simpa [mul_comm] using hnormDet

/-- The inverse chart of a positive normal patch is Lipschitz on its projection image. -/
theorem lipschitzOnWith_orthogonalProjectionPatchInverse_positivePatch {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hclosed : IsClosed C)
    {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1)
    {a : ℝ} (ha : 0 < a) :
    LipschitzOnWith (Real.toNNReal (1 + a⁻¹))
      (orthogonalProjectionPatchInverse θ (positiveSupportingNormalPatch C θ a))
      (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto ''
        positiveSupportingNormalPatch C θ a) := by
  have hinj := injOn_orthogonalProjectionOnto_positiveSupportingNormalPatch hclosed θ ha
  intro z hz z' hz'
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨y, hy, rfl⟩ := hz'
  rw [orthogonalProjectionPatchInverse_apply_projection hinj hx,
    orthogonalProjectionPatchInverse_apply_projection hinj hy]
  have hcoef : 0 ≤ 1 + a⁻¹ := by positivity
  have hdist :=
    dist_le_one_add_inv_mul_dist_orthogonalProjectionOnto_of_mem_positivePatch
      hclosed hθ ha hx hy
  rw [edist_dist, edist_dist]
  change ENNReal.ofReal (dist x y) ≤
    ENNReal.ofReal (1 + a⁻¹) * ENNReal.ofReal
      (dist (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto x)
        (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto y))
  rw [← ENNReal.ofReal_mul hcoef]
  exact ENNReal.ofReal_le_ofReal hdist

/-- The inverse chart of a negative normal patch is Lipschitz on its projection image. -/
theorem lipschitzOnWith_orthogonalProjectionPatchInverse_negativePatch {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hclosed : IsClosed C)
    {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1)
    {a : ℝ} (ha : 0 < a) :
    LipschitzOnWith (Real.toNNReal (1 + a⁻¹))
      (orthogonalProjectionPatchInverse θ (negativeSupportingNormalPatch C θ a))
      (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto ''
        negativeSupportingNormalPatch C θ a) := by
  have hinj := injOn_orthogonalProjectionOnto_negativeSupportingNormalPatch hclosed θ ha
  intro z hz z' hz'
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨y, hy, rfl⟩ := hz'
  rw [orthogonalProjectionPatchInverse_apply_projection hinj hx,
    orthogonalProjectionPatchInverse_apply_projection hinj hy]
  have hcoef : 0 ≤ 1 + a⁻¹ := by positivity
  have hdist :=
    dist_le_one_add_inv_mul_dist_orthogonalProjectionOnto_of_mem_negativePatch
      hclosed hθ ha hx hy
  rw [edist_dist, edist_dist]
  change ENNReal.ofReal (dist x y) ≤
    ENNReal.ofReal (1 + a⁻¹) * ENNReal.ofReal
      (dist (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto x)
        (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto y))
  rw [← ENNReal.ofReal_mul hcoef]
  exact ENNReal.ofReal_le_ofReal hdist

/-- The inverse projection chart remains Lipschitz after restricting a positive patch to an
arbitrary subset. -/
theorem lipschitzOnWith_orthogonalProjectionPatchInverse_of_subset_positivePatch {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hclosed : IsClosed C)
    {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1)
    {a : ℝ} (ha : 0 < a) {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : s ⊆ positiveSupportingNormalPatch C θ a) :
    LipschitzOnWith (Real.toNNReal (1 + a⁻¹))
      (orthogonalProjectionPatchInverse θ s)
      (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' s) := by
  have hinj :=
    (injOn_orthogonalProjectionOnto_positiveSupportingNormalPatch hclosed θ ha).mono hs
  intro z hz z' hz'
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨y, hy, rfl⟩ := hz'
  rw [orthogonalProjectionPatchInverse_apply_projection hinj hx,
    orthogonalProjectionPatchInverse_apply_projection hinj hy]
  have hcoef : 0 ≤ 1 + a⁻¹ := by positivity
  have hdist :=
    dist_le_one_add_inv_mul_dist_orthogonalProjectionOnto_of_mem_positivePatch
      hclosed hθ ha (hs hx) (hs hy)
  rw [edist_dist, edist_dist]
  change ENNReal.ofReal (dist x y) ≤
    ENNReal.ofReal (1 + a⁻¹) * ENNReal.ofReal
      (dist (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto x)
        (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto y))
  rw [← ENNReal.ofReal_mul hcoef]
  exact ENNReal.ofReal_le_ofReal hdist

/-- The inverse projection chart remains Lipschitz after restricting a negative patch to an
arbitrary subset. -/
theorem lipschitzOnWith_orthogonalProjectionPatchInverse_of_subset_negativePatch {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hclosed : IsClosed C)
    {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1)
    {a : ℝ} (ha : 0 < a) {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : s ⊆ negativeSupportingNormalPatch C θ a) :
    LipschitzOnWith (Real.toNNReal (1 + a⁻¹))
      (orthogonalProjectionPatchInverse θ s)
      (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' s) := by
  have hinj :=
    (injOn_orthogonalProjectionOnto_negativeSupportingNormalPatch hclosed θ ha).mono hs
  intro z hz z' hz'
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨y, hy, rfl⟩ := hz'
  rw [orthogonalProjectionPatchInverse_apply_projection hinj hx,
    orthogonalProjectionPatchInverse_apply_projection hinj hy]
  have hcoef : 0 ≤ 1 + a⁻¹ := by positivity
  have hdist :=
    dist_le_one_add_inv_mul_dist_orthogonalProjectionOnto_of_mem_negativePatch
      hclosed hθ ha (hs hx) (hs hy)
  rw [edist_dist, edist_dist]
  change ENNReal.ofReal (dist x y) ≤
    ENNReal.ofReal (1 + a⁻¹) * ENNReal.ofReal
      (dist (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto x)
        (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto y))
  rw [← ENNReal.ofReal_mul hcoef]
  exact ENNReal.ofReal_le_ofReal hdist

private lemma finrank_orthogonal_span_unit {d : ℕ}
    {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1) :
    Module.finrank ℝ ((ℝ ∙ θ)ᗮ) = d - 1 := by
  have hθ0 : θ ≠ 0 := norm_ne_zero_iff.mp (by rw [hθ]; exact one_ne_zero)
  have hspan : Module.finrank ℝ (ℝ ∙ θ) = 1 := finrank_span_singleton hθ0
  have hsum := (ℝ ∙ θ).finrank_add_finrank_orthogonal
  have hambient : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by
    simp [finrank_euclideanSpace]
  rw [hspan, hambient] at hsum
  omega

private lemma injOn_orthogonalProjectionPatchInverse {d : ℕ}
    {θ : EuclideanSpace ℝ (Fin d)} {s : Set (EuclideanSpace ℝ (Fin d))} :
    InjOn (orthogonalProjectionPatchInverse θ s)
      (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' s) := by
  intro z hz z' hz' hzz'
  have h := congrArg ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto hzz'
  rw [orthogonalProjectionOnto_patchInverse hz,
    orthogonalProjectionOnto_patchInverse hz'] at h
  exact h

/-- Weighted area formula on a strictly positive supporting-normal patch. -/
theorem lintegral_positiveSupportingNormalPatch_eq_chart {d : ℕ}
    (hd : 2 ≤ d) {C : Set (EuclideanSpace ℝ (Fin d))}
    (hcompact : IsCompact C) {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1)
    {a : ℝ} (ha : 0 < a) (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hg : Measurable g) :
    (∫⁻ x in positiveSupportingNormalPatch C θ a, g x
        ∂Measure.euclideanHausdorffMeasure (d - 1)) =
      ∫⁻ z in ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto ''
          positiveSupportingNormalPatch C θ a,
        ENNReal.ofReal
            (fderivWithin ℝ
              (orthogonalProjectionPatchInverse θ
                (positiveSupportingNormalPatch C θ a))
              (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto ''
                positiveSupportingNormalPatch C θ a) z).toLinearMap.normDet *
          g (orthogonalProjectionPatchInverse θ
            (positiveSupportingNormalPatch C θ a) z) ∂volume := by
  let S := positiveSupportingNormalPatch C θ a
  let P := ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto
  let T := P '' S
  let φ := orthogonalProjectionPatchInverse θ S
  have hclosed := hcompact.isClosed
  have hprojInj : InjOn P S :=
    injOn_orthogonalProjectionOnto_positiveSupportingNormalPatch hclosed θ ha
  have hTcompact : IsCompact T := by
    exact (IsCompact.positiveSupportingNormalPatch hcompact θ a).image P.continuous
  have harea := lintegral_image_eq_lintegral_normDet_fderivWithin_mul_of_comp_eq_id
    (U := (ℝ ∙ θ)ᗮ) (V := EuclideanSpace ℝ (Fin d))
    hTcompact.measurableSet
    (lipschitzOnWith_orthogonalProjectionPatchInverse_positivePatch hclosed hθ ha)
    (injOn_orthogonalProjectionPatchInverse (θ := θ) (s := S))
    P
    (fun z hz ↦ (orthogonalProjectionOnto_patchInverse hz).symm)
    g hg
  rw [image_orthogonalProjectionPatchInverse hprojInj,
    finrank_orthogonal_span_unit hθ] at harea
  exact harea

/-- Weighted area formula on a strictly negative supporting-normal patch. -/
theorem lintegral_negativeSupportingNormalPatch_eq_chart {d : ℕ}
    (hd : 2 ≤ d) {C : Set (EuclideanSpace ℝ (Fin d))}
    (hcompact : IsCompact C) {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1)
    {a : ℝ} (ha : 0 < a) (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hg : Measurable g) :
    (∫⁻ x in negativeSupportingNormalPatch C θ a, g x
        ∂Measure.euclideanHausdorffMeasure (d - 1)) =
      ∫⁻ z in ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto ''
          negativeSupportingNormalPatch C θ a,
        ENNReal.ofReal
            (fderivWithin ℝ
              (orthogonalProjectionPatchInverse θ
                (negativeSupportingNormalPatch C θ a))
              (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto ''
                negativeSupportingNormalPatch C θ a) z).toLinearMap.normDet *
          g (orthogonalProjectionPatchInverse θ
            (negativeSupportingNormalPatch C θ a) z) ∂volume := by
  let S := negativeSupportingNormalPatch C θ a
  let P := ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto
  let T := P '' S
  let φ := orthogonalProjectionPatchInverse θ S
  have hclosed := hcompact.isClosed
  have hprojInj : InjOn P S :=
    injOn_orthogonalProjectionOnto_negativeSupportingNormalPatch hclosed θ ha
  have hTcompact : IsCompact T := by
    exact (IsCompact.negativeSupportingNormalPatch hcompact θ a).image P.continuous
  have harea := lintegral_image_eq_lintegral_normDet_fderivWithin_mul_of_comp_eq_id
    (U := (ℝ ∙ θ)ᗮ) (V := EuclideanSpace ℝ (Fin d))
    hTcompact.measurableSet
    (lipschitzOnWith_orthogonalProjectionPatchInverse_negativePatch hclosed hθ ha)
    (injOn_orthogonalProjectionPatchInverse (θ := θ) (s := S))
    P
    (fun z hz ↦ (orthogonalProjectionOnto_patchInverse hz).symm)
    g hg
  rw [image_orthogonalProjectionPatchInverse hprojInj,
    finrank_orthogonal_span_unit hθ] at harea
  exact harea

/-- Boundary points admitting an outward supporting normal with strictly positive component in
the projection direction. -/
def positiveSupportingNormalPoints {d : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin d))) (θ : EuclideanSpace ℝ (Fin d)) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  ⋃ k : ℕ, positiveSupportingNormalPatch C θ (1 / (k + 1 : ℝ))

/-- Boundary points admitting an outward supporting normal with strictly negative component in
the projection direction. -/
def negativeSupportingNormalPoints {d : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin d))) (θ : EuclideanSpace ℝ (Fin d)) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  ⋃ k : ℕ, negativeSupportingNormalPatch C θ (1 / (k + 1 : ℝ))

theorem transverseSupportingNormalPoints_eq_positive_union_negative {d : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin d))) (θ : EuclideanSpace ℝ (Fin d)) :
    transverseSupportingNormalPoints C θ =
      positiveSupportingNormalPoints C θ ∪ negativeSupportingNormalPoints C θ := by
  rw [transverseSupportingNormalPoints_eq_iUnion_patches]
  rfl

theorem measurableSet_positiveSupportingNormalPoints {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : IsCompact C)
    (θ : EuclideanSpace ℝ (Fin d)) :
    MeasurableSet (positiveSupportingNormalPoints C θ) := by
  unfold positiveSupportingNormalPoints
  exact MeasurableSet.iUnion fun k ↦
    (IsCompact.positiveSupportingNormalPatch hC θ (1 / (k + 1 : ℝ))).measurableSet

theorem measurableSet_negativeSupportingNormalPoints {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : IsCompact C)
    (θ : EuclideanSpace ℝ (Fin d)) :
    MeasurableSet (negativeSupportingNormalPoints C θ) := by
  unfold negativeSupportingNormalPoints
  exact MeasurableSet.iUnion fun k ↦
    (IsCompact.negativeSupportingNormalPatch hC θ (1 / (k + 1 : ℝ))).measurableSet

/-- The standard coordinate direction used to choose finitely many boundary graph charts. -/
def ballBoundaryCoordinateDirection {d : ℕ} (i : Fin d) :
    EuclideanSpace ℝ (Fin d) :=
  EuclideanSpace.single i 1

@[simp]
theorem norm_ballBoundaryCoordinateDirection {d : ℕ} (i : Fin d) :
    ‖ballBoundaryCoordinateDirection i‖ = 1 := by
  simp [ballBoundaryCoordinateDirection]

@[simp]
theorem inner_ballBoundaryCoordinateDirection {d : ℕ}
    (i : Fin d) (u : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (ballBoundaryCoordinateDirection i) u = u i := by
  simp [ballBoundaryCoordinateDirection, EuclideanSpace.inner_single_left]

/-- A unit vector in dimension at least two has a coordinate of absolute value at least `1 / d`.
The deliberately nonsharp threshold gives a uniform Lipschitz constant for a finite chart cover. -/
theorem exists_coordinate_abs_ge_inv_natCast {d : ℕ} (hd : 2 ≤ d)
    {u : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1) :
    ∃ i : Fin d, (d : ℝ)⁻¹ ≤ |u i| := by
  by_contra h
  push Not at h
  have hd0 : d ≠ 0 := by omega
  have hnonempty : (Finset.univ : Finset (Fin d)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hsumlt :
      (∑ i : Fin d, (u i) ^ 2) <
        ∑ _i : Fin d, ((d : ℝ)⁻¹) ^ 2 := by
    apply Finset.sum_lt_sum_of_nonempty hnonempty
    intro i _hi
    have hi : |u i| < (d : ℝ)⁻¹ := h i
    have hinv : 0 ≤ (d : ℝ)⁻¹ := by positivity
    simpa [sq_abs] using (sq_lt_sq₀ (abs_nonneg (u i)) hinv).2 hi
  have hnormsq : (∑ i : Fin d, (u i) ^ 2) = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hu, one_pow]
  have hconst :
      (∑ _i : Fin d, ((d : ℝ)⁻¹) ^ 2) = (d : ℝ)⁻¹ := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  rw [hnormsq, hconst] at hsumlt
  have hinvle : (d : ℝ)⁻¹ ≤ 1 / 2 := by
    have hdcast : (2 : ℝ) ≤ d := by exact_mod_cast hd
    simpa [one_div] using one_div_le_one_div_of_le (by norm_num) hdcast
  linarith

/-- The positive or negative fixed-threshold patch selected by a coordinate and a sign bit. -/
def ballBoundaryCoordinatePatch {d : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin d))) (j : Fin d × Bool) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  if j.2 = true then
    positiveSupportingNormalPatch C (ballBoundaryCoordinateDirection j.1) (d : ℝ)⁻¹
  else
    negativeSupportingNormalPatch C (ballBoundaryCoordinateDirection j.1) (d : ℝ)⁻¹

/-- The fixed-threshold coordinate patches cover the boundary of a full-dimensional closed
convex set. -/
theorem frontier_subset_iUnion_ballBoundaryCoordinatePatch {d : ℕ} (hd : 2 ≤ d)
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : Convexity.IsConvexSet ℝ C)
    (hclosed : IsClosed C) (hinterior : (interior C).Nonempty) :
    frontier C ⊆ ⋃ j : Fin d × Bool, ballBoundaryCoordinatePatch C j := by
  intro x hx
  obtain ⟨u, hu, hsupport⟩ := exists_unit_supportingNormal hC hclosed hinterior hx
  obtain ⟨i, hi⟩ := exists_coordinate_abs_ge_inv_natCast hd hu
  rcases le_total 0 (u i) with hnonneg | hnonpos
  · have hcoord : (d : ℝ)⁻¹ ≤ u i := by
      simpa [abs_of_nonneg hnonneg] using hi
    apply Set.mem_iUnion.mpr
    refine ⟨(i, true), ?_⟩
    simp only [ballBoundaryCoordinatePatch, if_pos rfl]
    apply mem_positiveSupportingNormalPatch.mpr
    exact ⟨u, hx, hu, hsupport, by
      simpa using hcoord⟩
  · have hcoord : u i ≤ -(d : ℝ)⁻¹ := by
      have habs : |u i| = -(u i) := abs_of_nonpos hnonpos
      rw [habs] at hi
      linarith
    apply Set.mem_iUnion.mpr
    refine ⟨(i, false), ?_⟩
    simp only [ballBoundaryCoordinatePatch, Bool.false_eq_true, if_false]
    apply mem_negativeSupportingNormalPatch.mpr
    exact ⟨u, hx, hu, hsupport, by
      simpa using hcoord⟩

theorem ballBoundaryCoordinatePatch_subset_frontier {d : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin d))) (j : Fin d × Bool) :
    ballBoundaryCoordinatePatch C j ⊆ frontier C := by
  intro x hx
  unfold ballBoundaryCoordinatePatch at hx
  split at hx
  · obtain ⟨u, hxfrontier, _hu, _hsupport, _hpos⟩ :=
      mem_positiveSupportingNormalPatch.mp hx
    exact hxfrontier
  · obtain ⟨u, hxfrontier, _hu, _hsupport, _hneg⟩ :=
      mem_negativeSupportingNormalPatch.mp hx
    exact hxfrontier

theorem isCompact_ballBoundaryCoordinatePatch {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : IsCompact C) (j : Fin d × Bool) :
    IsCompact (ballBoundaryCoordinatePatch C j) := by
  unfold ProbabilityTheory.ballBoundaryCoordinatePatch
  split
  · exact IsCompact.positiveSupportingNormalPatch hC _ _
  · exact IsCompact.negativeSupportingNormalPatch hC _ _

/-- Disjointification of the finite coordinate graph cover in lexicographic chart order. -/
def ballBoundaryCoordinatePiece {d : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin d))) (j : Fin d × Bool) :
    Set (EuclideanSpace ℝ (Fin d)) := by
  classical
  exact ballBoundaryCoordinatePatch C j \
    (⋃ k ∈ Finset.univ.filter
      (fun k : Fin d × Bool ↦ Encodable.encode k < Encodable.encode j),
        ballBoundaryCoordinatePatch C k)

theorem measurableSet_ballBoundaryCoordinatePiece {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : IsCompact C) (j : Fin d × Bool) :
    MeasurableSet (ballBoundaryCoordinatePiece C j) := by
  classical
  apply (isCompact_ballBoundaryCoordinatePatch hC j).measurableSet.diff
  exact MeasurableSet.iUnion fun k ↦ MeasurableSet.iUnion fun _hk ↦
    (isCompact_ballBoundaryCoordinatePatch hC k).measurableSet

theorem pairwise_disjoint_ballBoundaryCoordinatePiece {d : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin d))) :
    Pairwise (fun i j ↦ Disjoint
      (ballBoundaryCoordinatePiece C i) (ballBoundaryCoordinatePiece C j)) := by
  classical
  intro i j hij
  have hencode : Encodable.encode i ≠ Encodable.encode j := by
    exact fun h ↦ hij (Encodable.encode_injective h)
  rcases lt_or_gt_of_ne hencode with hijlt | hjilt
  · rw [Set.disjoint_left]
    intro x hxi hxj
    apply hxj.2
    apply Set.mem_iUnion.mpr
    refine ⟨i, Set.mem_iUnion.mpr ⟨by simp [hijlt], hxi.1⟩⟩
  · rw [Set.disjoint_left]
    intro x hxi hxj
    apply hxi.2
    apply Set.mem_iUnion.mpr
    refine ⟨j, Set.mem_iUnion.mpr ⟨by simp [hjilt], hxj.1⟩⟩

/-- The disjoint coordinate pieces cover exactly the boundary of a compact full-dimensional
convex set. -/
theorem iUnion_ballBoundaryCoordinatePiece_eq_frontier {d : ℕ} (hd : 2 ≤ d)
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : Convexity.IsConvexSet ℝ C)
    (hcompact : IsCompact C) (hinterior : (interior C).Nonempty) :
    (⋃ j : Fin d × Bool, ballBoundaryCoordinatePiece C j) = frontier C := by
  classical
  apply Set.Subset.antisymm
  · apply Set.iUnion_subset
    intro j
    exact Set.diff_subset.trans
      (ballBoundaryCoordinatePatch_subset_frontier C j)
  · intro x hx
    have hcover := frontier_subset_iUnion_ballBoundaryCoordinatePatch
      hd hC hcompact.isClosed hinterior hx
    obtain ⟨j₀, hxj₀⟩ := Set.mem_iUnion.mp hcover
    let J : Finset (Fin d × Bool) :=
      Finset.univ.filter fun j ↦ x ∈ ballBoundaryCoordinatePatch C j
    have hJ : J.Nonempty := by
      refine ⟨j₀, ?_⟩
      simp [J, hxj₀]
    obtain ⟨j, hjJ, hjmin⟩ :=
      Finset.exists_min_image J Encodable.encode hJ
    have hxj : x ∈ ballBoundaryCoordinatePatch C j := by
      exact (Finset.mem_filter.mp hjJ).2
    apply Set.mem_iUnion.mpr
    refine ⟨j, hxj, ?_⟩
    intro hxearlier
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxearlier
    obtain ⟨hkj, hxpatch⟩ := Set.mem_iUnion.mp hxk
    have hkJ : k ∈ J := by
      simp [J, hxpatch]
    have hjk : Encodable.encode j ≤ Encodable.encode k := hjmin k hkJ
    have hkjlt : Encodable.encode k < Encodable.encode j := by
      simpa using (Finset.mem_filter.mp hkj).2
    exact (not_lt_of_ge hjk) hkjlt

/-- The orthogonal-projection image serving as the source of one disjoint boundary chart. -/
def ballBoundaryCoordinateChartDomain {d : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin d))) (j : Fin d × Bool) :
    Set ((ℝ ∙ ballBoundaryCoordinateDirection j.1)ᗮ) :=
  ((ℝ ∙ ballBoundaryCoordinateDirection j.1)ᗮ).orthogonalProjectionOnto ''
    ballBoundaryCoordinatePiece C j

/-- The inverse orthogonal-projection parameterization of one disjoint boundary chart. -/
def ballBoundaryCoordinateChart {d : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin d))) (j : Fin d × Bool) :
    (ℝ ∙ ballBoundaryCoordinateDirection j.1)ᗮ →
      EuclideanSpace ℝ (Fin d) :=
  orthogonalProjectionPatchInverse (ballBoundaryCoordinateDirection j.1)
    (ballBoundaryCoordinatePiece C j)

/-- One disjoint boundary chart followed by orthogonal projection in an arbitrary direction. -/
def ballBoundaryCoordinateProjectedChart {d : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin d))) (j : Fin d × Bool)
    (θ : EuclideanSpace ℝ (Fin d)) :
    (ℝ ∙ ballBoundaryCoordinateDirection j.1)ᗮ → (ℝ ∙ θ)ᗮ :=
  fun z ↦ ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto
    (ballBoundaryCoordinateChart C j z)

theorem injOn_ballBoundaryCoordinateProjection {d : ℕ} (hd : 2 ≤ d)
    {C : Set (EuclideanSpace ℝ (Fin d))} (hclosed : IsClosed C)
    (j : Fin d × Bool) :
    InjOn
      ((ℝ ∙ ballBoundaryCoordinateDirection j.1)ᗮ).orthogonalProjectionOnto
      (ballBoundaryCoordinatePiece C j) := by
  have ha : 0 < (d : ℝ)⁻¹ := by positivity
  have hs : ballBoundaryCoordinatePiece C j ⊆ ballBoundaryCoordinatePatch C j :=
    Set.sdiff_subset
  unfold ballBoundaryCoordinatePatch at hs
  split at hs
  · exact
      (injOn_orthogonalProjectionOnto_positiveSupportingNormalPatch hclosed
        (ballBoundaryCoordinateDirection j.1) ha).mono hs
  · exact
      (injOn_orthogonalProjectionOnto_negativeSupportingNormalPatch hclosed
        (ballBoundaryCoordinateDirection j.1) ha).mono hs

theorem measurableSet_ballBoundaryCoordinateChartDomain {d : ℕ} (hd : 2 ≤ d)
    {C : Set (EuclideanSpace ℝ (Fin d))} (hcompact : IsCompact C)
    (j : Fin d × Bool) :
    MeasurableSet (ballBoundaryCoordinateChartDomain C j) := by
  unfold ballBoundaryCoordinateChartDomain
  exact (measurableSet_ballBoundaryCoordinatePiece hcompact j).image_of_continuousOn_injOn
    ((ℝ ∙ ballBoundaryCoordinateDirection j.1)ᗮ).orthogonalProjectionOnto.continuous.continuousOn
    (injOn_ballBoundaryCoordinateProjection hd hcompact.isClosed j)

theorem lipschitzOnWith_ballBoundaryCoordinateChart {d : ℕ} (hd : 2 ≤ d)
    {C : Set (EuclideanSpace ℝ (Fin d))} (hclosed : IsClosed C)
    (j : Fin d × Bool) :
    LipschitzOnWith (Real.toNNReal (1 + ((d : ℝ)⁻¹)⁻¹))
      (ballBoundaryCoordinateChart C j)
      (ballBoundaryCoordinateChartDomain C j) := by
  have ha : 0 < (d : ℝ)⁻¹ := by positivity
  have hs : ballBoundaryCoordinatePiece C j ⊆ ballBoundaryCoordinatePatch C j :=
    Set.sdiff_subset
  unfold ballBoundaryCoordinatePatch at hs
  unfold ballBoundaryCoordinateChart ballBoundaryCoordinateChartDomain
  split at hs
  · exact
      lipschitzOnWith_orthogonalProjectionPatchInverse_of_subset_positivePatch
        hclosed (norm_ballBoundaryCoordinateDirection j.1) ha hs
  · exact
      lipschitzOnWith_orthogonalProjectionPatchInverse_of_subset_negativePatch
        hclosed (norm_ballBoundaryCoordinateDirection j.1) ha hs

theorem lipschitzOnWith_ballBoundaryCoordinateProjectedChart {d : ℕ} (hd : 2 ≤ d)
    {C : Set (EuclideanSpace ℝ (Fin d))} (hclosed : IsClosed C)
    (j : Fin d × Bool) (θ : EuclideanSpace ℝ (Fin d)) :
    LipschitzOnWith (Real.toNNReal (1 + ((d : ℝ)⁻¹)⁻¹))
      (ballBoundaryCoordinateProjectedChart C j θ)
      (ballBoundaryCoordinateChartDomain C j) := by
  have hcomp := ((ℝ ∙ θ)ᗮ).lipschitzWith_orthogonalProjectionOnto.comp_lipschitzOnWith
    (lipschitzOnWith_ballBoundaryCoordinateChart hd hclosed j)
  change LipschitzOnWith (Real.toNNReal (1 + ((d : ℝ)⁻¹)⁻¹))
    (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto ∘ ballBoundaryCoordinateChart C j)
    (ballBoundaryCoordinateChartDomain C j)
  simpa only [one_mul] using hcomp

theorem image_ballBoundaryCoordinateChart {d : ℕ} (hd : 2 ≤ d)
    {C : Set (EuclideanSpace ℝ (Fin d))} (hclosed : IsClosed C)
    (j : Fin d × Bool) :
    ballBoundaryCoordinateChart C j '' ballBoundaryCoordinateChartDomain C j =
      ballBoundaryCoordinatePiece C j := by
  unfold ballBoundaryCoordinateChart ballBoundaryCoordinateChartDomain
  exact image_orthogonalProjectionPatchInverse
    (injOn_ballBoundaryCoordinateProjection hd hclosed j)

/-- Weighted area formula for one member of the disjoint finite boundary-chart cover. -/
theorem lintegral_ballBoundaryCoordinatePiece_eq_chart {d : ℕ} (hd : 2 ≤ d)
    {C : Set (EuclideanSpace ℝ (Fin d))} (hcompact : IsCompact C)
    (j : Fin d × Bool) (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hg : Measurable g) :
    (∫⁻ x in ballBoundaryCoordinatePiece C j, g x
        ∂Measure.euclideanHausdorffMeasure (d - 1)) =
      ∫⁻ z in ballBoundaryCoordinateChartDomain C j,
        ENNReal.ofReal
            (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
              (ballBoundaryCoordinateChartDomain C j) z).toLinearMap.normDet *
          g (ballBoundaryCoordinateChart C j z) ∂volume := by
  let θ := ballBoundaryCoordinateDirection j.1
  let S := ballBoundaryCoordinatePiece C j
  let T := ballBoundaryCoordinateChartDomain C j
  let φ := ballBoundaryCoordinateChart C j
  let P := ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto
  have harea := lintegral_image_eq_lintegral_normDet_fderivWithin_mul_of_comp_eq_id
    (U := (ℝ ∙ θ)ᗮ) (V := EuclideanSpace ℝ (Fin d))
    (measurableSet_ballBoundaryCoordinateChartDomain hd hcompact j)
    (lipschitzOnWith_ballBoundaryCoordinateChart hd hcompact.isClosed j)
    (injOn_orthogonalProjectionPatchInverse
      (θ := θ) (s := S))
    P
    (fun z hz ↦ (orthogonalProjectionOnto_patchInverse hz).symm)
    g hg
  rw [image_ballBoundaryCoordinateChart hd hcompact.isClosed j,
    finrank_orthogonal_span_unit (norm_ballBoundaryCoordinateDirection j.1)] at harea
  exact harea

/-- Almost every point of a disjoint coordinate chart has a unit tangent normal.  Its normal
components in every projection direction are represented without choosing a measurable normal:
they are exactly the corresponding projected derivative Jacobians divided by the chart surface
Jacobian. -/
theorem ae_exists_unit_normal_ballBoundaryCoordinateChart {d : ℕ} (hd : 2 ≤ d)
    {C : Set (EuclideanSpace ℝ (Fin d))} (hcompact : IsCompact C)
    (j : Fin d × Bool) :
    ∀ᵐ z ∂volume.restrict (ballBoundaryCoordinateChartDomain C j),
      ∃ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 ∧
        (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
          (ballBoundaryCoordinateChartDomain C j) z).toLinearMap.range =
            (ℝ ∙ u)ᗮ ∧
        |inner ℝ (ballBoundaryCoordinateDirection j.1) u| *
            (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
              (ballBoundaryCoordinateChartDomain C j) z).toLinearMap.normDet = 1 ∧
        ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ = 1 →
          (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto.toLinearMap.comp
              (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
                (ballBoundaryCoordinateChartDomain C j) z).toLinearMap).normDet =
            |inner ℝ θ u| *
              (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
                (ballBoundaryCoordinateChartDomain C j) z).toLinearMap.normDet := by
  let q := ballBoundaryCoordinateDirection j.1
  let S := ballBoundaryCoordinatePiece C j
  let T := ballBoundaryCoordinateChartDomain C j
  let φ := ballBoundaryCoordinateChart C j
  let P := ((ℝ ∙ q)ᗮ).orthogonalProjectionOnto
  have hcomp := ae_comp_fderivWithin_eq_id_of_lipschitzOnWith
    (measurableSet_ballBoundaryCoordinateChartDomain hd hcompact j)
    (lipschitzOnWith_ballBoundaryCoordinateChart hd hcompact.isClosed j)
    P (fun z hz ↦ (orthogonalProjectionOnto_patchInverse hz).symm)
  filter_upwards [hcomp] with z hz
  have hzlin :
      P.toLinearMap.comp
          (fderivWithin ℝ φ T z).toLinearMap = LinearMap.id := by
    exact congrArg ContinuousLinearMap.toLinearMap hz
  obtain ⟨u, hu, hrange, hcancel⟩ :=
    exists_unit_normal_normDet_mul_eq_one_of_projection_comp_eq_id
      hd (norm_ballBoundaryCoordinateDirection j.1)
      (fderivWithin ℝ φ T z).toLinearMap hzlin
  refine ⟨u, hu, hrange, hcancel, ?_⟩
  intro θ hθ
  exact normDet_orthogonalProjection_comp_eq_abs_inner_mul
    hd (norm_ballBoundaryCoordinateDirection j.1) hθ
    (fderivWithin ℝ φ T z).toLinearMap hu hrange

/-- The derivative of a projected boundary chart is almost everywhere the orthogonal projection
composed with the derivative of the original boundary chart. -/
theorem ae_fderivWithin_ballBoundaryCoordinateProjectedChart {d : ℕ} (hd : 2 ≤ d)
    {C : Set (EuclideanSpace ℝ (Fin d))} (hcompact : IsCompact C)
    (j : Fin d × Bool) (θ : EuclideanSpace ℝ (Fin d)) :
    ∀ᵐ z ∂volume.restrict (ballBoundaryCoordinateChartDomain C j),
      fderivWithin ℝ (ballBoundaryCoordinateProjectedChart C j θ)
          (ballBoundaryCoordinateChartDomain C j) z =
        ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto.comp
          (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
            (ballBoundaryCoordinateChartDomain C j) z) := by
  exact ae_fderivWithin_clm_comp_of_lipschitzOnWith
    (measurableSet_ballBoundaryCoordinateChartDomain hd hcompact j)
    (lipschitzOnWith_ballBoundaryCoordinateChart hd hcompact.isClosed j)
    ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto

/-- Equal-rank area-with-multiplicity for one projected boundary chart, with the Jacobian written
as the projection composed with the original chart derivative. -/
theorem exists_ballBoundaryCoordinateProjectedChart_multiplicity_partition {d : ℕ}
    (hd : 2 ≤ d) {C : Set (EuclideanSpace ℝ (Fin d))} (hcompact : IsCompact C)
    (j : Fin d × Bool) {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1)
    (w : (ℝ ∙ θ)ᗮ → ℝ≥0∞) (hw : Measurable w) :
    ∃ p : ℕ → Set ((ℝ ∙ ballBoundaryCoordinateDirection j.1)ᗮ),
      Pairwise (fun m n ↦ Disjoint (p m) (p n)) ∧
        (∀ n, MeasurableSet (p n)) ∧
        (∀ n, p n ⊆ ballBoundaryCoordinateChartDomain C j) ∧
        (∀ n, InjOn (ballBoundaryCoordinateProjectedChart C j θ) (p n)) ∧
        (∀ n, MeasurableSet (ballBoundaryCoordinateProjectedChart C j θ '' p n)) ∧
        (∀ᵐ z ∂volume.restrict (ballBoundaryCoordinateChartDomain C j),
          ENNReal.ofReal
              (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto.toLinearMap.comp
                (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
                  (ballBoundaryCoordinateChartDomain C j) z).toLinearMap).normDet ≠ 0 ↔
            z ∈ ⋃ n, p n) ∧
        (∫⁻ z in ballBoundaryCoordinateChartDomain C j,
            ENNReal.ofReal
                (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto.toLinearMap.comp
                  (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
                    (ballBoundaryCoordinateChartDomain C j) z).toLinearMap).normDet *
              w (ballBoundaryCoordinateProjectedChart C j θ z) ∂volume) =
          ∫⁻ y, ∑' n,
            (ballBoundaryCoordinateProjectedChart C j θ '' p n).indicator w y := by
  have hrank :
      Module.finrank ℝ ((ℝ ∙ ballBoundaryCoordinateDirection j.1)ᗮ) =
        Module.finrank ℝ ((ℝ ∙ θ)ᗮ) := by
    rw [finrank_orthogonal_span_unit (norm_ballBoundaryCoordinateDirection j.1),
      finrank_orthogonal_span_unit hθ]
  obtain ⟨p, hpdisj, hpmeas, hpsub, hpinj, hpimage, hpcover, hparea⟩ :=
    exists_equalRank_lipschitz_area_multiplicity_partition
      hrank
      (measurableSet_ballBoundaryCoordinateChartDomain hd hcompact j)
      (lipschitzOnWith_ballBoundaryCoordinateProjectedChart
        hd hcompact.isClosed j θ)
      w hw
  refine ⟨p, hpdisj, hpmeas, hpsub, hpinj, hpimage, ?_, ?_⟩
  · filter_upwards [hpcover,
      ae_fderivWithin_ballBoundaryCoordinateProjectedChart hd hcompact j θ] with z hz hderiv
    rw [hderiv] at hz
    exact hz
  · rw [← hparea]
    apply lintegral_congr_ae
    filter_upwards [ae_fderivWithin_ballBoundaryCoordinateProjectedChart
      hd hcompact j θ] with z hderiv
    have hderiv' := congrArg ContinuousLinearMap.toLinearMap hderiv
    change
      (fderivWithin ℝ (ballBoundaryCoordinateProjectedChart C j θ)
        (ballBoundaryCoordinateChartDomain C j) z).toLinearMap =
      ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto.toLinearMap.comp
        (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
          (ballBoundaryCoordinateChartDomain C j) z).toLinearMap at hderiv'
    rw [hderiv']

/-- A compact full-dimensional convex boundary is the finite disjoint sum of its weighted
coordinate-chart area formulas.  The Jacobian field replaces any measurable choice of unit
normal in the subsequent spherical averaging argument. -/
theorem lintegral_frontier_eq_tsum_ballBoundaryCoordinateCharts {d : ℕ} (hd : 2 ≤ d)
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : Convexity.IsConvexSet ℝ C)
    (hcompact : IsCompact C) (hinterior : (interior C).Nonempty)
    (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x in frontier C, g x ∂Measure.euclideanHausdorffMeasure (d - 1)) =
      ∑' j : Fin d × Bool,
        ∫⁻ z in ballBoundaryCoordinateChartDomain C j,
          ENNReal.ofReal
              (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
                (ballBoundaryCoordinateChartDomain C j) z).toLinearMap.normDet *
            g (ballBoundaryCoordinateChart C j z) ∂volume := by
  rw [← iUnion_ballBoundaryCoordinatePiece_eq_frontier hd hC hcompact hinterior]
  rw [lintegral_iUnion
    (fun j ↦ measurableSet_ballBoundaryCoordinatePiece hcompact j)
    (pairwise_disjoint_ballBoundaryCoordinatePiece C)]
  congr 1
  funext j
  exact lintegral_ballBoundaryCoordinatePiece_eq_chart hd hcompact j g hg

theorem injOn_orthogonalProjectionOnto_positiveSupportingNormalPoints {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hclosed : IsClosed C)
    (θ : EuclideanSpace ℝ (Fin d)) :
    InjOn ((ℝ ∙ θ)ᗮ.orthogonalProjectionOnto)
      (positiveSupportingNormalPoints C θ) := by
  intro x hx y hy hproj
  obtain ⟨kx, hkx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨ky, hky⟩ := Set.mem_iUnion.mp hy
  obtain ⟨ux, hxfrontier, _hux, hsupportx, hposx⟩ :=
    mem_positiveSupportingNormalPatch.mp hkx
  obtain ⟨uy, hyfrontier, _huy, hsupporty, hposy⟩ :=
    mem_positiveSupportingNormalPatch.mp hky
  have hxC : x ∈ C := hclosed.frontier_subset hxfrontier
  have hyC : y ∈ C := hclosed.frontier_subset hyfrontier
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
    (sub_mem_span_of_orthogonalProjectionOnto_eq hproj)
  have htx : t * inner ℝ θ ux ≤ 0 := by
    have h := hsupportx y hyC
    rw [← ht, real_inner_smul_left] at h
    exact h
  have hty : -t * inner ℝ θ uy ≤ 0 := by
    have h := hsupporty x hxC
    have hxy : x - y = (-t) • θ := by rw [← neg_sub, ← ht, neg_smul]
    rw [hxy, real_inner_smul_left] at h
    exact h
  have hthresholdx : 0 < (1 / (kx + 1 : ℝ)) := by positivity
  have hthresholdy : 0 < (1 / (ky + 1 : ℝ)) := by positivity
  have hinnerx : 0 < inner ℝ θ ux := hthresholdx.trans_le hposx
  have hinnery : 0 < inner ℝ θ uy := hthresholdy.trans_le hposy
  have ht_nonpos : t ≤ 0 := nonpos_of_mul_nonpos_left htx hinnerx
  have ht_nonneg : 0 ≤ t := by
    have : -t ≤ 0 := nonpos_of_mul_nonpos_left hty hinnery
    linarith
  have htzero : t = 0 := le_antisymm ht_nonpos ht_nonneg
  have hyx : y - x = 0 := by rw [← ht, htzero, zero_smul]
  exact (sub_eq_zero.mp hyx).symm

theorem injOn_orthogonalProjectionOnto_negativeSupportingNormalPoints {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hclosed : IsClosed C)
    (θ : EuclideanSpace ℝ (Fin d)) :
    InjOn ((ℝ ∙ θ)ᗮ.orthogonalProjectionOnto)
      (negativeSupportingNormalPoints C θ) := by
  intro x hx y hy hproj
  obtain ⟨kx, hkx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨ky, hky⟩ := Set.mem_iUnion.mp hy
  obtain ⟨ux, hxfrontier, _hux, hsupportx, hnegx⟩ :=
    mem_negativeSupportingNormalPatch.mp hkx
  obtain ⟨uy, hyfrontier, _huy, hsupporty, hnegy⟩ :=
    mem_negativeSupportingNormalPatch.mp hky
  have hxC : x ∈ C := hclosed.frontier_subset hxfrontier
  have hyC : y ∈ C := hclosed.frontier_subset hyfrontier
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
    (sub_mem_span_of_orthogonalProjectionOnto_eq hproj)
  have htx : t * inner ℝ θ ux ≤ 0 := by
    have h := hsupportx y hyC
    rw [← ht, real_inner_smul_left] at h
    exact h
  have hty : -t * inner ℝ θ uy ≤ 0 := by
    have h := hsupporty x hxC
    have hxy : x - y = (-t) • θ := by rw [← neg_sub, ← ht, neg_smul]
    rw [hxy, real_inner_smul_left] at h
    exact h
  have hthresholdx : 0 < (1 / (kx + 1 : ℝ)) := by positivity
  have hthresholdy : 0 < (1 / (ky + 1 : ℝ)) := by positivity
  have hinnerx : inner ℝ θ ux < 0 := hnegx.trans_lt (neg_neg_of_pos hthresholdx)
  have hinnery : inner ℝ θ uy < 0 := hnegy.trans_lt (neg_neg_of_pos hthresholdy)
  have ht_nonneg : 0 ≤ t := nonneg_of_mul_nonpos_left htx hinnerx
  have ht_nonpos : t ≤ 0 := by
    have : 0 ≤ -t := nonneg_of_mul_nonpos_left hty hinnery
    linarith
  have htzero : t = 0 := le_antisymm ht_nonpos ht_nonneg
  have hyx : y - x = 0 := by rw [← ht, htzero, zero_smul]
  exact (sub_eq_zero.mp hyx).symm

/-- The points of a convex boundary lying over one orthogonal-projection value. -/
def ballBoundaryProjectionFiber {d : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin d)))
    (θ : EuclideanSpace ℝ (Fin d)) (z : (ℝ ∙ θ)ᗮ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | x ∈ frontier C ∧ ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto x = z}

/-- Above the relative interior of a projected convex body, a line meets its boundary at at most
two points.  The two possible points belong to the globally injective positive and negative
supporting-normal sheets. -/
theorem encard_ballBoundaryProjectionFiber_le_two_of_mem_interior {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : Convexity.IsConvexSet ℝ C)
    (hcompact : IsCompact C) (hinterior : (interior C).Nonempty)
    (θ : EuclideanSpace ℝ (Fin d)) {z : (ℝ ∙ θ)ᗮ}
    (hz : z ∈ interior (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' C)) :
    (ballBoundaryProjectionFiber C θ z).encard ≤ 2 := by
  let F := ballBoundaryProjectionFiber C θ z
  let A := F ∩ positiveSupportingNormalPoints C θ
  let B := F ∩ negativeSupportingNormalPoints C θ
  have hsubset : F ⊆ A ∪ B := by
    intro x hx
    have hxproj : ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto x ∈
        interior (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' C) := by
      rw [hx.2]
      exact hz
    have htrans := mem_transverseSupportingNormalPoints_of_projection_mem_interior
      hC hcompact.isClosed hinterior θ hx.1 hxproj
    rw [transverseSupportingNormalPoints_eq_positive_union_negative] at htrans
    rcases htrans with hpos | hneg
    · exact Or.inl ⟨hx, hpos⟩
    · exact Or.inr ⟨hx, hneg⟩
  have hA : A.encard ≤ 1 := by
    rw [Set.encard_le_one_iff]
    intro x y hx hy
    apply injOn_orthogonalProjectionOnto_positiveSupportingNormalPoints
      hcompact.isClosed θ hx.2 hy.2
    exact hx.1.2.trans hy.1.2.symm
  have hB : B.encard ≤ 1 := by
    rw [Set.encard_le_one_iff]
    intro x y hx hy
    apply injOn_orthogonalProjectionOnto_negativeSupportingNormalPoints
      hcompact.isClosed θ hx.2 hy.2
    exact hx.1.2.trans hy.1.2.symm
  calc
    F.encard ≤ (A ∪ B).encard := Set.encard_le_encard hsubset
    _ ≤ A.encard + B.encard := Set.encard_union_le A B
    _ ≤ 1 + 1 := add_le_add hA hB
    _ = 2 := by norm_num

/-- The relative boundary of the orthogonal projection of a convex set is Haar-null. -/
theorem volume_frontier_image_orthogonalProjectionOnto_eq_zero {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : Convexity.IsConvexSet ℝ C)
    (θ : EuclideanSpace ℝ (Fin d)) :
    volume (frontier (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' C)) = 0 := by
  have hconv : Convex ℝ C := legacyConvex_of_isConvexSet_ballProjectionArea hC
  have himage : Convex ℝ
      (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' C) := by
    simpa using hconv.linear_image
      ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto.toLinearMap
  exact himage.addHaar_frontier volume

private theorem mem_interior_image_orthogonalProjectionOnto_of_mem_projection_frontier
    {d : ℕ} {C : Set (EuclideanSpace ℝ (Fin d))} (hcompact : IsCompact C)
    (θ : EuclideanSpace ℝ (Fin d)) {z : (ℝ ∙ θ)ᗮ}
    (hz : z ∈ ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' frontier C)
    (hznot : z ∉ frontier (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' C)) :
    z ∈ interior (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' C) := by
  obtain ⟨x, hxfrontier, rfl⟩ := hz
  have hxC : x ∈ C := hcompact.isClosed.frontier_subset hxfrontier
  have hmem : ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto x ∈
      ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' C := ⟨x, hxC, rfl⟩
  by_contra hnotint
  apply hznot
  rw [frontier, (hcompact.image
    ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto.continuous).isClosed.closure_eq]
  exact ⟨hmem, hnotint⟩

/-- For almost every projection value, a compact full-dimensional convex boundary has at most
two points in the corresponding projection fiber. -/
theorem ae_encard_ballBoundaryProjectionFiber_le_two {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : Convexity.IsConvexSet ℝ C)
    (hcompact : IsCompact C) (hinterior : (interior C).Nonempty)
    (θ : EuclideanSpace ℝ (Fin d)) :
    ∀ᵐ z : (ℝ ∙ θ)ᗮ ∂volume,
      (ballBoundaryProjectionFiber C θ z).encard ≤ 2 := by
  filter_upwards [compl_mem_ae_iff.mpr
    (volume_frontier_image_orthogonalProjectionOnto_eq_zero hC θ)] with z hz
  by_cases hfiber : (ballBoundaryProjectionFiber C θ z).Nonempty
  · obtain ⟨x, hx⟩ := hfiber
    have hzproj : z ∈ ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto '' frontier C :=
      ⟨x, hx.1, hx.2⟩
    exact encard_ballBoundaryProjectionFiber_le_two_of_mem_interior
      hC hcompact hinterior θ
        (mem_interior_image_orthogonalProjectionOnto_of_mem_projection_frontier
          hcompact θ hzproj hz)
  · rw [Set.not_nonempty_iff_eq_empty.mp hfiber, Set.encard_empty]
    norm_num

/-- Summing the projected Jacobians of all disjoint boundary charts costs at most two copies of
the target weight.  The factor two is the exact convex-line multiplicity; it is independent of
the number of coordinate charts. -/
theorem tsum_lintegral_ballBoundaryCoordinateProjectedChart_le_two_mul {d : ℕ}
    (hd : 2 ≤ d) {C : Set (EuclideanSpace ℝ (Fin d))}
    (hC : Convexity.IsConvexSet ℝ C) (hcompact : IsCompact C)
    (hinterior : (interior C).Nonempty)
    {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1)
    (w : (ℝ ∙ θ)ᗮ → ℝ≥0∞) (hw : Measurable w) :
    (∑' j : Fin d × Bool,
      ∫⁻ z in ballBoundaryCoordinateChartDomain C j,
        ENNReal.ofReal
            (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto.toLinearMap.comp
              (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
                (ballBoundaryCoordinateChartDomain C j) z).toLinearMap).normDet *
          w (ballBoundaryCoordinateProjectedChart C j θ z) ∂volume) ≤
      2 * ∫⁻ y, w y ∂volume := by
  classical
  choose p hpdisj hpmeas hpsub hpinj hpimage hpcover hparea using
    fun j : Fin d × Bool ↦
      exists_ballBoundaryCoordinateProjectedChart_multiplicity_partition
        hd hcompact j hθ w hw
  let I : (Fin d × Bool) × ℕ → Set ((ℝ ∙ θ)ᗮ) := fun k ↦
    ballBoundaryCoordinateProjectedChart C k.1 θ '' p k.1 k.2
  let A : (ℝ ∙ θ)ᗮ → Set ((Fin d × Bool) × ℕ) := fun y ↦
    {k | y ∈ I k}
  have hactive (y : (ℝ ∙ θ)ᗮ) :
      (A y).encard ≤ (ballBoundaryProjectionFiber C θ y).encard := by
    let z : (k : A y) →
        (ℝ ∙ ballBoundaryCoordinateDirection k.1.1.1)ᗮ := fun k ↦
      Classical.choose k.property
    have hzmem (k : A y) : z k ∈ p k.1.1 k.1.2 :=
      (Classical.choose_spec k.property).1
    have hzeq (k : A y) :
        ballBoundaryCoordinateProjectedChart C k.1.1 θ (z k) = y :=
      (Classical.choose_spec k.property).2
    have hzdomain (k : A y) :
        z k ∈ ballBoundaryCoordinateChartDomain C k.1.1 :=
      hpsub k.1.1 k.1.2 (hzmem k)
    have hxpiece (k : A y) :
        ballBoundaryCoordinateChart C k.1.1 (z k) ∈
          ballBoundaryCoordinatePiece C k.1.1 := by
      change orthogonalProjectionPatchInverse
        (ballBoundaryCoordinateDirection k.1.1.1)
        (ballBoundaryCoordinatePiece C k.1.1) (z k) ∈
          ballBoundaryCoordinatePiece C k.1.1
      exact orthogonalProjectionPatchInverse_mem (hzdomain k)
    let e : A y ↪ ballBoundaryProjectionFiber C θ y :=
      { toFun := fun k ↦
          ⟨ballBoundaryCoordinateChart C k.1.1 (z k),
            (ballBoundaryCoordinatePatch_subset_frontier C k.1.1)
              (Set.sdiff_subset (hxpiece k)),
            show ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto
                (ballBoundaryCoordinateChart C k.1.1 (z k)) = y by
              exact hzeq k⟩
        inj' := by
          intro k l hkl
          apply Subtype.ext
          rcases k with ⟨⟨j, n⟩, hk⟩
          rcases l with ⟨⟨j', n'⟩, hl⟩
          have hpoint : ballBoundaryCoordinateChart C j (z ⟨(j, n), hk⟩) =
              ballBoundaryCoordinateChart C j' (z ⟨(j', n'), hl⟩) :=
            congrArg
              (fun q : ballBoundaryProjectionFiber C θ y ↦
                (q : EuclideanSpace ℝ (Fin d))) hkl
          have hj : j = j' := by
            by_contra hjne
            have hdisj := pairwise_disjoint_ballBoundaryCoordinatePiece C hjne
            have hxother :
                ballBoundaryCoordinateChart C j (z ⟨(j, n), hk⟩) ∈
                  ballBoundaryCoordinatePiece C j' := by
              change ballBoundaryCoordinateChart C j (z ⟨(j, n), hk⟩) ∈
                ballBoundaryCoordinatePiece C j'
              exact hpoint.symm ▸ hxpiece ⟨(j', n'), hl⟩
            exact (Set.disjoint_left.mp hdisj)
              (hxpiece ⟨(j, n), hk⟩) hxother
          subst j'
          have hz : z ⟨(j, n), hk⟩ = z ⟨(j, n'), hl⟩ := by
            have hproj := congrArg
              ((ℝ ∙ ballBoundaryCoordinateDirection j.1)ᗮ).orthogonalProjectionOnto
              hpoint
            change
              ((ℝ ∙ ballBoundaryCoordinateDirection j.1)ᗮ).orthogonalProjectionOnto
                  (orthogonalProjectionPatchInverse
                    (ballBoundaryCoordinateDirection j.1)
                    (ballBoundaryCoordinatePiece C j) (z ⟨(j, n), hk⟩)) =
                ((ℝ ∙ ballBoundaryCoordinateDirection j.1)ᗮ).orthogonalProjectionOnto
                  (orthogonalProjectionPatchInverse
                    (ballBoundaryCoordinateDirection j.1)
                    (ballBoundaryCoordinatePiece C j) (z ⟨(j, n'), hl⟩)) at hproj
            rw [orthogonalProjectionOnto_patchInverse (hzdomain ⟨(j, n), hk⟩),
              orthogonalProjectionOnto_patchInverse (hzdomain ⟨(j, n'), hl⟩)] at hproj
            exact hproj
          have hn : n = n' := by
            by_contra hnne
            have hdisj := hpdisj j hnne
            have hzother : z ⟨(j, n), hk⟩ ∈ p j n' := by
              exact hz.symm ▸ hzmem ⟨(j, n'), hl⟩
            exact (Set.disjoint_left.mp hdisj) (hzmem ⟨(j, n), hk⟩) hzother
          subst n'
          rfl }
    exact e.encard_le
  have hsum (y : (ℝ ∙ θ)ᗮ) :
      (∑' j : Fin d × Bool, ∑' n : ℕ,
        (ballBoundaryCoordinateProjectedChart C j θ '' p j n).indicator w y) =
        (A y).encard * w y := by
    calc
      (∑' j : Fin d × Bool, ∑' n : ℕ,
          (ballBoundaryCoordinateProjectedChart C j θ '' p j n).indicator w y) =
          ∑' k : (Fin d × Bool) × ℕ,
            (ballBoundaryCoordinateProjectedChart C k.1 θ '' p k.1 k.2).indicator w y :=
        (ENNReal.tsum_prod' (f := fun k : (Fin d × Bool) × ℕ ↦
          (ballBoundaryCoordinateProjectedChart C k.1 θ '' p k.1 k.2).indicator w y)).symm
      _ = ∑' k : (Fin d × Bool) × ℕ,
          (A y).indicator (fun _ ↦ w y) k := by
        apply tsum_congr
        intro k
        by_cases hk : y ∈ I k
        · have hkI : y ∈
              ballBoundaryCoordinateProjectedChart C k.1 θ '' p k.1 k.2 := hk
          have hkA : k ∈ A y := hk
          rw [Set.indicator_of_mem hkI, Set.indicator_of_mem hkA]
        · have hkI : y ∉
              ballBoundaryCoordinateProjectedChart C k.1 θ '' p k.1 k.2 := hk
          have hkA : k ∉ A y := hk
          rw [Set.indicator_of_notMem hkI, Set.indicator_of_notMem hkA]
      _ = ∑' _k : A y, w y :=
        (tsum_subtype (A y) (fun _ ↦ w y)).symm
      _ = (A y).encard * w y := ENNReal.tsum_set_const (A y) (w y)
  have hpoint : ∀ᵐ y : (ℝ ∙ θ)ᗮ ∂volume,
      (∑' j : Fin d × Bool, ∑' n : ℕ,
        (ballBoundaryCoordinateProjectedChart C j θ '' p j n).indicator w y) ≤
        2 * w y := by
    filter_upwards [ae_encard_ballBoundaryProjectionFiber_le_two
      hC hcompact hinterior θ] with y hy
    rw [hsum]
    have hAy : (A y).encard ≤ 2 := (hactive y).trans hy
    have hcoe : ((A y).encard : ℝ≥0∞) ≤ 2 := by
      simpa using ENat.toENNReal_mono hAy
    exact mul_le_mul_right' hcoe (w y)
  have hmeas (j : Fin d × Bool) : Measurable fun y : (ℝ ∙ θ)ᗮ ↦
      ∑' n : ℕ,
        (ballBoundaryCoordinateProjectedChart C j θ '' p j n).indicator w y :=
    Measurable.ennreal_tsum fun n ↦ hw.indicator (hpimage j n)
  calc
    (∑' j : Fin d × Bool,
        ∫⁻ z in ballBoundaryCoordinateChartDomain C j,
          ENNReal.ofReal
              (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto.toLinearMap.comp
                (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
                  (ballBoundaryCoordinateChartDomain C j) z).toLinearMap).normDet *
            w (ballBoundaryCoordinateProjectedChart C j θ z) ∂volume) =
        ∑' j : Fin d × Bool, ∫⁻ y, ∑' n : ℕ,
          (ballBoundaryCoordinateProjectedChart C j θ '' p j n).indicator w y := by
      apply tsum_congr
      intro j
      exact hparea j
    _ = ∫⁻ y, ∑' j : Fin d × Bool, ∑' n : ℕ,
        (ballBoundaryCoordinateProjectedChart C j θ '' p j n).indicator w y :=
      (lintegral_tsum fun j ↦ (hmeas j).aemeasurable).symm
    _ ≤ ∫⁻ y, 2 * w y := lintegral_mono_ae hpoint
    _ = 2 * ∫⁻ y, w y := lintegral_const_mul 2 hw

/-- Fixed-direction projection bound with Ball's radial majorant and exact final constant. -/
theorem tsum_lintegral_ballBoundaryCoordinateProjectedChart_ballRadialMajorant_le {d : ℕ}
    (hd : 2 ≤ d) {C : Set (EuclideanSpace ℝ (Fin d))}
    (hC : Convexity.IsConvexSet ℝ C) (hcompact : IsCompact C)
    (hinterior : (interior C).Nonempty)
    {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1) :
    (∑' j : Fin d × Bool,
      ∫⁻ z in ballBoundaryCoordinateChartDomain C j,
        ENNReal.ofReal
            (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto.toLinearMap.comp
              (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
                (ballBoundaryCoordinateChartDomain C j) z).toLinearMap).normDet *
          ENNReal.ofReal
            (ballRadialMajorant d
              ‖ballBoundaryCoordinateProjectedChart C j θ z‖) ∂volume) ≤
      ENNReal.ofReal (4 * (d : ℝ) ^ (1 / 4 : ℝ)) := by
  let w : (ℝ ∙ θ)ᗮ → ℝ≥0∞ := fun z ↦
    ENNReal.ofReal (ballRadialMajorant d ‖z‖)
  have hw : Measurable w :=
    ENNReal.measurable_ofReal.comp
      ((continuous_ballRadialMajorant d).comp continuous_norm).measurable
  have hproj := tsum_lintegral_ballBoundaryCoordinateProjectedChart_le_two_mul
    hd hC hcompact hinterior hθ w hw
  have hmass := lintegral_ballRadialMajorant_norm_le_of_finrank
    (E := (ℝ ∙ θ)ᗮ) hd (finrank_orthogonal_span_unit hθ)
  calc
    (∑' j : Fin d × Bool,
        ∫⁻ z in ballBoundaryCoordinateChartDomain C j,
          ENNReal.ofReal
              (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto.toLinearMap.comp
                (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
                  (ballBoundaryCoordinateChartDomain C j) z).toLinearMap).normDet *
            ENNReal.ofReal
              (ballRadialMajorant d
                ‖ballBoundaryCoordinateProjectedChart C j θ z‖) ∂volume) ≤
        2 * ∫⁻ y : (ℝ ∙ θ)ᗮ,
          ENNReal.ofReal (ballRadialMajorant d ‖y‖) := hproj
    _ ≤ 2 * ENNReal.ofReal (2 * (d : ℝ) ^ (1 / 4 : ℝ)) :=
      mul_le_mul_left' hmass 2
    _ = ENNReal.ofReal (4 * (d : ℝ) ^ (1 / 4 : ℝ)) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

/-- The two strict-sign projection images consume at most twice the full radial mass. -/
theorem lintegral_projection_images_ballRadialMajorant_le {d : ℕ}
    (hd : 2 ≤ d) (C : Set (EuclideanSpace ℝ (Fin d)))
    {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1) :
    (∫⁻ z in ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto ''
          positiveSupportingNormalPoints C θ,
        ENNReal.ofReal (ballRadialMajorant d ‖z‖) ∂volume) +
      (∫⁻ z in ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto ''
          negativeSupportingNormalPoints C θ,
        ENNReal.ofReal (ballRadialMajorant d ‖z‖) ∂volume) ≤
      2 * ENNReal.ofReal (2 * (d : ℝ) ^ (1 / 4 : ℝ)) := by
  have hfull := lintegral_ballRadialMajorant_norm_le_of_finrank
    (E := (ℝ ∙ θ)ᗮ) hd (finrank_orthogonal_span_unit hθ)
  have hpos :
      (∫⁻ z in ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto ''
          positiveSupportingNormalPoints C θ,
        ENNReal.ofReal (ballRadialMajorant d ‖z‖) ∂volume) ≤
      ∫⁻ z : (ℝ ∙ θ)ᗮ, ENNReal.ofReal (ballRadialMajorant d ‖z‖) :=
    by
      simpa [Measure.restrict_univ] using
        lintegral_mono_set (μ := volume)
          (Set.subset_univ
            (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto ''
              positiveSupportingNormalPoints C θ))
  have hneg :
      (∫⁻ z in ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto ''
          negativeSupportingNormalPoints C θ,
        ENNReal.ofReal (ballRadialMajorant d ‖z‖) ∂volume) ≤
      ∫⁻ z : (ℝ ∙ θ)ᗮ, ENNReal.ofReal (ballRadialMajorant d ‖z‖) :=
    by
      simpa [Measure.restrict_univ] using
        lintegral_mono_set (μ := volume)
          (Set.subset_univ
            (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto ''
              negativeSupportingNormalPoints C θ))
  calc
    _ ≤ (∫⁻ z : (ℝ ∙ θ)ᗮ, ENNReal.ofReal (ballRadialMajorant d ‖z‖)) +
        ∫⁻ z : (ℝ ∙ θ)ᗮ, ENNReal.ofReal (ballRadialMajorant d ‖z‖) :=
      add_le_add hpos hneg
    _ ≤ ENNReal.ofReal (2 * (d : ℝ) ^ (1 / 4 : ℝ)) +
        ENNReal.ofReal (2 * (d : ℝ) ^ (1 / 4 : ℝ)) := add_le_add hfull hfull
    _ = 2 * ENNReal.ofReal (2 * (d : ℝ) ^ (1 / 4 : ℝ)) :=
      (two_mul _).symm

end ProbabilityTheory
