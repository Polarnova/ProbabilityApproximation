/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.ConvexGeometry.GaussianShell
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Ball's Gaussian perimeter theorem

This module develops the dimension-at-least-two boundary-content estimate in Keith Ball,
*The reverse isoperimetric problem for Gaussian measure* (1993), Theorem 4, printed pp. 415--419.

The first domain-completion theorem below treats every convex set with empty ambient interior.
Such a set lies in its proper affine span.  If that span has codimension at least two, normalized
`(d - 1)`-dimensional Euclidean Hausdorff measure vanishes on it.  In codimension one, an
isometric parametrization identifies the affine span with a hyperplane, whose exact Gaussian
surface content is a one-dimensional standard-Gaussian density and hence at most one.

For sets with nonempty interior, the remaining domain reductions are exact: increasing-ball
truncation reduces an arbitrary convex set to bounded ones, and closure preserves both the
frontier and its Gaussian boundary content while turning a bounded set into a compact convex
body.  Thus `standardGaussianBoundaryContent_le_of_convexBody_case_all` isolates precisely the
compact, full-dimensional source domain of Ball's projection argument.  The projection/area
argument itself is the remaining theorem core.
-/

open Set MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

local instance {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

local instance {d : ℕ} :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.ofModule

private lemma legacyConvex_of_isConvexSet {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : Convexity.IsConvexSet ℝ s) :
    Convex ℝ s := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  simpa [Convexity.convexCombPair_eq_sum] using
    hs.convexCombPair_mem hx hy ha hb hab

private lemma isConvexSet_of_legacyConvex {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : Convex ℝ s) :
    Convexity.IsConvexSet ℝ s := by
  apply Convexity.IsConvexSet.of_convexCombPair_mem
  intro a b ha hb hab x hx y hy
  simpa [Convexity.convexCombPair_eq_sum] using
    (convex_iff_add_mem.mp hs) hx hy ha hb hab

private lemma euclideanHausdorffMeasure_affineSubspace_eq_zero {d m : ℕ}
    (A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)))
    (hne : (A : Set (EuclideanSpace ℝ (Fin d))).Nonempty)
    (hrank : Module.finrank ℝ A.direction < m) :
    Measure.euclideanHausdorffMeasure m
        (A : Set (EuclideanSpace ℝ (Fin d))) = 0 := by
  let U : Set A := univ
  have himage : Subtype.val '' U = (A : Set (EuclideanSpace ℝ (Fin d))) := by
    ext x
    simp [U]
  rw [← himage, AffineSubspace.euclideanHausdorffMeasure_coe_image]
  obtain ⟨p, hp⟩ := hne
  let eEquiv : A ≃ A.direction :=
    { toFun := fun q ↦ ⟨q.1 - p, A.vsub_mem_direction q.2 hp⟩
      invFun := fun v ↦ ⟨v.1 + p, A.vadd_mem_of_mem_direction v.2 hp⟩
      left_inv := by
        intro q
        ext
        simp
      right_inv := by
        intro v
        ext
        simp }
  let e : A ≃ᵢ A.direction := IsometryEquiv.mk eEquiv (by
    rw [isometry_iff_dist_eq]
    intro q r
    change dist (q.1 - p) (r.1 - p) = dist q.1 r.1
    exact dist_sub_right q.1 r.1 p)
  have hzero : (Measure.euclideanHausdorffMeasure m : Measure A.direction) = 0 := by
    rw [Measure.euclideanHausdorffMeasure_def,
      Real.hausdorffMeasure_of_finrank_lt (Nat.cast_lt.mpr hrank), smul_zero]
  have hpres := e.measurePreserving_euclideanHausdorffMeasure m
  have hmap := hpres.map_eq
  rw [hzero] at hmap
  have hzeroA : (Measure.euclideanHausdorffMeasure m : Measure A) = 0 :=
    (Measure.map_eq_zero_iff hpres.measurable.aemeasurable).mp hmap
  rw [hzeroA]
  rfl

private lemma exists_unit_normal_affineSubspace {n : ℕ}
    (A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    (hne : (A : Set (EuclideanSpace ℝ (Fin (n + 1)))).Nonempty)
    (hrank : Module.finrank ℝ A.direction = n) :
    ∃ p u : EuclideanSpace ℝ (Fin (n + 1)), p ∈ A ∧ ‖u‖ = 1 ∧
      A = AffineSubspace.mk' p (ℝ ∙ u)ᗮ := by
  have htotal : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := by
    simp [finrank_euclideanSpace]
  have hperp : Module.finrank ℝ A.directionᗮ = 1 := by
    apply Submodule.finrank_add_finrank_orthogonal'
    rw [hrank, htotal]
  have hperp_ne : A.directionᗮ ≠ ⊥ := by
    intro hzero
    rw [hzero, finrank_bot] at hperp
    omega
  obtain ⟨v, hvperp, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp_ne
  let u := ‖v‖⁻¹ • v
  have hu0 : u ≠ 0 := by
    dsimp [u]
    exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hv0)) hv0
  have huperp : u ∈ A.directionᗮ := A.directionᗮ.smul_mem _ hvperp
  have hunorm : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  have hspan : A.directionᗮ = ℝ ∙ u :=
    eq_span_singleton_of_mem_of_finrank_eq_one hperp huperp hu0
  have hdir : A.direction = (ℝ ∙ u)ᗮ := by
    calc
      A.direction = A.directionᗮᗮ := (Submodule.orthogonal_orthogonal A.direction).symm
      _ = (ℝ ∙ u)ᗮ := by rw [hspan]
  obtain ⟨p, hp⟩ := hne
  refine ⟨p, u, hp, hunorm, ?_⟩
  rw [← hdir]
  exact (AffineSubspace.mk'_eq hp).symm

/-- A convex set with empty ambient interior has Gaussian boundary content at most one.  This
includes the empty set and every lower-dimensional, unbounded, or nonclosed convex set. -/
theorem standardGaussianBoundaryContent_le_one_of_interior_eq_empty {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : Convexity.IsConvexSet ℝ s)
    (hempty : interior s = ∅) :
    standardGaussianBoundaryContent s ≤ 1 := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp [standardGaussianBoundaryContent]
  let A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)) := affineSpan ℝ s
  have hconv : Convex ℝ s := legacyConvex_of_isConvexSet hs
  have hspan : A ≠ ⊤ := by
    intro htop
    have hinter : (interior s).Nonempty :=
      hconv.interior_nonempty_iff_affineSpan_eq_top.mpr htop
    simp [hempty] at hinter
  have hneA : (A : Set (EuclideanSpace ℝ (Fin d))).Nonempty :=
    hne.mono (subset_affineSpan ℝ s)
  have hdir_ne : A.direction ≠ ⊤ := by
    intro htop
    exact hspan ((AffineSubspace.direction_eq_top_iff_of_nonempty hneA).mp htop)
  have hdirlt : A.direction < ⊤ := lt_top_iff_ne_top.mpr hdir_ne
  have hranklt : Module.finrank ℝ A.direction < d := by
    have h := Submodule.finrank_lt_finrank_of_lt hdirlt
    simpa [finrank_euclideanSpace] using h
  have hfrontier : frontier s ⊆ (A : Set (EuclideanSpace ℝ (Fin d))) :=
    frontier_subset_closure.trans
      (closure_minimal (subset_affineSpan ℝ s) A.closed_of_finiteDimensional)
  unfold standardGaussianBoundaryContent
  calc
    (∫⁻ x in frontier s, ENNReal.ofReal (standardGaussianDensityReal x)
        ∂Measure.euclideanHausdorffMeasure (d - 1)) ≤
        ∫⁻ x in (A : Set (EuclideanSpace ℝ (Fin d))),
          ENNReal.ofReal (standardGaussianDensityReal x)
          ∂Measure.euclideanHausdorffMeasure (d - 1) :=
      lintegral_mono_set hfrontier
    _ ≤ 1 := by
      by_cases hrank : Module.finrank ℝ A.direction < d - 1
      · have hzero := euclideanHausdorffMeasure_affineSubspace_eq_zero A hneA hrank
        change (∫⁻ x, ENNReal.ofReal (standardGaussianDensityReal x)
          ∂(Measure.euclideanHausdorffMeasure (d - 1)).restrict
            (A : Set (EuclideanSpace ℝ (Fin d)))) ≤ 1
        rw [Measure.restrict_eq_zero.mpr hzero, lintegral_zero_measure]
        exact zero_le_one
      · have hd0 : d ≠ 0 := ((Nat.zero_le _).trans_lt hranklt).ne'
        obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
        have hrankeq : Module.finrank ℝ A.direction = n := by omega
        obtain ⟨p, u, _hp, hu, hA⟩ :=
          exists_unit_normal_affineSubspace A hneA hrankeq
        rw [hA]
        have hsurface := standardGaussianDensity_affineHyperplane_add_base p u hu 0
        simp only [zero_smul, zero_add] at hsurface
        have hpdf := standardGaussianDensity_affineHyperplane_le_one
          u hu (inner ℝ p u)
        rw [standardGaussianDensity_affineHyperplane u hu] at hpdf
        calc
          (∫⁻ x in (AffineSubspace.mk' p (ℝ ∙ u)ᗮ :
              Set (EuclideanSpace ℝ (Fin (n + 1)))),
              ENNReal.ofReal (standardGaussianDensityReal x)
              ∂Measure.euclideanHausdorffMeasure (n + 1 - 1)) =
              ENNReal.ofReal (gaussianPDFReal 0 1 (inner ℝ p u)) := by
            simpa only [Nat.add_sub_cancel] using hsurface
          _ ≤ 1 := hpdf

/-- It is enough to prove a uniform Gaussian boundary-content estimate for bounded convex sets
with nonempty interior.  Intersect an arbitrary convex set with an increasing sequence of balls
centred at an interior point.  Inside each ball the original frontier is contained in the
frontier of the bounded truncation, and the original frontier is the directed union of these
pieces. -/
theorem standardGaussianBoundaryContent_le_of_isBounded_case {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {K : ℝ≥0∞}
    (hs : Convexity.IsConvexSet ℝ s) (hne : (interior s).Nonempty)
    (hbounded : ∀ t : Set (EuclideanSpace ℝ (Fin d)),
      Convexity.IsConvexSet ℝ t → (interior t).Nonempty → Bornology.IsBounded t →
        standardGaussianBoundaryContent t ≤ K) :
    standardGaussianBoundaryContent s ≤ K := by
  obtain ⟨x, hx⟩ := hne
  let B : ℕ → Set (EuclideanSpace ℝ (Fin d)) := fun n ↦ Metric.ball x (n + 1)
  let T : ℕ → Set (EuclideanSpace ℝ (Fin d)) := fun n ↦ s ∩ B n
  let F : ℕ → Set (EuclideanSpace ℝ (Fin d)) := fun n ↦ frontier s ∩ B n
  have hBopen (n : ℕ) : IsOpen (B n) := Metric.isOpen_ball
  have hBconvex (n : ℕ) : Convexity.IsConvexSet ℝ (B n) :=
    isConvexSet_of_legacyConvex (convex_ball x (n + 1))
  have hTconvex (n : ℕ) : Convexity.IsConvexSet ℝ (T n) := hs.inter (hBconvex n)
  have hTinterior (n : ℕ) : (interior (T n)).Nonempty := by
    refine ⟨x, ?_⟩
    change x ∈ interior (s ∩ B n)
    rw [interior_inter, (hBopen n).interior_eq]
    exact ⟨hx, Metric.mem_ball_self (by positivity)⟩
  have hTbounded (n : ℕ) : Bornology.IsBounded (T n) :=
    Metric.isBounded_ball.subset inter_subset_right
  have hFsubset (n : ℕ) : F n ⊆ frontier (T n) := by
    have h := frontier_inter_open_inter (s := s) (hBopen n)
    intro y hy
    have hy' : y ∈ frontier (T n) ∩ B n := by
      change y ∈ frontier (s ∩ B n) ∩ B n
      rw [h]
      exact hy
    exact hy'.1
  have hFunion : (⋃ n, F n) = frontier s := by
    apply Set.Subset.antisymm
    · exact iUnion_subset fun n ↦ inter_subset_left
    · intro y hy
      obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (dist y x)
      exact mem_iUnion.2 ⟨n, hy, by
        simp only [B, Metric.mem_ball]
        linarith⟩
  have hFdirected : Directed (· ⊆ ·) F := by
    intro m n
    refine ⟨max m n, ?_, ?_⟩
    · rintro y ⟨hyfrontier, hyball⟩
      refine ⟨hyfrontier, ?_⟩
      simp only [B, Metric.mem_ball] at hyball ⊢
      exact hyball.trans_le (by
        exact_mod_cast Nat.add_le_add_right (Nat.le_max_left m n) 1)
    · rintro y ⟨hyfrontier, hyball⟩
      refine ⟨hyfrontier, ?_⟩
      simp only [B, Metric.mem_ball] at hyball ⊢
      exact hyball.trans_le (by
        exact_mod_cast Nat.add_le_add_right (Nat.le_max_right m n) 1)
  unfold standardGaussianBoundaryContent
  rw [← hFunion, setLIntegral_iUnion_of_directed _ hFdirected]
  apply iSup_le
  intro n
  calc
    (∫⁻ y in F n, ENNReal.ofReal (standardGaussianDensityReal y)
        ∂Measure.euclideanHausdorffMeasure (d - 1)) ≤
      ∫⁻ y in frontier (T n), ENNReal.ofReal (standardGaussianDensityReal y)
        ∂Measure.euclideanHausdorffMeasure (d - 1) :=
      lintegral_mono_set (hFsubset n)
    _ ≤ K := hbounded (T n) (hTconvex n) (hTinterior n) (hTbounded n)

/-- A full-dimensional convex set and its closure have the same frontier. -/
theorem frontier_closure_eq_of_isConvexSet {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) (hne : (interior s).Nonempty) :
    frontier (closure s) = frontier s := by
  have hconv : Convex ℝ s := legacyConvex_of_isConvexSet hs
  rw [← closure_sdiff_interior (closure s), ← closure_sdiff_interior s,
    closure_closure, hconv.interior_closure_eq_interior_of_nonempty_interior hne]

/-- Closing a full-dimensional convex set does not change its Gaussian boundary content. -/
theorem standardGaussianBoundaryContent_closure_eq {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) (hne : (interior s).Nonempty) :
    standardGaussianBoundaryContent (closure s) = standardGaussianBoundaryContent s := by
  unfold standardGaussianBoundaryContent
  rw [frontier_closure_eq_of_isConvexSet hs hne]

private lemma standardGaussianBoundaryContent_le_of_bounded_convexBody_case {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {K : ℝ≥0∞}
    (hs : Convexity.IsConvexSet ℝ s) (hne : (interior s).Nonempty)
    (hbounded : Bornology.IsBounded s)
    (hbody : ∀ t : Set (EuclideanSpace ℝ (Fin d)),
      Convexity.IsConvexSet ℝ t → (interior t).Nonempty → IsCompact t →
        standardGaussianBoundaryContent t ≤ K) :
    standardGaussianBoundaryContent s ≤ K := by
  have hconv : Convex ℝ s := legacyConvex_of_isConvexSet hs
  rw [← standardGaussianBoundaryContent_closure_eq hs hne]
  apply hbody (closure s)
  · exact isConvexSet_of_legacyConvex hconv.closure
  · rwa [hconv.interior_closure_eq_interior_of_nonempty_interior hne]
  · exact hbounded.isCompact_closure

/-- To prove a uniform Gaussian boundary-content estimate for all full-dimensional convex sets,
it is enough to prove it for convex bodies: compact convex sets with nonempty ambient interior.
The reduction first truncates an unbounded set by increasing balls and then takes the closure of
each bounded truncation. -/
theorem standardGaussianBoundaryContent_le_of_convexBody_case {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {K : ℝ≥0∞}
    (hs : Convexity.IsConvexSet ℝ s) (hne : (interior s).Nonempty)
    (hbody : ∀ t : Set (EuclideanSpace ℝ (Fin d)),
      Convexity.IsConvexSet ℝ t → (interior t).Nonempty → IsCompact t →
        standardGaussianBoundaryContent t ≤ K) :
    standardGaussianBoundaryContent s ≤ K := by
  apply standardGaussianBoundaryContent_le_of_isBounded_case hs hne
  intro t ht htinterior htbounded
  exact standardGaussianBoundaryContent_le_of_bounded_convexBody_case
    ht htinterior htbounded hbody

/-- Domain completion for Ball's theorem.  If a constant `K ≥ 1` bounds Gaussian boundary
content on convex bodies, then it bounds every convex set.  Empty-interior sets use the exact
lower-dimensional estimate; full-dimensional sets use truncation and closure. -/
theorem standardGaussianBoundaryContent_le_of_convexBody_case_all {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {K : ℝ≥0∞}
    (hs : Convexity.IsConvexSet ℝ s) (hK : 1 ≤ K)
    (hbody : ∀ t : Set (EuclideanSpace ℝ (Fin d)),
      Convexity.IsConvexSet ℝ t → (interior t).Nonempty → IsCompact t →
        standardGaussianBoundaryContent t ≤ K) :
    standardGaussianBoundaryContent s ≤ K := by
  by_cases hempty : interior s = ∅
  · exact (standardGaussianBoundaryContent_le_one_of_interior_eq_empty hs hempty).trans hK
  · exact standardGaussianBoundaryContent_le_of_convexBody_case hs
      (nonempty_iff_ne_empty.mpr hempty) hbody

end ProbabilityTheory
