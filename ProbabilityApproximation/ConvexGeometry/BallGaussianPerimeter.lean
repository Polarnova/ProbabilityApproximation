/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.ConvexGeometry.BallSphericalProjection
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

For sets with nonempty interior, increasing-ball truncation reduces an arbitrary convex set to
bounded ones, and closure preserves both the frontier and its Gaussian boundary content while
turning a bounded set into a compact convex body.  The compact full-dimensional case is then
closed by Ball's supporting-normal spherical projection and the radial Gaussian majorant.  The
final declaration covers every finite dimension and every convex set.
-/

open Set MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

local instance instConvexSpaceRealEuclideanSpaceFin_ballGaussianPerimeter {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

local instance instIsModuleConvexSpaceRealEuclideanSpaceFin_ballGaussianPerimeter {d : ℕ} :
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

/-- In dimensions at least two, the displayed Ball perimeter constant dominates the
lower-dimensional boundary-content fallback used in the domain-completion reduction. -/
lemma one_le_ofReal_ballGaussianPerimeterConstant {d : ℕ} (hd : 2 ≤ d) :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal (ballGaussianPerimeterConstant d) := by
  have hdR : (1 : ℝ) ≤ d := by
    exact_mod_cast (show 1 ≤ d by omega)
  have hpow : (1 : ℝ) ≤ (d : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow hdR (by norm_num)
  have hK : (1 : ℝ) ≤ ballGaussianPerimeterConstant d := by
    unfold ballGaussianPerimeterConstant
    nlinarith
  simpa using ENNReal.ofReal_le_ofReal hK

/-- Ball's Gaussian boundary-content theorem reduces, without changing the public constant or
the domain, to the compact full-dimensional convex-body projection theorem in dimension at least
two. -/
theorem standardGaussianBoundaryContent_le_ballGaussianPerimeterConstant_of_convexBody_case
    {d : ℕ} (hd : 2 ≤ d) {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s)
    (hbody : ∀ t : Set (EuclideanSpace ℝ (Fin d)),
      Convexity.IsConvexSet ℝ t → (interior t).Nonempty → IsCompact t →
        standardGaussianBoundaryContent t ≤
          ENNReal.ofReal (ballGaussianPerimeterConstant d)) :
    standardGaussianBoundaryContent s ≤
      ENNReal.ofReal (ballGaussianPerimeterConstant d) :=
  standardGaussianBoundaryContent_le_of_convexBody_case_all hs
    (one_le_ofReal_ballGaussianPerimeterConstant hd) hbody

private def ballAmbientHyperplaneProjection {d : ℕ}
    (θ : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) -
    InnerProductSpace.rankOne ℝ θ θ

private lemma norm_rankOne_self_sub_rankOne_self_le {d : ℕ}
    (θ φ : EuclideanSpace ℝ (Fin d)) :
    ‖InnerProductSpace.rankOne ℝ θ θ - InnerProductSpace.rankOne ℝ φ φ‖ ≤
      ‖θ - φ‖ * (‖θ‖ + ‖φ‖) := by
  have hdecomp :
      InnerProductSpace.rankOne ℝ θ θ - InnerProductSpace.rankOne ℝ φ φ =
        InnerProductSpace.rankOne ℝ (θ - φ) θ +
          InnerProductSpace.rankOne ℝ φ (θ - φ) := by
    ext x
    simp [InnerProductSpace.rankOne_apply]
  rw [hdecomp]
  calc
    ‖InnerProductSpace.rankOne ℝ (θ - φ) θ +
        InnerProductSpace.rankOne ℝ φ (θ - φ)‖ ≤
      ‖InnerProductSpace.rankOne ℝ (θ - φ) θ‖ +
        ‖InnerProductSpace.rankOne ℝ φ (θ - φ)‖ := norm_add_le _ _
    _ = ‖θ - φ‖ * ‖θ‖ + ‖φ‖ * ‖θ - φ‖ := by
      rw [InnerProductSpace.norm_rankOne, InnerProductSpace.norm_rankOne]
    _ = ‖θ - φ‖ * (‖θ‖ + ‖φ‖) := by ring

private lemma continuous_ballAmbientHyperplaneProjection {d : ℕ} :
    Continuous (ballAmbientHyperplaneProjection (d := d)) := by
  rw [continuous_iff_continuousAt]
  intro φ
  rw [Metric.continuousAt_iff]
  intro ε hε
  let M : ℝ := 2 * ‖φ‖ + 1
  have hM : 0 < M := by dsimp only [M]; positivity
  refine ⟨min 1 (ε / M), lt_min zero_lt_one (div_pos hε hM), ?_⟩
  intro θ hθ
  have hdistOne : dist θ φ < 1 := hθ.trans_le (min_le_left _ _)
  have hnormθ : ‖θ‖ < ‖φ‖ + 1 := by
    calc
      ‖θ‖ ≤ ‖θ - φ‖ + ‖φ‖ := by
        have := norm_add_le (θ - φ) φ
        simpa using this
      _ < 1 + ‖φ‖ := by
        rw [dist_eq_norm] at hdistOne
        linarith
      _ = ‖φ‖ + 1 := by ring
  have hdistDiv : dist θ φ < ε / M := hθ.trans_le (min_le_right _ _)
  have hrank := norm_rankOne_self_sub_rankOne_self_le θ φ
  have hfactor : ‖θ‖ + ‖φ‖ < M := by
    dsimp only [M]
    linarith
  rw [dist_eq_norm]
  unfold ballAmbientHyperplaneProjection
  rw [sub_sub_sub_cancel_left]
  calc
    ‖InnerProductSpace.rankOne ℝ φ φ - InnerProductSpace.rankOne ℝ θ θ‖ =
        ‖InnerProductSpace.rankOne ℝ θ θ - InnerProductSpace.rankOne ℝ φ φ‖ :=
      norm_sub_rev _ _
    _ ≤ ‖θ - φ‖ * (‖θ‖ + ‖φ‖) := hrank
    _ ≤ ‖θ - φ‖ * M :=
      mul_le_mul_of_nonneg_left hfactor.le (norm_nonneg _)
    _ < (ε / M) * M := by
      rw [← dist_eq_norm]
      exact mul_lt_mul_of_pos_right hdistDiv hM
    _ = ε := by field_simp

private lemma ballAmbientHyperplaneProjection_apply {d : ℕ}
    {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1)
    (x : EuclideanSpace ℝ (Fin d)) :
    ballAmbientHyperplaneProjection θ x =
      (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto x : EuclideanSpace ℝ (Fin d)) := by
  unfold ballAmbientHyperplaneProjection
  rw [Submodule.orthogonalProjectionOnto_orthogonal]
  simp [Submodule.starProjection_unit_singleton ℝ hθ,
    InnerProductSpace.rankOne_apply]

private lemma normDet_ballAmbientHyperplaneProjection_comp {d : ℕ}
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U]
    {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1)
    (L : U →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :
    ((ballAmbientHyperplaneProjection θ).toLinearMap.comp L).normDet =
      (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto.toLinearMap.comp L).normDet := by
  let B := (ballAmbientHyperplaneProjection θ).toLinearMap.comp L
  have hB (x : U) : B x ∈ (ℝ ∙ θ)ᗮ := by
    change ballAmbientHyperplaneProjection θ (L x) ∈ (ℝ ∙ θ)ᗮ
    rw [ballAmbientHyperplaneProjection_apply hθ]
    exact Subtype.coe_prop _
  have hmaps : B.codRestrict ((ℝ ∙ θ)ᗮ) hB =
      ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto.toLinearMap.comp L := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact ballAmbientHyperplaneProjection_apply hθ (L x)
  rw [← LinearMap.normDet_codRestrict hB, hmaps]

private theorem aemeasurable_ballBoundaryCoordinateProjectedChart_integrand
    {d : ℕ} (hd : 2 ≤ d)
    {C : Set (EuclideanSpace ℝ (Fin d))} (hcompact : IsCompact C)
    (j : Fin d × Bool) :
    AEMeasurable
      (Function.uncurry fun
        z : (ℝ ∙ ballBoundaryCoordinateDirection j.1)ᗮ ↦
        fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ↦
          ENNReal.ofReal
              (((ℝ ∙ (θ : EuclideanSpace ℝ (Fin d)))ᗮ).orthogonalProjectionOnto.toLinearMap.comp
                (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
                  (ballBoundaryCoordinateChartDomain C j) z).toLinearMap).normDet *
            ENNReal.ofReal
              (ballRadialMajorant d
                ‖ballBoundaryCoordinateProjectedChart C j θ z‖))
      ((volume.restrict (ballBoundaryCoordinateChartDomain C j)).prod
        (standardSphereHausdorffMeasure d)) := by
  let U := (ℝ ∙ ballBoundaryCoordinateDirection j.1)ᗮ
  let E := EuclideanSpace ℝ (Fin d)
  let T : Set U := ballBoundaryCoordinateChartDomain C j
  let φ : U → E := ballBoundaryCoordinateChart C j
  let D : U → U →L[ℝ] E := fun z ↦ fderivWithin ℝ φ T z
  let μ : Measure U := volume.restrict T
  let ν : Measure (Metric.sphere (0 : E) 1) := standardSphereHausdorffMeasure d
  have hT : MeasurableSet T :=
    measurableSet_ballBoundaryCoordinateChartDomain hd hcompact j
  have hφlip := lipschitzOnWith_ballBoundaryCoordinateChart hd hcompact.isClosed j
  have hDinj : ∀ᵐ z ∂μ, Function.Injective (D z) := by
    filter_upwards [ae_exists_unit_normal_ballBoundaryCoordinateChart hd hcompact j] with z hz
    rcases hz with ⟨u, hu, hrange, hcancel, hprojection⟩
    apply ((D z).toLinearMap.normDet_ne_zero_tfae.out 0 4).mp
    intro hzero
    rw [hzero, mul_zero] at hcancel
    norm_num at hcancel
  obtain ⟨t, htT, htmeas, hteq, htdiff, _htinj⟩ :=
    exists_measurable_fullMeasure_differentiableWithinAt_injective
      hT hφlip hDinj
  have hD_t : AEMeasurable D (volume.restrict t) := by
    apply aemeasurable_fderivWithin_general htmeas
    intro z hz
    exact (htdiff z hz).hasFDerivWithinAt.mono htT
  have hD : AEMeasurable D μ := by
    change AEMeasurable D (volume.restrict T)
    rw [← Measure.restrict_congr_set hteq]
    exact hD_t
  have hφ : AEMeasurable φ μ :=
    hφlip.continuousOn.aemeasurable hT
  have hDprod : AEMeasurable (fun p : U × Metric.sphere (0 : E) 1 ↦ D p.1)
      (μ.prod ν) :=
    hD.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hφprod : AEMeasurable (fun p : U × Metric.sphere (0 : E) 1 ↦ φ p.1)
      (μ.prod ν) :=
    hφ.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hQ : Measurable (fun p : U × Metric.sphere (0 : E) 1 ↦
      ballAmbientHyperplaneProjection (p.2 : E)) :=
    (continuous_ballAmbientHyperplaneProjection.comp
      (continuous_subtype_val.comp continuous_snd)).measurable
  have hcompContinuous : Continuous fun
      p : (E →L[ℝ] E) × (U →L[ℝ] E) ↦ p.1.comp p.2 :=
    continuous_fst.clm_comp continuous_snd
  have hQD : AEMeasurable (fun p : U × Metric.sphere (0 : E) 1 ↦
      (ballAmbientHyperplaneProjection (p.2 : E)).comp (D p.1))
      (μ.prod ν) :=
    hcompContinuous.measurable.comp_aemeasurable
      (hQ.aemeasurable.prodMk hDprod)
  have happlyContinuous : Continuous fun p : (E →L[ℝ] E) × E ↦ p.1 p.2 :=
    continuous_fst.clm_apply continuous_snd
  have hQφ : AEMeasurable (fun p : U × Metric.sphere (0 : E) 1 ↦
      ballAmbientHyperplaneProjection (p.2 : E) (φ p.1))
      (μ.prod ν) :=
    happlyContinuous.measurable.comp_aemeasurable
      (hQ.aemeasurable.prodMk hφprod)
  have hJ : AEMeasurable (fun p : U × Metric.sphere (0 : E) 1 ↦
      ENNReal.ofReal
        ((ballAmbientHyperplaneProjection (p.2 : E)).comp
          (D p.1)).toLinearMap.normDet) (μ.prod ν) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (continuous_normDet.measurable.comp_aemeasurable hQD)
  have hM : AEMeasurable (fun p : U × Metric.sphere (0 : E) 1 ↦
      ENNReal.ofReal
        (ballRadialMajorant d
          ‖ballAmbientHyperplaneProjection (p.2 : E) (φ p.1)‖))
      (μ.prod ν) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((continuous_ballRadialMajorant d).comp continuous_norm).measurable.comp_aemeasurable hQφ)
  have hambient := hJ.mul hM
  apply hambient.congr
  filter_upwards with p
  rcases p with ⟨z, θ⟩
  have hθ : ‖(θ : E)‖ = 1 := by
    have hθ := θ.property
    change dist (θ : E) 0 = 1 at hθ
    rw [dist_zero_right] at hθ
    exact hθ
  change
    ENNReal.ofReal
        ((ballAmbientHyperplaneProjection (θ : E)).toLinearMap.comp
          (D z).toLinearMap).normDet *
      ENNReal.ofReal
        (ballRadialMajorant d
          ‖ballAmbientHyperplaneProjection (θ : E) (φ z)‖) = _
  rw [normDet_ballAmbientHyperplaneProjection_comp hθ]
  rw [ballAmbientHyperplaneProjection_apply hθ]
  rfl

private theorem lintegral_lintegral_ballBoundaryCoordinateProjectedChart_swap
    {d : ℕ} (hd : 2 ≤ d)
    {C : Set (EuclideanSpace ℝ (Fin d))} (hcompact : IsCompact C)
    (j : Fin d × Bool) :
    (∫⁻ z in ballBoundaryCoordinateChartDomain C j,
      ∫⁻ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        ENNReal.ofReal
            (((ℝ ∙ (θ : EuclideanSpace ℝ (Fin d)))ᗮ).orthogonalProjectionOnto.toLinearMap.comp
              (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
                (ballBoundaryCoordinateChartDomain C j) z).toLinearMap).normDet *
          ENNReal.ofReal
            (ballRadialMajorant d
              ‖ballBoundaryCoordinateProjectedChart C j θ z‖)
        ∂standardSphereHausdorffMeasure d ∂volume) =
      ∫⁻ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        ∫⁻ z in ballBoundaryCoordinateChartDomain C j,
          ENNReal.ofReal
              (((ℝ ∙ (θ : EuclideanSpace ℝ (Fin d)))ᗮ).orthogonalProjectionOnto.toLinearMap.comp
                (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
                  (ballBoundaryCoordinateChartDomain C j) z).toLinearMap).normDet *
            ENNReal.ofReal
              (ballRadialMajorant d
                ‖ballBoundaryCoordinateProjectedChart C j θ z‖)
          ∂volume ∂standardSphereHausdorffMeasure d := by
  exact lintegral_lintegral_swap
    (aemeasurable_ballBoundaryCoordinateProjectedChart_integrand hd hcompact j)

private theorem lintegral_ballBoundaryCoordinateChart_gaussianDensity_le_sphereProjection
    {d : ℕ} (hd : 2 ≤ d)
    {C : Set (EuclideanSpace ℝ (Fin d))} (hcompact : IsCompact C)
    (j : Fin d × Bool) :
    (∫⁻ z in ballBoundaryCoordinateChartDomain C j,
        ENNReal.ofReal
            (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
              (ballBoundaryCoordinateChartDomain C j) z).toLinearMap.normDet *
          ENNReal.ofReal
            (standardGaussianDensityReal (ballBoundaryCoordinateChart C j z)) ∂volume) ≤
      (standardSphereHausdorffMeasure d univ)⁻¹ *
        ∫⁻ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
          ∫⁻ z in ballBoundaryCoordinateChartDomain C j,
            ENNReal.ofReal
                (((ℝ ∙ (θ : EuclideanSpace ℝ (Fin d)))ᗮ).orthogonalProjectionOnto.toLinearMap.comp
                  (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
                    (ballBoundaryCoordinateChartDomain C j) z).toLinearMap).normDet *
              ENNReal.ofReal
                (ballRadialMajorant d
                  ‖ballBoundaryCoordinateProjectedChart C j θ z‖)
            ∂volume ∂standardSphereHausdorffMeasure d := by
  let T := ballBoundaryCoordinateChartDomain C j
  let φ := ballBoundaryCoordinateChart C j
  let F := fun
      z : (ℝ ∙ ballBoundaryCoordinateDirection j.1)ᗮ ↦
      fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ↦
        ENNReal.ofReal
            (((ℝ ∙ (θ : EuclideanSpace ℝ (Fin d)))ᗮ).orthogonalProjectionOnto.toLinearMap.comp
              (fderivWithin ℝ φ T z).toLinearMap).normDet *
          ENNReal.ofReal
            (ballRadialMajorant d
              ‖ballBoundaryCoordinateProjectedChart C j θ z‖)
  have hF : AEMeasurable (Function.uncurry F)
      ((volume.restrict T).prod (standardSphereHausdorffMeasure d)) := by
    simpa only [T, φ, F] using
      aemeasurable_ballBoundaryCoordinateProjectedChart_integrand hd hcompact j
  have hFinner : AEMeasurable
      (fun z ↦ ∫⁻ θ, F z θ ∂standardSphereHausdorffMeasure d)
      (volume.restrict T) := hF.lintegral_prod_right
  have hpoint : ∀ᵐ z ∂volume.restrict T,
      ENNReal.ofReal
          (fderivWithin ℝ φ T z).toLinearMap.normDet *
        ENNReal.ofReal (standardGaussianDensityReal (φ z)) ≤
      (standardSphereHausdorffMeasure d univ)⁻¹ *
        ∫⁻ θ, F z θ ∂standardSphereHausdorffMeasure d := by
    filter_upwards [ae_exists_unit_normal_ballBoundaryCoordinateChart hd hcompact j] with z hz
    rcases hz with ⟨u, hu, hrange, hcancel, hprojection⟩
    let J : ℝ := (fderivWithin ℝ φ T z).toLinearMap.normDet
    let N : EuclideanSpace ℝ (Fin d) := J • u
    have hJ : 0 ≤ J := LinearMap.normDet_nonneg _
    have hnormN : ‖N‖ = J := by
      dsimp only [N]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hJ, hu, mul_one]
    have hleft :
        ENNReal.ofReal J * ENNReal.ofReal (standardGaussianDensityReal (φ z)) =
          ENNReal.ofReal (standardGaussianDensityReal (φ z) * ‖N‖) := by
      rw [hnormN, ENNReal.ofReal_mul (standardGaussianDensityReal_nonneg (φ z))]
      ac_rfl
    have hright :
        (∫⁻ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
          ENNReal.ofReal
              (ballRadialMajorant d
                ‖((ℝ ∙ (θ : EuclideanSpace ℝ (Fin d)))ᗮ).orthogonalProjectionOnto (φ z)‖) *
            ENNReal.ofReal |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) N|
          ∂standardSphereHausdorffMeasure d) =
        ∫⁻ θ, F z θ ∂standardSphereHausdorffMeasure d := by
      apply lintegral_congr
      intro θ
      have hθ : ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := by
        have hθ := θ.property
        change dist (θ : EuclideanSpace ℝ (Fin d)) 0 = 1 at hθ
        rw [dist_zero_right] at hθ
        exact hθ
      have hinnerN :
          |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) N| =
            |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u| * J := by
        dsimp only [N]
        rw [real_inner_smul_right, abs_mul, abs_of_nonneg hJ]
        ring
      have hproj := hprojection (θ : EuclideanSpace ℝ (Fin d)) hθ
      dsimp only [F]
      rw [hinnerN, ← hproj]
      unfold ballBoundaryCoordinateProjectedChart
      rw [mul_comm]
    rw [hleft]
    have hball :=
      standardGaussianDensityReal_mul_norm_le_sphere_ballRadialMajorant_absInner
        hd (φ z) N
    rw [hright] at hball
    exact hball
  calc
    (∫⁻ z in T,
        ENNReal.ofReal (fderivWithin ℝ φ T z).toLinearMap.normDet *
          ENNReal.ofReal (standardGaussianDensityReal (φ z)) ∂volume) ≤
        ∫⁻ z in T,
          (standardSphereHausdorffMeasure d univ)⁻¹ *
            (∫⁻ θ, F z θ ∂standardSphereHausdorffMeasure d) ∂volume :=
      lintegral_mono_ae hpoint
    _ = (standardSphereHausdorffMeasure d univ)⁻¹ *
        ∫⁻ z in T, ∫⁻ θ, F z θ ∂standardSphereHausdorffMeasure d ∂volume := by
      rw [lintegral_const_mul'' _ hFinner]
    _ = (standardSphereHausdorffMeasure d univ)⁻¹ *
        ∫⁻ θ, ∫⁻ z in T, F z θ ∂volume
          ∂standardSphereHausdorffMeasure d := by
      rw [lintegral_lintegral_ballBoundaryCoordinateProjectedChart_swap
        hd hcompact j]
    _ = _ := by rfl

/-- Ball's Gaussian perimeter estimate for the compact full-dimensional source domain of the
projection argument. -/
theorem standardGaussianBoundaryContent_le_ballGaussianPerimeterConstant_compactBody
    {d : ℕ} (hd : 2 ≤ d) {C : Set (EuclideanSpace ℝ (Fin d))}
    (hC : Convexity.IsConvexSet ℝ C) (hcompact : IsCompact C)
    (hinterior : (interior C).Nonempty) :
    standardGaussianBoundaryContent C ≤
      ENNReal.ofReal (ballGaussianPerimeterConstant d) := by
  let S : ℝ≥0∞ := standardSphereHausdorffMeasure d univ
  let K : ℝ≥0∞ := ENNReal.ofReal (ballGaussianPerimeterConstant d)
  let A : (j : Fin d × Bool) →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ≥0∞ := fun j θ ↦
    ∫⁻ z in ballBoundaryCoordinateChartDomain C j,
      ENNReal.ofReal
          (((ℝ ∙ (θ : EuclideanSpace ℝ (Fin d)))ᗮ).orthogonalProjectionOnto.toLinearMap.comp
            (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
              (ballBoundaryCoordinateChartDomain C j) z).toLinearMap).normDet *
        ENNReal.ofReal
          (ballRadialMajorant d
            ‖ballBoundaryCoordinateProjectedChart C j θ z‖) ∂volume
  have hA (j : Fin d × Bool) : AEMeasurable (A j)
      (standardSphereHausdorffMeasure d) := by
    exact (aemeasurable_ballBoundaryCoordinateProjectedChart_integrand
      hd hcompact j).lintegral_prod_left
  have hchart (j : Fin d × Bool) :
      (∫⁻ z in ballBoundaryCoordinateChartDomain C j,
          ENNReal.ofReal
              (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
                (ballBoundaryCoordinateChartDomain C j) z).toLinearMap.normDet *
            ENNReal.ofReal
              (standardGaussianDensityReal (ballBoundaryCoordinateChart C j z)) ∂volume) ≤
        S⁻¹ * ∫⁻ θ, A j θ ∂standardSphereHausdorffMeasure d := by
    simpa only [S, A] using
      lintegral_ballBoundaryCoordinateChart_gaussianDensity_le_sphereProjection
        hd hcompact j
  have hfixed (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
      (∑' j : Fin d × Bool, A j θ) ≤ K := by
    have hθ : ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := by
      have hθ := θ.property
      change dist (θ : EuclideanSpace ℝ (Fin d)) 0 = 1 at hθ
      rw [dist_zero_right] at hθ
      exact hθ
    simpa only [A, K, ballGaussianPerimeterConstant] using
      tsum_lintegral_ballBoundaryCoordinateProjectedChart_ballRadialMajorant_le
        hd hC hcompact hinterior hθ
  have hSne : S ≠ 0 := by
    exact standardSphereHausdorffMeasure_apply_univ_ne_zero d (by omega)
  have hStop : S ≠ ∞ := by
    exact measure_ne_top (standardSphereHausdorffMeasure d) univ
  unfold standardGaussianBoundaryContent
  rw [lintegral_frontier_eq_tsum_ballBoundaryCoordinateCharts
    hd hC hcompact hinterior
      (fun x ↦ ENNReal.ofReal (standardGaussianDensityReal x))
      measurable_standardGaussianDensityReal.ennreal_ofReal]
  change (∑' j : Fin d × Bool,
      ∫⁻ z in ballBoundaryCoordinateChartDomain C j,
        ENNReal.ofReal
            (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
              (ballBoundaryCoordinateChartDomain C j) z).toLinearMap.normDet *
          ENNReal.ofReal
            (standardGaussianDensityReal (ballBoundaryCoordinateChart C j z)) ∂volume) ≤ K
  calc
    (∑' j : Fin d × Bool,
        ∫⁻ z in ballBoundaryCoordinateChartDomain C j,
          ENNReal.ofReal
              (fderivWithin ℝ (ballBoundaryCoordinateChart C j)
                (ballBoundaryCoordinateChartDomain C j) z).toLinearMap.normDet *
            ENNReal.ofReal
              (standardGaussianDensityReal (ballBoundaryCoordinateChart C j z)) ∂volume) ≤
        ∑' j : Fin d × Bool,
          S⁻¹ * ∫⁻ θ, A j θ ∂standardSphereHausdorffMeasure d := by
      gcongr with j
      exact hchart j
    _ = S⁻¹ * ∑' j : Fin d × Bool,
        ∫⁻ θ, A j θ ∂standardSphereHausdorffMeasure d :=
      ENNReal.tsum_mul_left
    _ = S⁻¹ * ∫⁻ θ, ∑' j : Fin d × Bool, A j θ
        ∂standardSphereHausdorffMeasure d := by
      rw [lintegral_tsum fun j ↦ hA j]
    _ ≤ S⁻¹ * ∫⁻ _θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1, K
        ∂standardSphereHausdorffMeasure d := by
      gcongr with θ
      exact hfixed θ
    _ = S⁻¹ * (K * S) := by
      rw [lintegral_const]
    _ = K := by
      rw [show S⁻¹ * (K * S) = (S⁻¹ * S) * K by ac_rfl,
        ENNReal.inv_mul_cancel hSne hStop, one_mul]

/-- Ball's boundary-content theorem for every convex set in dimension at least two. -/
theorem standardGaussianBoundaryContent_le_ballGaussianPerimeterConstant
    {d : ℕ} (hd : 2 ≤ d) {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) :
    standardGaussianBoundaryContent s ≤
      ENNReal.ofReal (ballGaussianPerimeterConstant d) := by
  apply standardGaussianBoundaryContent_le_ballGaussianPerimeterConstant_of_convexBody_case hd hs
  intro t ht htinterior htcompact
  exact standardGaussianBoundaryContent_le_ballGaussianPerimeterConstant_compactBody hd ht htcompact htinterior

end ProbabilityTheory
