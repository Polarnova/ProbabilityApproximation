/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.ConvexGeometry.SmoothCutoff
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Bentkus's smoothing inequality for convex sets

This file formalizes the smoothing step in Bentkus (2004), Lemmas 2.1--2.2.  The smooth tests are
the distance cutoffs constructed in `ProbabilityApproximation.ConvexGeometry.SmoothCutoff`.

The outer parallel set is the closed enlargement `Metric.cthickening ε (closure A)`.  The inner
parallel set is the complement of the open enlargement of the complement,
`(Metric.thickening ε Aᶜ)ᶜ`.  These conventions retain the boundary in the shell terms instead of
silently replacing `< ε` by `≤ ε`.  The final inequality leaves both shell measures explicit; the
Gaussian shell theorem is a separate downstream input.

The underlying scalar smoothing argument is also Lemma 2.1 of Bentkus (2003).  The empty-set
branch is explicit because Mathlib defines real-valued distance to the empty set to be zero.
-/

open Set Topology MeasureTheory

noncomputable section

namespace ProbabilityTheory

local instance instConvexSpaceRealEuclideanSpaceFin_smoothingInequality {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

local instance instIsModuleConvexSpaceRealEuclideanSpaceFin_smoothingInequality {d : ℕ} :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.ofModule

/-- The inner parallel set at radius `ε`, with the boundary convention obtained by taking the
complement of the *open* `ε`-thickening of the complement. -/
def convexInnerParallel {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  (Metric.thickening ε sᶜ)ᶜ

/-- The inner parallel set is closed. -/
lemma convexInnerParallel_isClosed {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) :
    IsClosed (convexInnerParallel s ε) :=
  Metric.isOpen_thickening.isClosed_compl

/-- The inner parallel set is measurable. -/
lemma measurableSet_convexInnerParallel {d : ℕ}
    (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) :
    MeasurableSet (convexInnerParallel s ε) :=
  (convexInnerParallel_isClosed s ε).measurableSet

/-- Membership in the inner parallel set means that the *open* `ε`-ball is contained in the
original set.  This lemma records the boundary convention used by the smoothing inequality. -/
lemma mem_convexInnerParallel_iff_ball_subset {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {ε : ℝ} {x : EuclideanSpace ℝ (Fin d)} :
    x ∈ convexInnerParallel s ε ↔ Metric.ball x ε ⊆ s := by
  constructor
  · intro hx y hy
    by_contra hys
    have hxy : dist x y < ε := by simpa only [Metric.mem_ball, dist_comm] using hy
    exact hx ((Metric.mem_thickening_iff (E := sᶜ) (x := x)).2 ⟨y, hys, hxy⟩)
  · intro hball hx
    obtain ⟨y, hys, hxy⟩ := (Metric.mem_thickening_iff (E := sᶜ) (x := x)).1 hx
    exact hys (hball (by simpa only [Metric.mem_ball, dist_comm] using hxy))

/-- At positive radius the inner parallel set is contained in the original set. -/
lemma convexInnerParallel_subset {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d)))
    {ε : ℝ} (hε : 0 < ε) : convexInnerParallel s ε ⊆ s := by
  intro x hx
  by_contra hxs
  exact hx (Metric.self_subset_thickening hε sᶜ hxs)

/-- The positive-radius inner parallel set of the empty set is empty. -/
@[simp]
lemma convexInnerParallel_empty {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    convexInnerParallel (∅ : Set (EuclideanSpace ℝ (Fin d))) ε = ∅ := by
  simp [convexInnerParallel, thickening_univ_of_pos hε]

/-- The inner parallel set of the whole space is the whole space. -/
@[simp]
lemma convexInnerParallel_univ {d : ℕ} (ε : ℝ) :
    convexInnerParallel (Set.univ : Set (EuclideanSpace ℝ (Fin d))) ε = Set.univ := by
  simp [convexInnerParallel]

/-- The inner parallel set of a convex set is convex. -/
lemma convexInnerParallel_isConvexSet {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : Convexity.IsConvexSet ℝ s) (ε : ℝ) :
    Convexity.IsConvexSet ℝ (convexInnerParallel s ε) := by
  refine Convexity.IsConvexSet.of_convexCombPair_mem ?_
  intro a b ha hb hab x hx y hy
  rw [convexInnerParallel, mem_compl_iff] at hx hy ⊢
  intro hz
  rw [Metric.mem_thickening_iff] at hz
  obtain ⟨u, hu, hzu⟩ := hz
  let z := Convexity.convexCombPair a b ha hb hab x y
  let h := u - z
  have hx' : x + h ∈ s := by
    by_contra hxs
    apply hx
    rw [Metric.mem_thickening_iff]
    refine ⟨x + h, hxs, ?_⟩
    calc
      dist x (x + h) = ‖z - u‖ := by
        rw [dist_eq_norm]
        congr 1
        dsimp [h]
        abel
      _ = dist z u := by rw [dist_eq_norm]
      _ < ε := hzu
  have hy' : y + h ∈ s := by
    by_contra hys
    apply hy
    rw [Metric.mem_thickening_iff]
    refine ⟨y + h, hys, ?_⟩
    calc
      dist y (y + h) = ‖z - u‖ := by
        rw [dist_eq_norm]
        congr 1
        dsimp [h]
        abel
      _ = dist z u := by rw [dist_eq_norm]
      _ < ε := hzu
  have hmem := hs.convexCombPair_mem hx' hy' ha hb hab
  have heq : Convexity.convexCombPair a b ha hb hab (x + h) (y + h) = u := by
    rw [Convexity.convexCombPair_eq_sum]
    calc
      a • (x + h) + b • (y + h) = (a • x + b • y) + (a + b) • h := by module
      _ = z + h := by
        rw [hab, one_smul]
        congr 1
        exact (Convexity.convexCombPair_eq_sum a b ha hb hab x y).symm
      _ = u := by
        dsimp [h]
        abel
  exact hu (heq ▸ hmem)

/-- Closure preserves convexity in finite-dimensional Euclidean space, stated directly in the
new `Convexity.IsConvexSet` API. -/
lemma closure_isConvexSet {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) : Convexity.IsConvexSet ℝ (closure s) := by
  refine Convexity.IsConvexSet.of_convexCombPair_mem ?_
  intro a b ha hb hab x hx y hy
  rw [Convexity.convexCombPair_eq_sum]
  let f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) := fun x' y' ↦ a • x' + b • y'
  have hf : Continuous (Function.uncurry f) :=
    (continuous_fst.const_smul a).add (continuous_snd.const_smul b)
  change f x y ∈ closure s
  exact map_mem_closure₂ hf hx hy fun x' hx' y' hy' ↦ by
    simpa only [f, Convexity.convexCombPair_eq_sum a b ha hb hab] using
      hs.convexCombPair_mem hx' hy' ha hb hab

/-- A total version of the Bentkus cutoff.  For a nonempty set it is the exact distance cutoff of
its closure; for the empty set it is the constant-zero smooth function. -/
def convexSetCutoff {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ := by
  classical
  exact if s.Nonempty then bentkusCutoff (closure s) ε else 0

/-- The total convex-set cutoff is unchanged when its defining set is replaced by its closure. -/
@[simp]
lemma convexSetCutoff_closure {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) :
    convexSetCutoff (closure s) ε = convexSetCutoff s ε := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · simp only [convexSetCutoff, if_pos hs, if_pos hs.closure, closure_closure]

/-- The total convex-set cutoff is nonnegative. -/
lemma convexSetCutoff_nonneg {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ convexSetCutoff s ε x := by
  simp only [convexSetCutoff]
  split_ifs
  · exact bentkusCutoff_nonneg _ _ _
  · exact le_rfl

/-- The total convex-set cutoff is at most one. -/
lemma convexSetCutoff_le_one {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : convexSetCutoff s ε x ≤ 1 := by
  simp only [convexSetCutoff]
  split_ifs
  · exact bentkusCutoff_le_one _ _ _
  · norm_num

/-- The total convex-set cutoff is measurable. -/
lemma measurable_convexSetCutoff {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) :
    Measurable (convexSetCutoff s ε) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · have hzero : convexSetCutoff (∅ : Set (EuclideanSpace ℝ (Fin d))) ε =
        fun _ ↦ (0 : ℝ) := by
      simp [convexSetCutoff]
      funext x
      rfl
    rw [hzero]
    exact measurable_const
  · simpa [convexSetCutoff, hs] using measurable_bentkusCutoff (closure s) ε

/-- The total convex-set cutoff is integrable against every finite measure. -/
lemma integrable_convexSetCutoff {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ] :
    Integrable (convexSetCutoff s ε) μ := by
  refine Integrable.of_bound (measurable_convexSetCutoff s ε).aestronglyMeasurable 1 ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (convexSetCutoff_nonneg s ε x)]
  exact convexSetCutoff_le_one s ε x

/-- The total cutoff equals one on the original set. -/
lemma convexSetCutoff_eq_one_of_mem {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {ε : ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ s) : convexSetCutoff s ε x = 1 := by
  have hs : s.Nonempty := ⟨x, hx⟩
  simp only [convexSetCutoff, if_pos hs]
  exact bentkusCutoff_eq_one_of_mem (subset_closure hx)

/-- The total cutoff of the empty set is the constant-zero function. -/
@[simp]
lemma convexSetCutoff_empty {d : ℕ} (ε : ℝ) :
    convexSetCutoff (∅ : Set (EuclideanSpace ℝ (Fin d))) ε = 0 := by
  simp [convexSetCutoff]

/-- The total cutoff of the whole space is the constant-one function. -/
@[simp]
lemma convexSetCutoff_univ {d : ℕ} (ε : ℝ) :
    convexSetCutoff (Set.univ : Set (EuclideanSpace ℝ (Fin d))) ε = 1 := by
  funext x
  exact convexSetCutoff_eq_one_of_mem (Set.mem_univ x)

/-- The total cutoff vanishes outside the closed outer parallel set. -/
lemma convexSetCutoff_eq_zero_of_notMem_cthickening {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {ε : ℝ} (hε : 0 < ε)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∉ Metric.cthickening ε (closure s)) :
    convexSetCutoff s ε x = 0 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [convexSetCutoff]
  · simp only [convexSetCutoff, if_pos hs]
    apply bentkusCutoff_eq_zero_of_le_infDist hε
    have hnot : x ∉ Metric.thickening ε (closure s) :=
      fun h ↦ hx (Metric.thickening_subset_cthickening ε (closure s) h)
    exact not_lt.mp (mt (Metric.mem_thickening_iff_infDist_lt hs.closure).2 hnot)

/-- For convex `s`, the total cutoff is continuously differentiable, including the empty and
whole-space edge cases. -/
lemma contDiff_convexSetCutoff {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 1 (convexSetCutoff s ε) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · have hzero : convexSetCutoff (∅ : Set (EuclideanSpace ℝ (Fin d))) ε =
        fun _ ↦ (0 : ℝ) := by
      simp [convexSetCutoff]
      funext x
      rfl
    rw [hzero]
    exact contDiff_const
  · simpa [convexSetCutoff, hne] using
      contDiff_bentkusCutoff isClosed_closure hne.closure (closure_isConvexSet hs) hε

/-- The total convex-set cutoff retains the exact `2 / ε` first-derivative bound. -/
lemma norm_fderiv_convexSetCutoff_le {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : Convexity.IsConvexSet ℝ s)
    {ε : ℝ} (hε : 0 < ε) (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ (convexSetCutoff s ε) x‖ ≤ 2 / ε := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · have hzero : convexSetCutoff (∅ : Set (EuclideanSpace ℝ (Fin d))) ε =
        fun _ ↦ (0 : ℝ) := by
      simp [convexSetCutoff]
      funext y
      rfl
    have hfzero : fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin d) ↦ (0 : ℝ)) x = 0 :=
      (hasFDerivAt_const (0 : ℝ) x).fderiv
    rw [hzero, hfzero, norm_zero]
    exact div_nonneg (by norm_num) hε.le
  · simpa [convexSetCutoff, hne] using
      norm_fderiv_bentkusCutoff_le isClosed_closure hne.closure
        (closure_isConvexSet hs) hε x

/-- The total convex-set cutoff retains the exact `8 / ε²` Lipschitz bound on its derivative. -/
lemma norm_fderiv_convexSetCutoff_sub_le {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : Convexity.IsConvexSet ℝ s)
    {ε : ℝ} (hε : 0 < ε) (x y : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ (convexSetCutoff s ε) x - fderiv ℝ (convexSetCutoff s ε) y‖ ≤
      8 * ‖x - y‖ / ε ^ 2 := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · have hzero : convexSetCutoff (∅ : Set (EuclideanSpace ℝ (Fin d))) ε =
        fun _ ↦ (0 : ℝ) := by
      simp [convexSetCutoff]
      funext z
      rfl
    have hfx : fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin d) ↦ (0 : ℝ)) x = 0 :=
      (hasFDerivAt_const (0 : ℝ) x).fderiv
    have hfy : fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin d) ↦ (0 : ℝ)) y = 0 :=
      (hasFDerivAt_const (0 : ℝ) y).fderiv
    rw [hzero, hfx, hfy, sub_self, norm_zero]
    positivity
  · simpa [convexSetCutoff, hne] using
      norm_fderiv_bentkusCutoff_sub_le isClosed_closure hne.closure
        (closure_isConvexSet hs) hε x y

/-- The cutoff of the inner parallel set vanishes off the original set.  This is where the open
thickening in the definition of `convexInnerParallel` fixes the boundary convention. -/
lemma convexSetCutoff_inner_eq_zero_of_notMem {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {ε : ℝ} (hε : 0 < ε)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∉ s) :
    convexSetCutoff (convexInnerParallel s ε) ε x = 0 := by
  rcases (convexInnerParallel s ε).eq_empty_or_nonempty with hi | hi
  · rw [hi]
    simp [convexSetCutoff]
  · have hthick : Metric.thickening ε (convexInnerParallel s ε) ⊆ s := by
      dsimp [convexInnerParallel]
      simpa only [compl_compl] using
        Metric.thickening_compl_thickening_self_subset_compl ε sᶜ
    have hnot : x ∉ Metric.thickening ε (convexInnerParallel s ε) :=
      fun hxi ↦ hx (hthick hxi)
    have hdist : ε ≤ Metric.infDist x (convexInnerParallel s ε) :=
      not_lt.mp (mt (Metric.mem_thickening_iff_infDist_lt hi).2 hnot)
    have hclosed := convexInnerParallel_isClosed s ε
    simp only [convexSetCutoff, if_pos hi, hclosed.closure_eq]
    exact bentkusCutoff_eq_zero_of_le_infDist hε hdist

/-- The probability of a measurable set is bounded above by the expectation of its Bentkus
cutoff. -/
lemma measureReal_le_integral_convexSetCutoff {d : ℕ}
    (mu : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure mu]
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : MeasurableSet s) (ε : ℝ) :
    mu.real s ≤ ∫ x, convexSetCutoff s ε x ∂mu := by
  rw [← integral_indicator_one hs]
  refine integral_mono ((integrable_const (μ := mu) (1 : ℝ)).indicator hs)
    (integrable_convexSetCutoff s ε mu) ?_
  intro x
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, Pi.one_apply, convexSetCutoff_eq_one_of_mem hx]
  · rw [indicator_of_notMem hx]
    exact convexSetCutoff_nonneg s ε x

/-- The expectation of the cutoff is bounded by the probability of the closed outer parallel
set. -/
lemma integral_convexSetCutoff_le_measureReal_cthickening {d : ℕ}
    (mu : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure mu]
    (s : Set (EuclideanSpace ℝ (Fin d))) {ε : ℝ} (hε : 0 < ε) :
    (∫ x, convexSetCutoff s ε x ∂mu) ≤ mu.real (Metric.cthickening ε (closure s)) := by
  rw [← integral_indicator_one (measurableSet_cthickening (closure s) ε)]
  refine integral_mono (integrable_convexSetCutoff s ε mu)
    ((integrable_const (μ := mu) (1 : ℝ)).indicator
      (measurableSet_cthickening (closure s) ε)) ?_
  intro x
  by_cases hx : x ∈ Metric.cthickening ε (closure s)
  · rw [indicator_of_mem hx, Pi.one_apply]
    exact convexSetCutoff_le_one s ε x
  · rw [indicator_of_notMem hx, convexSetCutoff_eq_zero_of_notMem_cthickening hε hx]

/-- The expectation of the inner-parallel cutoff is bounded by the probability of the original
set. -/
lemma integral_convexSetCutoff_inner_le_measureReal {d : ℕ}
    (mu : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure mu]
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : MeasurableSet s)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ x, convexSetCutoff (convexInnerParallel s ε) ε x ∂mu) ≤ mu.real s := by
  rw [← integral_indicator_one hs]
  refine integral_mono (integrable_convexSetCutoff (convexInnerParallel s ε) ε mu)
    ((integrable_const (μ := mu) (1 : ℝ)).indicator hs) ?_
  intro x
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, Pi.one_apply]
    exact convexSetCutoff_le_one (convexInnerParallel s ε) ε x
  · rw [indicator_of_notMem hx, convexSetCutoff_inner_eq_zero_of_notMem hε hx]

/-- **Bentkus smoothing inequality, setwise form.**

For two probability measures `mu` and `nu`, the convex-set probability error is bounded by the
larger of the two smooth cutoff expectation errors, plus the larger of the outer and inner shell
probabilities under the reference measure `nu`.  This is the exact form that will consume the
Gaussian shell theorem: no shell estimate is assumed here.

The two cutoffs are `C¹` and satisfy the exact derivative bounds `2 / ε` and `8 / ε²` by
`contDiff_convexSetCutoff`, `norm_fderiv_convexSetCutoff_le`, and
`norm_fderiv_convexSetCutoff_sub_le`. -/
theorem bentkus_convexSet_smoothingInequality {d : ℕ}
    (mu nu : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {s : Set (EuclideanSpace ℝ (Fin d))} (hsmeas : MeasurableSet s)
    (_hsconv : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε) :
    |mu.real s - nu.real s| ≤
      max
          |∫ x, convexSetCutoff s ε x ∂mu - ∫ x, convexSetCutoff s ε x ∂nu|
          |∫ x, convexSetCutoff (convexInnerParallel s ε) ε x ∂mu -
            ∫ x, convexSetCutoff (convexInnerParallel s ε) ε x ∂nu| +
        max
          (nu.real (Metric.cthickening ε (closure s) \ s))
          (nu.real (s \ convexInnerParallel s ε)) := by
  let eOuter :=
    (∫ x, convexSetCutoff s ε x ∂mu) - ∫ x, convexSetCutoff s ε x ∂nu
  let eInner :=
    (∫ x, convexSetCutoff (convexInnerParallel s ε) ε x ∂mu) -
      ∫ x, convexSetCutoff (convexInnerParallel s ε) ε x ∂nu
  let shellOuter := nu.real (Metric.cthickening ε (closure s) \ s)
  let shellInner := nu.real (s \ convexInnerParallel s ε)
  change |mu.real s - nu.real s| ≤
    max |eOuter| |eInner| + max shellOuter shellInner
  have hmuOuter := measureReal_le_integral_convexSetCutoff mu hsmeas ε
  have hnuOuter := integral_convexSetCutoff_le_measureReal_cthickening nu s hε
  have hnuInner := measureReal_le_integral_convexSetCutoff nu
    (measurableSet_convexInnerParallel s ε) ε
  have hmuInner := integral_convexSetCutoff_inner_le_measureReal mu hsmeas hε
  have houterSubset : s ⊆ Metric.cthickening ε (closure s) :=
    subset_closure.trans (Metric.self_subset_cthickening (closure s))
  have hinnerSubset : convexInnerParallel s ε ⊆ s := convexInnerParallel_subset s hε
  have houterShell :
      nu.real (Metric.cthickening ε (closure s)) - nu.real s = shellOuter := by
    dsimp [shellOuter]
    exact (measureReal_sdiff (μ := nu) houterSubset hsmeas).symm
  have hinnerShell :
      nu.real s - nu.real (convexInnerParallel s ε) = shellInner := by
    dsimp [shellInner]
    exact (measureReal_sdiff (μ := nu) hinnerSubset
      (measurableSet_convexInnerParallel s ε)).symm
  have hpositive : mu.real s - nu.real s ≤ |eOuter| + shellOuter := by
    calc
      mu.real s - nu.real s ≤
          eOuter + (nu.real (Metric.cthickening ε (closure s)) - nu.real s) := by
        dsimp [eOuter]
        linarith
      _ = eOuter + shellOuter := by rw [houterShell]
      _ ≤ |eOuter| + shellOuter := add_le_add (le_abs_self eOuter) le_rfl
  have hnegative : nu.real s - mu.real s ≤ |eInner| + shellInner := by
    calc
      nu.real s - mu.real s ≤
          -eInner + (nu.real s - nu.real (convexInnerParallel s ε)) := by
        dsimp [eInner]
        linarith
      _ = -eInner + shellInner := by rw [hinnerShell]
      _ ≤ |eInner| + shellInner := add_le_add (neg_le_abs eInner) le_rfl
  apply abs_le.2
  constructor
  · have h := hnegative.trans <| add_le_add
      (le_max_right |eOuter| |eInner|) (le_max_right shellOuter shellInner)
    linarith
  · exact hpositive.trans <| add_le_add
      (le_max_left |eOuter| |eInner|) (le_max_left shellOuter shellInner)

end ProbabilityTheory
