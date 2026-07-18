/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.Bentkus.Induction.GaussianDensityComparison

/-!
# Split-Gaussian shell estimates for Bentkus's induction

This module proves the translated closed-shell estimates for the split-Gaussian comparator,
including Ball's scaled shell bound, frontier nullity, affine-noise transport, and the
dimension-normalized uniform form used in the small-angle argument.
-/

open MeasureTheory InnerProductSpace Matrix Set
open scoped ENNReal MatrixOrder Pointwise RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

universe u

local instance splitGaussianShellConvexSpace {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

local instance splitGaussianShellIsModuleConvexSpace {d : ℕ} :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.ofModule

namespace BentkusInduction

set_option maxHeartbeats 2000000

/-- Averaging a translated affine shell against the first Gaussian-density contraction costs
only the uniform translated-shell probability and `‖w‖`.  This is the conditional Fubini step
between Bentkus (3.32) and (3.33). -/
theorem
    integral_setIntegral_abs_standardGaussianDensityD1_le_of_uniform_shell
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ν : Measure Θ} [IsProbabilityMeasure ν]
    (F : Θ → EuclideanSpace ℝ (Fin d)) (hF : Measurable F)
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : MeasurableSet S)
    (w : EuclideanSpace ℝ (Fin d)) {J : ℝ} (hJ : 0 ≤ J)
    (hshell : ∀ u, ν.real ((fun a ↦ F a + L u) ⁻¹' S) ≤ J) :
    (∫ a, ∫ u in (fun u ↦ F a + L u) ⁻¹' S,
        |standardGaussianDensityD1 u w| ∂volume ∂ν) ≤ J * ‖w‖ := by
  let Q : Θ × EuclideanSpace ℝ (Fin d) → ℝ := fun p ↦
    S.indicator (fun _ ↦ |standardGaussianDensityD1 p.2 w|) (F p.1 + L p.2)
  have hjoint : MeasurableSet
      ((fun p : Θ × EuclideanSpace ℝ (Fin d) ↦ F p.1 + L p.2) ⁻¹' S) :=
    hS.preimage
      ((hF.comp measurable_fst).add (L.continuous.measurable.comp measurable_snd))
  have hbase : Integrable
      (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦
        |standardGaussianDensityD1 p.2 w|) (ν.prod volume) :=
    (integrable_standardGaussianDensityD1_volume w).abs.comp_snd ν
  have hQint : Integrable Q (ν.prod volume) := by
    apply hbase.indicator hjoint
  have hfiber (a : Θ) :
      MeasurableSet ((fun u ↦ F a + L u) ⁻¹' S) :=
    hS.preimage (continuous_const.add L.continuous).measurable
  have hleft :
      (∫ a, ∫ u in (fun u ↦ F a + L u) ⁻¹' S,
          |standardGaussianDensityD1 u w| ∂volume ∂ν) =
        ∫ a, ∫ u, Q (a, u) ∂volume ∂ν := by
    apply integral_congr_ae
    filter_upwards with a
    rw [← integral_indicator (hfiber a)]
    rfl
  have hinner (u : EuclideanSpace ℝ (Fin d)) :
      (∫ a, Q (a, u) ∂ν) =
        ν.real ((fun a ↦ F a + L u) ⁻¹' S) *
          |standardGaussianDensityD1 u w| := by
    let T : Set Θ := (fun a ↦ F a + L u) ⁻¹' S
    have hT : MeasurableSet T :=
      hS.preimage (hF.add measurable_const)
    have hfun : (fun a ↦ Q (a, u)) =
        T.indicator (fun _ ↦ |standardGaussianDensityD1 u w|) := by
      funext a
      by_cases ha : F a + L u ∈ S
      · simp [Q, T, ha]
      · simp [Q, T, ha]
    rw [hfun, integral_indicator_const _ hT, smul_eq_mul]
  rw [hleft, integral_integral_swap hQint]
  calc
    (∫ u, ∫ a, Q (a, u) ∂ν ∂volume) ≤
        ∫ u, J * |standardGaussianDensityD1 u w| ∂volume := by
      apply integral_mono hQint.integral_prod_right
        ((integrable_standardGaussianDensityD1_volume w).abs.const_mul J)
      intro u
      change (∫ a, Q (a, u) ∂ν) ≤ J * |standardGaussianDensityD1 u w|
      rw [hinner u]
      exact mul_le_mul_of_nonneg_right (hshell u) (abs_nonneg _)
    _ = J * ∫ u, |standardGaussianDensityD1 u w| ∂volume := by
      rw [integral_const_mul]
    _ ≤ J * ‖w‖ :=
      mul_le_mul_of_nonneg_left
        (integral_abs_standardGaussianDensityD1_volume_le w) hJ

/-- A positive scalar multiple of a standard Gaussian has the Ball outer-shell bound with the
shell width divided by the scalar.  This is the Gaussian-comparator normalization in Bentkus
(3.31). -/
private theorem map_stdGaussian_smul_outerShell_le_ball
    {d : ℕ} (c : ℝ) (hc : 0 < c)
    (A : Set (EuclideanSpace ℝ (Fin d))) (hA : MeasurableSet A)
    (hAconv : Convexity.IsConvexSet ℝ A) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun x ↦ c • x)).real
        (Metric.cthickening δ (closure A) \ A) ≤
      ballGaussianPerimeterConstant d * (δ / c) := by
  let E := EuclideanSpace ℝ (Fin d)
  let scale : E → E := fun x ↦ c • x
  let L : E →L[ℝ] E := c • ContinuousLinearMap.id ℝ E
  let B : Set E := scale ⁻¹' A
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hscale : Measurable scale := by
    dsimp only [scale]
    fun_prop
  have hBmeas : MeasurableSet B := hA.preimage hscale
  have hBconv : Convexity.IsConvexSet ℝ B := by
    have hL : (fun x : E ↦ L x) = scale := by
      funext x
      simp only [L, scale, _root_.smul_apply,
        ContinuousLinearMap.id_apply]
    have hpre := isConvexSet_preimage_continuousLinearMap L hAconv
    dsimp only [B]
    rw [← hL]
    exact hpre
  by_cases hAempty : A = ∅
  · subst A
    simp
    exact mul_nonneg (by
      unfold ballGaussianPerimeterConstant
      positivity) (div_nonneg hδ hc.le)
  have hAne : A.Nonempty := nonempty_iff_ne_empty.mpr hAempty
  have hBne : B.Nonempty := by
    obtain ⟨a, ha⟩ := hAne
    refine ⟨c⁻¹ • a, ?_⟩
    change c • (c⁻¹ • a) ∈ A
    rw [smul_inv_smul₀ hc0]
    exact ha
  have hclosure : c • closure B = closure A := by
    let e : E ≃ₜ E := Homeomorph.smulOfNeZero c hc0
    have himage : e '' B = A := by
      dsimp only [e, B, scale]
      exact e.image_preimage A
    change e '' closure B = closure A
    rw [e.image_closure, himage]
  have hpreimage :
      scale ⁻¹' (Metric.cthickening δ (closure A) \ A) ⊆
        Metric.cthickening (δ / c) (closure B) \ B := by
    intro x hx
    have hxthick : scale x ∈ Metric.cthickening δ (closure A) := hx.1
    have hAclosureNe : (closure A).Nonempty := hAne.closure
    have hBclosureNe : (closure B).Nonempty := hBne.closure
    have hscaled :
        Metric.infDist (scale x) (closure A) =
          c * Metric.infDist x (closure B) := by
      dsimp only [scale]
      rw [← hclosure, infDist_smul₀ hc0, Real.norm_of_nonneg hc.le]
    have hdistScaled :
        Metric.infDist (scale x) (closure A) ≤ δ := by
      rw [Metric.mem_cthickening_iff] at hxthick
      exact (ENNReal.le_ofReal_iff_toReal_le
        (Metric.infEDist_ne_top hAclosureNe) hδ).mp hxthick
    have hdist : Metric.infDist x (closure B) ≤ δ / c := by
      apply (le_div_iff₀ hc).2
      rw [mul_comm, ← hscaled]
      exact hdistScaled
    constructor
    · rw [Metric.mem_cthickening_iff]
      exact (ENNReal.le_ofReal_iff_toReal_le
        (Metric.infEDist_ne_top hBclosureNe) (div_nonneg hδ hc.le)).mpr hdist
    · exact hx.2
  have hshellMeas :
      MeasurableSet (Metric.cthickening δ (closure A) \ A) := by
    have hthick : MeasurableSet (Metric.cthickening δ (closure A)) := by
      exact measurableSet_cthickening (closure A) δ
    exact MeasurableSet.diff hthick hA
  rw [map_measureReal_apply hscale hshellMeas]
  calc
    (stdGaussian E).real
        (scale ⁻¹' (Metric.cthickening δ (closure A) \ A)) ≤
        (stdGaussian E).real
          (Metric.cthickening (δ / c) (closure B) \ B) :=
      measureReal_mono hpreimage
    _ ≤ ballGaussianPerimeterConstant d * (δ / c) :=
      (stdGaussian_shell_pair_le_ball hBconv (div_nonneg hδ hc.le)).1

/-- A nonzero scalar image of a standard Gaussian gives zero mass to every convex frontier. -/
private theorem map_stdGaussian_smul_frontier_eq_zero
    {d : ℕ} (c : ℝ) (hc : 0 < c)
    (A : Set (EuclideanSpace ℝ (Fin d)))
    (hAconv : Convexity.IsConvexSet ℝ A) :
    ((stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun x ↦ c • x)).real
        (frontier A) = 0 := by
  let E := EuclideanSpace ℝ (Fin d)
  let scale : E → E := fun x ↦ c • x
  let L : E →L[ℝ] E := c • ContinuousLinearMap.id ℝ E
  let B : Set E := scale ⁻¹' A
  have hscale : Measurable scale := by
    dsimp only [scale]
    fun_prop
  have hL : (fun x : E ↦ L x) = scale := by
    funext x
    simp only [L, scale, _root_.smul_apply,
      ContinuousLinearMap.id_apply]
  have hBconv : Convexity.IsConvexSet ℝ B := by
    dsimp only [B]
    rw [← hL]
    exact isConvexSet_preimage_continuousLinearMap L hAconv
  have hpre : scale ⁻¹' frontier A = frontier B := by
    dsimp only [scale, B]
    exact (Homeomorph.smulOfNeZero c (ne_of_gt hc)).preimage_frontier A
  have hfrontierMeas : MeasurableSet (frontier A) := by
    exact measurableSet_frontier
  rw [map_measureReal_apply hscale hfrontierMeas, hpre]
  simp only [Measure.real, stdGaussian_frontier_eq_zero hBconv, ENNReal.toReal_zero]

/-- Convex-distance control, an outer-shell bound for the comparator, and zero comparator
frontier mass together control the full closed support shell. -/
private theorem closedShell_le_of_convexDistance
    {d : ℕ}
    {ν τ : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]
    {D G : ℝ} (_hD : 0 ≤ D)
    (hbound : ∀ A : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet A →
      Convexity.IsConvexSet ℝ A → |ν.real A - τ.real A| ≤ D)
    (A : Set (EuclideanSpace ℝ (Fin d))) (hAclosed : IsClosed A)
    (hAconv : Convexity.IsConvexSet ℝ A) {δ : ℝ} (hδ : 0 ≤ δ)
    (houter : τ.real (Metric.cthickening δ A \ A) ≤ G)
    (hfrontier : τ.real (frontier A) = 0) :
    ν.real (Metric.cthickening δ A \ interior A) ≤ G + 4 * D := by
  let B := Metric.cthickening δ A
  have hAmeas : MeasurableSet A := hAclosed.measurableSet
  have hImeas : MeasurableSet (interior A) := isOpen_interior.measurableSet
  have hIconv : Convexity.IsConvexSet ℝ (interior A) :=
    isConvexSet_interior hAconv
  have hAB : A ⊆ B := by
    dsimp only [B]
    exact Metric.self_subset_cthickening A
  have hBm : MeasurableSet B := by
    dsimp only [B]
    exact measurableSet_cthickening A δ
  have hBc : Convexity.IsConvexSet ℝ B := by
    dsimp only [B]
    exact cthickening_isConvexSet hAconv hδ
  have houterν :
      ν.real (B \ A) ≤ τ.real (B \ A) + 2 * D :=
    measureReal_sdiff_le_add_two_mul_of_abs_sub_le
      hAB hAmeas (hbound A hAmeas hAconv) (hbound B hBm hBc)
  have hfrontierν :
      ν.real (A \ interior A) ≤ τ.real (A \ interior A) + 2 * D :=
    measureReal_sdiff_le_add_two_mul_of_abs_sub_le
      interior_subset hImeas (hbound (interior A) hImeas hIconv)
        (hbound A hAmeas hAconv)
  have hfrontierSet : A \ interior A = frontier A := by
    calc
      A \ interior A = closure A \ interior A := by
        rw [hAclosed.closure_eq]
      _ = frontier A := closure_sdiff_interior A
  have hsplit :
      B \ interior A = (B \ A) ∪ (A \ interior A) := by
    ext x
    constructor
    · intro hx
      by_cases hxA : x ∈ A
      · exact Or.inr ⟨hxA, hx.2⟩
      · exact Or.inl ⟨hx.1, hxA⟩
    · rintro (hx | hx)
      · exact ⟨hx.1, fun hxi ↦ hx.2 (interior_subset hxi)⟩
      · exact ⟨hAB hx.1, hx.2⟩
  calc
    ν.real (Metric.cthickening δ A \ interior A) =
        ν.real ((B \ A) ∪ (A \ interior A)) := by
      rw [show Metric.cthickening δ A = B by rfl, hsplit]
    _ ≤ ν.real (B \ A) + ν.real (A \ interior A) :=
      measureReal_union_le _ _
    _ ≤ (τ.real (B \ A) + 2 * D) +
        (τ.real (A \ interior A) + 2 * D) :=
      add_le_add houterν hfrontierν
    _ ≤ (G + 2 * D) + (0 + 2 * D) := by
      have houter' : τ.real (B \ A) ≤ G := by
        simpa only [B] using houter
      have hfrontier' : τ.real (A \ interior A) ≤ 0 := by
        rw [hfrontierSet, hfrontier]
      linarith
    _ = G + 4 * D := by ring

/-- Pulling a closed support shell through the inverse of a continuous linear equivalence
multiplies its width by at most the operator norm of the forward equivalence. -/
private theorem map_continuousLinearEquiv_symm_closedShell_le
    {d : ℕ} {ν : Measure (EuclideanSpace ℝ (Fin d))} [IsFiniteMeasure ν]
    (e : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (A : Set (EuclideanSpace ℝ (Fin d))) (hAclosed : IsClosed A)
    (hAconv : Convexity.IsConvexSet ℝ A) {δ : ℝ} (hδ : 0 ≤ δ) :
    (ν.map e.symm).real (Metric.cthickening δ A \ interior A) ≤
      ν.real
        (Metric.cthickening (‖e.toContinuousLinearMap‖ * δ) (e '' A) \
          interior (e '' A)) := by
  let E := EuclideanSpace ℝ (Fin d)
  have heMeas : Measurable (e.symm : E → E) := e.symm.continuous.measurable
  have hAimageClosed : IsClosed (e '' A) :=
    e.toHomeomorph.isClosedMap A hAclosed
  have hAimageConv : Convexity.IsConvexSet ℝ (e '' A) := by
    refine Convexity.IsConvexSet.of_convexCombPair_mem ?_
    intro a b ha hb hab x hx y hy
    obtain ⟨x, hxA, rfl⟩ := hx
    obtain ⟨y, hyA, rfl⟩ := hy
    refine ⟨Convexity.convexCombPair a b ha hb hab x y,
      hAconv.convexCombPair_mem hxA hyA ha hb hab, ?_⟩
    rw [Convexity.convexCombPair_eq_sum,
      Convexity.convexCombPair_eq_sum, map_add, map_smul, map_smul]
  by_cases hAempty : A = ∅
  · subst A
    simp
  have hAne : A.Nonempty := nonempty_iff_ne_empty.mpr hAempty
  have hpreimage :
      (e.symm : E → E) ⁻¹' (Metric.cthickening δ A \ interior A) ⊆
        Metric.cthickening (‖e.toContinuousLinearMap‖ * δ) (e '' A) \
          interior (e '' A) := by
    intro x hx
    change e.symm x ∈ Metric.cthickening δ A \ interior A at hx
    obtain ⟨a, haA, haDist⟩ :=
      hAclosed.exists_infDist_eq_dist hAne (e.symm x)
    have hinfDist : Metric.infDist (e.symm x) A ≤ δ := by
      have hxthick := hx.1
      rw [Metric.mem_cthickening_iff] at hxthick
      exact (ENNReal.le_ofReal_iff_toReal_le
        (Metric.infEDist_ne_top hAne) hδ).mp hxthick
    have hdist : dist (e.symm x) a ≤ δ := by
      rw [← haDist]
      exact hinfDist
    have hscaledDist :
        dist x (e a) ≤ ‖e.toContinuousLinearMap‖ * δ := by
      calc
        dist x (e a) = ‖e (e.symm x - a)‖ := by
          rw [dist_eq_norm, map_sub, e.apply_symm_apply]
        _ ≤ ‖e.toContinuousLinearMap‖ * ‖e.symm x - a‖ :=
          e.toContinuousLinearMap.le_opNorm _
        _ = ‖e.toContinuousLinearMap‖ * dist (e.symm x) a := by
          rw [dist_eq_norm]
        _ ≤ ‖e.toContinuousLinearMap‖ * δ :=
          mul_le_mul_of_nonneg_left hdist (norm_nonneg e.toContinuousLinearMap)
    constructor
    · exact Metric.mem_cthickening_of_dist_le
        x (e a) (‖e.toContinuousLinearMap‖ * δ) (e '' A)
          ⟨a, haA, rfl⟩ hscaledDist
    · intro hxInterior
      have himageInterior :
          e '' interior A = interior (e '' A) :=
        e.toHomeomorph.image_interior A
      rw [← himageInterior] at hxInterior
      obtain ⟨y, hy, hyx⟩ := hxInterior
      apply hx.2
      rw [← hyx, e.symm_apply_apply]
      exact hy
  have hshellMeas : MeasurableSet
      (Metric.cthickening δ A \ interior A) :=
    MeasurableSet.diff (measurableSet_cthickening A δ)
      isOpen_interior.measurableSet
  rw [map_measureReal_apply heMeas hshellMeas]
  exact measureReal_mono hpreimage

/-- A common independent Gaussian perturbation preserves the induction error, while the
Gaussian comparator is normalized by its total scalar variance before applying Ball's shell
bound. -/
private theorem map_prod_affineGaussianNoise_outerShell_le
    {d : ℕ} {ν : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure ν]
    {D p q c : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ A : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet A →
      Convexity.IsConvexSet ℝ A →
      |ν.real A -
        (stdGaussian (EuclideanSpace ℝ (Fin d))).real A| ≤ D)
    (hc : 0 < c) (hpq : p ^ 2 + q ^ 2 = c ^ 2)
    (A : Set (EuclideanSpace ℝ (Fin d))) (hA : MeasurableSet A)
    (hAconv : Convexity.IsConvexSet ℝ A) {δ : ℝ} (hδ : 0 ≤ δ) :
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let κ := γ.map (fun x ↦ q • x)
    let T := (κ.prod ν).map
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        p • z.2 + z.1)
    T.real (Metric.cthickening δ (closure A) \ A) ≤
      ballGaussianPerimeterConstant d * (δ / c) + 2 * D := by
  let E := EuclideanSpace ℝ (Fin d)
  let γ := stdGaussian E
  let Q : E → E := fun x ↦ q • x
  let κ := γ.map Q
  let F : E × E → E := fun z ↦ p • z.2 + z.1
  let W : E × E → E := fun z ↦ q • z.1 + p • z.2
  let scale : E → E := fun x ↦ c • x
  let T := (κ.prod ν).map F
  let G := (κ.prod γ).map F
  let B := Metric.cthickening δ (closure A)
  letI : IsProbabilityMeasure κ :=
    Measure.isProbabilityMeasure_map (by
      dsimp only [Q]
      fun_prop)
  have hQ : Measurable Q := by
    dsimp only [Q]
    fun_prop
  have hF : Measurable F := by
    dsimp only [F]
    fun_prop
  have hW : Measurable W := by
    dsimp only [W]
    fun_prop
  have hscale : Measurable scale := by
    dsimp only [scale]
    fun_prop
  have hκν := convexDistance_map_prod_affineNoise_le
    (ν := ν) (τ := γ) (κ := κ) hD hbound p
  have hprod :
      κ.prod γ = (γ.prod γ).map (Prod.map Q id) := by
    simpa only [κ, Measure.map_id] using
      Measure.map_prod_map γ γ hQ measurable_id
  have hcomp : F ∘ Prod.map Q id = W := by
    funext z
    dsimp only [F, Q, W, Function.comp_apply, Prod.map_apply, id_eq]
    exact add_comm _ _
  have hGlaw : G = γ.map scale := by
    dsimp only [G]
    rw [hprod, Measure.map_map hF (hQ.prodMap measurable_id), hcomp]
    simpa only [γ, W, scale] using
      map_prod_stdGaussian_weightedAdd_eq_map_smul
        (d := d) hc hpq
  have hAB : A ⊆ B := by
    dsimp only [B]
    exact subset_closure.trans (Metric.self_subset_cthickening (closure A))
  have hBm : MeasurableSet B := by
    dsimp only [B]
    exact measurableSet_cthickening (closure A) δ
  have hBc : Convexity.IsConvexSet ℝ B := by
    dsimp only [B]
    exact cthickening_isConvexSet (closure_isConvexSet hAconv) hδ
  have hcompare (S : Set E) (hSm : MeasurableSet S)
      (hSc : Convexity.IsConvexSet ℝ S) :
      |T.real S - G.real S| ≤ D := by
    simpa only [T, G, F, κ, γ] using hκν S hSm hSc
  have hshell :
      T.real (B \ A) ≤ G.real (B \ A) + 2 * D :=
    measureReal_sdiff_le_add_two_mul_of_abs_sub_le
      hAB hA (hcompare A hA hAconv) (hcompare B hBm hBc)
  have hGaussian :
      G.real (Metric.cthickening δ (closure A) \ A) ≤
        ballGaussianPerimeterConstant d * (δ / c) := by
    rw [hGlaw]
    simpa only [γ, scale] using
      map_stdGaussian_smul_outerShell_le_ball c hc A hA hAconv hδ
  change T.real (B \ A) ≤
    ballGaussianPerimeterConstant d * (δ / c) + 2 * D
  have hGaussian' : G.real (B \ A) ≤
      ballGaussianPerimeterConstant d * (δ / c) := by
    simpa only [B] using hGaussian
  linarith

/-- Closed-support-shell version of
`map_prod_affineGaussianNoise_outerShell_le`, including the convex frontier. -/
private theorem map_prod_affineGaussianNoise_closedShell_le
    {d : ℕ} {ν : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure ν]
    {D p q c : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ A : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet A →
      Convexity.IsConvexSet ℝ A →
      |ν.real A -
        (stdGaussian (EuclideanSpace ℝ (Fin d))).real A| ≤ D)
    (hc : 0 < c) (hpq : p ^ 2 + q ^ 2 = c ^ 2)
    (A : Set (EuclideanSpace ℝ (Fin d))) (hAclosed : IsClosed A)
    (hAconv : Convexity.IsConvexSet ℝ A) {δ : ℝ} (hδ : 0 ≤ δ) :
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let κ := γ.map (fun x ↦ q • x)
    let T := (κ.prod ν).map
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        p • z.2 + z.1)
    T.real (Metric.cthickening δ A \ interior A) ≤
      ballGaussianPerimeterConstant d * (δ / c) + 4 * D := by
  let E := EuclideanSpace ℝ (Fin d)
  let γ := stdGaussian E
  let Q : E → E := fun x ↦ q • x
  let κ := γ.map Q
  let F : E × E → E := fun z ↦ p • z.2 + z.1
  let W : E × E → E := fun z ↦ q • z.1 + p • z.2
  let scale : E → E := fun x ↦ c • x
  let T := (κ.prod ν).map F
  let G := (κ.prod γ).map F
  letI : IsProbabilityMeasure κ :=
    Measure.isProbabilityMeasure_map (by
      dsimp only [Q]
      fun_prop)
  have hQ : Measurable Q := by
    dsimp only [Q]
    fun_prop
  have hF : Measurable F := by
    dsimp only [F]
    fun_prop
  letI : IsProbabilityMeasure T :=
    Measure.isProbabilityMeasure_map hF.aemeasurable
  letI : IsProbabilityMeasure G :=
    Measure.isProbabilityMeasure_map hF.aemeasurable
  have hprod :
      κ.prod γ = (γ.prod γ).map (Prod.map Q id) := by
    simpa only [κ, Measure.map_id] using
      Measure.map_prod_map γ γ hQ measurable_id
  have hcomp : F ∘ Prod.map Q id = W := by
    funext z
    dsimp only [F, Q, W, Function.comp_apply, Prod.map_apply, id_eq]
    exact add_comm _ _
  have hGlaw : G = γ.map scale := by
    dsimp only [G]
    rw [hprod, Measure.map_map hF (hQ.prodMap measurable_id), hcomp]
    simpa only [γ, W, scale] using
      map_prod_stdGaussian_weightedAdd_eq_map_smul
        (d := d) hc hpq
  have hκν := convexDistance_map_prod_affineNoise_le
    (ν := ν) (τ := γ) (κ := κ) hD hbound p
  have hcompare (S : Set E) (hSm : MeasurableSet S)
      (hSc : Convexity.IsConvexSet ℝ S) :
      |T.real S - G.real S| ≤ D := by
    simpa only [T, G, F, κ, γ] using hκν S hSm hSc
  have houter :
      G.real (Metric.cthickening δ A \ A) ≤
        ballGaussianPerimeterConstant d * (δ / c) := by
    rw [hGlaw]
    have hs := map_stdGaussian_smul_outerShell_le_ball
      c hc A hAclosed.measurableSet hAconv hδ
    simpa only [γ, scale, hAclosed.closure_eq] using hs
  have hfrontier : G.real (frontier A) = 0 := by
    rw [hGlaw]
    simpa only [γ, scale] using
      map_stdGaussian_smul_frontier_eq_zero c hc A hAconv
  change T.real (Metric.cthickening δ A \ interior A) ≤
    ballGaussianPerimeterConstant d * (δ / c) + 4 * D
  exact closedShell_le_of_convexDistance hD hcompare A hAclosed hAconv hδ
    houter hfrontier

/-- The concrete split-Gaussian base `pU + (q / √2)PN`, transported back through the
leave-one-out unwhitening map, has a uniform closed-shell bound from induction and Ball. -/
private theorem bentkus_splitGaussianBase_closedShell_le_of_induction
    {C : ℝ} (hC : 0 ≤ C) {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hIH : bentkusIdentityCovarianceBoundAt.{u} C n)
    (hd : 0 < d) (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (α : ℝ) (hcos : 0 < Real.cos α)
    (A : Set (EuclideanSpace ℝ (Fin d))) (hAclosed : IsClosed A)
    (hAconv : Convexity.IsConvexSet ℝ A) {δ : ℝ} (hδ : 0 ≤ δ) :
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let U := bentkusLeaveOneOut X k
    let ν := μ.map (fun ω ↦ e (U ω))
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let θ := (Real.sqrt 2)⁻¹
    let p := Real.cos α
    let q := θ * Real.sin α
    let c := Real.sqrt (p ^ 2 + q ^ 2)
    let T := ((γ.map (fun x ↦ q • x)).prod ν).map
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        p • z.2 + z.1)
    let D := C * (d : ℝ) ^ (1 / 4 : ℝ) *
      ∑ i : Fin n, ∫ ω,
        ‖bentkusWhiteningCLM S (X (k.succAbove i) ω)‖ ^ 3 ∂μ
    (T.map e.symm).real (Metric.cthickening δ A \ interior A) ≤
      ballGaussianPerimeterConstant d *
          (‖e.toContinuousLinearMap‖ * δ / c) + 4 * D := by
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let U := bentkusLeaveOneOut X k
  let ν := μ.map (fun ω ↦ e (U ω))
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let θ := (Real.sqrt 2)⁻¹
  let p := Real.cos α
  let q := θ * Real.sin α
  let c := Real.sqrt (p ^ 2 + q ^ 2)
  let T := ((γ.map (fun x ↦ q • x)).prod ν).map
    (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      p • z.2 + z.1)
  let D := C * (d : ℝ) ^ (1 / 4 : ℝ) *
    ∑ i : Fin n, ∫ ω,
      ‖bentkusWhiteningCLM S (X (k.succAbove i) ω)‖ ^ 3 ∂μ
  have hUmeas : Measurable U := by
    dsimp only [U, bentkusLeaveOneOut]
    exact Finset.measurable_sum (Finset.univ.erase k) fun i _ ↦ hXm i
  letI : IsProbabilityMeasure ν := by
    dsimp only [ν]
    exact Measure.isProbabilityMeasure_map
      (e.continuous.measurable.comp hUmeas).aemeasurable
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hbound (B : Set (EuclideanSpace ℝ (Fin d))) (hBm : MeasurableSet B)
      (hBc : Convexity.IsConvexSet ℝ B) :
      |ν.real B - γ.real B| ≤ D := by
    simpa only [ν, γ, D, S, e, U] using
      bentkusWhitenedLeaveOneOut_error_le_of_induction
        hIH hd hX3 h_indep hX0 k hS B hBm hBc
  have hpqNonneg : 0 ≤ p ^ 2 + q ^ 2 := by positivity
  have hpqPos : 0 < p ^ 2 + q ^ 2 := by
    have hpPos : 0 < p := by simpa only [p] using hcos
    nlinarith [sq_pos_of_pos hpPos, sq_nonneg q]
  have hc : 0 < c := by
    dsimp only [c]
    exact Real.sqrt_pos.2 hpqPos
  have hpq : p ^ 2 + q ^ 2 = c ^ 2 := by
    dsimp only [c]
    exact (Real.sq_sqrt hpqNonneg).symm
  have hAimageClosed : IsClosed (e '' A) :=
    e.toHomeomorph.isClosedMap A hAclosed
  have hAimageConv : Convexity.IsConvexSet ℝ (e '' A) := by
    refine Convexity.IsConvexSet.of_convexCombPair_mem ?_
    intro a b ha hb hab x hx y hy
    obtain ⟨x, hxA, rfl⟩ := hx
    obtain ⟨y, hyA, rfl⟩ := hy
    refine ⟨Convexity.convexCombPair a b ha hb hab x y,
      hAconv.convexCombPair_mem hxA hyA ha hb hab, ?_⟩
    rw [Convexity.convexCombPair_eq_sum,
      Convexity.convexCombPair_eq_sum, map_add, map_smul, map_smul]
  have htransport :=
    map_continuousLinearEquiv_symm_closedShell_le
      (ν := T) e A hAclosed hAconv hδ
  have hmixture :=
    map_prod_affineGaussianNoise_closedShell_le
      (ν := ν) hD hbound hc hpq (e '' A) hAimageClosed hAimageConv
        (mul_nonneg (norm_nonneg e.toContinuousLinearMap) hδ)
  change (T.map e.symm).real
      (Metric.cthickening δ A \ interior A) ≤
    ballGaussianPerimeterConstant d *
        (‖e.toContinuousLinearMap‖ * δ / c) + 4 * D
  exact htransport.trans (by
    simpa only [T, p, q, γ, ν] using hmixture)

/-- A shell estimate that is uniform over closed convex sets is automatically uniform over
translations of the random vector. -/
private theorem uniform_translated_closedShell_le
    {d : ℕ} {ν : Measure (EuclideanSpace ℝ (Fin d))} {δ J : ℝ}
    (hbound : ∀ B : Set (EuclideanSpace ℝ (Fin d)), IsClosed B →
      Convexity.IsConvexSet ℝ B →
      ν.real (Metric.cthickening δ B \ interior B) ≤ J)
    (A : Set (EuclideanSpace ℝ (Fin d))) (hAclosed : IsClosed A)
    (hAconv : Convexity.IsConvexSet ℝ A) :
    ∀ z, ν.real ((fun a ↦ a + z) ⁻¹'
      (Metric.cthickening δ A \ interior A)) ≤ J := by
  intro (z : EuclideanSpace ℝ (Fin d))
  let B : Set (EuclideanSpace ℝ (Fin d)) := (-z) +ᵥ A
  have hBclosed : IsClosed B := by
    dsimp only [B]
    rw [← Set.image_vadd]
    exact (Homeomorph.addLeft (-z)).isClosedMap A hAclosed
  have hBconv : Convexity.IsConvexSet ℝ B := by
    dsimp only [B]
    exact vadd_isConvexSet hAconv (-z)
  have hshell :
      (fun a ↦ a + z) ⁻¹' (Metric.cthickening δ A \ interior A) =
        Metric.cthickening δ B \ interior B := by
    dsimp only [B]
    rw [cthickening_vadd, interior_vadd]
    ext a
    simp only [Set.mem_preimage, Set.mem_sdiff, mem_vadd_set_iff_neg_vadd_mem,
      vadd_eq_add, neg_neg]
    constructor <;> intro h
    · simpa only [add_comm] using h
    · simpa only [add_comm] using h
  rw [hshell]
  exact hbound B hBclosed hBconv

/-- The concrete split-Gaussian shell bound is uniform under arbitrary deterministic
translations, as required by the conditional Fubini estimate in Bentkus (3.32)--(3.33). -/
theorem bentkus_splitGaussianBase_uniform_translated_closedShell_le_of_induction
    {C : ℝ} (hC : 0 ≤ C) {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hIH : bentkusIdentityCovarianceBoundAt.{u} C n)
    (hd : 0 < d) (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (α : ℝ) (hcos : 0 < Real.cos α)
    (A : Set (EuclideanSpace ℝ (Fin d))) (hAclosed : IsClosed A)
    (hAconv : Convexity.IsConvexSet ℝ A) {δ : ℝ} (hδ : 0 ≤ δ) :
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let U := bentkusLeaveOneOut X k
    let ν := μ.map (fun ω ↦ e (U ω))
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let θ := (Real.sqrt 2)⁻¹
    let p := Real.cos α
    let q := θ * Real.sin α
    let c := Real.sqrt (p ^ 2 + q ^ 2)
    let T := ((γ.map (fun x ↦ q • x)).prod ν).map
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        p • z.2 + z.1)
    let D := C * (d : ℝ) ^ (1 / 4 : ℝ) *
      ∑ i : Fin n, ∫ ω,
        ‖bentkusWhiteningCLM S (X (k.succAbove i) ω)‖ ^ 3 ∂μ
    ∀ z, (T.map e.symm).real ((fun a ↦ a + z) ⁻¹'
        (Metric.cthickening δ A \ interior A)) ≤
      ballGaussianPerimeterConstant d *
          (‖e.toContinuousLinearMap‖ * δ / c) + 4 * D := by
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let U := bentkusLeaveOneOut X k
  let ν := μ.map (fun ω ↦ e (U ω))
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let θ := (Real.sqrt 2)⁻¹
  let p := Real.cos α
  let q := θ * Real.sin α
  let c := Real.sqrt (p ^ 2 + q ^ 2)
  let T := ((γ.map (fun x ↦ q • x)).prod ν).map
    (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      p • z.2 + z.1)
  let D := C * (d : ℝ) ^ (1 / 4 : ℝ) *
    ∑ i : Fin n, ∫ ω,
      ‖bentkusWhiteningCLM S (X (k.succAbove i) ω)‖ ^ 3 ∂μ
  refine uniform_translated_closedShell_le
    (ν := T.map e.symm) (δ := δ)
    (J := ballGaussianPerimeterConstant d *
      (‖e.toContinuousLinearMap‖ * δ / c) + 4 * D)
    ?_ A hAclosed hAconv
  intro B hBclosed hBconv
  simpa only [S, hS, e, U, ν, γ, θ, p, q, c, T, D] using
    bentkus_splitGaussianBase_closedShell_le_of_induction
      hC hIH hd hXm hX3 h_indep hX0 hidentity k hk α hcos
        B hBclosed hBconv hδ

/-- Dimension-normalized form of the translated split-Gaussian shell bound.  Whitening costs
`8` in the third moments, unwhitening costs `2` in shell width, and the half-Gaussian
normalization is bounded below by `1 / 2`; the resulting conservative constant is `32`. -/
theorem
    bentkus_splitGaussianBase_uniform_translated_closedShell_normalized_le_of_induction
    {C : ℝ} (hC : 0 ≤ C) {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hIH : bentkusIdentityCovarianceBoundAt.{u} C n)
    (hd : 0 < d) (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (α : ℝ) (hcos : 0 < Real.cos α)
    (A : Set (EuclideanSpace ℝ (Fin d))) (hAclosed : IsClosed A)
    (hAconv : Convexity.IsConvexSet ℝ A) {ε : ℝ} (hε : 0 ≤ ε) :
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let U := bentkusLeaveOneOut X k
    let ν := μ.map (fun ω ↦ e (U ω))
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let θ := (Real.sqrt 2)⁻¹
    let p := Real.cos α
    let q := θ * Real.sin α
    let T := ((γ.map (fun y ↦ q • y)).prod ν).map
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        p • z.2 + z.1)
    let β := ∑ i : Fin n, ∫ ω, ‖X (k.succAbove i) ω‖ ^ 3 ∂μ
    ∀ z : EuclideanSpace ℝ (Fin d),
      (T.map e.symm).real ((fun a : EuclideanSpace ℝ (Fin d) ↦ a + z) ⁻¹'
        (Metric.cthickening ε A \ interior A)) ≤
      32 * (d : ℝ) ^ (1 / 4 : ℝ) * (C * β + ε) := by
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let U := bentkusLeaveOneOut X k
  let ν := μ.map (fun ω ↦ e (U ω))
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let θ := (Real.sqrt 2)⁻¹
  let p := Real.cos α
  let q := θ * Real.sin α
  let c := Real.sqrt (p ^ 2 + q ^ 2)
  let T := ((γ.map (fun y ↦ q • y)).prod ν).map
    (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      p • z.2 + z.1)
  let β := ∑ i : Fin n, ∫ ω, ‖X (k.succAbove i) ω‖ ^ 3 ∂μ
  let βw := ∑ i : Fin n, ∫ ω,
    ‖bentkusWhiteningCLM S (X (k.succAbove i) ω)‖ ^ 3 ∂μ
  let D := C * (d : ℝ) ^ (1 / 4 : ℝ) * βw
  have hp : 0 < p := by simpa only [p] using hcos
  have hc : 0 < c := by
    dsimp only [c]
    exact Real.sqrt_pos.2 (by
      have hp2 : 0 < p ^ 2 := sq_pos_of_pos hp
      nlinarith [sq_nonneg q])
  have hθsq : θ ^ 2 = (1 / 2 : ℝ) := by
    have hsqrtSq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by norm_num
    dsimp only [θ]
    rw [inv_pow, hsqrtSq]
    norm_num
  have hpqHalf : (1 / 2 : ℝ) ≤ p ^ 2 + q ^ 2 := by
    dsimp only [p, q]
    rw [mul_pow, hθsq]
    nlinarith [Real.cos_sq_add_sin_sq α, sq_nonneg (Real.cos α)]
  have hcSq : c ^ 2 = p ^ 2 + q ^ 2 := by
    dsimp only [c]
    exact Real.sq_sqrt (by positivity)
  have hcHalf : (1 / 2 : ℝ) ≤ c := by
    by_contra hnot
    have hlt : c < 1 / 2 := lt_of_not_ge hnot
    nlinarith [hcSq, hpqHalf, sq_nonneg c]
  have heNorm : ‖e.toContinuousLinearMap‖ ≤ 2 := by
    simpa only [e, S] using
      norm_bentkusWhiteningEquiv_leaveOneOut_le_two
        hX3 h_indep hX0 hidentity k hk hS
  have hratio : ‖e.toContinuousLinearMap‖ * ε / c ≤ 4 * ε := by
    apply (div_le_iff₀ hc).2
    calc
      ‖e.toContinuousLinearMap‖ * ε ≤ 2 * ε :=
        mul_le_mul_of_nonneg_right heNorm hε
      _ ≤ (4 * ε) * c := by
        have htwo : (2 : ℝ) ≤ 4 * c := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right htwo hε]
  have hmom : βw ≤ 8 * β := by
    dsimp only [βw, β]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦
      integral_norm_bentkusWhiteningCLM_leaveOneOut_pow_three_le
        hX3 h_indep hX0 hidentity k hk (hX3 (k.succAbove i))
  have hdim : 0 ≤ (d : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hβ : 0 ≤ β := by
    dsimp only [β]
    exact Finset.sum_nonneg fun i _ ↦
      integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg _) 3
  have hβw : 0 ≤ βw := by
    dsimp only [βw]
    exact Finset.sum_nonneg fun i _ ↦
      integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg _) 3
  have hshell := bentkus_splitGaussianBase_uniform_translated_closedShell_le_of_induction
    hC hIH hd hXm hX3 h_indep hX0 hidentity k hk α hcos
      A hAclosed hAconv hε
  dsimp only
  intro (z : EuclideanSpace ℝ (Fin d))
  have hGaussian :
      ballGaussianPerimeterConstant d *
          (‖e.toContinuousLinearMap‖ * ε / c) ≤
        16 * (d : ℝ) ^ (1 / 4 : ℝ) * ε := by
    unfold ballGaussianPerimeterConstant
    calc
      (4 * (d : ℝ) ^ (1 / 4 : ℝ)) *
          (‖e.toContinuousLinearMap‖ * ε / c) ≤
        (4 * (d : ℝ) ^ (1 / 4 : ℝ)) * (4 * ε) :=
          mul_le_mul_of_nonneg_left hratio (mul_nonneg (by norm_num) hdim)
      _ = 16 * (d : ℝ) ^ (1 / 4 : ℝ) * ε := by ring
  have hInduction :
      4 * D ≤ 32 * C * (d : ℝ) ^ (1 / 4 : ℝ) * β := by
    dsimp only [D]
    calc
      4 * (C * (d : ℝ) ^ (1 / 4 : ℝ) * βw) ≤
          4 * (C * (d : ℝ) ^ (1 / 4 : ℝ) * (8 * β)) := by
        gcongr
      _ = 32 * C * (d : ℝ) ^ (1 / 4 : ℝ) * β := by ring
  calc
    (T.map e.symm).real ((fun a ↦ a + z) ⁻¹'
        (Metric.cthickening ε A \ interior A)) ≤
      ballGaussianPerimeterConstant d *
          (‖e.toContinuousLinearMap‖ * ε / c) + 4 * D := by
        simpa only [S, hS, e, U, ν, γ, θ, p, q, c, T, D, βw] using hshell z
    _ ≤ 16 * (d : ℝ) ^ (1 / 4 : ℝ) * ε +
        32 * C * (d : ℝ) ^ (1 / 4 : ℝ) * β :=
      add_le_add hGaussian hInduction
    _ ≤ 32 * (d : ℝ) ^ (1 / 4 : ℝ) * (C * β + ε) := by
      nlinarith [mul_nonneg hdim hε,
        mul_nonneg (mul_nonneg hC hdim) hβ]

end BentkusInduction

end ProbabilityTheory
