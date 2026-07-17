/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.Bentkus.SmoothingInequality
import ProbabilityApproximation.Bentkus.GaussianDensityIntegrationByParts

/-!
# Gaussian integration by parts for a pulled-back cutoff derivative

This module isolates the deterministic integration-by-parts input in Bentkus (2004), equation
(3.32), p. 407.  A directional derivative of the convex-set cutoff is pulled back along an affine
linear Gaussian coordinate.  The exact `8 / ε²` Lipschitz estimate for the cutoff derivative then
feeds the Gaussian density integration-by-parts theorem.
-/

open MeasureTheory
open Filter Topology
open scoped RealInnerProductSpace Topology

noncomputable section

namespace ProbabilityTheory

local instance instConvexSpaceRealEuclideanSpaceFin_cutoffDerivativeGaussianIBP {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

local instance instIsModuleConvexSpaceRealEuclideanSpaceFin_cutoffDerivativeGaussianIBP {d : ℕ} :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.ofModule

/-- The directional derivative of the Bentkus cutoff after an affine linear pullback. -/
def convexSetCutoffDirectionalPullback {d : ℕ}
    (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (a x : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun u ↦ (fderiv ℝ (convexSetCutoff s ε) (a + L u)) x

/-- Pulling a cutoff derivative back by `u ↦ a + L u` multiplies its Lipschitz constant by
`‖L‖`; evaluation in direction `x` contributes `‖x‖`. -/
theorem lipschitzWith_convexSetCutoffDirectionalPullback {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε)
    (a x : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    LipschitzWith
      ⟨(8 / ε ^ 2) * ‖L‖ * ‖x‖,
        mul_nonneg (mul_nonneg (div_nonneg (by norm_num) (sq_nonneg ε)) (norm_nonneg L))
          (norm_nonneg x)⟩
      (convexSetCutoffDirectionalPullback s ε a x L) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro u v
  change ‖(fderiv ℝ (convexSetCutoff s ε) (a + L u)) x -
      (fderiv ℝ (convexSetCutoff s ε) (a + L v)) x‖ ≤
    ((8 / ε ^ 2) * ‖L‖ * ‖x‖) * ‖u - v‖
  let p := a + L u
  let q := a + L v
  have hderiv := norm_fderiv_convexSetCutoff_sub_le hs hε p q
  have happly :
      ‖(fderiv ℝ (convexSetCutoff s ε) p -
          fderiv ℝ (convexSetCutoff s ε) q) x‖ ≤
        ‖fderiv ℝ (convexSetCutoff s ε) p -
          fderiv ℝ (convexSetCutoff s ε) q‖ * ‖x‖ :=
    ContinuousLinearMap.le_opNorm _ x
  have hL : ‖L (u - v)‖ ≤ ‖L‖ * ‖u - v‖ := L.le_opNorm (u - v)
  change ‖(fderiv ℝ (convexSetCutoff s ε) p) x -
      (fderiv ℝ (convexSetCutoff s ε) q) x‖ ≤
    ((8 / ε ^ 2) * ‖L‖ * ‖x‖) * ‖u - v‖
  calc
    ‖(fderiv ℝ (convexSetCutoff s ε) p) x -
        (fderiv ℝ (convexSetCutoff s ε) q) x‖ =
        ‖(fderiv ℝ (convexSetCutoff s ε) p -
          fderiv ℝ (convexSetCutoff s ε) q) x‖ := by
      rw [sub_apply]
    _ ≤ ‖fderiv ℝ (convexSetCutoff s ε) p -
          fderiv ℝ (convexSetCutoff s ε) q‖ * ‖x‖ := happly
    _ ≤ (8 * ‖p - q‖ / ε ^ 2) * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right hderiv (norm_nonneg x)
    _ = (8 / ε ^ 2) * ‖L (u - v)‖ * ‖x‖ := by
      rw [show p - q = L (u - v) by simp [p, q, map_sub]]
      ring
    _ ≤ (8 / ε ^ 2) * (‖L‖ * ‖u - v‖) * ‖x‖ := by
      gcongr
    _ = ((8 / ε ^ 2) * ‖L‖ * ‖x‖) * ‖u - v‖ := by ring

/-- The pulled-back cutoff derivative is supported on the closed outer shell.  The inner set is
removed only through its interior: boundary points can belong to the topological support even
though the derivative itself vanishes there.  This is the support convention needed in Bentkus
(2004), equation (3.32), p. 407. -/
theorem tsupport_convexSetCutoffDirectionalPullback_subset {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))}
    (hsclosed : IsClosed s) (_hs : Convexity.IsConvexSet ℝ s)
    {ε : ℝ} (hε : 0 < ε)
    (a x : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    tsupport (convexSetCutoffDirectionalPullback s ε a x L) ⊆
      (fun u ↦ a + L u) ⁻¹' (Metric.cthickening ε s \ interior s) := by
  let T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun u ↦ a + L u
  have hT : Continuous T := continuous_const.add L.continuous
  have htarget : IsClosed (T ⁻¹' (Metric.cthickening ε s \ interior s)) :=
    (Metric.isClosed_cthickening.sdiff isOpen_interior).preimage hT
  rw [tsupport]
  refine closure_minimal ?_ htarget
  intro u hu
  change T u ∈ Metric.cthickening ε s \ interior s
  constructor
  · by_contra hout
    have hnhds : (Metric.cthickening ε s)ᶜ ∈ 𝓝 (T u) :=
      Metric.isClosed_cthickening.isOpen_compl.mem_nhds hout
    have hevent : convexSetCutoff s ε =ᶠ[𝓝 (T u)] fun _ ↦ (0 : ℝ) := by
      filter_upwards [hnhds] with y hy
      apply convexSetCutoff_eq_zero_of_notMem_cthickening hε
      have hy' : y ∉ Metric.cthickening ε s := by
        exact hy
      simpa only [hsclosed.closure_eq] using hy'
    have hfderiv : fderiv ℝ (convexSetCutoff s ε) (T u) = 0 :=
      (hasFDerivAt_zero_of_eventually_const (0 : ℝ) hevent).fderiv
    apply hu
    simp [convexSetCutoffDirectionalPullback, T, hfderiv]
  · intro hin
    have hnhds : s ∈ 𝓝 (T u) := mem_interior_iff_mem_nhds.mp hin
    have hevent : convexSetCutoff s ε =ᶠ[𝓝 (T u)] fun _ ↦ (1 : ℝ) := by
      filter_upwards [hnhds] with y hy
      exact convexSetCutoff_eq_one_of_mem hy
    have hfderiv : fderiv ℝ (convexSetCutoff s ε) (T u) = 0 :=
      (hasFDerivAt_zero_of_eventually_const (1 : ℝ) hevent).fderiv
    apply hu
    simp [convexSetCutoffDirectionalPullback, T, hfderiv]

/-- Bentkus's Gaussian density integration-by-parts bound for the affine pullback of a cutoff
directional derivative.  This is the deterministic core of equation (3.32), p. 407. -/
theorem convexSetCutoffDirectionalPullback_D2_bound {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε)
    (a x : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (w h : EuclideanSpace ℝ (Fin d)) :
    |∫ u, convexSetCutoffDirectionalPullback s ε a x L u *
        standardGaussianDensityD2 u w h| ≤
      ((8 / ε ^ 2) * ‖L‖ * ‖x‖) * ‖h‖ *
        ∫ u in tsupport (convexSetCutoffDirectionalPullback s ε a x L),
          |standardGaussianDensityD1 u w| := by
  have hbound :=
    bentkus_lipschitz_standardGaussianDensityD1_integral_D2_bound
      (lipschitzWith_convexSetCutoffDirectionalPullback hs hε a x L) w h
  change |∫ u, convexSetCutoffDirectionalPullback s ε a x L u *
      standardGaussianDensityD2 u w h| ≤
    ((8 / ε ^ 2) * ‖L‖ * ‖x‖) * ‖h‖ *
      ∫ u in tsupport (convexSetCutoffDirectionalPullback s ε a x L),
        |standardGaussianDensityD1 u w| at hbound
  exact hbound

/-- The integration-by-parts estimate with the topological support replaced by the explicit
closed shell.  This is the form inserted into the leave-one-out shell probabilities in Bentkus
(2004), equations (3.30)--(3.34), pp. 407--408. -/
theorem convexSetCutoffDirectionalPullback_D2_shell_bound {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))}
    (hsclosed : IsClosed s) (hs : Convexity.IsConvexSet ℝ s)
    {ε : ℝ} (hε : 0 < ε)
    (a x : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (w h : EuclideanSpace ℝ (Fin d)) :
    |∫ u, convexSetCutoffDirectionalPullback s ε a x L u *
        standardGaussianDensityD2 u w h| ≤
      ((8 / ε ^ 2) * ‖L‖ * ‖x‖) * ‖h‖ *
        ∫ u in (fun u ↦ a + L u) ⁻¹'
            (Metric.cthickening ε s \ interior s),
          |standardGaussianDensityD1 u w| := by
  have hsupp := tsupport_convexSetCutoffDirectionalPullback_subset
    hsclosed hs hε a x L
  have hmono :
      (∫ u in tsupport (convexSetCutoffDirectionalPullback s ε a x L),
          |standardGaussianDensityD1 u w|) ≤
        ∫ u in (fun u ↦ a + L u) ⁻¹'
            (Metric.cthickening ε s \ interior s),
          |standardGaussianDensityD1 u w| := by
    apply setIntegral_mono_set
    · exact (integrable_standardGaussianDensityD1_volume w).abs.integrableOn
    · exact Eventually.of_forall fun u ↦ abs_nonneg _
    · exact hsupp.eventuallyLE
  calc
    |∫ u, convexSetCutoffDirectionalPullback s ε a x L u *
        standardGaussianDensityD2 u w h| ≤
        ((8 / ε ^ 2) * ‖L‖ * ‖x‖) * ‖h‖ *
          ∫ u in tsupport (convexSetCutoffDirectionalPullback s ε a x L),
            |standardGaussianDensityD1 u w| :=
      convexSetCutoffDirectionalPullback_D2_bound hs hε a x L w h
    _ ≤ ((8 / ε ^ 2) * ‖L‖ * ‖x‖) * ‖h‖ *
        ∫ u in (fun u ↦ a + L u) ⁻¹'
            (Metric.cthickening ε s \ interior s),
          |standardGaussianDensityD1 u w| := by
      exact mul_le_mul_of_nonneg_left hmono (by positivity)

end ProbabilityTheory
