/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.ConvexGeometry.GaussianShell
import ProbabilityApproximation.ConvexGeometry.ScalarCoarea

/-!
# Signed-distance coarea for Gaussian convex shells

This module composes the global weighted scalar coarea formula with the almost-everywhere eikonal
identity for convex signed distance.  It identifies outer and inner standard-Gaussian shell masses
with integrals of their Gaussian boundary profiles.  These identities are the exact interface
between Ball's Gaussian perimeter estimate and the shell bounds used by Bentkus.
-/

open Set MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

local instance gaussianShellCoareaConvexSpace {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

local instance gaussianShellCoareaIsModuleConvexSpace {d : ℕ} :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.ofModule

private def gaussianCoareaWeight {d : ℕ}
    (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ENNReal.ofReal (standardGaussianDensityReal x)

private lemma measurable_gaussianCoareaWeight {d : ℕ} :
    Measurable (gaussianCoareaWeight (d := d)) :=
  measurable_standardGaussianDensityReal.ennreal_ofReal

private lemma scalarCoareaFiber_setSignedDistance_eq_outerProfile {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hne : s.Nonempty)
    (hs : Convexity.IsConvexSet ℝ s) {t : ℝ} (ht : 0 < t) :
    scalarCoareaFiber (setSignedDistance s) gaussianCoareaWeight t =
      outerGaussianBoundaryProfile s t := by
  rw [outerGaussianBoundaryProfile_eq_levelLIntegral hne hs ht]
  rfl

private lemma scalarCoareaFiber_setSignedDistance_eq_innerProfile {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hsne : s ≠ univ)
    {t : ℝ} (ht : t < 0) :
    scalarCoareaFiber (setSignedDistance s) gaussianCoareaWeight t =
      innerGaussianBoundaryProfile s t := by
  rw [innerGaussianBoundaryProfile_eq_levelLIntegral hsne ht]
  rfl

/-- The outer Gaussian shell is the scalar-coarea integral of the outer parallel-frontier
profile.  This is Raič's positive signed-distance disintegration with Mathlib's normalized
Euclidean Hausdorff measure. -/
theorem stdGaussian_outer_shell_eq_lintegral_outerGaussianBoundaryProfile {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hne : s.Nonempty) (hsne : s ≠ univ)
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 ≤ ε) :
    stdGaussian (EuclideanSpace ℝ (Fin d))
        (Metric.cthickening ε (closure s) \ s) =
      ∫⁻ t in Ioc (0 : ℝ) ε, outerGaussianBoundaryProfile s t := by
  rw [stdGaussian_outer_shell_eq_signedDistance_slab hne hs hε,
    stdGaussian_eq_withDensity_standardGaussianDensityReal,
    withDensity_apply _
      (measurableSet_lipschitz_slab (setSignedDistance_lipschitzWith_two s) 0 ε)]
  change (∫⁻ x in setSignedDistance s ⁻¹' Ioc (0 : ℝ) ε,
      gaussianCoareaWeight x ∂volume) = _
  rw [LipschitzWith.setLIntegral_slab_of_ae_norm_fderiv_eq_one
    (setSignedDistance_lipschitzWith_two s)
    gaussianCoareaWeight measurable_gaussianCoareaWeight 0 ε
    (ae_norm_fderiv_setSignedDistance_eq_one hne hsne hs)]
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro t ht
  exact scalarCoareaFiber_setSignedDistance_eq_outerProfile hne hs ht.1

/-- The inner Gaussian shell is the scalar-coarea integral of the negative parallel-frontier
profile.  The integration variable retains the signed-distance convention `t ∈ (-ε, 0]`. -/
theorem stdGaussian_inner_shell_eq_lintegral_innerGaussianBoundaryProfile {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hne : s.Nonempty) (hsne : s ≠ univ)
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (_hε : 0 ≤ ε) :
    stdGaussian (EuclideanSpace ℝ (Fin d))
        (s \ convexInnerParallel s ε) =
      ∫⁻ t in Ioc (-ε) 0, innerGaussianBoundaryProfile s t := by
  rw [stdGaussian_inner_shell_eq_signedDistance_slab hne hsne hs ε,
    stdGaussian_eq_withDensity_standardGaussianDensityReal,
    withDensity_apply _
      (measurableSet_lipschitz_slab (setSignedDistance_lipschitzWith_two s) (-ε) 0)]
  change (∫⁻ x in setSignedDistance s ⁻¹' Ioc (-ε) (0 : ℝ),
      gaussianCoareaWeight x ∂volume) = _
  rw [LipschitzWith.setLIntegral_slab_of_ae_norm_fderiv_eq_one
    (setSignedDistance_lipschitzWith_two s)
    gaussianCoareaWeight measurable_gaussianCoareaWeight (-ε) 0
    (ae_norm_fderiv_setSignedDistance_eq_one hne hsne hs)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (Measure.ae_ne (volume : Measure ℝ) 0)] with t ht ht0
  exact scalarCoareaFiber_setSignedDistance_eq_innerProfile hsne (lt_of_le_of_ne ht.2 ht0)

/-- A uniform Gaussian boundary-content estimate for convex sets implies both Gaussian shell
bounds with the same constant.  This theorem is the final coarea composition used after Ball's
perimeter theorem; it contains no convex-boundary geometry of its own. -/
theorem stdGaussian_shell_pair_le_ball_of_boundaryContent {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hne : s.Nonempty) (hsne : s ≠ univ)
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 ≤ ε)
    (hboundary : ∀ t : Set (EuclideanSpace ℝ (Fin d)),
      Convexity.IsConvexSet ℝ t →
        standardGaussianBoundaryContent t ≤
          ENNReal.ofReal (ballGaussianPerimeterConstant d)) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).real
          (Metric.cthickening ε (closure s) \ s) ≤
        ballGaussianPerimeterConstant d * ε ∧
      (stdGaussian (EuclideanSpace ℝ (Fin d))).real
          (s \ convexInnerParallel s ε) ≤
        ballGaussianPerimeterConstant d * ε := by
  have hK : 0 ≤ ballGaussianPerimeterConstant d := by
    unfold ballGaussianPerimeterConstant
    positivity
  have hOuterCoarea :=
    stdGaussian_outer_shell_eq_lintegral_outerGaussianBoundaryProfile hne hsne hs hε
  have hInnerCoarea :=
    stdGaussian_inner_shell_eq_lintegral_innerGaussianBoundaryProfile hne hsne hs hε
  have hOuterBound : ∀ t ∈ Ioc (0 : ℝ) ε,
      outerGaussianBoundaryProfile s t ≤
        ENNReal.ofReal (ballGaussianPerimeterConstant d) := by
    intro t ht
    exact hboundary (Metric.cthickening t (closure s))
      (cthickening_isConvexSet (closure_isConvexSet hs) ht.1.le)
  have hInnerBound : ∀ t ∈ Ioc (-ε) (0 : ℝ),
      innerGaussianBoundaryProfile s t ≤
        ENNReal.ofReal (ballGaussianPerimeterConstant d) := by
    intro t _ht
    exact hboundary (convexInnerParallel s (-t))
      (convexInnerParallel_isConvexSet hs (-t))
  constructor
  · change (stdGaussian (EuclideanSpace ℝ (Fin d))
        (Metric.cthickening ε (closure s) \ s)).toReal ≤
      ballGaussianPerimeterConstant d * ε
    apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg hK hε)
    simpa only [sub_zero] using
      (measure_le_of_lintegral_Ioc
        (stdGaussian (EuclideanSpace ℝ (Fin d)))
        (Metric.cthickening ε (closure s) \ s) hK hOuterCoarea hOuterBound)
  · change (stdGaussian (EuclideanSpace ℝ (Fin d))
        (s \ convexInnerParallel s ε)).toReal ≤
      ballGaussianPerimeterConstant d * ε
    apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg hK hε)
    simpa only [sub_neg_eq_add, zero_add] using
      (measure_le_of_lintegral_Ioc
        (stdGaussian (EuclideanSpace ℝ (Fin d)))
        (s \ convexInnerParallel s ε) hK hInnerCoarea hInnerBound)

end ProbabilityTheory
