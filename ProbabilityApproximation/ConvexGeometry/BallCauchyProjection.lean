/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.ConvexGeometry.BallProjectionArea
import ProbabilityApproximation.ConvexGeometry.BallSphereHausdorff

/-!
# Cauchy's projection formula for the Euclidean sphere

This module proves the fixed-direction weighted Cauchy projection formula used in Keith Ball's
Gaussian-perimeter argument.  The sphere carries its intrinsic codimension-one Euclidean
Hausdorff measure.  For a unit direction `v`, orthogonal projection maps each strict hemisphere
onto the open unit ball in `v⊥`; the projection Jacobian cancels the absolute normal component.
Summing the two hemispheres gives

`∫ g(P_v θ) |<θ,v>| dH^(d-1)(θ) = 2 ∫_{B(v⊥)} g(z) dz`.

The proof uses the supporting-normal projection charts from `BallProjectionArea`.  It does not
identify Hausdorff surface measure with Mathlib's independently constructed `Measure.toSphere`.
-/

open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory


private lemma unit_supportingNormal_closedBall_eq_self {d : ℕ}
    {x u : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1)
    (hu : ‖u‖ = 1)
    (hsupport : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
      inner ℝ (y - x) u ≤ 0) :
    u = x := by
  have hxnorm : ‖x‖ = 1 := by
    simpa [Metric.mem_sphere] using hx
  have huC : u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
    simp [Metric.mem_closedBall, hu]
  have hinner_lower := hsupport u huC
  rw [inner_sub_left, real_inner_self_eq_norm_sq, hu, one_pow] at hinner_lower
  have hinner_upper : inner ℝ x u ≤ 1 := by
    calc
      inner ℝ x u ≤ |inner ℝ x u| := le_abs_self _
      _ ≤ ‖x‖ * ‖u‖ := abs_real_inner_le_norm x u
      _ = 1 := by rw [hxnorm, hu, one_mul]
  have hinner : inner ℝ x u = 1 := le_antisymm hinner_upper (by linarith)
  have hnormsq : ‖u - x‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq,
      hu, hxnorm, one_pow]
    rw [show inner ℝ u x = 1 by simpa [real_inner_comm] using hinner]
    linarith
  have hnorm : ‖u - x‖ = 0 := sq_eq_zero_iff.mp hnormsq
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

private lemma self_supportingNormal_closedBall {d : ℕ}
    {x : EuclideanSpace ℝ (Fin d)} (hx : ‖x‖ = 1) :
    ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
      inner ℝ (y - x) x ≤ 0 := by
  intro y hy
  have hynorm : ‖y‖ ≤ 1 := by
    simpa [Metric.mem_closedBall] using hy
  have hinner : inner ℝ y x ≤ 1 := by
    calc
      inner ℝ y x ≤ |inner ℝ y x| := le_abs_self _
      _ ≤ ‖y‖ * ‖x‖ := abs_real_inner_le_norm y x
      _ ≤ 1 := by rw [hx, mul_one]; exact hynorm
  rw [inner_sub_left, real_inner_self_eq_norm_sq, hx, one_pow]
  linarith

private lemma mem_positiveSupportingNormalPatch_closedBall_iff {d : ℕ}
    {v x : EuclideanSpace ℝ (Fin d)} {a : ℝ} :
    x ∈ positiveSupportingNormalPatch
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) v a ↔
      x ∈ Metric.sphere 0 1 ∧ a ≤ inner ℝ v x := by
  constructor
  · intro hx
    obtain ⟨u, hfrontier, hu, hsupport, ha⟩ :=
      mem_positiveSupportingNormalPatch.mp hx
    have hxsphere : x ∈ Metric.sphere 0 1 := by
      simpa [frontier_closedBall (0 : EuclideanSpace ℝ (Fin d)) one_ne_zero]
        using hfrontier
    have hux := unit_supportingNormal_closedBall_eq_self hxsphere hu hsupport
    exact ⟨hxsphere, by simpa [hux] using ha⟩
  · rintro ⟨hxsphere, ha⟩
    have hxnorm : ‖x‖ = 1 := by simpa [Metric.mem_sphere] using hxsphere
    apply mem_positiveSupportingNormalPatch.mpr
    refine ⟨x, ?_, hxnorm, self_supportingNormal_closedBall hxnorm, ha⟩
    simpa [frontier_closedBall (0 : EuclideanSpace ℝ (Fin d)) one_ne_zero]
      using hxsphere

private lemma mem_negativeSupportingNormalPatch_closedBall_iff {d : ℕ}
    {v x : EuclideanSpace ℝ (Fin d)} {a : ℝ} :
    x ∈ negativeSupportingNormalPatch
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) v a ↔
      x ∈ Metric.sphere 0 1 ∧ inner ℝ v x ≤ -a := by
  constructor
  · intro hx
    obtain ⟨u, hfrontier, hu, hsupport, ha⟩ :=
      mem_negativeSupportingNormalPatch.mp hx
    have hxsphere : x ∈ Metric.sphere 0 1 := by
      simpa [frontier_closedBall (0 : EuclideanSpace ℝ (Fin d)) one_ne_zero]
        using hfrontier
    have hux := unit_supportingNormal_closedBall_eq_self hxsphere hu hsupport
    exact ⟨hxsphere, by simpa [hux] using ha⟩
  · rintro ⟨hxsphere, ha⟩
    have hxnorm : ‖x‖ = 1 := by simpa [Metric.mem_sphere] using hxsphere
    apply mem_negativeSupportingNormalPatch.mpr
    refine ⟨x, ?_, hxnorm, self_supportingNormal_closedBall hxnorm, ha⟩
    simpa [frontier_closedBall (0 : EuclideanSpace ℝ (Fin d)) one_ne_zero]
      using hxsphere

private lemma norm_orthogonalProjectionOnto_sq_eq_sub_inner_sq {d : ℕ}
    {v x : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) :
    ‖((ℝ ∙ v)ᗮ).orthogonalProjectionOnto x‖ ^ 2 =
      ‖x‖ ^ 2 - inner ℝ x v ^ 2 := by
  have hpyth := Submodule.norm_sq_eq_add_norm_sq_projection x (ℝ ∙ v)
  have hspan : ‖(ℝ ∙ v).orthogonalProjectionOnto x‖ ^ 2 =
      inner ℝ x v ^ 2 := by
    change ‖(ℝ ∙ v).starProjection x‖ ^ 2 = _
    rw [Submodule.starProjection_unit_singleton ℝ hv]
    rw [norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs]
    rw [real_inner_comm v x]
  rw [hspan] at hpyth
  linarith

private lemma projection_mem_ball_of_mem_sphere_inner_ne {d : ℕ}
    {v x : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1)
    (hinner : inner ℝ v x ≠ 0) :
    ((ℝ ∙ v)ᗮ).orthogonalProjectionOnto x ∈
      Metric.ball (0 : (ℝ ∙ v)ᗮ) 1 := by
  have hxnorm : ‖x‖ = 1 := by simpa [Metric.mem_sphere] using hx
  have hsq := norm_orthogonalProjectionOnto_sq_eq_sub_inner_sq hv (x := x)
  rw [hxnorm, one_pow] at hsq
  have hinner' : inner ℝ x v ≠ 0 := by simpa [real_inner_comm] using hinner
  have hinnerSq : 0 < inner ℝ x v ^ 2 := sq_pos_of_ne_zero hinner'
  rw [Metric.mem_ball, dist_zero_right]
  nlinarith [sq_nonneg ‖((ℝ ∙ v)ᗮ).orthogonalProjectionOnto x‖]

private lemma positiveSphereLift_mem_sphere {d : ℕ}
    {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    (z : (ℝ ∙ v)ᗮ) (hz : z ∈ Metric.ball 0 1) :
    z.1 + Real.sqrt (1 - ‖z‖ ^ 2) • v ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by
  have hzlt : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz
  have hsub : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have horth : inner ℝ z.1 v = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp z.2
  rw [Metric.mem_sphere, dist_zero_right, ← sq_eq_sq₀ (norm_nonneg _) (by norm_num)]
  rw [norm_add_sq_real, real_inner_smul_right, horth, mul_zero,
    norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs, Real.sq_sqrt hsub]
  rw [Submodule.coe_norm]
  ring

private lemma orthogonalProjectionOnto_positiveSphereLift {d : ℕ}
    {v : EuclideanSpace ℝ (Fin d)} (z : (ℝ ∙ v)ᗮ) :
    ((ℝ ∙ v)ᗮ).orthogonalProjectionOnto
        (z.1 + Real.sqrt (1 - ‖z‖ ^ 2) • v) = z := by
  rw [map_add, map_smul]
  simp

private lemma inner_positiveSphereLift {d : ℕ}
    {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    (z : (ℝ ∙ v)ᗮ) :
    inner ℝ v (z.1 + Real.sqrt (1 - ‖z‖ ^ 2) • v) =
      Real.sqrt (1 - ‖z‖ ^ 2) := by
  have horth : inner ℝ z.1 v = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp z.2
  have horth' : inner ℝ v z.1 = 0 := by simpa [real_inner_comm] using horth
  rw [inner_add_right, horth', zero_add,
    real_inner_smul_right, real_inner_self_eq_norm_sq, hv, one_pow, mul_one]

private lemma iUnion_image_positiveSupportingNormalPatch_closedBall_eq_ball {d : ℕ}
    {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) :
    (⋃ k : ℕ, ((ℝ ∙ v)ᗮ).orthogonalProjectionOnto ''
      positiveSupportingNormalPatch
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) v
        (1 / (k + 1 : ℝ))) =
      Metric.ball (0 : (ℝ ∙ v)ᗮ) 1 := by
  ext z
  constructor
  · intro hz
    obtain ⟨k, x, hxpatch, rfl⟩ := by
      simpa only [Set.mem_iUnion, Set.mem_image] using hz
    obtain ⟨hxsphere, hinner⟩ :=
      mem_positiveSupportingNormalPatch_closedBall_iff.mp hxpatch
    have hthreshold : 0 < (1 / (k + 1 : ℝ)) := by positivity
    exact projection_mem_ball_of_mem_sphere_inner_ne hv hxsphere
      (ne_of_gt (hthreshold.trans_le hinner))
  · intro hz
    let t : ℝ := Real.sqrt (1 - ‖z‖ ^ 2)
    let x : EuclideanSpace ℝ (Fin d) := z.1 + t • v
    have hzlt : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz
    have htpos : 0 < t := by
      dsimp only [t]
      apply Real.sqrt_pos.2
      nlinarith [norm_nonneg z]
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt htpos
    apply Set.mem_iUnion.mpr
    refine ⟨k, ⟨x, ?_, ?_⟩⟩
    · apply mem_positiveSupportingNormalPatch_closedBall_iff.mpr
      refine ⟨?_, ?_⟩
      · simpa only [x, t] using positiveSphereLift_mem_sphere hv z hz
      · simpa only [x, t] using hk.le.trans_eq (inner_positiveSphereLift hv z).symm
    · simpa only [x, t] using orthogonalProjectionOnto_positiveSphereLift z

private lemma negativeSphereLift_mem_sphere {d : ℕ}
    {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    (z : (ℝ ∙ v)ᗮ) (hz : z ∈ Metric.ball 0 1) :
    z.1 - Real.sqrt (1 - ‖z‖ ^ 2) • v ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by
  have hzlt : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz
  have hsub : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have horth : inner ℝ z.1 v = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp z.2
  rw [Metric.mem_sphere, dist_zero_right, ← sq_eq_sq₀ (norm_nonneg _) (by norm_num)]
  rw [norm_sub_sq_real, real_inner_smul_right, horth, mul_zero,
    norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs, Real.sq_sqrt hsub]
  rw [Submodule.coe_norm]
  ring

private lemma orthogonalProjectionOnto_negativeSphereLift {d : ℕ}
    {v : EuclideanSpace ℝ (Fin d)} (z : (ℝ ∙ v)ᗮ) :
    ((ℝ ∙ v)ᗮ).orthogonalProjectionOnto
        (z.1 - Real.sqrt (1 - ‖z‖ ^ 2) • v) = z := by
  rw [map_sub, map_smul]
  simp

private lemma inner_negativeSphereLift {d : ℕ}
    {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    (z : (ℝ ∙ v)ᗮ) :
    inner ℝ v (z.1 - Real.sqrt (1 - ‖z‖ ^ 2) • v) =
      -Real.sqrt (1 - ‖z‖ ^ 2) := by
  have horth : inner ℝ z.1 v = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp z.2
  have horth' : inner ℝ v z.1 = 0 := by simpa [real_inner_comm] using horth
  rw [inner_sub_right, horth', zero_sub,
    real_inner_smul_right, real_inner_self_eq_norm_sq, hv, one_pow, mul_one]

private lemma iUnion_image_negativeSupportingNormalPatch_closedBall_eq_ball {d : ℕ}
    {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) :
    (⋃ k : ℕ, ((ℝ ∙ v)ᗮ).orthogonalProjectionOnto ''
      negativeSupportingNormalPatch
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) v
        (1 / (k + 1 : ℝ))) =
      Metric.ball (0 : (ℝ ∙ v)ᗮ) 1 := by
  ext z
  constructor
  · intro hz
    obtain ⟨k, x, hxpatch, rfl⟩ := by
      simpa only [Set.mem_iUnion, Set.mem_image] using hz
    obtain ⟨hxsphere, hinner⟩ :=
      mem_negativeSupportingNormalPatch_closedBall_iff.mp hxpatch
    have hthreshold : 0 < (1 / (k + 1 : ℝ)) := by positivity
    apply projection_mem_ball_of_mem_sphere_inner_ne hv hxsphere
    exact ne_of_lt (hinner.trans_lt (neg_neg_of_pos hthreshold))
  · intro hz
    let t : ℝ := Real.sqrt (1 - ‖z‖ ^ 2)
    let x : EuclideanSpace ℝ (Fin d) := z.1 - t • v
    have hzlt : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz
    have htpos : 0 < t := by
      dsimp only [t]
      apply Real.sqrt_pos.2
      nlinarith [norm_nonneg z]
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt htpos
    apply Set.mem_iUnion.mpr
    refine ⟨k, ⟨x, ?_, ?_⟩⟩
    · apply mem_negativeSupportingNormalPatch_closedBall_iff.mpr
      refine ⟨?_, ?_⟩
      · simpa only [x, t] using negativeSphereLift_mem_sphere hv z hz
      · have hinner := inner_negativeSphereLift hv z
        dsimp only [x, t]
        rw [hinner]
        linarith
    · simpa only [x, t] using orthogonalProjectionOnto_negativeSphereLift z

private theorem lintegral_patchInverse_jacobian_mul_absInner_eq {d : ℕ}
    (hd : 2 ≤ d) {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {S : Set (EuclideanSpace ℝ (Fin d))}
    (hSsphere : S ⊆ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1)
    (hTmeas : MeasurableSet (((ℝ ∙ v)ᗮ).orthogonalProjectionOnto '' S))
    {K : ℝ≥0}
    (hlip : LipschitzOnWith K (orthogonalProjectionPatchInverse v S)
      (((ℝ ∙ v)ᗮ).orthogonalProjectionOnto '' S))
    (g : (ℝ ∙ v)ᗮ → ℝ≥0∞) :
    (∫⁻ z in ((ℝ ∙ v)ᗮ).orthogonalProjectionOnto '' S,
        ENNReal.ofReal
            (fderivWithin ℝ (orthogonalProjectionPatchInverse v S)
              (((ℝ ∙ v)ᗮ).orthogonalProjectionOnto '' S) z).toLinearMap.normDet *
          (g (((ℝ ∙ v)ᗮ).orthogonalProjectionOnto
              (orthogonalProjectionPatchInverse v S z)) *
            ENNReal.ofReal
              |inner ℝ (orthogonalProjectionPatchInverse v S z) v|) ∂volume) =
      ∫⁻ z in ((ℝ ∙ v)ᗮ).orthogonalProjectionOnto '' S, g z ∂volume := by
  let T := ((ℝ ∙ v)ᗮ).orthogonalProjectionOnto '' S
  let φ := orthogonalProjectionPatchInverse v S
  let P := ((ℝ ∙ v)ᗮ).orthogonalProjectionOnto
  have hcomp := ae_comp_fderivWithin_eq_id_of_lipschitzOnWith
    hTmeas hlip P (fun z hz ↦ (orthogonalProjectionOnto_patchInverse hz).symm)
  have hdensity := Besicovitch.ae_tendsto_measure_inter_div volume T
  have hdiff : ∀ᵐ z : (ℝ ∙ v)ᗮ ∂volume.restrict T,
      DifferentiableWithinAt ℝ φ T z :=
    hlip.ae_differentiableWithinAt hTmeas
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hTmeas, hcomp, hdensity, hdiff] with
      z hz hcompz hdensityz hdiffz
  have hcompLin :
      P.toLinearMap.comp (fderivWithin ℝ φ T z).toLinearMap = LinearMap.id :=
    congrArg ContinuousLinearMap.toLinearMap hcompz
  obtain ⟨u, hu, hrange, hcancel⟩ :=
    exists_unit_normal_normDet_mul_eq_one_of_projection_comp_eq_id
      hd hv (fderivWithin ℝ φ T z).toLinearMap hcompLin
  have hφS : φ z ∈ S := orthogonalProjectionPatchInverse_mem hz
  have hφsphere : φ z ∈ Metric.sphere 0 1 := hSsphere hφS
  have hφnorm : ‖φ z‖ = 1 := by simpa [Metric.mem_sphere] using hφsphere
  have hnormEq : EqOn (fun y : (ℝ ∙ v)ᗮ ↦ ‖φ y‖ ^ 2) (fun _ ↦ (1 : ℝ)) T := by
    intro y hy
    have hyS : φ y ∈ S := orthogonalProjectionPatchInverse_mem hy
    have hynorm : ‖φ y‖ = 1 := by
      simpa [Metric.mem_sphere] using hSsphere hyS
    change ‖φ y‖ ^ 2 = 1
    rw [hynorm, one_pow]
  have hnormDeriv : HasFDerivWithinAt (fun y : (ℝ ∙ v)ᗮ ↦ ‖φ y‖ ^ 2)
      (2 • (innerSL ℝ (φ z)).comp (fderivWithin ℝ φ T z)) T z :=
    hdiffz.hasFDerivWithinAt.norm_sq
  have hnormDerivConst : HasFDerivWithinAt (fun _ : (ℝ ∙ v)ᗮ ↦ (1 : ℝ))
      (2 • (innerSL ℝ (φ z)).comp (fderivWithin ℝ φ T z)) T z :=
    hnormDeriv.congr' hnormEq.symm hz
  have hzeroDeriv : HasFDerivWithinAt (fun _ : (ℝ ∙ v)ᗮ ↦ (1 : ℝ)) 0 T z :=
    (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) z).hasFDerivWithinAt
  have hnormalZero :
      (2 • (innerSL ℝ (φ z)).comp (fderivWithin ℝ φ T z)) = 0 :=
    HasFDerivWithinAt.eq_of_volume_density_one hdensityz hnormDerivConst hzeroDeriv
  have hφperp : φ z ∈ (fderivWithin ℝ φ T z).toLinearMap.rangeᗮ := by
    rw [Submodule.mem_orthogonal']
    intro y hy
    obtain ⟨w, rfl⟩ := hy
    have hzeroApply := congrArg
      (fun A : (ℝ ∙ v)ᗮ →L[ℝ] ℝ ↦ A w) hnormalZero
    simpa [real_inner_comm] using hzeroApply
  have hφspan : φ z ∈ ℝ ∙ u := by
    rw [hrange, Submodule.orthogonal_orthogonal] at hφperp
    exact hφperp
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hφspan
  have hcabs : |c| = 1 := by
    have hnorm := congrArg norm hc
    rw [hφnorm, norm_smul, hu, mul_one, Real.norm_eq_abs] at hnorm
    exact hnorm
  have habs : |inner ℝ (φ z) v| = |inner ℝ v u| := by
    rw [← hc, real_inner_smul_left, abs_mul, hcabs, one_mul,
      real_inner_comm u v]
  rw [orthogonalProjectionOnto_patchInverse hz]
  rw [habs]
  calc
    ENNReal.ofReal
          (fderivWithin ℝ φ T z).toLinearMap.normDet *
        (g z * ENNReal.ofReal |inner ℝ v u|) =
        g z * (ENNReal.ofReal |inner ℝ v u| *
          ENNReal.ofReal (fderivWithin ℝ φ T z).toLinearMap.normDet) := by
      ac_rfl
    _ = g z * ENNReal.ofReal
          (|inner ℝ v u| * (fderivWithin ℝ φ T z).toLinearMap.normDet) := by
      rw [ENNReal.ofReal_mul (abs_nonneg _)]
    _ = g z := by rw [hcancel, ENNReal.ofReal_one, mul_one]

private theorem lintegral_positiveSupportingNormalPatch_closedBall_mul_absInner_eq
    {d : ℕ} (hd : 2 ≤ d) {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {a : ℝ} (ha : 0 < a) (g : (ℝ ∙ v)ᗮ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x in positiveSupportingNormalPatch
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) v a,
        g (((ℝ ∙ v)ᗮ).orthogonalProjectionOnto x) *
          ENNReal.ofReal |inner ℝ x v|
        ∂Measure.euclideanHausdorffMeasure (d - 1)) =
      ∫⁻ z in ((ℝ ∙ v)ᗮ).orthogonalProjectionOnto ''
          positiveSupportingNormalPatch
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) v a,
        g z ∂volume := by
  let C := Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
  let S := positiveSupportingNormalPatch C v a
  let P := ((ℝ ∙ v)ᗮ).orthogonalProjectionOnto
  have hweight : Measurable (fun x : EuclideanSpace ℝ (Fin d) ↦
      g (P x) * ENNReal.ofReal |inner ℝ x v|) :=
    (hg.comp P.measurable).mul
      (ENNReal.measurable_ofReal.comp
        ((continuous_id.inner continuous_const).abs.measurable))
  rw [lintegral_positiveSupportingNormalPatch_eq_chart
    hd (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) hv ha _ hweight]
  apply lintegral_patchInverse_jacobian_mul_absInner_eq hd hv
  · intro x hx
    exact (mem_positiveSupportingNormalPatch_closedBall_iff.mp hx).1
  · exact ((IsCompact.positiveSupportingNormalPatch
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) v a).image
      P.continuous).measurableSet
  · exact lipschitzOnWith_orthogonalProjectionPatchInverse_positivePatch
      isClosed_closedBall hv ha

private theorem lintegral_negativeSupportingNormalPatch_closedBall_mul_absInner_eq
    {d : ℕ} (hd : 2 ≤ d) {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {a : ℝ} (ha : 0 < a) (g : (ℝ ∙ v)ᗮ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x in negativeSupportingNormalPatch
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) v a,
        g (((ℝ ∙ v)ᗮ).orthogonalProjectionOnto x) *
          ENNReal.ofReal |inner ℝ x v|
        ∂Measure.euclideanHausdorffMeasure (d - 1)) =
      ∫⁻ z in ((ℝ ∙ v)ᗮ).orthogonalProjectionOnto ''
          negativeSupportingNormalPatch
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) v a,
        g z ∂volume := by
  let C := Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
  let S := negativeSupportingNormalPatch C v a
  let P := ((ℝ ∙ v)ᗮ).orthogonalProjectionOnto
  have hweight : Measurable (fun x : EuclideanSpace ℝ (Fin d) ↦
      g (P x) * ENNReal.ofReal |inner ℝ x v|) :=
    (hg.comp P.measurable).mul
      (ENNReal.measurable_ofReal.comp
        ((continuous_id.inner continuous_const).abs.measurable))
  rw [lintegral_negativeSupportingNormalPatch_eq_chart
    hd (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) hv ha _ hweight]
  apply lintegral_patchInverse_jacobian_mul_absInner_eq hd hv
  · intro x hx
    exact (mem_negativeSupportingNormalPatch_closedBall_iff.mp hx).1
  · exact ((IsCompact.negativeSupportingNormalPatch
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) v a).image
      P.continuous).measurableSet
  · exact lipschitzOnWith_orthogonalProjectionPatchInverse_negativePatch
      isClosed_closedBall hv ha

private lemma directed_positiveSupportingNormalPatch_closedBall {d : ℕ}
    (v : EuclideanSpace ℝ (Fin d)) :
    Directed (· ⊆ ·) (fun k : ℕ ↦
      positiveSupportingNormalPatch
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) v
        (1 / (k + 1 : ℝ))) := by
  intro m n
  refine ⟨max m n, ?_, ?_⟩
  · intro x hx
    apply mem_positiveSupportingNormalPatch_closedBall_iff.mpr
    obtain ⟨hxsphere, hxinner⟩ :=
      mem_positiveSupportingNormalPatch_closedBall_iff.mp hx
    refine ⟨hxsphere, ?_⟩
    exact (one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right (Nat.le_max_left m n) 1)).trans hxinner
  · intro x hx
    apply mem_positiveSupportingNormalPatch_closedBall_iff.mpr
    obtain ⟨hxsphere, hxinner⟩ :=
      mem_positiveSupportingNormalPatch_closedBall_iff.mp hx
    refine ⟨hxsphere, ?_⟩
    exact (one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right (Nat.le_max_right m n) 1)).trans hxinner

private lemma directed_negativeSupportingNormalPatch_closedBall {d : ℕ}
    (v : EuclideanSpace ℝ (Fin d)) :
    Directed (· ⊆ ·) (fun k : ℕ ↦
      negativeSupportingNormalPatch
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) v
        (1 / (k + 1 : ℝ))) := by
  intro m n
  refine ⟨max m n, ?_, ?_⟩
  · intro x hx
    apply mem_negativeSupportingNormalPatch_closedBall_iff.mpr
    obtain ⟨hxsphere, hxinner⟩ :=
      mem_negativeSupportingNormalPatch_closedBall_iff.mp hx
    refine ⟨hxsphere, ?_⟩
    have hthreshold : 1 / (max m n + 1 : ℝ) ≤ 1 / (m + 1 : ℝ) :=
      one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right (Nat.le_max_left m n) 1)
    linarith
  · intro x hx
    apply mem_negativeSupportingNormalPatch_closedBall_iff.mpr
    obtain ⟨hxsphere, hxinner⟩ :=
      mem_negativeSupportingNormalPatch_closedBall_iff.mp hx
    refine ⟨hxsphere, ?_⟩
    have hthreshold : 1 / (max m n + 1 : ℝ) ≤ 1 / (n + 1 : ℝ) :=
      one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right (Nat.le_max_right m n) 1)
    linarith

private theorem lintegral_positiveSupportingNormalPoints_closedBall_mul_absInner_eq
    {d : ℕ} (hd : 2 ≤ d) {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    (g : (ℝ ∙ v)ᗮ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x in positiveSupportingNormalPoints
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) v,
        g (((ℝ ∙ v)ᗮ).orthogonalProjectionOnto x) *
          ENNReal.ofReal |inner ℝ x v|
        ∂Measure.euclideanHausdorffMeasure (d - 1)) =
      ∫⁻ z in Metric.ball (0 : (ℝ ∙ v)ᗮ) 1, g z ∂volume := by
  let S : ℕ → Set (EuclideanSpace ℝ (Fin d)) := fun k ↦
    positiveSupportingNormalPatch
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) v
      (1 / (k + 1 : ℝ))
  let T : ℕ → Set ((ℝ ∙ v)ᗮ) := fun k ↦
    ((ℝ ∙ v)ᗮ).orthogonalProjectionOnto '' S k
  have hSdirected : Directed (· ⊆ ·) S :=
    directed_positiveSupportingNormalPatch_closedBall v
  have hTdirected : Directed (· ⊆ ·) T := by
    intro m n
    obtain ⟨k, hmk, hnk⟩ := hSdirected m n
    exact ⟨k, Set.image_mono hmk, Set.image_mono hnk⟩
  unfold positiveSupportingNormalPoints
  calc
    (∫⁻ x in ⋃ k, S k,
        g (((ℝ ∙ v)ᗮ).orthogonalProjectionOnto x) *
          ENNReal.ofReal |inner ℝ x v|
        ∂Measure.euclideanHausdorffMeasure (d - 1)) =
        ⨆ k, ∫⁻ x in S k,
          g (((ℝ ∙ v)ᗮ).orthogonalProjectionOnto x) *
            ENNReal.ofReal |inner ℝ x v|
          ∂Measure.euclideanHausdorffMeasure (d - 1) :=
      setLIntegral_iUnion_of_directed _ hSdirected
    _ = ⨆ k, ∫⁻ z in T k, g z ∂volume := by
      congr 1
      funext k
      exact lintegral_positiveSupportingNormalPatch_closedBall_mul_absInner_eq
        hd hv (by positivity) g hg
    _ = ∫⁻ z in ⋃ k, T k, g z ∂volume :=
      (setLIntegral_iUnion_of_directed g hTdirected).symm
    _ = ∫⁻ z in Metric.ball (0 : (ℝ ∙ v)ᗮ) 1, g z ∂volume := by
      rw [show (⋃ k, T k) = Metric.ball (0 : (ℝ ∙ v)ᗮ) 1 from
        iUnion_image_positiveSupportingNormalPatch_closedBall_eq_ball hv]

private theorem lintegral_negativeSupportingNormalPoints_closedBall_mul_absInner_eq
    {d : ℕ} (hd : 2 ≤ d) {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    (g : (ℝ ∙ v)ᗮ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x in negativeSupportingNormalPoints
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) v,
        g (((ℝ ∙ v)ᗮ).orthogonalProjectionOnto x) *
          ENNReal.ofReal |inner ℝ x v|
        ∂Measure.euclideanHausdorffMeasure (d - 1)) =
      ∫⁻ z in Metric.ball (0 : (ℝ ∙ v)ᗮ) 1, g z ∂volume := by
  let S : ℕ → Set (EuclideanSpace ℝ (Fin d)) := fun k ↦
    negativeSupportingNormalPatch
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) v
      (1 / (k + 1 : ℝ))
  let T : ℕ → Set ((ℝ ∙ v)ᗮ) := fun k ↦
    ((ℝ ∙ v)ᗮ).orthogonalProjectionOnto '' S k
  have hSdirected : Directed (· ⊆ ·) S :=
    directed_negativeSupportingNormalPatch_closedBall v
  have hTdirected : Directed (· ⊆ ·) T := by
    intro m n
    obtain ⟨k, hmk, hnk⟩ := hSdirected m n
    exact ⟨k, Set.image_mono hmk, Set.image_mono hnk⟩
  unfold negativeSupportingNormalPoints
  calc
    (∫⁻ x in ⋃ k, S k,
        g (((ℝ ∙ v)ᗮ).orthogonalProjectionOnto x) *
          ENNReal.ofReal |inner ℝ x v|
        ∂Measure.euclideanHausdorffMeasure (d - 1)) =
        ⨆ k, ∫⁻ x in S k,
          g (((ℝ ∙ v)ᗮ).orthogonalProjectionOnto x) *
            ENNReal.ofReal |inner ℝ x v|
          ∂Measure.euclideanHausdorffMeasure (d - 1) :=
      setLIntegral_iUnion_of_directed _ hSdirected
    _ = ⨆ k, ∫⁻ z in T k, g z ∂volume := by
      congr 1
      funext k
      exact lintegral_negativeSupportingNormalPatch_closedBall_mul_absInner_eq
        hd hv (by positivity) g hg
    _ = ∫⁻ z in ⋃ k, T k, g z ∂volume :=
      (setLIntegral_iUnion_of_directed g hTdirected).symm
    _ = ∫⁻ z in Metric.ball (0 : (ℝ ∙ v)ᗮ) 1, g z ∂volume := by
      rw [show (⋃ k, T k) = Metric.ball (0 : (ℝ ∙ v)ᗮ) 1 from
        iUnion_image_negativeSupportingNormalPatch_closedBall_eq_ball hv]

private lemma mem_positiveSupportingNormalPoints_closedBall_iff {d : ℕ}
    {v x : EuclideanSpace ℝ (Fin d)} :
    x ∈ positiveSupportingNormalPoints
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) v ↔
      x ∈ Metric.sphere 0 1 ∧ 0 < inner ℝ v x := by
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hxsphere, hinner⟩ :=
      mem_positiveSupportingNormalPatch_closedBall_iff.mp hk
    exact ⟨hxsphere, (by positivity : 0 < 1 / (k + 1 : ℝ)).trans_le hinner⟩
  · rintro ⟨hxsphere, hinner⟩
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hinner
    apply Set.mem_iUnion.mpr
    exact ⟨k, mem_positiveSupportingNormalPatch_closedBall_iff.mpr
      ⟨hxsphere, hk.le⟩⟩

private lemma mem_negativeSupportingNormalPoints_closedBall_iff {d : ℕ}
    {v x : EuclideanSpace ℝ (Fin d)} :
    x ∈ negativeSupportingNormalPoints
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) v ↔
      x ∈ Metric.sphere 0 1 ∧ inner ℝ v x < 0 := by
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hxsphere, hinner⟩ :=
      mem_negativeSupportingNormalPatch_closedBall_iff.mp hk
    exact ⟨hxsphere, hinner.trans_lt
      (neg_neg_of_pos (by positivity : 0 < 1 / (k + 1 : ℝ)))⟩
  · rintro ⟨hxsphere, hinner⟩
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (neg_pos.mpr hinner)
    apply Set.mem_iUnion.mpr
    refine ⟨k, mem_negativeSupportingNormalPatch_closedBall_iff.mpr
      ⟨hxsphere, ?_⟩⟩
    linarith

/-- Ambient-set form of the Cauchy projection formula for the Euclidean unit sphere. -/
theorem lintegral_unitSphere_orthogonalProjection_mul_absInner_ambient {d : ℕ}
    (hd : 2 ≤ d) {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    (g : (ℝ ∙ v)ᗮ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x in Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        g (((ℝ ∙ v)ᗮ).orthogonalProjectionOnto x) *
          ENNReal.ofReal |inner ℝ x v|
        ∂Measure.euclideanHausdorffMeasure (d - 1)) =
      2 * ∫⁻ z in Metric.ball (0 : (ℝ ∙ v)ᗮ) 1, g z ∂volume := by
  let C := Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
  let A := positiveSupportingNormalPoints C v
  let B := negativeSupportingNormalPoints C v
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1
  let w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun x ↦
    g (((ℝ ∙ v)ᗮ).orthogonalProjectionOnto x) *
      ENNReal.ofReal |inner ℝ x v|
  have hAmeas : MeasurableSet A :=
    measurableSet_positiveSupportingNormalPoints
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) v
  have hBmeas : MeasurableSet B :=
    measurableSet_negativeSupportingNormalPoints
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) v
  have hSmeas : MeasurableSet S := isClosed_sphere.measurableSet
  have hABsub : A ∪ B ⊆ S := by
    intro x hx
    rcases hx with hx | hx
    · exact (mem_positiveSupportingNormalPoints_closedBall_iff.mp hx).1
    · exact (mem_negativeSupportingNormalPoints_closedBall_iff.mp hx).1
  have hABdisj : Disjoint A B := Set.disjoint_left.2 fun x hxA hxB ↦ by
    have hpos := (mem_positiveSupportingNormalPoints_closedBall_iff.mp hxA).2
    have hneg := (mem_negativeSupportingNormalPoints_closedBall_iff.mp hxB).2
    linarith
  have hzero : (∫⁻ x in S \ (A ∪ B), w x
      ∂Measure.euclideanHausdorffMeasure (d - 1)) = 0 := by
    calc
      (∫⁻ x in S \ (A ∪ B), w x
          ∂Measure.euclideanHausdorffMeasure (d - 1)) =
          ∫⁻ _x in S \ (A ∪ B), (0 : ℝ≥0∞)
            ∂Measure.euclideanHausdorffMeasure (d - 1) := by
        apply setLIntegral_congr_fun (hSmeas.diff (hAmeas.union hBmeas))
        intro x hx
        have hxS : x ∈ S := hx.1
        have hxnot : x ∉ A ∪ B := hx.2
        have hinner : inner ℝ v x = 0 := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with hneg | hpos
          · exact hxnot (Or.inr
              (mem_negativeSupportingNormalPoints_closedBall_iff.mpr ⟨hxS, hneg⟩))
          · exact hxnot (Or.inl
              (mem_positiveSupportingNormalPoints_closedBall_iff.mpr ⟨hxS, hpos⟩))
        unfold w
        rw [show inner ℝ x v = 0 by simpa [real_inner_comm] using hinner,
          abs_zero, ENNReal.ofReal_zero, mul_zero]
      _ = 0 := by simp
  have hsphereSplit : S = (A ∪ B) ∪ (S \ (A ∪ B)) := by
    ext x
    constructor
    · intro hx
      by_cases hAB : x ∈ A ∪ B
      · exact Or.inl hAB
      · exact Or.inr ⟨hx, hAB⟩
    · rintro (hx | hx)
      · exact hABsub hx
      · exact hx.1
  calc
    (∫⁻ x in S, w x ∂Measure.euclideanHausdorffMeasure (d - 1)) =
        ∫⁻ x in (A ∪ B) ∪ (S \ (A ∪ B)), w x
          ∂Measure.euclideanHausdorffMeasure (d - 1) := by
      nth_rewrite 1 [hsphereSplit]
      rfl
    _ = (∫⁻ x in A ∪ B, w x ∂Measure.euclideanHausdorffMeasure (d - 1)) +
        ∫⁻ x in S \ (A ∪ B), w x
          ∂Measure.euclideanHausdorffMeasure (d - 1) := by
      rw [lintegral_union (hSmeas.diff (hAmeas.union hBmeas))]
      exact Set.disjoint_sdiff_right
    _ = ∫⁻ x in A ∪ B, w x ∂Measure.euclideanHausdorffMeasure (d - 1) := by
      rw [hzero, add_zero]
    _ = (∫⁻ x in A, w x ∂Measure.euclideanHausdorffMeasure (d - 1)) +
        ∫⁻ x in B, w x ∂Measure.euclideanHausdorffMeasure (d - 1) := by
      rw [lintegral_union hBmeas hABdisj]
    _ = (∫⁻ z in Metric.ball (0 : (ℝ ∙ v)ᗮ) 1, g z ∂volume) +
        ∫⁻ z in Metric.ball (0 : (ℝ ∙ v)ᗮ) 1, g z ∂volume := by
      rw [lintegral_positiveSupportingNormalPoints_closedBall_mul_absInner_eq
        hd hv g hg,
        lintegral_negativeSupportingNormalPoints_closedBall_mul_absInner_eq
          hd hv g hg]
    _ = 2 * ∫⁻ z in Metric.ball (0 : (ℝ ∙ v)ᗮ) 1, g z ∂volume :=
      (two_mul _).symm

/-- Cauchy's projection formula for intrinsic codimension-one Hausdorff measure on the unit
sphere, written with an arbitrary nonnegative measurable weight on the projected unit ball. -/
theorem lintegral_unitSphere_orthogonalProjection_mul_absInner {d : ℕ}
    (hd : 2 ≤ d) {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    (g : (ℝ ∙ v)ᗮ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        g (((ℝ ∙ v)ᗮ).orthogonalProjectionOnto θ.1) *
          ENNReal.ofReal |inner ℝ θ.1 v|
        ∂standardSphereHausdorffMeasure d) =
      2 * ∫⁻ z in Metric.ball (0 : (ℝ ∙ v)ᗮ) 1, g z ∂volume := by
  let F : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun x ↦
    g (((ℝ ∙ v)ᗮ).orthogonalProjectionOnto x) *
      ENNReal.ofReal |inner ℝ x v|
  have hF : Measurable F :=
    (hg.comp ((ℝ ∙ v)ᗮ).orthogonalProjectionOnto.measurable).mul
      (ENNReal.measurable_ofReal.comp
        ((continuous_id.inner continuous_const).abs.measurable))
  rw [show (∫⁻ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      g (((ℝ ∙ v)ᗮ).orthogonalProjectionOnto θ.1) *
        ENNReal.ofReal |inner ℝ θ.1 v|
      ∂standardSphereHausdorffMeasure d) =
      ∫⁻ θ, F θ.1 ∂standardSphereHausdorffMeasure d by rfl]
  rw [lintegral_standardSphereHausdorffMeasure_eq_ambient F hF]
  exact lintegral_unitSphere_orthogonalProjection_mul_absInner_ambient
    hd hv g hg

end ProbabilityTheory
