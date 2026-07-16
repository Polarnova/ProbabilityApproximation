/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.ConvexGeometry.BallProjectionArea
import ProbabilityApproximation.ConvexGeometry.BallCauchyProjection
import ProbabilityApproximation.ConvexGeometry.BallSphericalRearrangement
import ProbabilityApproximation.ConvexGeometry.BallRadialMajorant
import ProbabilityApproximation.ConvexGeometry.GaussianShell
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The spherical projection identity in Ball's perimeter argument

This module joins two independent parts of Keith Ball's proof of the Gaussian perimeter bound:
the supporting-normal projection charts and the spherical rearrangement inequality.  Its central
normalization identifies the orthogonal spherical average with Ball's one-dimensional radial
projection transform.  Keeping that identity here makes the import graph acyclic: boundary chart
geometry and spherical rearrangement remain independent inputs.
-/

open Set Metric MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

/-- The ordinary Euclidean volume of the open unit ball in dimension `n`. -/
private def ballUnitVolume (n : ℕ) : ℝ :=
  volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)

private lemma ballUnitVolume_zero : ballUnitVolume 0 = 1 := by
  rw [ballUnitVolume, volume_euclideanSpace_eq_dirac (Fin 0)]
  simp [Measure.real_def]

private lemma ballUnitVolume_eq_gamma {n : ℕ} (hn : n ≠ 0) :
    ballUnitVolume n =
      Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1) := by
  letI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  rw [ballUnitVolume, Measure.real_def, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal]
  positivity

/-- The two-step recurrence for Euclidean unit-ball volumes. -/
private theorem two_pi_mul_ballUnitVolume_sub_two {d : ℕ} (hd : 2 ≤ d) :
    2 * Real.pi * ballUnitVolume (d - 2) = d * ballUnitVolume d := by
  by_cases hd2 : d = 2
  · subst d
    rw [show 2 - 2 = 0 by omega, ballUnitVolume_zero,
      ballUnitVolume_eq_gamma (by norm_num : 2 ≠ 0)]
    rw [show ((2 : ℕ) : ℝ) / 2 + 1 = 2 by norm_num, Real.Gamma_two]
    norm_num [Real.sq_sqrt Real.pi_nonneg]
  · have hdm2 : d - 2 ≠ 0 := by omega
    rw [ballUnitVolume_eq_gamma hdm2, ballUnitVolume_eq_gamma (by omega : d ≠ 0)]
    have harg : (d : ℝ) / 2 ≠ 0 := by positivity
    have hgamma := Real.Gamma_add_one harg
    have hcast : (((d - 2 : ℕ) : ℝ) / 2 + 1) = (d : ℝ) / 2 := by
      norm_num [Nat.cast_sub hd]
      ring
    rw [hcast, hgamma]
    have hsqrt : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_nonneg
    rw [show Real.sqrt Real.pi ^ d =
        Real.sqrt Real.pi ^ (d - 2) * Real.sqrt Real.pi ^ 2 by
      rw [← pow_add]
      congr 2
      omega]
    rw [hsqrt]
    field_simp

private lemma add_smul_mem_unitBall_iff_norm_lt_sqrt_sub_sq
    {m : ℕ} {u : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ = 1)
    (z : (ℝ ∙ u)ᗮ) (t : ℝ) :
    z.1 + t • u ∈ Metric.ball 0 1 ↔ ‖z‖ < Real.sqrt (1 - t ^ 2) := by
  have hzu : inner ℝ z.1 u = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp z.2
  rw [Metric.mem_ball, dist_zero_right, Real.lt_sqrt (norm_nonneg z)]
  rw [← (sq_lt_sq₀ (norm_nonneg (z.1 + t • u)) (by norm_num : (0 : ℝ) ≤ 1))]
  rw [norm_add_sq_real]
  simp only [real_inner_smul_right, hzu, mul_zero, add_zero, norm_smul, hu, mul_one,
    Real.norm_eq_abs, sq_abs, Submodule.coe_norm, one_pow]
  change ‖z‖ ^ 2 + t ^ 2 < 1 ↔ ‖z‖ ^ 2 < 1 - t ^ 2
  constructor <;> intro h <;> linarith

private def ballOrthogonalSliceWeight {m : ℕ}
    (u : EuclideanSpace ℝ (Fin m)) (f : ℝ → ℝ) (r : ℝ)
    (y : EuclideanSpace ℝ (Fin m)) : ℝ≥0∞ :=
  (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1).indicator
    (fun x ↦ ENNReal.ofReal (f (r * Real.sqrt (1 - (inner ℝ x u) ^ 2)))) y

private lemma measurable_ballOrthogonalSliceWeight {m : ℕ}
    (u : EuclideanSpace ℝ (Fin m)) {f : ℝ → ℝ} (hF : Continuous f) (r : ℝ) :
    Measurable (ballOrthogonalSliceWeight u f r) := by
  unfold ballOrthogonalSliceWeight
  apply Measurable.indicator _ measurableSet_ball
  fun_prop

private lemma inner_add_smul_unit_of_mem_orthogonal {m : ℕ}
    {u : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ = 1)
    (z : (ℝ ∙ u)ᗮ) (t : ℝ) :
    inner ℝ (z.1 + t • u) u = t := by
  have hzu : inner ℝ z.1 u = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp z.2
  rw [inner_add_left, hzu, zero_add, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hu, one_pow, mul_one]

private theorem lintegral_ballOrthogonalSliceWeight_add_smul {m : ℕ}
    {u : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ = 1)
    (f : ℝ → ℝ) (r t : ℝ) :
    (∫⁻ z : (ℝ ∙ u)ᗮ, ballOrthogonalSliceWeight u f r (z.1 + t • u)) =
      ENNReal.ofReal (f (r * Real.sqrt (1 - t ^ 2))) *
        volume (Metric.ball (0 : (ℝ ∙ u)ᗮ) (Real.sqrt (1 - t ^ 2))) := by
  have hpoint (z : (ℝ ∙ u)ᗮ) :
      ballOrthogonalSliceWeight u f r (z.1 + t • u) =
        (Metric.ball (0 : (ℝ ∙ u)ᗮ) (Real.sqrt (1 - t ^ 2))).indicator
          (fun _ ↦ ENNReal.ofReal (f (r * Real.sqrt (1 - t ^ 2)))) z := by
    unfold ballOrthogonalSliceWeight
    by_cases hz : z ∈ Metric.ball (0 : (ℝ ∙ u)ᗮ) (Real.sqrt (1 - t ^ 2))
    · have hznorm : ‖z‖ < Real.sqrt (1 - t ^ 2) := by
        simpa [Metric.mem_ball] using hz
      have hz' : z.1 + t • u ∈
          Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1 :=
        (add_smul_mem_unitBall_iff_norm_lt_sqrt_sub_sq hu z t).2 hznorm
      rw [Set.indicator_of_mem hz', Set.indicator_of_mem hz,
        inner_add_smul_unit_of_mem_orthogonal hu z t]
    · have hz' : z.1 + t • u ∉
          Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1 := fun h ↦
        hz (by simpa [Metric.mem_ball] using
          (add_smul_mem_unitBall_iff_norm_lt_sqrt_sub_sq hu z t).1 h)
      rw [Set.indicator_of_notMem hz', Set.indicator_of_notMem hz]
  simp_rw [hpoint]
  rw [lintegral_indicator measurableSet_ball, setLIntegral_const]

private theorem lintegral_ballOrthogonalSliceWeight_eq_sections {m : ℕ}
    {u : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ = 1)
    {f : ℝ → ℝ} (hF : Continuous f) (r : ℝ) :
    (∫⁻ y : EuclideanSpace ℝ (Fin m), ballOrthogonalSliceWeight u f r y) =
      ∫⁻ t : ℝ, ENNReal.ofReal (f (r * Real.sqrt (1 - t ^ 2))) *
        volume (Metric.ball (0 : (ℝ ∙ u)ᗮ) (Real.sqrt (1 - t ^ 2))) := by
  have hu0 : u ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hu
    norm_num at hu
  have hcoarea := lintegral_eq_lintegral_codimOneSections
    (d := m) (0 : EuclideanSpace ℝ (Fin m)) hu0
    (ballOrthogonalSliceWeight u f r)
    (measurable_ballOrthogonalSliceWeight u hF r)
  have henorm : ‖u‖ₑ = 1 := by
    rw [← ofReal_norm, hu]
    norm_num
  rw [henorm, one_mul] at hcoarea
  rw [hcoarea]
  apply lintegral_congr
  intro t
  rw [lintegral_affineHyperplane_eq_lintegral_orthogonal
    (0 : EuclideanSpace ℝ (Fin m)) hu0 t
    (ballOrthogonalSliceWeight u f r)
    (measurable_ballOrthogonalSliceWeight u hF r)]
  simpa only [add_zero] using lintegral_ballOrthogonalSliceWeight_add_smul hu f r t

private lemma finrank_orthogonal_span_unit {m : ℕ}
    {u : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ = 1) :
    Module.finrank ℝ (ℝ ∙ u)ᗮ = m - 1 := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; exact one_ne_zero)
  have hspan : Module.finrank ℝ (ℝ ∙ u) = 1 := finrank_span_singleton hu0
  have hsum := (ℝ ∙ u).finrank_add_finrank_orthogonal
  rw [hspan] at hsum
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hsum
  omega

private lemma volume_ball_orthogonal_unit_eq {m : ℕ}
    {u : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ = 1)
    {R : ℝ} (hR : 0 < R) :
    volume (Metric.ball (0 : (ℝ ∙ u)ᗮ) R) =
      ENNReal.ofReal (R ^ (m - 1) * ballUnitVolume (m - 1)) := by
  have hm : 1 ≤ m := by
    by_contra hm0
    have : m = 0 := by omega
    subst m
    have : u = 0 := Subsingleton.elim _ _
    rw [this, norm_zero] at hu
    norm_num at hu
  have hrank : Module.finrank ℝ (ℝ ∙ u)ᗮ = m - 1 :=
    finrank_orthogonal_span_unit hu
  by_cases hm1 : m = 1
  · subst m
    have hrank0 : Module.finrank ℝ (ℝ ∙ u)ᗮ = 0 := by simpa using hrank
    let b := stdOrthonormalBasis ℝ (ℝ ∙ u)ᗮ
    have hpre : b.repr ⁻¹' Metric.ball
          (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ (ℝ ∙ u)ᗮ))) R =
        Metric.ball (0 : (ℝ ∙ u)ᗮ) R := by
      ext z
      simp [Metric.mem_ball]
    calc
      volume (Metric.ball (0 : (ℝ ∙ u)ᗮ) R) =
          volume (b.repr ⁻¹' Metric.ball
            (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ (ℝ ∙ u)ᗮ))) R) := by
        rw [hpre]
      _ = volume (Metric.ball
            (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ (ℝ ∙ u)ᗮ))) R) :=
        b.repr.measurePreserving.measure_preimage measurableSet_ball.nullMeasurableSet
      _ = 1 := by
        rw [hrank0, volume_euclideanSpace_eq_dirac (Fin 0)]
        simp [Metric.mem_ball, hR]
      _ = ENNReal.ofReal (R ^ (1 - 1) * ballUnitVolume (1 - 1)) := by
        rw [show 1 - 1 = 0 by omega, pow_zero, one_mul, ballUnitVolume_zero]
        norm_num
  · have hm2 : 2 ≤ m := by omega
    letI : Nontrivial (ℝ ∙ u)ᗮ :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (hrank ▸ by omega)
    rw [InnerProductSpace.volume_ball, hrank]
    have hgamma :
        Real.sqrt Real.pi ^ (m - 1) /
            Real.Gamma (((m - 1 : ℕ) : ℝ) / 2 + 1) =
          ballUnitVolume (m - 1) := by
      exact (ballUnitVolume_eq_gamma (by omega : m - 1 ≠ 0)).symm
    rw [hgamma, ← ENNReal.ofReal_pow hR.le,
      ← ENNReal.ofReal_mul (pow_nonneg hR.le (m - 1))]

private def ballSectionIntegrand (m : ℕ) (f : ℝ → ℝ) (r t : ℝ) : ℝ :=
  f (r * Real.sqrt (1 - t ^ 2)) *
    Real.sqrt (1 - t ^ 2) ^ (m - 1) * ballUnitVolume (m - 1)

private def ballSectionProfile (m : ℕ) (f : ℝ → ℝ) (r : ℝ) : ℝ → ℝ :=
  (Set.Ioo (-1 : ℝ) 1).indicator (ballSectionIntegrand m f r)

private lemma continuous_ballSectionIntegrand
    (m : ℕ) {f : ℝ → ℝ} (hF : Continuous f) (r : ℝ) :
    Continuous (ballSectionIntegrand m f r) := by
  unfold ballSectionIntegrand
  fun_prop

private lemma integrable_ballSectionProfile
    (m : ℕ) {f : ℝ → ℝ} (hF : Continuous f) (r : ℝ) :
    Integrable (ballSectionProfile m f r) := by
  unfold ballSectionProfile
  rw [integrable_indicator_iff measurableSet_Ioo]
  exact ((continuous_ballSectionIntegrand m hF r).continuousOn.integrableOn_compact
    isCompact_Icc).mono_set Set.Ioo_subset_Icc_self

private lemma ballUnitVolume_nonneg (n : ℕ) : 0 ≤ ballUnitVolume n := by
  unfold ballUnitVolume Measure.real
  exact ENNReal.toReal_nonneg

private lemma ballUnitVolume_pos (n : ℕ) : 0 < ballUnitVolume n := by
  unfold ballUnitVolume Measure.real
  apply ENNReal.toReal_pos
  · exact (Metric.measure_ball_pos volume
      (0 : EuclideanSpace ℝ (Fin n)) (by norm_num : (0 : ℝ) < 1)).ne'
  · exact (measure_ball_lt_top :
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) < ∞).ne

private theorem standardSphereSurfaceMass_real_eq {d : ℕ} (_hd : d ≠ 0) :
    ((standardSphereSurfaceFiniteMeasure d).mass : ℝ) =
      d * ballUnitVolume d := by
  letI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero _hd⟩⟩
  change volume.toSphere.real Set.univ =
    d * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
  rw [Measure.toSphere_real_apply_univ]
  simp only [finrank_euclideanSpace, Fintype.card_fin]

private theorem standardSphereSurfaceMass_coe_eq {d : ℕ} (hd : d ≠ 0) :
    ((standardSphereSurfaceFiniteMeasure d).mass : ℝ≥0∞) =
      ENNReal.ofReal (d * ballUnitVolume d) := by
  rw [← ENNReal.toReal_eq_toReal_iff'
    (ENNReal.coe_ne_top :
      ((standardSphereSurfaceFiniteMeasure d).mass : ℝ≥0∞) ≠ ∞)
    ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_ofReal]
  · exact standardSphereSurfaceMass_real_eq hd
  · exact mul_nonneg (Nat.cast_nonneg _) (ballUnitVolume_nonneg d)

private theorem four_ballUnitVolume_sub_two_div_surfaceMass {d : ℕ} (hd : 2 ≤ d) :
    (4 * ballUnitVolume (d - 2)) / (d * ballUnitVolume d) =
      2 / Real.pi := by
  rw [← two_pi_mul_ballUnitVolume_sub_two hd]
  have hk : ballUnitVolume (d - 2) ≠ 0 := (ballUnitVolume_pos (d - 2)).ne'
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp
  ring

private theorem normalizedSphere_four_ballUnitVolume_sub_two {d : ℕ} (hd : 2 ≤ d)
    (A : ℝ) :
    (((standardSphereSurfaceFiniteMeasure d).mass⁻¹ : ℝ≥0) : ℝ≥0∞) *
        ENNReal.ofReal (4 * ballUnitVolume (d - 2) * A) =
      ENNReal.ofReal ((2 / Real.pi) * A) := by
  have hd0 : d ≠ 0 := by omega
  have hmassReal : 0 < ((standardSphereSurfaceFiniteMeasure d).mass : ℝ) := by
    rw [standardSphereSurfaceMass_real_eq hd0]
    exact mul_pos (Nat.cast_pos.mpr (by omega)) (ballUnitVolume_pos d)
  have hmass : (standardSphereSurfaceFiniteMeasure d).mass ≠ 0 := by
    intro hzero
    rw [hzero] at hmassReal
    norm_num at hmassReal
  have hsurface : 0 < d * ballUnitVolume d :=
    mul_pos (Nat.cast_pos.mpr (by omega)) (ballUnitVolume_pos d)
  rw [ENNReal.coe_inv hmass, standardSphereSurfaceMass_coe_eq hd0,
    ← ENNReal.ofReal_inv_of_pos hsurface,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hsurface.le)]
  congr 1
  calc
    (d * ballUnitVolume d)⁻¹ * (4 * ballUnitVolume (d - 2) * A) =
        ((4 * ballUnitVolume (d - 2)) / (d * ballUnitVolume d)) * A := by
      rw [div_eq_mul_inv]
      ring
    _ = (2 / Real.pi) * A := by
      rw [four_ballUnitVolume_sub_two_div_surfaceMass hd]

private theorem normalizedHausdorff_four_ballUnitVolume_sub_two {d : ℕ}
    (hd : 2 ≤ d) (A : ℝ) :
    (standardSphereHausdorffMeasure d univ)⁻¹ *
        ENNReal.ofReal (4 * ballUnitVolume (d - 2) * A) =
      ENNReal.ofReal ((2 / Real.pi) * A) := by
  have hd0 : d ≠ 0 := by omega
  have hsurface : 0 < d * ballUnitVolume d :=
    mul_pos (Nat.cast_pos.mpr (by omega)) (ballUnitVolume_pos d)
  rw [standardSphereHausdorffMeasure_apply_univ d hd0]
  change (ENNReal.ofReal (d * ballUnitVolume d))⁻¹ *
      ENNReal.ofReal (4 * ballUnitVolume (d - 2) * A) = _
  rw [← ENNReal.ofReal_inv_of_pos hsurface,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hsurface.le)]
  congr 1
  calc
    (d * ballUnitVolume d)⁻¹ * (4 * ballUnitVolume (d - 2) * A) =
        ((4 * ballUnitVolume (d - 2)) / (d * ballUnitVolume d)) * A := by
      rw [div_eq_mul_inv]
      ring
    _ = (2 / Real.pi) * A := by
      rw [four_ballUnitVolume_sub_two_div_surfaceMass hd]

private lemma ballSectionProfile_nonneg
    (m : ℕ) {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (r t : ℝ) :
    0 ≤ ballSectionProfile m f r t := by
  unfold ballSectionProfile
  by_cases ht : t ∈ Set.Ioo (-1 : ℝ) 1
  · rw [Set.indicator_of_mem ht]
    exact mul_nonneg
      (mul_nonneg (hf _) (pow_nonneg (Real.sqrt_nonneg _) _))
      (ballUnitVolume_nonneg _)
  · rw [Set.indicator_of_notMem ht]

private lemma sections_integrand_eq_ofReal_ballSectionProfile {m : ℕ}
    {u : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ = 1)
    {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (r t : ℝ) :
    ENNReal.ofReal (f (r * Real.sqrt (1 - t ^ 2))) *
        volume (Metric.ball (0 : (ℝ ∙ u)ᗮ) (Real.sqrt (1 - t ^ 2))) =
      ENNReal.ofReal (ballSectionProfile m f r t) := by
  by_cases ht : t ∈ Set.Ioo (-1 : ℝ) 1
  · have hsub : 0 < 1 - t ^ 2 := by
      rcases ht with ⟨htl, htu⟩
      nlinarith
    have hsqrt : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.2 hsub
    rw [volume_ball_orthogonal_unit_eq hu hsqrt]
    unfold ballSectionProfile
    rw [Set.indicator_of_mem ht]
    unfold ballSectionIntegrand
    rw [← ENNReal.ofReal_mul (hf _)]
    congr 1
    ring
  · have hsub : 1 - t ^ 2 ≤ 0 := by
      simp only [Set.mem_Ioo, not_and_or, not_lt] at ht
      rcases ht with h | h <;> nlinarith
    rw [Real.sqrt_eq_zero_of_nonpos hsub, Metric.ball_eq_empty.mpr le_rfl,
      measure_empty, mul_zero]
    unfold ballSectionProfile
    rw [Set.indicator_of_notMem ht, ENNReal.ofReal_zero]

private theorem lintegral_ballOrthogonalSliceWeight_eq_profile {m : ℕ}
    {u : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ = 1)
    {f : ℝ → ℝ} (hF : Continuous f) (hf : ∀ x, 0 ≤ f x) (r : ℝ) :
    (∫⁻ y : EuclideanSpace ℝ (Fin m), ballOrthogonalSliceWeight u f r y) =
      ENNReal.ofReal (∫ t : ℝ, ballSectionProfile m f r t) := by
  rw [lintegral_ballOrthogonalSliceWeight_eq_sections hu hF r]
  calc
    (∫⁻ t : ℝ, ENNReal.ofReal (f (r * Real.sqrt (1 - t ^ 2))) *
        volume (Metric.ball (0 : (ℝ ∙ u)ᗮ) (Real.sqrt (1 - t ^ 2)))) =
        ∫⁻ t : ℝ, ENNReal.ofReal (ballSectionProfile m f r t) := by
      apply lintegral_congr
      intro t
      exact sections_integrand_eq_ofReal_ballSectionProfile hu hf r t
    _ = ENNReal.ofReal (∫ t : ℝ, ballSectionProfile m f r t) := by
      rw [ofReal_integral_eq_lintegral_ofReal
        (integrable_ballSectionProfile m hF r)
        (Filter.Eventually.of_forall (ballSectionProfile_nonneg m hf r))]

private lemma ballSectionIntegrand_neg (m : ℕ) (f : ℝ → ℝ) (r t : ℝ) :
    ballSectionIntegrand m f r (-t) = ballSectionIntegrand m f r t := by
  simp [ballSectionIntegrand]

private theorem integral_ballSectionProfile_eq_two_mul {m : ℕ}
    {f : ℝ → ℝ} (hF : Continuous f) (r : ℝ) :
    (∫ t : ℝ, ballSectionProfile m f r t) =
      2 * ∫ t in (0 : ℝ)..1, ballSectionIntegrand m f r t := by
  have hg := continuous_ballSectionIntegrand m hF r
  have hneg :
      (∫ t in (-1 : ℝ)..0, ballSectionIntegrand m f r t) =
        ∫ t in (0 : ℝ)..1, ballSectionIntegrand m f r t := by
    calc
      (∫ t in (-1 : ℝ)..0, ballSectionIntegrand m f r t) =
          ∫ t in (0 : ℝ)..1, ballSectionIntegrand m f r (-t) := by
        simpa using (intervalIntegral.integral_comp_neg
          (f := ballSectionIntegrand m f r) (a := (0 : ℝ)) (b := 1)).symm
      _ = ∫ t in (0 : ℝ)..1, ballSectionIntegrand m f r t := by
        apply intervalIntegral.integral_congr
        intro t _ht
        exact ballSectionIntegrand_neg m f r t
  calc
    (∫ t : ℝ, ballSectionProfile m f r t) =
        ∫ t in Set.Ioo (-1 : ℝ) 1, ballSectionIntegrand m f r t := by
      unfold ballSectionProfile
      rw [integral_indicator measurableSet_Ioo]
    _ = ∫ t in Set.Ioc (-1 : ℝ) 1, ballSectionIntegrand m f r t :=
      integral_Ioc_eq_integral_Ioo.symm
    _ = ∫ t in (-1 : ℝ)..1, ballSectionIntegrand m f r t :=
      (intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)).symm
    _ = (∫ t in (-1 : ℝ)..0, ballSectionIntegrand m f r t) +
          ∫ t in (0 : ℝ)..1, ballSectionIntegrand m f r t :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)).symm
    _ = 2 * ∫ t in (0 : ℝ)..1, ballSectionIntegrand m f r t := by
      rw [hneg]
      ring

private theorem intervalIntegral_ballSectionIntegrand_eq_angular (m : ℕ) (hm : 1 ≤ m)
    {f : ℝ → ℝ} (hF : Continuous f) (r : ℝ) :
    (∫ t in (0 : ℝ)..1, ballSectionIntegrand m f r t) =
      ballUnitVolume (m - 1) *
        ∫ θ in (0 : ℝ)..Real.pi / 2, f (r * Real.sin θ) * Real.sin θ ^ m := by
  have hsubst := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := Real.pi / 2)
    (f := Real.cos) (f' := fun θ ↦ -Real.sin θ)
    (g := ballSectionIntegrand m f r)
    (fun θ _ ↦ Real.hasDerivAt_cos θ)
    Real.continuous_sin.neg.continuousOn
    (continuous_ballSectionIntegrand m hF r)
  have hchange :
      (∫ t in (0 : ℝ)..1, ballSectionIntegrand m f r t) =
        ∫ θ in (0 : ℝ)..Real.pi / 2,
          ballSectionIntegrand m f r (Real.cos θ) * Real.sin θ := by
    have hsubst' :
        (∫ θ in (0 : ℝ)..Real.pi / 2,
            ballSectionIntegrand m f r (Real.cos θ) * (-Real.sin θ)) =
          ∫ t in (1 : ℝ)..0, ballSectionIntegrand m f r t := by
      simpa only [Function.comp_apply, Real.cos_zero, Real.cos_pi_div_two] using hsubst
    calc
      (∫ t in (0 : ℝ)..1, ballSectionIntegrand m f r t) =
          -(∫ t in (1 : ℝ)..0, ballSectionIntegrand m f r t) := by
        rw [intervalIntegral.integral_symm]
      _ =
          -(∫ θ in (0 : ℝ)..Real.pi / 2,
            ballSectionIntegrand m f r (Real.cos θ) * (-Real.sin θ)) := by
        rw [hsubst']
      _ = ∫ θ in (0 : ℝ)..Real.pi / 2,
            ballSectionIntegrand m f r (Real.cos θ) * Real.sin θ := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro θ _hθ
        ring
  rw [hchange, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ hθ
  have hθ' : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    simpa [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hθ
  have hsqrt : Real.sqrt (1 - Real.cos θ ^ 2) = Real.sin θ :=
    (Real.sin_eq_sqrt_one_sub_cos_sq hθ'.1 (hθ'.2.trans (by linarith [Real.pi_pos]))).symm
  have hpow : Real.sin θ * Real.sin θ ^ (m - 1) = Real.sin θ ^ m := by
    calc
      Real.sin θ * Real.sin θ ^ (m - 1) = Real.sin θ ^ ((m - 1) + 1) :=
        (pow_succ' (Real.sin θ) (m - 1)).symm
      _ = Real.sin θ ^ m := by congr 1; omega
  unfold ballSectionIntegrand
  simp only [hsqrt]
  rw [← hpow]
  ring

private theorem lintegral_ballOrthogonalSliceWeight_eq_angular {m : ℕ} (hm : 1 ≤ m)
    {u : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ = 1)
    {f : ℝ → ℝ} (hF : Continuous f) (hf : ∀ x, 0 ≤ f x) (r : ℝ) :
    (∫⁻ y : EuclideanSpace ℝ (Fin m), ballOrthogonalSliceWeight u f r y) =
      ENNReal.ofReal
        (2 * ballUnitVolume (m - 1) *
          ∫ θ in (0 : ℝ)..Real.pi / 2,
            f (r * Real.sin θ) * Real.sin θ ^ m) := by
  rw [lintegral_ballOrthogonalSliceWeight_eq_profile hu hF hf r,
    integral_ballSectionProfile_eq_two_mul hF r,
    intervalIntegral_ballSectionIntegrand_eq_angular m hm hF r]
  congr 1
  ring

private def unitBallRadialSliceWeight
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : E) (f : ℝ → ℝ) (r : ℝ) (x : E) : ℝ≥0∞ :=
  (Metric.ball (0 : E) 1).indicator
    (fun y ↦ ENNReal.ofReal (f (r * Real.sqrt (1 - (inner ℝ y u) ^ 2)))) x

private lemma measurable_unitBallRadialSliceWeight
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (u : E) {f : ℝ → ℝ} (hF : Continuous f) (r : ℝ) :
    Measurable (unitBallRadialSliceWeight u f r) := by
  unfold unitBallRadialSliceWeight
  apply Measurable.indicator _ measurableSet_ball
  fun_prop

private theorem lintegral_unitBallRadialSliceWeight_eq_angular
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (hm : 1 ≤ Module.finrank ℝ E) {u : E} (hu : ‖u‖ = 1)
    {f : ℝ → ℝ} (hF : Continuous f) (hf : ∀ x, 0 ≤ f x) (r : ℝ) :
    (∫⁻ x : E, unitBallRadialSliceWeight u f r x) =
      ENNReal.ofReal
        (2 * ballUnitVolume (Module.finrank ℝ E - 1) *
          ∫ θ in (0 : ℝ)..Real.pi / 2,
            f (r * Real.sin θ) * Real.sin θ ^ Module.finrank ℝ E) := by
  let b := stdOrthonormalBasis ℝ E
  have hu' : ‖b.repr u‖ = 1 := by rw [b.repr.norm_map, hu]
  have hcomp :
      unitBallRadialSliceWeight u f r =
        ballOrthogonalSliceWeight (b.repr u) f r ∘ b.repr := by
    funext x
    unfold unitBallRadialSliceWeight ballOrthogonalSliceWeight
    have hball :
        x ∈ Metric.ball (0 : E) 1 ↔
          b.repr x ∈ Metric.ball
            (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1 := by
      simp only [Metric.mem_ball, dist_zero_right, b.repr.norm_map]
    by_cases hx : x ∈ Metric.ball (0 : E) 1
    · rw [Set.indicator_of_mem hx, Function.comp_apply,
        Set.indicator_of_mem (hball.mp hx), b.repr.inner_map_map]
    · rw [Set.indicator_of_notMem hx, Function.comp_apply,
        Set.indicator_of_notMem (fun h ↦ hx (hball.mpr h))]
  rw [hcomp]
  calc
    (∫⁻ x : E, ballOrthogonalSliceWeight (b.repr u) f r (b.repr x)) =
        ∫⁻ y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
          ballOrthogonalSliceWeight (b.repr u) f r y :=
      b.repr.measurePreserving.lintegral_comp
        (measurable_ballOrthogonalSliceWeight (b.repr u) hF r)
    _ = _ := lintegral_ballOrthogonalSliceWeight_eq_angular hm hu' hF hf r

/-- The one-dimensional profile obtained by radially projecting a point of radius `r`
onto the hyperplane perpendicular to a sphere direction with axial coordinate `s`. -/
def ballSphericalRadialProfile (f : ℝ → ℝ) (r s : ℝ) : ℝ :=
  f (r * Real.sqrt (1 - s ^ 2))

theorem continuous_ballSphericalRadialProfile
    {f : ℝ → ℝ} (hF : Continuous f) (r : ℝ) :
    Continuous (ballSphericalRadialProfile f r) := by
  unfold ballSphericalRadialProfile
  fun_prop

/-- An antitone radial density gives a nondecreasing axial profile on the nonnegative axis. -/
theorem monotoneOn_ballSphericalRadialProfile
    {f : ℝ → ℝ} (hf : AntitoneOn f (Set.Ici 0)) {r : ℝ} (hr : 0 ≤ r) :
    MonotoneOn (ballSphericalRadialProfile f r) (Set.Ici 0) := by
  intro s hs t ht hst
  apply hf
  · exact mul_nonneg hr (Real.sqrt_nonneg _)
  · exact mul_nonneg hr (Real.sqrt_nonneg _)
  · apply mul_le_mul_of_nonneg_left _ hr
    apply Real.sqrt_le_sqrt
    nlinarith [mul_self_le_mul_self hs hst]

/-- Ball's spherical rearrangement specialized to a radial projection profile and an arbitrary
finite rotation-invariant measure on the unit sphere. -/
theorem ballSphericalRearrangement_radialProfile_of_measure
    {d : ℕ} (μ : Measure (sphere (0 : EuclideanSpace ℝ (Fin d)) 1))
    [IsFiniteMeasure μ]
    (hμ : ∀ e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      MeasurePreserving (linearIsometryEquivUnitSphere e) μ μ)
    {f : ℝ → ℝ}
    (hF : Continuous f) (hf : AntitoneOn f (Set.Ici 0))
    {r : ℝ} (hr : 0 ≤ r)
    {u v : EuclideanSpace ℝ (Fin d)}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    (∫ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        ballSphericalRadialProfile f r
            |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u| *
          |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v|
        ∂μ) ≤
      ∫ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        ballSphericalRadialProfile f r
            |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u| *
          |inner ℝ (θ : EuclideanSpace ℝ (Fin d))
            (Real.cos α • u + Real.sin α • v)|
        ∂μ :=
  ballSphericalRearrangement_absInner_of_measure μ hμ
    (continuous_ballSphericalRadialProfile hF r)
    (monotoneOn_ballSphericalRadialProfile hf hr)
    hu hv huv hα

/-- Ball's spherical rearrangement specialized to a radial projection profile. -/
theorem ballSphericalRearrangement_radialProfile
    {d : ℕ} (hd : d ≠ 0) {f : ℝ → ℝ}
    (hF : Continuous f) (hf : AntitoneOn f (Set.Ici 0))
    {r : ℝ} (hr : 0 ≤ r)
    {u v : EuclideanSpace ℝ (Fin d)}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    (∫ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        ballSphericalRadialProfile f r
            |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u| *
          |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v|
        ∂(standardSphereProbability d hd).toMeasure) ≤
      ∫ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        ballSphericalRadialProfile f r
            |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u| *
          |inner ℝ (θ : EuclideanSpace ℝ (Fin d))
            (Real.cos α • u + Real.sin α • v)|
        ∂(standardSphereProbability d hd).toMeasure := by
  apply ballSphericalRearrangement_radialProfile_of_measure
    (standardSphereProbability d hd).toMeasure
    (fun e ↦
      measurePreserving_linearIsometryEquivUnitSphere_standardSphereProbability hd e)
    hF hf hr hu hv huv hα

/-- Two unit directions with nonnegative inner product admit the acute-angle decomposition used
in Ball's rearrangement argument.  In dimension at least two the auxiliary direction can always
be chosen unit and orthogonal to the first direction, including the coincident-vector case. -/
theorem exists_orthogonal_unit_acuteAngle_decomposition
    {d : ℕ} (hd : 2 ≤ d) {u w : EuclideanSpace ℝ (Fin d)}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : 0 ≤ inner ℝ u w) :
    ∃ v α, ‖v‖ = 1 ∧ inner ℝ u v = 0 ∧
      α ∈ Set.Icc (0 : ℝ) (Real.pi / 2) ∧
      w = Real.cos α • u + Real.sin α • v := by
  by_cases hwu : w = u
  · let K : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := (ℝ ∙ u)ᗮ
    have hrank : Module.finrank ℝ K = d - 1 := finrank_orthogonal_span_unit hu
    letI : Nontrivial K :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (hrank ▸ by omega)
    obtain ⟨z, hz⟩ : ∃ z : K, z ≠ 0 := exists_ne 0
    let v : EuclideanSpace ℝ (Fin d) := (NormedSpace.normalize z : K)
    have hv : ‖v‖ = 1 := by
      change ‖NormedSpace.normalize z‖ = 1
      exact NormedSpace.norm_normalize hz
    have huv : inner ℝ u v = 0 := by
      rw [real_inner_comm]
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp
        (show (NormedSpace.normalize z : K).1 ∈ (ℝ ∙ u)ᗮ from
          (NormedSpace.normalize z : K).2)
    refine ⟨v, 0, hv, huv, ⟨le_rfl, by positivity⟩, ?_⟩
    rw [hwu]
    simp
  · let c : ℝ := inner ℝ u w
    let z : EuclideanSpace ℝ (Fin d) := w - c • u
    let v : EuclideanSpace ℝ (Fin d) := NormedSpace.normalize z
    let α : ℝ := Real.arccos c
    have hc0 : 0 ≤ c := huw
    have hc1 : c ≤ 1 := by
      have habs := abs_real_inner_le_norm u w
      rw [hu, hw, mul_one] at habs
      exact le_trans (le_abs_self c) habs
    have hz : z ≠ 0 := by
      intro hzero
      have hwsmul : w = c • u := by
        exact sub_eq_zero.mp (by simpa [z] using hzero)
      have habs : |c| = 1 := by
        have hnorm := congrArg norm hwsmul
        rw [hw, norm_smul, hu, mul_one, Real.norm_eq_abs] at hnorm
        exact hnorm.symm
      have hc : c = 1 := by
        rw [abs_of_nonneg hc0] at habs
        exact habs
      rw [hc, one_smul] at hwsmul
      exact hwu hwsmul
    have hzinner : inner ℝ u z = 0 := by
      unfold z c
      rw [inner_sub_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hu, one_pow, mul_one]
      ring
    have hzsq : ‖z‖ ^ 2 = 1 - c ^ 2 := by
      have huu : inner ℝ u u = 1 := by
        rw [real_inner_self_eq_norm_sq, hu, one_pow]
      have hww : inner ℝ w w = 1 := by
        rw [real_inner_self_eq_norm_sq, hw, one_pow]
      rw [← real_inner_self_eq_norm_sq]
      unfold z c
      simp only [inner_sub_left, inner_sub_right,
        real_inner_smul_left, real_inner_smul_right]
      rw [huu, hww, real_inner_comm w u]
      ring
    have hsqrt : Real.sqrt (1 - c ^ 2) = ‖z‖ := by
      apply (Real.sqrt_eq_iff_eq_sq (by nlinarith [sq_nonneg ‖z‖]) (norm_nonneg z)).2
      exact hzsq.symm
    have hv : ‖v‖ = 1 := by
      exact NormedSpace.norm_normalize hz
    have huv : inner ℝ u v = 0 := by
      unfold v NormedSpace.normalize
      rw [real_inner_smul_right, hzinner, mul_zero]
    have hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
      exact ⟨Real.arccos_nonneg c, Real.arccos_le_pi_div_two.mpr hc0⟩
    refine ⟨v, α, hv, huv, hα, ?_⟩
    rw [show Real.cos α = c by
      exact Real.cos_arccos (by linarith) hc1,
      show Real.sin α = ‖z‖ by
        change Real.sin (Real.arccos c) = ‖z‖
        rw [Real.sin_arccos, hsqrt]]
    rw [show ‖z‖ • v = z by
      exact NormedSpace.norm_smul_normalize z]
    unfold z
    abel

private theorem lintegral_orthogonalUnitBall_ballSphericalRadialProfile_eq_angular
    {d : ℕ} (hd : 2 ≤ d) {u v : EuclideanSpace ℝ (Fin d)}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    {f : ℝ → ℝ} (hF : Continuous f) (hf : ∀ x, 0 ≤ f x) (r : ℝ) :
    (∫⁻ z : (ℝ ∙ v)ᗮ in Metric.ball 0 1,
        ENNReal.ofReal
          (ballSphericalRadialProfile f r
            |inner ℝ (z : EuclideanSpace ℝ (Fin d)) u|) ∂volume) =
      ENNReal.ofReal
        (2 * ballUnitVolume (d - 2) *
          ∫ θ in (0 : ℝ)..Real.pi / 2,
            f (r * Real.sin θ) * Real.sin θ ^ (d - 1)) := by
  let u' : (ℝ ∙ v)ᗮ :=
    ⟨u, Submodule.mem_orthogonal_singleton_iff_inner_left.mpr huv⟩
  have hu' : ‖u'‖ = 1 := hu
  have hrank : Module.finrank ℝ (ℝ ∙ v)ᗮ = d - 1 :=
    finrank_orthogonal_span_unit hv
  have hm : 1 ≤ Module.finrank ℝ (ℝ ∙ v)ᗮ := by omega
  have hbase := lintegral_unitBallRadialSliceWeight_eq_angular
    hm hu' hF hf r
  rw [hrank] at hbase
  rw [show d - 1 - 1 = d - 2 by omega] at hbase
  rw [← hbase]
  rw [← lintegral_indicator measurableSet_ball]
  apply lintegral_congr
  intro z
  unfold unitBallRadialSliceWeight
  by_cases hz : z ∈ Metric.ball (0 : (ℝ ∙ v)ᗮ) 1
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    unfold ballSphericalRadialProfile
    simp only [Submodule.coe_inner, sq_abs, u']
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]

/-- The normalized intrinsic-Hausdorff spherical projection in two orthogonal directions is
exactly Ball's one-dimensional radial projection transform. -/
theorem normalizedHausdorff_lintegral_ballSphericalRadialProfile_absInner_orthogonal
    {d : ℕ} (hd : 2 ≤ d) {u v : EuclideanSpace ℝ (Fin d)}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    {f : ℝ → ℝ} (hF : Continuous f) (hf : ∀ x, 0 ≤ f x)
    (r : ℝ) :
    (standardSphereHausdorffMeasure d univ)⁻¹ *
        (∫⁻ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
          ENNReal.ofReal
              (ballSphericalRadialProfile f r
                |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u|) *
            ENNReal.ofReal
              |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v|
          ∂standardSphereHausdorffMeasure d) =
      ENNReal.ofReal (ballRadialProjectionTransform d f r) := by
  let u' : (ℝ ∙ v)ᗮ :=
    ⟨u, Submodule.mem_orthogonal_singleton_iff_inner_left.mpr huv⟩
  let g : (ℝ ∙ v)ᗮ → ℝ≥0∞ := fun z ↦
    ENNReal.ofReal
      (ballSphericalRadialProfile f r
        |inner ℝ (z : EuclideanSpace ℝ (Fin d)) u|)
  have hg : Measurable g := by
    dsimp only [g]
    exact ENNReal.measurable_ofReal.comp
      ((continuous_ballSphericalRadialProfile hF r).measurable.comp
        ((continuous_subtype_val.inner continuous_const).abs.measurable))
  have hprojection (θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
      inner ℝ
          (((ℝ ∙ v)ᗮ).orthogonalProjectionOnto
            (θ : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d)) u =
        inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u := by
    change inner ℝ
        (((ℝ ∙ v)ᗮ).orthogonalProjectionOnto
          (θ : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d))
          (u' : EuclideanSpace ℝ (Fin d)) =
        inner ℝ (θ : EuclideanSpace ℝ (Fin d))
          (u' : EuclideanSpace ℝ (Fin d))
    exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right u' θ
  have hcauchy := lintegral_unitSphere_orthogonalProjection_mul_absInner
    hd hv g hg
  have hleft :
      (∫⁻ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
          ENNReal.ofReal
              (ballSphericalRadialProfile f r
                |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u|) *
            ENNReal.ofReal
              |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v|
          ∂standardSphereHausdorffMeasure d) =
        2 * ∫⁻ z in Metric.ball (0 : (ℝ ∙ v)ᗮ) 1, g z ∂volume := by
    rw [← hcauchy]
    apply lintegral_congr
    intro θ
    unfold g
    rw [hprojection θ]
  have hball :=
    lintegral_orthogonalUnitBall_ballSphericalRadialProfile_eq_angular
      hd hu hv huv hF hf r
  rw [hleft, hball]
  have htwo (A : ℝ) : (2 : ℝ≥0∞) * ENNReal.ofReal A =
      ENNReal.ofReal (2 * A) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
    exact (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [htwo]
  rw [show 2 *
      (2 * ballUnitVolume (d - 2) *
        ∫ θ in (0 : ℝ)..Real.pi / 2,
          f (r * Real.sin θ) * Real.sin θ ^ (d - 1)) =
      4 * ballUnitVolume (d - 2) *
        ∫ θ in (0 : ℝ)..Real.pi / 2,
          f (r * Real.sin θ) * Real.sin θ ^ (d - 1) by ring]
  rw [normalizedHausdorff_four_ballUnitVolume_sub_two hd]
  rfl

/-- ENNReal form of Ball's rearrangement inequality for intrinsic sphere Hausdorff measure.
The nonnegative form composes directly with Cauchy's projection formula. -/
theorem lintegral_ballSphericalRearrangement_radialProfile
    {d : ℕ} {f : ℝ → ℝ}
    (hF : Continuous f) (hfanti : AntitoneOn f (Set.Ici 0))
    (hf : ∀ x, 0 ≤ f x) {r : ℝ} (hr : 0 ≤ r)
    {u v : EuclideanSpace ℝ (Fin d)}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    (∫⁻ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        ENNReal.ofReal
            (ballSphericalRadialProfile f r
              |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u|) *
          ENNReal.ofReal
            |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v|
        ∂standardSphereHausdorffMeasure d) ≤
      ∫⁻ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        ENNReal.ofReal
            (ballSphericalRadialProfile f r
              |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u|) *
          ENNReal.ofReal
            |inner ℝ (θ : EuclideanSpace ℝ (Fin d))
              (Real.cos α • u + Real.sin α • v)|
        ∂standardSphereHausdorffMeasure d := by
  let μ := standardSphereHausdorffMeasure d
  let w := Real.cos α • u + Real.sin α • v
  let I : EuclideanSpace ℝ (Fin d) →
      sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ := fun q θ ↦
    ballSphericalRadialProfile f r
        |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u| *
      |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) q|
  have hreal := ballSphericalRearrangement_radialProfile_of_measure μ
    (fun e ↦ by
      simpa [μ, standardSphereHausdorffMeasure] using
        measurePreserving_linearIsometryEquivUnitSphere_euclideanHausdorffMeasure
          e (d - 1))
    hF hfanti hr hu hv huv hα
  have hcontinuous (q : EuclideanSpace ℝ (Fin d)) : Continuous (I q) := by
    dsimp only [I]
    exact ((continuous_ballSphericalRadialProfile hF r).comp
      ((continuous_subtype_val.inner continuous_const).abs)).mul
        ((continuous_subtype_val.inner continuous_const).abs)
  have hintegrable (q : EuclideanSpace ℝ (Fin d)) : Integrable (I q) μ := by
    exact integrableOn_univ.mp
      ((hcontinuous q).continuousOn.integrableOn_compact (μ := μ) isCompact_univ)
  have hnonneg (q : EuclideanSpace ℝ (Fin d)) : 0 ≤ᵐ[μ] I q := by
    filter_upwards with θ
    exact mul_nonneg (hf _) (abs_nonneg _)
  have hconvert (q : EuclideanSpace ℝ (Fin d)) :
      ENNReal.ofReal (∫ θ, I q θ ∂μ) =
        ∫⁻ θ, ENNReal.ofReal
            (ballSphericalRadialProfile f r
              |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u|) *
          ENNReal.ofReal
            |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) q| ∂μ := by
    rw [ofReal_integral_eq_lintegral_ofReal (hintegrable q) (hnonneg q)]
    apply lintegral_congr
    intro θ
    dsimp only [I]
    exact ENNReal.ofReal_mul
      (p := ballSphericalRadialProfile f r
        |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u|)
      (q := |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) q|) (hf _)
  have h := ENNReal.ofReal_le_ofReal hreal
  change ENNReal.ofReal (∫ θ, I v θ ∂μ) ≤
    ENNReal.ofReal (∫ θ, I w θ ∂μ) at h
  rw [hconvert v, hconvert w] at h
  simpa only [μ, w] using h

/-- Ball's radial projection transform is bounded by the normalized intrinsic-Hausdorff
spherical average in every unit direction. -/
theorem ofReal_ballRadialProjectionTransform_le_normalizedHausdorff_lintegral
    {d : ℕ} (hd : 2 ≤ d) {f : ℝ → ℝ}
    (hF : Continuous f) (hfanti : AntitoneOn f (Set.Ici 0))
    (hf : ∀ x, 0 ≤ f x) {r : ℝ} (hr : 0 ≤ r)
    {u w : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    ENNReal.ofReal (ballRadialProjectionTransform d f r) ≤
      (standardSphereHausdorffMeasure d univ)⁻¹ *
        ∫⁻ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
          ENNReal.ofReal
              (ballSphericalRadialProfile f r
                |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u|) *
            ENNReal.ofReal
              |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) w|
          ∂standardSphereHausdorffMeasure d := by
  let w' : EuclideanSpace ℝ (Fin d) :=
    if 0 ≤ inner ℝ u w then w else -w
  have hw' : ‖w'‖ = 1 := by
    dsimp only [w']
    split <;> simp [hw]
  have huw' : 0 ≤ inner ℝ u w' := by
    dsimp only [w']
    split
    · assumption
    · rw [inner_neg_right]
      linarith
  have habs (θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
      |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) w'| =
        |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) w| := by
    dsimp only [w']
    split
    · rfl
    · simp
  obtain ⟨v, α, hv, huv, hα, hw'decomp⟩ :=
    exists_orthogonal_unit_acuteAngle_decomposition hd hu hw' huw'
  have hrearr := lintegral_ballSphericalRearrangement_radialProfile
    hF hfanti hf hr hu hv huv hα
  rw [← hw'decomp] at hrearr
  have horth :=
    normalizedHausdorff_lintegral_ballSphericalRadialProfile_absInner_orthogonal
      hd hu hv huv hF hf r
  calc
    ENNReal.ofReal (ballRadialProjectionTransform d f r) =
        (standardSphereHausdorffMeasure d univ)⁻¹ *
          (∫⁻ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
            ENNReal.ofReal
                (ballSphericalRadialProfile f r
                  |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u|) *
              ENNReal.ofReal
                |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v|
            ∂standardSphereHausdorffMeasure d) := horth.symm
    _ ≤ (standardSphereHausdorffMeasure d univ)⁻¹ *
          (∫⁻ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
            ENNReal.ofReal
                (ballSphericalRadialProfile f r
                  |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u|) *
              ENNReal.ofReal
                |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) w'|
            ∂standardSphereHausdorffMeasure d) :=
      mul_le_mul_right hrearr _
    _ = (standardSphereHausdorffMeasure d univ)⁻¹ *
          ∫⁻ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
            ENNReal.ofReal
                (ballSphericalRadialProfile f r
                  |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u|) *
              ENNReal.ofReal
                |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) w|
            ∂standardSphereHausdorffMeasure d := by
      congr 1
      apply lintegral_congr
      intro θ
      rw [habs θ]

/-- Ball's radial majorant makes the normalized spherical average dominate the radial standard
Gaussian density. -/
theorem ofReal_ballGaussianRadialDensity_le_normalizedHausdorff_lintegral
    {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr : 0 ≤ r)
    {u w : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    ENNReal.ofReal
        (ballGaussianNormalization d * Real.exp (-(r ^ 2) / 2)) ≤
      (standardSphereHausdorffMeasure d univ)⁻¹ *
        ∫⁻ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
          ENNReal.ofReal
              (ballSphericalRadialProfile (ballRadialMajorant d) r
                |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u|) *
            ENNReal.ofReal
              |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) w|
          ∂standardSphereHausdorffMeasure d := by
  calc
    ENNReal.ofReal
        (ballGaussianNormalization d * Real.exp (-(r ^ 2) / 2)) ≤
        ENNReal.ofReal
          (ballRadialProjectionTransform d (ballRadialMajorant d) r) :=
      ENNReal.ofReal_le_ofReal
        (standardGaussianDensityReal_le_ballRadialMajorant_projection hd r)
    _ ≤ _ :=
      ofReal_ballRadialProjectionTransform_le_normalizedHausdorff_lintegral
        hd (continuous_ballRadialMajorant d) (antitoneOn_ballRadialMajorant hd)
        (ballRadialMajorant_nonneg d) hr hu hw

end ProbabilityTheory
