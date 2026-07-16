/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.ConvexGeometry.ScalarCoarea
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Hausdorff mass of the Euclidean unit sphere

This file identifies intrinsic codimension-one Euclidean Hausdorff measure on the unit sphere
with its exact surface-area normalization.  The proof applies scalar coarea to the norm, uses
homogeneity of Euclidean Hausdorff measure on positive-radius spheres, and evaluates the remaining
one-dimensional power integral.
-/

open Set Metric MeasureTheory
open scoped ENNReal NNReal Pointwise RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

/-- Intrinsic codimension-one Euclidean Hausdorff measure on the standard unit sphere. -/
def standardSphereHausdorffMeasure (d : ℕ) :
    Measure (sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
  Measure.euclideanHausdorffMeasure (d - 1)

/-- The intrinsic sphere measure, pushed through subtype inclusion, is ambient Hausdorff measure
restricted to the unit sphere. -/
theorem map_subtype_standardSphereHausdorffMeasure (d : ℕ) :
    Measure.map
        ((↑) : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
          EuclideanSpace ℝ (Fin d))
        (standardSphereHausdorffMeasure d) =
      (Measure.euclideanHausdorffMeasure (d - 1) :
        Measure (EuclideanSpace ℝ (Fin d))).restrict
          (sphere (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  calc
    Measure.map
        ((↑) : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
          EuclideanSpace ℝ (Fin d))
        (standardSphereHausdorffMeasure d) =
        (Measure.euclideanHausdorffMeasure (d - 1) :
          Measure (EuclideanSpace ℝ (Fin d))).restrict
            (Set.range ((↑) : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
              EuclideanSpace ℝ (Fin d))) := by
      exact (isometry_subtype_coe
        (s := sphere (0 : EuclideanSpace ℝ (Fin d)) 1)).map_euclideanHausdorffMeasure
    _ = (Measure.euclideanHausdorffMeasure (d - 1) :
        Measure (EuclideanSpace ℝ (Fin d))).restrict
          (sphere (0 : EuclideanSpace ℝ (Fin d)) 1) := by
      rw [Subtype.range_coe]

/-- Intrinsic and ambient-restricted nonnegative sphere integrals agree. -/
theorem lintegral_standardSphereHausdorffMeasure_eq_ambient
    {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        F θ ∂standardSphereHausdorffMeasure d) =
      ∫⁻ x in sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        F x ∂(Measure.euclideanHausdorffMeasure (d - 1)) := by
  calc
    (∫⁻ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        F θ ∂standardSphereHausdorffMeasure d) =
        ∫⁻ x : EuclideanSpace ℝ (Fin d), F x ∂Measure.map
          ((↑) : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
            EuclideanSpace ℝ (Fin d))
          (standardSphereHausdorffMeasure d) :=
      (lintegral_map hF measurable_subtype_coe).symm
    _ = ∫⁻ x in sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        F x ∂(Measure.euclideanHausdorffMeasure (d - 1)) := by
      rw [map_subtype_standardSphereHausdorffMeasure]

/-- Intrinsic total mass equals the ambient codimension-one Hausdorff mass of the unit sphere. -/
theorem standardSphereHausdorffMeasure_apply_univ_eq_ambient (d : ℕ) :
    standardSphereHausdorffMeasure d univ =
      (Measure.euclideanHausdorffMeasure (d - 1) :
        Measure (EuclideanSpace ℝ (Fin d)))
          (sphere (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  simpa only [lintegral_one, Measure.restrict_apply_univ] using
    lintegral_standardSphereHausdorffMeasure_eq_ambient
      (d := d) (fun _ ↦ 1) measurable_const

private theorem scalarCoareaFiber_norm_one {d : ℕ} (_hd : d ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    scalarCoareaFiber
        (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖) (fun _ ↦ 1) t =
      ENNReal.ofReal t ^ (d - 1) * standardSphereHausdorffMeasure d univ := by
  let E := EuclideanSpace ℝ (Fin d)
  letI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero _hd⟩⟩
  have hfiber : (fun x : E ↦ ‖x‖) ⁻¹' {t} = sphere (0 : E) t := by
    ext x
    simp
  have hsphere : t • sphere (0 : E) 1 = sphere (0 : E) t := by
    simpa [Real.norm_of_nonneg ht.le] using
      (smul_sphere' (E := E) ht.ne' (0 : E) 1)
  rw [scalarCoareaFiber, setLIntegral_one, hfiber, ← hsphere,
    Measure.euclideanHausdorffMeasure_smul₀ (d - 1) ht.ne']
  rw [standardSphereHausdorffMeasure_apply_univ_eq_ambient]
  simp only [ENNReal.smul_def, smul_eq_mul,
    Real.nnnorm_of_nonneg ht.le, ENNReal.coe_nnreal_eq]
  rw [NNReal.coe_pow, NNReal.coe_mk, ENNReal.ofReal_pow ht.le (d - 1)]

private theorem lintegral_ofReal_pow_Ioc_zero_one (d : ℕ) (hd : d ≠ 0) :
    (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal t ^ (d - 1)) =
      ((d : ℝ≥0∞)⁻¹) := by
  have hpow_integrable : IntegrableOn (fun t : ℝ ↦ t ^ (d - 1)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_pow (d - 1)).1
  have hpow_nonneg : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
      0 ≤ t ^ (d - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact pow_nonneg ht.1.le _
  have hconvert :
      (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal t ^ (d - 1)) =
        ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (d - 1)) := by
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro t ht
    exact (ENNReal.ofReal_pow ht.1.le (d - 1)).symm
  rw [hconvert, ← ofReal_integral_eq_lintegral_ofReal hpow_integrable hpow_nonneg]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_pow]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hpred : (((d - 1 : ℕ) : ℝ) + 1) = (d : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd)
  simp [hpred, ENNReal.ofReal_inv_of_pos hdpos]

/-- Intrinsic codimension-one Hausdorff mass of the Euclidean unit sphere is exactly dimension
times the volume of the Euclidean unit ball. -/
theorem standardSphereHausdorffMeasure_apply_univ (d : ℕ) (hd : d ≠ 0) :
    standardSphereHausdorffMeasure d univ =
      ENNReal.ofReal
        ((d : ℝ) *
          volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) := by
  let E := EuclideanSpace ℝ (Fin d)
  letI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩
  have hnorm : ∀ᵐ x : E ∂volume,
      ‖fderiv ℝ (fun y : E ↦ ‖y‖) x‖ = 1 := by
    filter_upwards [ae_differentiableAt_norm (E := E) (μ := volume)] with x hx
    exact norm_fderiv_norm hx
  have hcoarea := LipschitzWith.setLIntegral_slab_of_ae_norm_fderiv_eq_one
    (f := fun x : E ↦ ‖x‖) lipschitzWith_one_norm
      (w := fun _ : E ↦ 1) measurable_const (0 : ℝ) 1 hnorm
  have hslab : (fun x : E ↦ ‖x‖) ⁻¹' Ioc (0 : ℝ) 1 =
      closedBall (0 : E) 1 \ {0} := by
    ext x
    simp only [mem_preimage, mem_Ioc, mem_sdiff, mem_closedBall_zero_iff,
      mem_singleton_iff]
    constructor
    · rintro ⟨hpos, hle⟩
      exact ⟨hle, fun hx ↦ (norm_pos_iff.mp hpos) hx⟩
    · rintro ⟨hle, hne⟩
      exact ⟨(norm_pos_iff.mpr hne), hle⟩
  have hleft : (∫⁻ _x : E in (fun x : E ↦ ‖x‖) ⁻¹' Ioc (0 : ℝ) 1, 1) =
      volume (ball (0 : E) 1) := by
    rw [hslab, setLIntegral_one, measure_sdiff_null (measure_singleton 0),
      volume.addHaar_closedBall_eq_addHaar_ball]
  have hright :
      (∫⁻ t in Ioc (0 : ℝ) 1,
        scalarCoareaFiber (fun x : E ↦ ‖x‖) (fun _ ↦ 1) t) =
        standardSphereHausdorffMeasure d univ * (d : ℝ≥0∞)⁻¹ := by
    calc
      (∫⁻ t in Ioc (0 : ℝ) 1,
          scalarCoareaFiber (fun x : E ↦ ‖x‖) (fun _ ↦ 1) t) =
          ∫⁻ t in Ioc (0 : ℝ) 1,
            ENNReal.ofReal t ^ (d - 1) * standardSphereHausdorffMeasure d univ := by
        apply setLIntegral_congr_fun measurableSet_Ioc
        intro t ht
        exact scalarCoareaFiber_norm_one hd ht.1
      _ = (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal t ^ (d - 1)) *
          standardSphereHausdorffMeasure d univ := by
        rw [lintegral_mul_const]
        exact ENNReal.measurable_ofReal.pow_const (d - 1)
      _ = standardSphereHausdorffMeasure d univ * (d : ℝ≥0∞)⁻¹ := by
        rw [lintegral_ofReal_pow_Ioc_zero_one d hd, mul_comm]
  have hvolume : volume (ball (0 : E) 1) =
      standardSphereHausdorffMeasure d univ * (d : ℝ≥0∞)⁻¹ := by
    rw [← hleft, hcoarea, hright]
  calc
    standardSphereHausdorffMeasure d univ =
        standardSphereHausdorffMeasure d univ * 1 := (mul_one _).symm
    _ = standardSphereHausdorffMeasure d univ *
        ((d : ℝ≥0∞) * (d : ℝ≥0∞)⁻¹) := by
      rw [ENNReal.mul_inv_cancel (by exact_mod_cast Nat.pos_of_ne_zero hd |>.ne')
        (ENNReal.natCast_ne_top d)]
    _ = (d : ℝ≥0∞) *
        (standardSphereHausdorffMeasure d univ * (d : ℝ≥0∞)⁻¹) := by ac_rfl
    _ = (d : ℝ≥0∞) * volume (ball (0 : E) 1) := by rw [← hvolume]
    _ = ENNReal.ofReal
        ((d : ℝ) * volume.real (ball (0 : E) 1)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg d), ofReal_measureReal]
      simp

/-- Raw intrinsic-Hausdorff form of the exact Euclidean unit-sphere surface-area identity. -/
theorem euclideanHausdorffMeasure_unitSphere (d : ℕ) (hd : d ≠ 0) :
    (Measure.euclideanHausdorffMeasure (d - 1) :
      Measure (sphere (0 : EuclideanSpace ℝ (Fin d)) 1)) univ =
        ENNReal.ofReal
          ((d : ℝ) *
            volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) := by
  simpa [standardSphereHausdorffMeasure] using
    standardSphereHausdorffMeasure_apply_univ d hd

/-- Intrinsic unit-sphere Hausdorff measure is finite in every Euclidean dimension. -/
instance isFiniteMeasure_standardSphereHausdorffMeasure (d : ℕ) :
    IsFiniteMeasure (standardSphereHausdorffMeasure d) where
  measure_univ_lt_top := by
    by_cases hd : d = 0
    · subst d
      simp [standardSphereHausdorffMeasure]
    · rw [standardSphereHausdorffMeasure_apply_univ d hd]
      exact ENNReal.ofReal_lt_top

/-- Intrinsic unit-sphere Hausdorff measure is nonzero in every positive dimension. -/
theorem standardSphereHausdorffMeasure_ne_zero (d : ℕ) (hd : d ≠ 0) :
    standardSphereHausdorffMeasure d ≠ 0 := by
  rw [← Measure.measure_univ_ne_zero, standardSphereHausdorffMeasure_apply_univ d hd]
  apply ENNReal.ofReal_ne_zero_iff.mpr
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hballpos :
      0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
    apply ENNReal.toReal_pos
    · exact (Metric.measure_ball_pos volume
        (0 : EuclideanSpace ℝ (Fin d)) (by norm_num : (0 : ℝ) < 1)).ne'
    · exact (measure_ball_lt_top :
        volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) < ∞).ne
  exact mul_pos hdpos hballpos

/-- The total intrinsic Hausdorff mass of a positive-dimensional unit sphere is nonzero. -/
theorem standardSphereHausdorffMeasure_apply_univ_ne_zero (d : ℕ) (hd : d ≠ 0) :
    standardSphereHausdorffMeasure d univ ≠ 0 :=
  Measure.measure_univ_ne_zero.mpr (standardSphereHausdorffMeasure_ne_zero d hd)

instance neZero_standardSphereHausdorffMeasure (d : ℕ) [NeZero d] :
    NeZero (standardSphereHausdorffMeasure d) :=
  ⟨standardSphereHausdorffMeasure_ne_zero d (NeZero.ne d)⟩

end ProbabilityTheory
