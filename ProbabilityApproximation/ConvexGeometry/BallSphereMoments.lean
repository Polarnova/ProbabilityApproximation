/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities
import ProbabilityApproximation.ConvexGeometry.BallSphereMeasure

/-!
# Second moments of the rotation-invariant sphere probability

This file proves the exact spherical second moment and its Cauchy--Schwarz consequence used in
Keith Ball, *The reverse isoperimetric problem for Gaussian measure* (1993), p. 416, immediately
before equation (4).  The proof first establishes rotation invariance of Mathlib's normalized
`Measure.toSphere`, then computes the scalar covariance by its trace.
-/

open Set Metric MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace Pointwise

noncomputable section

namespace ProbabilityTheory

/-- A linear isometry equivalence restricted to the unit sphere. -/
def linearIsometryEquivUnitSphere {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (e : E ≃ₗᵢ[ℝ] E) : sphere (0 : E) 1 ≃ᵐ sphere (0 : E) 1 where
  toEquiv :=
    { toFun := fun θ ↦ ⟨e θ, by
        rw [mem_sphere_zero_iff_norm]
        simp [mem_sphere_zero_iff_norm.mp θ.prop]⟩
      invFun := fun θ ↦ ⟨e.symm θ, by
        rw [mem_sphere_zero_iff_norm]
        simp [mem_sphere_zero_iff_norm.mp θ.prop]⟩
      left_inv := fun θ ↦ by ext; simp
      right_inv := fun θ ↦ by ext; simp }
  measurable_toFun :=
    (e.continuous.measurable.comp measurable_subtype_coe).subtype_mk
  measurable_invFun :=
    (e.symm.continuous.measurable.comp measurable_subtype_coe).subtype_mk

@[simp]
theorem coe_linearIsometryEquivUnitSphere {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (e : E ≃ₗᵢ[ℝ] E) (θ : sphere (0 : E) 1) :
    ((linearIsometryEquivUnitSphere e θ : sphere (0 : E) 1) : E) = e θ := rfl

/-- Intrinsic Euclidean Hausdorff measure on the unit sphere is preserved by every ambient
linear isometry.  Unlike the normalized `Measure.toSphere` result below, this theorem needs no
comparison between the two sphere-measure constructions. -/
theorem measurePreserving_linearIsometryEquivUnitSphere_euclideanHausdorffMeasure
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (e : E ≃ₗᵢ[ℝ] E) (k : ℕ) :
    MeasurePreserving (linearIsometryEquivUnitSphere e)
      (Measure.euclideanHausdorffMeasure k)
      (Measure.euclideanHausdorffMeasure k) := by
  have hisometry : Isometry (linearIsometryEquivUnitSphere e) := by
    intro x y
    change edist (e (x : E)) (e (y : E)) = edist (x : E) (y : E)
    exact e.isometry.edist_eq x y
  refine ⟨(linearIsometryEquivUnitSphere e).measurable, ?_⟩
  rw [hisometry.map_euclideanHausdorffMeasure,
    (linearIsometryEquivUnitSphere e).surjective.range_eq,
    Measure.restrict_univ]

private theorem image_radialSector_linearIsometryEquiv {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (e : E ≃ₗᵢ[ℝ] E) (s : Set (sphere (0 : E) 1)) :
    e '' (Ioo (0 : ℝ) 1 • ((↑) '' s : Set E)) =
      Ioo (0 : ℝ) 1 •
        ((↑) '' (linearIsometryEquivUnitSphere e '' s) : Set E) := by
  ext y
  constructor
  · rintro ⟨z, ⟨r, hr, z', ⟨θ, hθ, rfl⟩, rfl⟩, rfl⟩
    refine ⟨r, hr, linearIsometryEquivUnitSphere e θ,
      ⟨linearIsometryEquivUnitSphere e θ, ⟨θ, hθ, rfl⟩, rfl⟩, ?_⟩
    exact (e.map_smul r θ).symm
  · rintro ⟨r, hr, z', ⟨θ', ⟨θ, hθ, rfl⟩, rfl⟩, rfl⟩
    refine ⟨r • (θ : E), ⟨r, hr, θ, ⟨θ, hθ, rfl⟩, rfl⟩, ?_⟩
    exact e.map_smul r θ

private theorem volume_image_linearIsometryEquiv {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] E) (s : Set E) :
    volume (e '' s) = volume s := by
  have himage : e '' s = (e.symm : E → E) ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      refine ⟨e.symm x, hx, ?_⟩
      simp
  rw [himage]
  have hmp : MeasurePreserving (e.symm.toMeasurableEquiv : E → E) volume volume :=
    e.symm.measurePreserving
  exact hmp.measure_preimage_equiv s

/-- Mathlib's canonical surface measure is invariant under every linear isometry equivalence. -/
theorem map_linearIsometryEquivUnitSphere_toSphere {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] E) :
    Measure.map (linearIsometryEquivUnitSphere e) volume.toSphere = volume.toSphere := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (linearIsometryEquivUnitSphere e).measurable hs,
    Measure.toSphere_apply' volume (hs.preimage (linearIsometryEquivUnitSphere e).measurable),
    Measure.toSphere_apply' volume hs]
  congr 1
  let t := (linearIsometryEquivUnitSphere e) ⁻¹' s
  have himageSphere : linearIsometryEquivUnitSphere e '' t = s := by
    exact (linearIsometryEquivUnitSphere e).surjective.image_preimage s
  calc
    volume (Ioo (0 : ℝ) 1 • ((↑) '' t : Set E)) =
        volume (e '' (Ioo (0 : ℝ) 1 • ((↑) '' t : Set E))) :=
      (volume_image_linearIsometryEquiv e _).symm
    _ = volume (Ioo (0 : ℝ) 1 •
        ((↑) '' (linearIsometryEquivUnitSphere e '' t) : Set E)) := by
      rw [image_radialSector_linearIsometryEquiv]
    _ = volume (Ioo (0 : ℝ) 1 • ((↑) '' s : Set E)) := by rw [himageSphere]

/-- The normalized unit-sphere probability is invariant under linear isometry equivalences. -/
theorem map_linearIsometryEquivUnitSphere_standardSphereProbability
    {d : ℕ} (hd : d ≠ 0)
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Measure.map (linearIsometryEquivUnitSphere e)
        (standardSphereProbability d hd).toMeasure =
      (standardSphereProbability d hd).toMeasure := by
  calc
    Measure.map (linearIsometryEquivUnitSphere e)
        (standardSphereProbability d hd).toMeasure =
        Measure.map (linearIsometryEquivUnitSphere e)
          ((standardSphereSurfaceFiniteMeasure d).mass⁻¹ • volume.toSphere) := by
      rw [standardSphereProbability_toMeasure]
    _ = (standardSphereSurfaceFiniteMeasure d).mass⁻¹ •
        Measure.map (linearIsometryEquivUnitSphere e) volume.toSphere := by
      rw [Measure.map_smul]
    _ = (standardSphereSurfaceFiniteMeasure d).mass⁻¹ • volume.toSphere := by
      rw [map_linearIsometryEquivUnitSphere_toSphere]
    _ = (standardSphereProbability d hd).toMeasure :=
      (standardSphereProbability_toMeasure d hd).symm

/-- The sphere restriction of a Euclidean linear isometry is measure-preserving for the
normalized surface probability. -/
theorem measurePreserving_linearIsometryEquivUnitSphere_standardSphereProbability
    {d : ℕ} (hd : d ≠ 0)
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    MeasurePreserving (linearIsometryEquivUnitSphere e)
      (standardSphereProbability d hd).toMeasure
      (standardSphereProbability d hd).toMeasure :=
  ⟨(linearIsometryEquivUnitSphere e).measurable,
    map_linearIsometryEquivUnitSphere_standardSphereProbability hd e⟩

private theorem integrable_inner_sq_standardSphereProbability
    {d : ℕ} (hd : d ≠ 0) (u : EuclideanSpace ℝ (Fin d)) :
    Integrable
      (fun θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ↦
        inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u ^ 2)
      (standardSphereProbability d hd).toMeasure := by
  refine Integrable.of_bound (by fun_prop) (‖u‖ ^ 2) ?_
  filter_upwards with θ
  have hθnorm : ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp θ.prop
  have hinner :
      ‖inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u‖ ≤ ‖u‖ := by
    calc
      ‖inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u‖ ≤
          ‖(θ : EuclideanSpace ℝ (Fin d))‖ * ‖u‖ := norm_inner_le_norm _ _
      _ = ‖u‖ := by rw [hθnorm, one_mul]
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hinner 2

private theorem integral_inner_sq_linearIsometryEquiv {d : ℕ}
    (hd : d ≠ 0)
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d)) :
    (∫ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u ^ 2
        ∂(standardSphereProbability d hd).toMeasure) =
      ∫ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        inner ℝ (θ : EuclideanSpace ℝ (Fin d)) (e u) ^ 2
        ∂(standardSphereProbability d hd).toMeasure := by
  have h :=
    (measurePreserving_linearIsometryEquivUnitSphere_standardSphereProbability hd e).integral_comp
      (linearIsometryEquivUnitSphere e).measurableEmbedding
      (fun θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ↦
        inner ℝ (θ : EuclideanSpace ℝ (Fin d)) (e u) ^ 2)
  simpa using h

private theorem integral_inner_sq_smul {d : ℕ}
    (hd : d ≠ 0) (c : ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    (∫ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        inner ℝ (θ : EuclideanSpace ℝ (Fin d)) (c • u) ^ 2
        ∂(standardSphereProbability d hd).toMeasure) =
      c ^ 2 *
        ∫ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
          inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u ^ 2
          ∂(standardSphereProbability d hd).toMeasure := by
  simp_rw [real_inner_smul_right, mul_pow]
  exact integral_const_mul _ _

/-- The exact covariance of rotation-invariant probability on the Euclidean unit sphere.  This is
the spherical second-moment identity used in Ball (1993), p. 416. -/
theorem integral_inner_sq_standardSphereProbability {d : ℕ} (hd : d ≠ 0)
    (u : EuclideanSpace ℝ (Fin d)) :
    ∫ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u ^ 2
      ∂(standardSphereProbability d hd : Measure _) = ‖u‖ ^ 2 / d := by
  let i0 : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
  let b : Fin d → EuclideanSpace ℝ (Fin d) :=
    fun i ↦ EuclideanSpace.single i 1
  let q : EuclideanSpace ℝ (Fin d) → ℝ := fun v ↦
    ∫ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v ^ 2
      ∂(standardSphereProbability d hd : Measure _)
  have hbNorm (i : Fin d) : ‖b i‖ = 1 := by simp [b]
  have hcoord (i : Fin d) : q (b i) = q (b i0) := by
    let R : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
      (ℝ ∙ (b i - b i0))ᗮ.reflection
    have hR : R (b i) = b i0 := by
      exact Submodule.reflection_sub (by rw [hbNorm i, hbNorm i0])
    have hinv := integral_inner_sq_linearIsometryEquiv hd R (b i)
    change q (b i) = q (R (b i)) at hinv
    rw [hR] at hinv
    exact hinv
  have htrace : ∑ i : Fin d, q (b i) = 1 := by
    have hint := integral_finsetSum (μ := (standardSphereProbability d hd).toMeasure)
      Finset.univ (fun i _ ↦ integrable_inner_sq_standardSphereProbability hd (b i))
    have hpoint (θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
        (∑ i : Fin d, inner ℝ (θ : EuclideanSpace ℝ (Fin d)) (b i) ^ 2) = 1 := by
      simp_rw [b, EuclideanSpace.inner_single_right]
      simp only [one_mul, starRingEnd_apply, star_trivial]
      rw [← EuclideanSpace.real_norm_sq_eq]
      rw [mem_sphere_zero_iff_norm.mp θ.prop, one_pow]
    change (∫ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      ∑ i : Fin d, inner ℝ (θ : EuclideanSpace ℝ (Fin d)) (b i) ^ 2
      ∂(standardSphereProbability d hd).toMeasure) =
        ∑ i : Fin d, q (b i) at hint
    rw [← hint]
    calc
      (∫ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
          ∑ i : Fin d, inner ℝ (θ : EuclideanSpace ℝ (Fin d)) (b i) ^ 2
          ∂(standardSphereProbability d hd).toMeasure) =
          ∫ _θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1, (1 : ℝ)
            ∂(standardSphereProbability d hd).toMeasure := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = 1 := by simp
  have hdimq : (d : ℝ) * q (b i0) = 1 := by
    rw [show (∑ i : Fin d, q (b i)) = ∑ _i : Fin d, q (b i0) by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hcoord i] at htrace
    simpa [nsmul_eq_mul] using htrace
  have hq : q (b i0) = 1 / (d : ℝ) := by
    apply (eq_div_iff (Nat.cast_ne_zero.mpr hd)).2
    rw [mul_comm]
    exact hdimq
  by_cases hu : u = 0
  · simp [hu]
  · let v : EuclideanSpace ℝ (Fin d) := ‖u‖ • b i0
    have hvNorm : ‖v‖ = ‖u‖ := by
      rw [show v = ‖u‖ • b i0 by rfl, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg u), hbNorm i0, mul_one]
    let R : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
      (ℝ ∙ (u - v))ᗮ.reflection
    have hR : R u = v := Submodule.reflection_sub hvNorm.symm
    have hinv := integral_inner_sq_linearIsometryEquiv hd R u
    change q u = q (R u) at hinv
    rw [hR] at hinv
    have hsmul := integral_inner_sq_smul hd ‖u‖ (b i0)
    change q v = ‖u‖ ^ 2 * q (b i0) at hsmul
    calc
      q u = q v := hinv
      _ = ‖u‖ ^ 2 * q (b i0) := hsmul
      _ = ‖u‖ ^ 2 * (1 / (d : ℝ)) := by rw [hq]
      _ = ‖u‖ ^ 2 / d := by ring

/-- The spherical first absolute moment is bounded by the square root of the second moment.  In
Ball's projection average this contributes the factor `d⁻¹ᐟ²`. -/
theorem integral_abs_inner_standardSphereProbability_le {d : ℕ} (hd : d ≠ 0)
    (u : EuclideanSpace ℝ (Fin d)) :
    ∫ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u|
      ∂(standardSphereProbability d hd : Measure _) ≤ ‖u‖ / Real.sqrt d := by
  let μ : Measure (sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    (standardSphereProbability d hd).toMeasure
  let f : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ :=
    fun θ ↦ |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) u|
  have hfsq : Integrable (fun θ ↦ f θ ^ 2) μ := by
    have h := integrable_inner_sq_standardSphereProbability hd u
    apply h.congr
    exact Filter.Eventually.of_forall fun θ ↦ by simp [f, sq_abs]
  have hfmem : MemLp f 2 μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 hfsq
  have hfmem' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hfmem
  have hholder : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg hholder
    (μ := μ) (f := f) (g := fun _ ↦ (1 : ℝ))
    (Filter.Eventually.of_forall fun θ ↦ abs_nonneg _)
    (Filter.Eventually.of_forall fun _ ↦ zero_le_one)
    hfmem' (memLp_const 1)
  have hineq : (∫ θ, f θ ∂μ) ≤ (∫ θ, f θ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    simpa using hcs
  have hsecond : (∫ θ, f θ ^ 2 ∂μ) = ‖u‖ ^ 2 / (d : ℝ) := by
    simpa [μ, f, sq_abs] using integral_inner_sq_standardSphereProbability hd u
  change (∫ θ, f θ ∂μ) ≤ ‖u‖ / Real.sqrt d
  calc
    (∫ θ, f θ ∂μ) ≤ (∫ θ, f θ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := hineq
    _ = (‖u‖ ^ 2 / (d : ℝ)) ^ (1 / 2 : ℝ) := by rw [hsecond]
    _ = Real.sqrt (‖u‖ ^ 2 / (d : ℝ)) := (Real.sqrt_eq_rpow _).symm
    _ = Real.sqrt (‖u‖ ^ 2) / Real.sqrt (d : ℝ) := by
      rw [Real.sqrt_div (sq_nonneg ‖u‖)]
    _ = ‖u‖ / Real.sqrt d := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg u)]

end ProbabilityTheory
