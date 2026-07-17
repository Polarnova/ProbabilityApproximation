/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.Bentkus.Induction.IdentityCovarianceReduction

/-!
# Gaussian-density comparison lemmas for Bentkus's induction

This module collects the first-, second-, and third-density integrability estimates, conditional
Gaussian integration-by-parts identities, two-shift Taylor estimates, and the reusable second-order
remainder bound used by both angle regimes.
-/

open MeasureTheory InnerProductSpace Matrix Set
open scoped ENNReal MatrixOrder Pointwise RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

universe u

local instance gaussianDensityComparisonConvexSpace {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

local instance gaussianDensityComparisonIsModuleConvexSpace {d : ℕ} :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.ofModule

namespace BentkusInduction

set_option maxHeartbeats 2000000

/-- The first standard-Gaussian density contraction has its expected dimension-free `L¹`
bound. -/
lemma integral_abs_standardGaussianDensityD1_volume_le
    {d : ℕ} (g : EuclideanSpace ℝ (Fin d)) :
    ∫ x, |standardGaussianDensityD1 x g| ∂volume ≤ ‖g‖ := by
  have hEq :
      (∫ x : EuclideanSpace ℝ (Fin d), |inner ℝ x g|
          ∂stdGaussian (EuclideanSpace ℝ (Fin d))) =
        ∫ x, |standardGaussianDensityD1 x g| ∂volume := by
    rw [stdGaussian_eq_withDensity_standardGaussianDensityReal,
      integral_withDensity_eq_integral_toReal_smul]
    · apply integral_congr_ae
      filter_upwards with x
      rw [ENNReal.toReal_ofReal (standardGaussianDensityReal_nonneg _)]
      simp only [smul_eq_mul]
      unfold standardGaussianDensityD1
      have hdensityAbs : |standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x| =
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x := abs_of_nonneg (by
          rw [← standardGaussianDensityReal_eq_standardGaussianDensity]
          exact standardGaussianDensityReal_nonneg x)
      rw [standardGaussianDensityReal_eq_standardGaussianDensity,
        abs_mul, abs_neg, hdensityAbs]
      ring
    · exact measurable_standardGaussianDensityReal.ennreal_ofReal
    · filter_upwards with x
      simp
  rw [← hEq]
  simpa only [real_inner_comm] using integral_abs_inner_stdGaussian_le_norm g


/-- The second standard-Gaussian density contraction is integrable over Euclidean volume. -/
lemma integrable_standardGaussianDensityD2_volume
    {d : ℕ} (h g : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x ↦ standardGaussianDensityD2 x h g) volume := by
  let E := EuclideanSpace ℝ (Fin d)
  have heqh : (fun x : E ↦ inner ℝ x h) = innerSL ℝ h := by
    funext x
    exact (real_inner_comm x h).symm
  have heqg : (fun x : E ↦ inner ℝ x g) = innerSL ℝ g := by
    funext x
    exact (real_inner_comm x g).symm
  have hh2 : MemLp (fun x : E ↦ inner ℝ x h) 2 (stdGaussian E) := by
    have hm := IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ h) 2 (by norm_num)
    rw [heqh]
    exact hm
  have hg2 : MemLp (fun x : E ↦ inner ℝ x g) 2 (stdGaussian E) := by
    have hm := IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ g) 2 (by norm_num)
    rw [heqg]
    exact hm
  have hq : Integrable (fun x : E ↦
      inner ℝ x h * inner ℝ x g - inner ℝ h g) (stdGaussian E) :=
    (hh2.integrable_mul hg2).sub (integrable_const _)
  rw [stdGaussian_eq_withDensity_standardGaussianDensityReal] at hq
  have hweighted := (integrable_withDensity_iff_integrable_smul'
    measurable_standardGaussianDensityReal.ennreal_ofReal (by simp)).mp hq
  simp_rw [ENNReal.toReal_ofReal (standardGaussianDensityReal_nonneg _),
    smul_eq_mul] at hweighted
  apply hweighted.congr
  filter_upwards with x
  unfold standardGaussianDensityD2
  rw [standardGaussianDensityReal_eq_standardGaussianDensity]
  ring

/-- A coarse quadratic-moment majorant for the second density contraction, sufficient for the
Fubini exchange in Bentkus (3.18). -/
lemma integral_abs_standardGaussianDensityD2_volume_le
    {d : ℕ} (h g : EuclideanSpace ℝ (Fin d)) :
    ∫ x, |standardGaussianDensityD2 x h g| ∂volume ≤
      (‖h‖ ^ 2 + ‖g‖ ^ 2) / 2 + ‖h‖ * ‖g‖ := by
  let E := EuclideanSpace ℝ (Fin d)
  let q : E → ℝ := fun x ↦ inner ℝ x h * inner ℝ x g - inner ℝ h g
  have hEq : (∫ x : E, |q x| ∂stdGaussian E) =
      ∫ x, |standardGaussianDensityD2 x h g| ∂volume := by
    rw [stdGaussian_eq_withDensity_standardGaussianDensityReal,
      integral_withDensity_eq_integral_toReal_smul]
    · apply integral_congr_ae
      filter_upwards with x
      rw [ENNReal.toReal_ofReal (standardGaussianDensityReal_nonneg _)]
      simp only [smul_eq_mul]
      unfold standardGaussianDensityD2
      have hdensityAbs : |standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x| =
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x := abs_of_nonneg (by
          rw [← standardGaussianDensityReal_eq_standardGaussianDensity]
          exact standardGaussianDensityReal_nonneg x)
      rw [standardGaussianDensityReal_eq_standardGaussianDensity,
        abs_mul, hdensityAbs]
      dsimp only [q]
      ring
    · exact measurable_standardGaussianDensityReal.ennreal_ofReal
    · filter_upwards with x
      simp
  have hmajorInt : Integrable (fun x : E ↦
      ((inner ℝ x h) ^ 2 + (inner ℝ x g) ^ 2) / 2 + |inner ℝ h g|)
      (stdGaussian E) := by
    have hh := (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ h) 2 (by norm_num)
      ).integrable_norm_pow (by norm_num)
    have hg' := (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ g) 2 (by norm_num)
      ).integrable_norm_pow (by norm_num)
    have hh' : Integrable (fun x : E ↦ (inner ℝ x h) ^ 2) (stdGaussian E) := by
      simpa only [Real.norm_eq_abs, sq_abs, real_inner_comm, innerSL_apply_apply] using hh
    have hg'' : Integrable (fun x : E ↦ (inner ℝ x g) ^ 2) (stdGaussian E) := by
      simpa only [Real.norm_eq_abs, sq_abs, real_inner_comm, innerSL_apply_apply] using hg'
    exact ((hh'.add hg'').div_const 2).add (integrable_const _)
  have hqInt : Integrable q (stdGaussian E) := by
    have hh2 : MemLp (fun x : E ↦ inner ℝ x h) 2 (stdGaussian E) := by
      have hm := IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ h) 2 (by norm_num)
      have heq : (fun x : E ↦ inner ℝ x h) = innerSL ℝ h := by
        funext x
        exact (real_inner_comm x h).symm
      rw [heq]
      exact hm
    have hg2 : MemLp (fun x : E ↦ inner ℝ x g) 2 (stdGaussian E) := by
      have hm := IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ g) 2 (by norm_num)
      have heq : (fun x : E ↦ inner ℝ x g) = innerSL ℝ g := by
        funext x
        exact (real_inner_comm x g).symm
      rw [heq]
      exact hm
    exact (hh2.integrable_mul hg2).sub (integrable_const _)
  rw [← hEq]
  calc
    (∫ x : E, |q x| ∂stdGaussian E) ≤
        ∫ x : E, ((inner ℝ x h) ^ 2 + (inner ℝ x g) ^ 2) / 2 +
          |inner ℝ h g| ∂stdGaussian E := by
      apply integral_mono hqInt.abs hmajorInt
      intro x
      dsimp only [q]
      calc
        |inner ℝ x h * inner ℝ x g - inner ℝ h g| ≤
            |inner ℝ x h * inner ℝ x g| + |inner ℝ h g| := abs_sub _ _
        _ ≤ ((inner ℝ x h) ^ 2 + (inner ℝ x g) ^ 2) / 2 +
            |inner ℝ h g| := by
          rw [abs_mul]
          nlinarith [sq_nonneg (|inner ℝ x h| - |inner ℝ x g|),
            sq_abs (inner ℝ x h), sq_abs (inner ℝ x g)]
    _ = (‖h‖ ^ 2 + ‖g‖ ^ 2) / 2 + |inner ℝ h g| := by
      have hhInt : Integrable (fun x : E ↦ (inner ℝ x h) ^ 2) (stdGaussian E) := by
        have hh := (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ h) 2 (by norm_num)
          ).integrable_norm_pow (by norm_num)
        simpa only [Real.norm_eq_abs, sq_abs, real_inner_comm, innerSL_apply_apply] using hh
      have hgInt : Integrable (fun x : E ↦ (inner ℝ x g) ^ 2) (stdGaussian E) := by
        have hg' := (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ g) 2 (by norm_num)
          ).integrable_norm_pow (by norm_num)
        simpa only [Real.norm_eq_abs, sq_abs, real_inner_comm, innerSL_apply_apply] using hg'
      have hhEq : (∫ x : E, (inner ℝ x h) ^ 2 ∂stdGaussian E) = ‖h‖ ^ 2 := by
        simpa only [real_inner_comm] using integral_inner_sq_stdGaussian h
      have hgEq : (∫ x : E, (inner ℝ x g) ^ 2 ∂stdGaussian E) = ‖g‖ ^ 2 := by
        simpa only [real_inner_comm] using integral_inner_sq_stdGaussian g
      calc
        (∫ x : E, ((inner ℝ x h) ^ 2 + (inner ℝ x g) ^ 2) / 2 +
            |inner ℝ h g| ∂stdGaussian E) =
            (∫ x : E, ((inner ℝ x h) ^ 2 + (inner ℝ x g) ^ 2) / 2
              ∂stdGaussian E) +
              ∫ _x : E, |inner ℝ h g| ∂stdGaussian E := by
          exact integral_add ((hhInt.add hgInt).div_const 2) (integrable_const _)
        _ = ((∫ x : E, (inner ℝ x h) ^ 2 + (inner ℝ x g) ^ 2
              ∂stdGaussian E) / 2) +
              ∫ _x : E, |inner ℝ h g| ∂stdGaussian E := by
          rw [integral_div]
        _ = (((∫ x : E, (inner ℝ x h) ^ 2 ∂stdGaussian E) +
              ∫ x : E, (inner ℝ x g) ^ 2 ∂stdGaussian E) / 2) +
              ∫ _x : E, |inner ℝ h g| ∂stdGaussian E := by
          rw [integral_add hhInt hgInt]
        _ = (‖h‖ ^ 2 + ‖g‖ ^ 2) / 2 + |inner ℝ h g| := by
          rw [hhEq, hgEq, integral_const, probReal_univ, one_smul]
    _ ≤ (‖h‖ ^ 2 + ‖g‖ ^ 2) / 2 + ‖h‖ * ‖g‖ := by
      gcongr
      exact abs_real_inner_le_norm h g


lemma integrable_prod_bounded_mul_standardGaussianDensityD1
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ] {μ : Measure Θ} [SFinite μ]
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφm : Measurable φ) (hφ : ∀ x, |φ x| ≤ 1)
    {g : Θ → EuclideanSpace ℝ (Fin d)} (hgm : Measurable g)
    (hg : Integrable g μ) :
    Integrable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦
      φ p.2 * standardGaussianDensityD1 p.2 (g p.1)) (μ.prod volume) := by
  let F : Θ × EuclideanSpace ℝ (Fin d) → ℝ := fun p ↦
    φ p.2 * standardGaussianDensityD1 p.2 (g p.1)
  have hFm : Measurable F := by
    dsimp only [F]
    unfold standardGaussianDensityD1
    have hinner : Measurable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦
        inner ℝ p.2 (g p.1)) := by
      change Measurable ((fun q : EuclideanSpace ℝ (Fin d) ×
          EuclideanSpace ℝ (Fin d) ↦ inner ℝ q.1 q.2) ∘
        fun p : Θ × EuclideanSpace ℝ (Fin d) ↦ (p.2, g p.1))
      exact continuous_inner.measurable.comp
        (measurable_snd.prodMk (hgm.comp measurable_fst))
    exact (hφm.comp measurable_snd).mul
      (hinner.neg.mul (continuous_standardGaussianDensity.measurable.comp measurable_snd))
  apply (integrable_prod_iff hFm.aestronglyMeasurable).2
  constructor
  · filter_upwards with z
    exact (integrable_standardGaussianDensityD1_volume (g z)).bdd_mul
      hφm.aestronglyMeasurable (by
        filter_upwards with x
        simpa only [Real.norm_eq_abs] using hφ x)
  · have hinnerMeas : AEStronglyMeasurable
        (fun z ↦ ∫ x, ‖F (z, x)‖ ∂volume) μ :=
      hFm.aestronglyMeasurable.norm.integral_prod_right'
    apply hg.norm.mono' hinnerMeas
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x ↦ norm_nonneg _)]
    calc
      (∫ x, ‖F (z, x)‖ ∂volume) ≤
          ∫ x, |standardGaussianDensityD1 x (g z)| ∂volume := by
        apply integral_mono
        · exact ((integrable_standardGaussianDensityD1_volume (g z)).bdd_mul
            hφm.aestronglyMeasurable (by
              filter_upwards with x
              simpa only [Real.norm_eq_abs] using hφ x)).norm
        · exact (integrable_standardGaussianDensityD1_volume (g z)).abs
        · intro x
          dsimp only [F]
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hφ x)
      _ ≤ ‖g z‖ := integral_abs_standardGaussianDensityD1_volume_le (g z)

/-- Translation in the Euclidean variable does not change the `L¹` majorant for the first
Gaussian-density contraction. -/
lemma integrable_prod_bounded_mul_standardGaussianDensityD1_sub
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ] {μ : Measure Θ} [SFinite μ]
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφm : Measurable φ) (hφ : ∀ x, |φ x| ≤ 1)
    {h g : Θ → EuclideanSpace ℝ (Fin d)} (hhm : Measurable h) (hgm : Measurable g)
    (hg : Integrable g μ) :
    Integrable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦
      φ p.2 * standardGaussianDensityD1 (p.2 - h p.1) (g p.1))
      (μ.prod volume) := by
  let F : Θ × EuclideanSpace ℝ (Fin d) → ℝ := fun p ↦
    φ p.2 * standardGaussianDensityD1 (p.2 - h p.1) (g p.1)
  have hFm : Measurable F := by
    dsimp only [F]
    unfold standardGaussianDensityD1
    have hx : Measurable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦ p.2) := measurable_snd
    have hh' : Measurable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦ h p.1) :=
      hhm.comp measurable_fst
    have hg' : Measurable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦ g p.1) :=
      hgm.comp measurable_fst
    have hshift : Measurable
        (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦ p.2 - h p.1) := hx.sub hh'
    have hinner : Measurable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦
        inner ℝ (p.2 - h p.1) (g p.1)) := by
      change Measurable ((fun q : EuclideanSpace ℝ (Fin d) ×
          EuclideanSpace ℝ (Fin d) ↦ inner ℝ q.1 q.2) ∘
        fun p : Θ × EuclideanSpace ℝ (Fin d) ↦ (p.2 - h p.1, g p.1))
      exact continuous_inner.measurable.comp (hshift.prodMk hg')
    exact (hφm.comp hx).mul
      (hinner.neg.mul (continuous_standardGaussianDensity.measurable.comp hshift))
  apply (integrable_prod_iff hFm.aestronglyMeasurable).2
  constructor
  · filter_upwards with z
    exact ((integrable_standardGaussianDensityD1_volume (g z)).comp_sub_right (h z)).bdd_mul
      hφm.aestronglyMeasurable (by
        filter_upwards with x
        simpa only [Real.norm_eq_abs] using hφ x)
  · have hinnerMeas : AEStronglyMeasurable
        (fun z ↦ ∫ x, ‖F (z, x)‖ ∂volume) μ :=
      hFm.aestronglyMeasurable.norm.integral_prod_right'
    apply hg.norm.mono' hinnerMeas
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x ↦ norm_nonneg _)]
    calc
      (∫ x, ‖F (z, x)‖ ∂volume) ≤
          ∫ x, |standardGaussianDensityD1 (x - h z) (g z)| ∂volume := by
        apply integral_mono
        · exact (((integrable_standardGaussianDensityD1_volume (g z)).comp_sub_right (h z)
            ).bdd_mul hφm.aestronglyMeasurable (by
              filter_upwards with x
              simpa only [Real.norm_eq_abs] using hφ x)).norm
        · exact ((integrable_standardGaussianDensityD1_volume (g z)).comp_sub_right (h z)).abs
        · intro x
          dsimp only [F]
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hφ x)
      _ = ∫ x, |standardGaussianDensityD1 x (g z)| ∂volume := by
        exact integral_sub_right_eq_self
          (fun x ↦ |standardGaussianDensityD1 x (g z)|) (h z)
      _ ≤ ‖g z‖ := integral_abs_standardGaussianDensityD1_volume_le (g z)

/-- A bounded convex cutoff times a translated first Gaussian-density contraction is
product-integrable against any finite parameter measure. -/
private theorem integrable_prod_convexSetCutoff_affine_mul_standardGaussianDensityD1_sub
    {d : ℕ} {ν : Measure (EuclideanSpace ℝ (Fin d))}
    [SFinite ν] [IsFiniteMeasure ν]
    (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (P : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (p q : ℝ) (r a g : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      convexSetCutoff s ε (P (q • z.2 + p • z.1) + r) *
        standardGaussianDensityD1 (z.2 - a) g) (ν.prod volume) := by
  let F : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ := fun z ↦
    convexSetCutoff s ε (P (q • z.2 + p • z.1) + r) *
      standardGaussianDensityD1 (z.2 - a) g
  have hFm : Measurable F := by
    dsimp only [F]
    exact
      ((measurable_convexSetCutoff s ε).comp (by fun_prop)).mul
        ((continuous_standardGaussianDensityD1 g).measurable.comp (by fun_prop))
  have hD1 : Integrable
      (fun x : EuclideanSpace ℝ (Fin d) ↦
        standardGaussianDensityD1 (x - a) g) volume :=
    (integrable_standardGaussianDensityD1_volume g).comp_sub_right a
  apply (integrable_prod_iff hFm.aestronglyMeasurable).2
  constructor
  · filter_upwards with u
    apply hD1.bdd_mul
      ((measurable_convexSetCutoff s ε).comp (by fun_prop)).aestronglyMeasurable
    filter_upwards with x
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (convexSetCutoff_nonneg s ε _)]
    exact convexSetCutoff_le_one s ε _
  · have hinnerMeas : AEStronglyMeasurable
        (fun u ↦ ∫ x, ‖F (u, x)‖ ∂volume) ν :=
      hFm.aestronglyMeasurable.norm.integral_prod_right'
    apply Integrable.of_bound hinnerMeas ‖g‖
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x ↦ norm_nonneg _)]
    calc
      (∫ x, ‖F (u, x)‖ ∂volume) ≤
          ∫ x, |standardGaussianDensityD1 (x - a) g| ∂volume := by
        apply integral_mono
        · exact (hD1.bdd_mul
            ((measurable_convexSetCutoff s ε).comp (by fun_prop)
              ).aestronglyMeasurable (by
                filter_upwards with x
                simp only [Function.comp_apply]
                rw [Real.norm_eq_abs,
                  abs_of_nonneg (convexSetCutoff_nonneg s ε _)]
                exact convexSetCutoff_le_one s ε _)).norm
        · exact hD1.abs
        · intro x
          dsimp only [F]
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _)
            (by
              rw [abs_of_nonneg (convexSetCutoff_nonneg s ε _)]
              exact convexSetCutoff_le_one s ε _)
      _ = ∫ x, |standardGaussianDensityD1 x g| ∂volume := by
        exact integral_sub_right_eq_self
          (fun x ↦ |standardGaussianDensityD1 x g|) a
      _ ≤ ‖g‖ := integral_abs_standardGaussianDensityD1_volume_le g

/-- Conditioning a scalar Gaussian mixture and integrating by parts in its Gaussian coordinate
produces the translated first-density contraction used in Bentkus's large-angle argument. -/
private theorem
    integral_fderiv_convexSetCutoff_map_prod_weightedAdd_eq_neg_conditional_D1
    {d : ℕ} {ν : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure ν]
    (s : Set (EuclideanSpace ℝ (Fin d)))
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (p q : ℝ) (hq : q ≠ 0)
    (r r' : EuclideanSpace ℝ (Fin d)) :
    let e := bentkusWhiteningEquiv S hS
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let L : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) →
        EuclideanSpace ℝ (Fin d) := fun z ↦ q • z.1 + p • z.2
    (∫ w, (fderiv ℝ (convexSetCutoff s ε) (P w + r)) r' ∂((γ.prod ν).map L)) =
      -∫ x, (∫ u, convexSetCutoff s ε (P (q • x + p • u)) ∂ν) *
        standardGaussianDensityD1
          (x - q⁻¹ • B r) (q⁻¹ • B r') ∂volume := by
  let e := bentkusWhiteningEquiv S hS
  let P := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let L : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) := fun z ↦ q • z.1 + p • z.2
  let F : EuclideanSpace ℝ (Fin d) → ℝ := fun w ↦
    (fderiv ℝ (convexSetCutoff s ε) (P w + r)) r'
  let a := q⁻¹ • B r
  let g := q⁻¹ • B r'
  have hLm : Measurable L := by
    dsimp only [L]
    fun_prop
  have hFm : Measurable F := by
    dsimp only [F]
    exact ((contDiff_convexSetCutoff hs hε).continuous_fderiv_apply
      (by norm_num)).measurable.comp
        (((P.continuous.comp continuous_id).measurable.add measurable_const).prodMk
          measurable_const)
  have hFLm : Measurable (F ∘ L) := hFm.comp hLm
  have hFLint : Integrable (F ∘ L) (γ.prod ν) := by
    apply Integrable.of_bound hFLm.aestronglyMeasurable ((2 / ε) * ‖r'‖)
    filter_upwards with z
    rw [Real.norm_eq_abs]
    have happly := ContinuousLinearMap.le_opNorm
      (fderiv ℝ (convexSetCutoff s ε) (P (L z) + r)) r'
    calc
      |(F ∘ L) z| =
          ‖(fderiv ℝ (convexSetCutoff s ε) (P (L z) + r)) r'‖ := by
        rw [Real.norm_eq_abs]
        rfl
      _ ≤ ‖fderiv ℝ (convexSetCutoff s ε) (P (L z) + r)‖ * ‖r'‖ := happly
      _ ≤ (2 / ε) * ‖r'‖ :=
        mul_le_mul_of_nonneg_right
          (norm_fderiv_convexSetCutoff_le hs hε _) (norm_nonneg _)
  have hPB (x : EuclideanSpace ℝ (Fin d)) : P (B x) = x := by
    dsimp only [P, B, e]
    exact (bentkusWhiteningEquiv S hS).symm_apply_apply x
  have hqa : q • a = B r := by
    dsimp only [a]
    rw [smul_smul, mul_inv_cancel₀ hq, one_smul]
  have hibp (u : EuclideanSpace ℝ (Fin d)) :
      (∫ x, F (L (x, u)) ∂γ) =
        -∫ x, convexSetCutoff s ε (P (q • x + p • u)) *
          standardGaussianDensityD1 (x - a) g ∂volume := by
    have hbase :=
      integral_fderiv_convexSetCutoff_scaled_unwhitening_stdGaussian_eq_neg_D1
        hs hε S hS hq (P (p • u) + r) r'
    have hbase' :
        (∫ x, F (L (x, u)) ∂γ) =
          -∫ x, convexSetCutoff s ε (P (q • x + p • u) + r) *
            standardGaussianDensityD1 x g ∂volume := by
      simpa only [F, L, γ, P, B, e, g, map_add, map_smul, add_assoc] using hbase
    have htranslate :
        (∫ x, convexSetCutoff s ε (P (q • x + p • u) + r) *
            standardGaussianDensityD1 x g ∂volume) =
          ∫ x, convexSetCutoff s ε (P (q • x + p • u)) *
            standardGaussianDensityD1 (x - a) g ∂volume := by
      calc
        (∫ x, convexSetCutoff s ε (P (q • x + p • u) + r) *
            standardGaussianDensityD1 x g ∂volume) =
            ∫ x, convexSetCutoff s ε (P (q • (x + a) + p • u)) *
              standardGaussianDensityD1 ((x + a) - a) g ∂volume := by
          apply integral_congr_ae
          filter_upwards with x
          have hcutarg :
              P (q • x + p • u) + r = P (q • (x + a) + p • u) := by
            rw [smul_add, hqa, map_add, map_add, map_add, hPB]
            abel
          rw [hcutarg, show (x + a) - a = x by abel]
        _ = ∫ x, convexSetCutoff s ε (P (q • x + p • u)) *
              standardGaussianDensityD1 (x - a) g ∂volume :=
          integral_add_right_eq_self
            (fun x ↦ convexSetCutoff s ε (P (q • x + p • u)) *
              standardGaussianDensityD1 (x - a) g) a
    rw [hbase', htranslate]
  have hkernel : Integrable
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        convexSetCutoff s ε (P (q • z.2 + p • z.1)) *
          standardGaussianDensityD1 (z.2 - a) g) (ν.prod volume) := by
    simpa only [add_zero] using
      integrable_prod_convexSetCutoff_affine_mul_standardGaussianDensityD1_sub
        (ν := ν) s ε P p q 0 a g
  have hmap :
      (∫ w, F w ∂((γ.prod ν).map L)) =
        ∫ z, F (L z) ∂(γ.prod ν) :=
    integral_map hLm.aemeasurable hFm.aestronglyMeasurable
  calc
    (∫ w, F w ∂((γ.prod ν).map L)) =
        ∫ z, F (L z) ∂(γ.prod ν) := hmap
    _ = ∫ u, ∫ x, F (L (x, u)) ∂γ ∂ν := by
      calc
        (∫ z, F (L z) ∂(γ.prod ν)) =
            ∫ z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
              F (L z.swap) ∂(ν.prod γ) :=
          (integral_prod_swap (F ∘ L)).symm
        _ = ∫ u, ∫ x, F (L (x, u)) ∂γ ∂ν := by
          simpa only [Function.comp_apply, Prod.swap_prod_mk] using
            integral_prod ((F ∘ L) ∘ Prod.swap) hFLint.swap
    _ = ∫ u, -(∫ x, convexSetCutoff s ε (P (q • x + p • u)) *
          standardGaussianDensityD1 (x - a) g ∂volume) ∂ν := by
      apply integral_congr_ae
      filter_upwards with u
      exact hibp u
    _ = -∫ u, ∫ x, convexSetCutoff s ε (P (q • x + p • u)) *
          standardGaussianDensityD1 (x - a) g ∂volume ∂ν := integral_neg _
    _ = -∫ x, ∫ u, convexSetCutoff s ε (P (q • x + p • u)) *
          standardGaussianDensityD1 (x - a) g ∂ν ∂volume := by
      rw [integral_integral_swap hkernel]
    _ = -∫ x, (∫ u, convexSetCutoff s ε (P (q • x + p • u)) ∂ν) *
          standardGaussianDensityD1 (x - a) g ∂volume := by
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      exact integral_mul_const
        (standardGaussianDensityD1 (x - a) g)
        (fun u ↦ convexSetCutoff s ε (P (q • x + p • u)))

/-- A conditional convex cutoff is measurable and remains in the unit interval. -/
private theorem measurable_and_abs_integral_convexSetCutoff_affine_le_one
    {d : ℕ} {ν : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure ν]
    (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (P : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (p q : ℝ) :
    let ψ := fun x ↦
      ∫ u, convexSetCutoff s ε (P (q • x + p • u)) ∂ν
    Measurable ψ ∧ ∀ x, |ψ x| ≤ 1 := by
  let ψ := fun x ↦
    ∫ u, convexSetCutoff s ε (P (q • x + p • u)) ∂ν
  have hjoint : Measurable
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        convexSetCutoff s ε (P (q • z.1 + p • z.2))) :=
    (measurable_convexSetCutoff s ε).comp (by fun_prop)
  have hψm : Measurable ψ :=
    hjoint.stronglyMeasurable.integral_prod_right.measurable
  refine ⟨hψm, ?_⟩
  intro x
  have hint : Integrable
      (fun u ↦ convexSetCutoff s ε (P (q • x + p • u))) ν := by
    apply Integrable.of_bound
      ((measurable_convexSetCutoff s ε).comp (by fun_prop)).aestronglyMeasurable 1
    filter_upwards with u
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (convexSetCutoff_nonneg s ε _)]
    exact convexSetCutoff_le_one s ε _
  have hnonneg : 0 ≤ ψ x := integral_nonneg fun u ↦ convexSetCutoff_nonneg s ε _
  rw [abs_of_nonneg hnonneg]
  calc
    ψ x ≤ ∫ _u, (1 : ℝ) ∂ν := by
      exact integral_mono hint (integrable_const 1) fun u ↦
        convexSetCutoff_le_one s ε _
    _ = 1 := by rw [integral_const, probReal_univ, one_smul]

/-- An independent omitted pair converts the conditional Gaussian-coordinate identity into
Bentkus's exact two-direction density contraction. -/
private theorem
    integral_fderiv_convexSetCutoff_of_weightedAdd_leaveOneOut_eq_densityContraction
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ρ : Measure Θ} [IsProbabilityMeasure ρ]
    {ν : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure ν]
    (s : Set (EuclideanSpace ℝ (Fin d)))
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (W O G : Θ → EuclideanSpace ℝ (Fin d))
    (hWm : Measurable W) (hOm : Measurable O) (hGm : Measurable G)
    (hOint : Integrable O ρ) (hGint : Integrable G ρ)
    (p q : ℝ) (hq : q ≠ 0)
    (hjoint :
      let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
      let L : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) →
          EuclideanSpace ℝ (Fin d) := fun z ↦ q • z.1 + p • z.2
      let Z := fun ω ↦ (O ω, G ω)
      ρ.map (fun ω ↦ (W ω, Z ω)) =
        ((γ.prod ν).map L).prod (ρ.map Z)) :
    let e := bentkusWhiteningEquiv S hS
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
    let Z := fun ω ↦ (O ω, G ω)
    let ψ := fun x ↦ ∫ u, convexSetCutoff s ε (P (q • x + p • u)) ∂ν
    let r := p / q
    (∫ ω, (fderiv ℝ (convexSetCutoff s ε)
        (P (W ω) + (p • O ω + q • G ω)))
        ((-q) • O ω + p • G ω) ∂ρ) =
      ∫ z, ∫ x, ψ x *
        (standardGaussianDensityD1
            (x - B z.2 - r • B z.1) (B z.1) -
          r * standardGaussianDensityD1
            (x - B z.2 - r • B z.1) (B z.2)) ∂volume ∂(ρ.map Z) := by
  let e := bentkusWhiteningEquiv S hS
  let P := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let L : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) := fun z ↦ q • z.1 + p • z.2
  let Z := fun ω ↦ (O ω, G ω)
  let τ := ρ.map Z
  let κ := (γ.prod ν).map L
  let ψ := fun x ↦ ∫ u, convexSetCutoff s ε (P (q • x + p • u)) ∂ν
  let r := p / q
  let R := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    p • z.1 + q • z.2
  let R' := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    (-q) • z.1 + p • z.2
  let F : EuclideanSpace ℝ (Fin d) ×
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) → ℝ := fun z ↦
    (fderiv ℝ (convexSetCutoff s ε) (P z.1 + R z.2)) (R' z.2)
  have hLm : Measurable L := by
    dsimp only [L]
    fun_prop
  have hZm : Measurable Z := hOm.prodMk hGm
  have hRm : Measurable R := by
    dsimp only [R]
    fun_prop
  have hR'm : Measurable R' := by
    dsimp only [R']
    fun_prop
  letI : IsProbabilityMeasure τ := by
    dsimp only [τ]
    exact Measure.isProbabilityMeasure_map hZm.aemeasurable
  letI : IsProbabilityMeasure κ := by
    dsimp only [κ]
    exact Measure.isProbabilityMeasure_map hLm.aemeasurable
  have hnegqOint : Integrable (fun ω ↦ (-q) • O ω) ρ := by
    let Q : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
      (-q) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))
    simpa only [Q, _root_.smul_apply, ContinuousLinearMap.id_apply] using
      Q.integrable_comp hOint
  have hpGint : Integrable (fun ω ↦ p • G ω) ρ := by
    let Q : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
      p • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))
    simpa only [Q, _root_.smul_apply, ContinuousLinearMap.id_apply] using
      Q.integrable_comp hGint
  have hR'intρ : Integrable (fun ω ↦ (-q) • O ω + p • G ω) ρ :=
    hnegqOint.add hpGint
  have hR'int : Integrable R' τ := by
    apply (integrable_map_measure hR'm.aestronglyMeasurable hZm.aemeasurable).2
    apply hR'intρ.congr
    filter_upwards with ω
    rfl
  have hFm : Measurable F := by
    dsimp only [F]
    exact ((contDiff_convexSetCutoff hs hε).continuous_fderiv_apply
      (by norm_num)).measurable.comp
        ((((P.continuous.comp continuous_fst).measurable.add
          (hRm.comp measurable_snd))).prodMk (hR'm.comp measurable_snd))
  have hFint : Integrable F (κ.prod τ) := by
    have hmajor : Integrable (fun z : EuclideanSpace ℝ (Fin d) ×
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ↦
        (2 / ε) * ‖R' z.2‖) (κ.prod τ) :=
      (hR'int.norm.const_mul (2 / ε)).comp_snd κ
    apply hmajor.mono' hFm.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_eq_abs]
    have happly := ContinuousLinearMap.le_opNorm
      (fderiv ℝ (convexSetCutoff s ε) (P z.1 + R z.2)) (R' z.2)
    calc
      |F z| =
          ‖(fderiv ℝ (convexSetCutoff s ε) (P z.1 + R z.2)) (R' z.2)‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ ‖fderiv ℝ (convexSetCutoff s ε) (P z.1 + R z.2)‖ * ‖R' z.2‖ :=
        happly
      _ ≤ (2 / ε) * ‖R' z.2‖ :=
        mul_le_mul_of_nonneg_right
          (norm_fderiv_convexSetCutoff_le hs hε _) (norm_nonneg _)
  have hdisintegrate :
      (∫ ω, F (W ω, Z ω) ∂ρ) =
        ∫ z, ∫ w, F (w, z) ∂κ ∂τ := by
    exact integral_comp_pair_eq_iterated_of_map_eq_prod
      hWm hZm (by simpa only [γ, L, Z, κ, τ] using hjoint) hFint
  have hconditional
      (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
      (∫ w, F (w, z) ∂κ) =
        -∫ x, ψ x * standardGaussianDensityD1
          (x - q⁻¹ • B (R z)) (q⁻¹ • B (R' z)) ∂volume := by
    simpa only [F, κ, γ, L, ψ, R, R', P, B, e] using
      integral_fderiv_convexSetCutoff_map_prod_weightedAdd_eq_neg_conditional_D1
        (ν := ν) s hs hε S hS p q hq (R z) (R' z)
  have hinvp : q⁻¹ * p = p / q := by
    field_simp
  have hinvq : q⁻¹ * q = 1 := inv_mul_cancel₀ hq
  have hinvnegq : q⁻¹ * (-q) = -1 := by
    rw [mul_neg, hinvq]
  have hBR (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
      q⁻¹ • B (R z) = B z.2 + r • B z.1 := by
    dsimp only [R, r]
    rw [map_add, map_smul, map_smul, smul_add, smul_smul, smul_smul,
      hinvp, hinvq, one_smul]
    abel
  have hBR' (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
      q⁻¹ • B (R' z) = (-1 : ℝ) • B z.1 + r • B z.2 := by
    dsimp only [R', r]
    rw [map_add, map_smul, map_smul, smul_add, smul_smul, smul_smul,
      hinvnegq, hinvp]
  have halgebra
      (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))
      (x : EuclideanSpace ℝ (Fin d)) :
      -(ψ x * standardGaussianDensityD1
          (x - q⁻¹ • B (R z)) (q⁻¹ • B (R' z))) =
        ψ x * (standardGaussianDensityD1
            (x - B z.2 - r • B z.1) (B z.1) -
          r * standardGaussianDensityD1
            (x - B z.2 - r • B z.1) (B z.2)) := by
    rw [hBR, hBR']
    have hshift :
        x - (B z.2 + r • B z.1) =
          x - B z.2 - r • B z.1 := by abel
    rw [hshift]
    unfold standardGaussianDensityD1
    simp only [inner_add_right, inner_smul_right, neg_one_mul]
    ring
  change
    (∫ ω, (fderiv ℝ (convexSetCutoff s ε)
        (P (W ω) + (p • O ω + q • G ω)))
        ((-q) • O ω + p • G ω) ∂ρ) = _
  rw [show (∫ ω, (fderiv ℝ (convexSetCutoff s ε)
      (P (W ω) + (p • O ω + q • G ω)))
      ((-q) • O ω + p • G ω) ∂ρ) =
      ∫ ω, F (W ω, Z ω) ∂ρ by rfl,
    hdisintegrate]
  apply integral_congr_ae
  filter_upwards with z
  rw [hconditional]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  exact halgebra z x

/-- Pullback form of the independent omitted-pair density contraction, on the original
probability space rather than the image law of the omitted pair. -/
private theorem
    integral_fderiv_convexSetCutoff_of_weightedAdd_leaveOneOut_eq_densityContraction_comp
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ρ : Measure Θ} [IsProbabilityMeasure ρ]
    {ν : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure ν]
    (s : Set (EuclideanSpace ℝ (Fin d)))
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (W O G : Θ → EuclideanSpace ℝ (Fin d))
    (hWm : Measurable W) (hOm : Measurable O) (hGm : Measurable G)
    (hOint : Integrable O ρ) (hGint : Integrable G ρ)
    (p q : ℝ) (hq : q ≠ 0)
    (hjoint :
      let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
      let L : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) →
          EuclideanSpace ℝ (Fin d) := fun z ↦ q • z.1 + p • z.2
      let Z := fun ω ↦ (O ω, G ω)
      ρ.map (fun ω ↦ (W ω, Z ω)) =
        ((γ.prod ν).map L).prod (ρ.map Z)) :
    let e := bentkusWhiteningEquiv S hS
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
    let ψ := fun x ↦ ∫ u, convexSetCutoff s ε (P (q • x + p • u)) ∂ν
    let r := p / q
    (∫ ω, (fderiv ℝ (convexSetCutoff s ε)
        (P (W ω) + (p • O ω + q • G ω)))
        ((-q) • O ω + p • G ω) ∂ρ) =
      ∫ z, ∫ x, ψ x *
        (standardGaussianDensityD1
            (x - B (G z) - r • B (O z)) (B (O z)) -
          r * standardGaussianDensityD1
            (x - B (G z) - r • B (O z)) (B (G z))) ∂volume ∂ρ := by
  let e := bentkusWhiteningEquiv S hS
  let P := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  let Z := fun ω ↦ (O ω, G ω)
  let ψ := fun x ↦ ∫ u, convexSetCutoff s ε (P (q • x + p • u)) ∂ν
  let r := p / q
  let J := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    ∫ x, ψ x * (standardGaussianDensityD1
        (x - B z.2 - r • B z.1) (B z.1) -
      r * standardGaussianDensityD1
        (x - B z.2 - r • B z.1) (B z.2)) ∂volume
  have hψm := (measurable_and_abs_integral_convexSetCutoff_affine_le_one
    (ν := ν) s ε P p q).1
  have hJintegrand : Measurable
      (fun z : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
          EuclideanSpace ℝ (Fin d) ↦
        ψ z.2 * (standardGaussianDensityD1
            (z.2 - B z.1.2 - r • B z.1.1) (B z.1.1) -
          r * standardGaussianDensityD1
            (z.2 - B z.1.2 - r • B z.1.1) (B z.1.2))) := by
    have hshift : Measurable
        (fun z : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
            EuclideanSpace ℝ (Fin d) ↦
          z.2 - B z.1.2 - r • B z.1.1) := by
      fun_prop
    have hBO : Measurable
        (fun z : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
            EuclideanSpace ℝ (Fin d) ↦ B z.1.1) := by
      fun_prop
    have hBG : Measurable
        (fun z : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
            EuclideanSpace ℝ (Fin d) ↦ B z.1.2) := by
      fun_prop
    have hd1O : Measurable
        (fun z : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
            EuclideanSpace ℝ (Fin d) ↦ standardGaussianDensityD1
          (z.2 - B z.1.2 - r • B z.1.1) (B z.1.1)) := by
      unfold standardGaussianDensityD1
      have hinner : Measurable
          (fun z : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
              EuclideanSpace ℝ (Fin d) ↦
            inner ℝ (z.2 - B z.1.2 - r • B z.1.1) (B z.1.1)) :=
        continuous_inner.measurable.comp (hshift.prodMk hBO)
      exact hinner.neg.mul
        (continuous_standardGaussianDensity.measurable.comp hshift)
    have hd1G : Measurable
        (fun z : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
            EuclideanSpace ℝ (Fin d) ↦ standardGaussianDensityD1
          (z.2 - B z.1.2 - r • B z.1.1) (B z.1.2)) := by
      unfold standardGaussianDensityD1
      have hinner : Measurable
          (fun z : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
              EuclideanSpace ℝ (Fin d) ↦
            inner ℝ (z.2 - B z.1.2 - r • B z.1.1) (B z.1.2)) :=
        continuous_inner.measurable.comp (hshift.prodMk hBG)
      exact hinner.neg.mul
        (continuous_standardGaussianDensity.measurable.comp hshift)
    exact (hψm.comp measurable_snd).mul (hd1O.sub (hd1G.const_mul r))
  have hJm : Measurable J :=
    hJintegrand.stronglyMeasurable.integral_prod_right.measurable
  have hZm : Measurable Z := hOm.prodMk hGm
  have hmap : (∫ z, J z ∂(ρ.map Z)) = ∫ ω, J (Z ω) ∂ρ :=
    integral_map hZm.aemeasurable hJm.aestronglyMeasurable
  have hbase :=
    integral_fderiv_convexSetCutoff_of_weightedAdd_leaveOneOut_eq_densityContraction
      s hs hε S hS W O G hWm hOm hGm hOint hGint p q hq hjoint
  change
    (∫ ω, (fderiv ℝ (convexSetCutoff s ε)
        (P (W ω) + (p • O ω + q • G ω)))
        ((-q) • O ω + p • G ω) ∂ρ) = _
  rw [show (∫ ω, (fderiv ℝ (convexSetCutoff s ε)
      (P (W ω) + (p • O ω + q • G ω)))
      ((-q) • O ω + p • G ω) ∂ρ) =
      ∫ z, J z ∂(ρ.map Z) by
        simpa only [P, B, e, Z, ψ, r, J] using hbase,
    hmap]

/-- Product-integrability of the full two-direction density contraction for a bounded
conditional cutoff difference. -/
private theorem integrable_prod_bounded_largeAngle_densityContraction
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ρ : Measure Θ} [SFinite ρ]
    {O G : Θ → EuclideanSpace ℝ (Fin d)}
    (hOm : Measurable O) (hGm : Measurable G)
    (hOint : Integrable O ρ) (hGint : Integrable G ρ)
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (r : ℝ) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφm : Measurable φ) (hφ : ∀ x, |φ x| ≤ 1) :
    Integrable (fun z : Θ × EuclideanSpace ℝ (Fin d) ↦
      φ z.2 * (standardGaussianDensityD1
          (z.2 - B (G z.1) - r • B (O z.1)) (B (O z.1)) -
        r * standardGaussianDensityD1
          (z.2 - B (G z.1) - r • B (O z.1)) (B (G z.1))))
      (ρ.prod volume) := by
  let BO := fun z ↦ B (O z)
  let BG := fun z ↦ B (G z)
  let H := fun z ↦ BG z + r • BO z
  have hBOm : Measurable BO := B.continuous.measurable.comp hOm
  have hBGm : Measurable BG := B.continuous.measurable.comp hGm
  have hHm : Measurable H := hBGm.add (hBOm.const_smul r)
  have hBOint : Integrable BO ρ := B.integrable_comp hOint
  have hBGint : Integrable BG ρ := B.integrable_comp hGint
  have hfirst := integrable_prod_bounded_mul_standardGaussianDensityD1_sub
    hφm hφ hHm hBOm hBOint
  have hsecond := integrable_prod_bounded_mul_standardGaussianDensityD1_sub
    hφm hφ hHm hBGm hBGint
  apply (hfirst.sub (hsecond.const_mul r)).congr
  filter_upwards with z
  dsimp only [H, BO, BG]
  change
    φ z.2 * standardGaussianDensityD1
        (z.2 - (B (G z.1) + r • B (O z.1))) (B (O z.1)) -
      r * (φ z.2 * standardGaussianDensityD1
        (z.2 - (B (G z.1) + r • B (O z.1))) (B (G z.1))) =
    φ z.2 * (standardGaussianDensityD1
        (z.2 - B (G z.1) - r • B (O z.1)) (B (O z.1)) -
      r * standardGaussianDensityD1
        (z.2 - B (G z.1) - r • B (O z.1)) (B (G z.1)))
  rw [show z.2 - (B (G z.1) + r • B (O z.1)) =
    z.2 - B (G z.1) - r • B (O z.1) by abel]
  ring

/-- Exact actual-minus-Gaussian-reference identity under the two weighted leave-one-out laws.
The conditional cutoff difference is the sole non-Gaussian factor. -/
private theorem
    integral_fderiv_convexSetCutoff_weightedAdd_actual_sub_reference_eq_densityContraction
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ρ : Measure Θ} [IsProbabilityMeasure ρ]
    {ν : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure ν]
    (s : Set (EuclideanSpace ℝ (Fin d)))
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (W Wγ O G : Θ → EuclideanSpace ℝ (Fin d))
    (hWm : Measurable W) (hWγm : Measurable Wγ)
    (hOm : Measurable O) (hGm : Measurable G)
    (hOint : Integrable O ρ) (hGint : Integrable G ρ)
    (p q : ℝ) (hq : q ≠ 0)
    (hjoint :
      let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
      let L : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) →
          EuclideanSpace ℝ (Fin d) := fun z ↦ q • z.1 + p • z.2
      let Z := fun ω ↦ (O ω, G ω)
      ρ.map (fun ω ↦ (W ω, Z ω)) =
        ((γ.prod ν).map L).prod (ρ.map Z))
    (hjointγ :
      let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
      let L : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) →
          EuclideanSpace ℝ (Fin d) := fun z ↦ q • z.1 + p • z.2
      let Z := fun ω ↦ (O ω, G ω)
      ρ.map (fun ω ↦ (Wγ ω, Z ω)) =
        ((γ.prod γ).map L).prod (ρ.map Z)) :
    let e := bentkusWhiteningEquiv S hS
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let ψ := fun x ↦ ∫ u, convexSetCutoff s ε (P (q • x + p • u)) ∂ν
    let ψγ := fun x ↦ ∫ u, convexSetCutoff s ε (P (q • x + p • u)) ∂γ
    let r := p / q
    ((∫ ω, (fderiv ℝ (convexSetCutoff s ε)
        (P (W ω) + (p • O ω + q • G ω)))
        ((-q) • O ω + p • G ω) ∂ρ) -
      ∫ ω, (fderiv ℝ (convexSetCutoff s ε)
        (P (Wγ ω) + (p • O ω + q • G ω)))
        ((-q) • O ω + p • G ω) ∂ρ) =
      ∫ z, ∫ x, (ψ x - ψγ x) *
        (standardGaussianDensityD1
            (x - B (G z) - r • B (O z)) (B (O z)) -
          r * standardGaussianDensityD1
            (x - B (G z) - r • B (O z)) (B (G z))) ∂volume ∂ρ := by
  let e := bentkusWhiteningEquiv S hS
  let P := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let ψ := fun x ↦ ∫ u, convexSetCutoff s ε (P (q • x + p • u)) ∂ν
  let ψγ := fun x ↦ ∫ u, convexSetCutoff s ε (P (q • x + p • u)) ∂γ
  let r := p / q
  let K := fun (φ : EuclideanSpace ℝ (Fin d) → ℝ)
      (z : Θ × EuclideanSpace ℝ (Fin d)) ↦
    φ z.2 * (standardGaussianDensityD1
        (z.2 - B (G z.1) - r • B (O z.1)) (B (O z.1)) -
      r * standardGaussianDensityD1
        (z.2 - B (G z.1) - r • B (O z.1)) (B (G z.1)))
  have hψ := measurable_and_abs_integral_convexSetCutoff_affine_le_one
    (ν := ν) s ε P p q
  have hψγ := measurable_and_abs_integral_convexSetCutoff_affine_le_one
    (ν := γ) s ε P p q
  have hψ0 (x) : 0 ≤ ψ x :=
    integral_nonneg fun u ↦ convexSetCutoff_nonneg s ε _
  have hψγ0 (x) : 0 ≤ ψγ x :=
    integral_nonneg fun u ↦ convexSetCutoff_nonneg s ε _
  have hφ : ∀ x, |ψ x - ψγ x| ≤ 1 := by
    intro x
    have hψ1 : ψ x ≤ 1 := by
      simpa only [ψ, abs_of_nonneg (hψ0 x)] using hψ.2 x
    have hψγ1 : ψγ x ≤ 1 := by
      simpa only [ψγ, abs_of_nonneg (hψγ0 x)] using hψγ.2 x
    rw [abs_le]
    constructor <;> linarith [hψ0 x, hψγ0 x]
  have hφm : Measurable (fun x ↦ ψ x - ψγ x) := by
    have hψm : Measurable ψ := by simpa only [ψ] using hψ.1
    have hψγm : Measurable ψγ := by simpa only [ψγ] using hψγ.1
    exact hψm.sub hψγm
  have hKψ : Integrable (K ψ) (ρ.prod volume) := by
    simpa only [K] using integrable_prod_bounded_largeAngle_densityContraction
      hOm hGm hOint hGint B r hψ.1 hψ.2
  have hKψγ : Integrable (K ψγ) (ρ.prod volume) := by
    simpa only [K] using integrable_prod_bounded_largeAngle_densityContraction
      hOm hGm hOint hGint B r hψγ.1 hψγ.2
  have hKφ : Integrable (K (fun x ↦ ψ x - ψγ x)) (ρ.prod volume) := by
    simpa only [K] using integrable_prod_bounded_largeAngle_densityContraction
      hOm hGm hOint hGint B r hφm hφ
  have hKφ' : Integrable (Function.uncurry
      (fun z x ↦ K (fun y ↦ ψ y - ψγ y) (z, x))) (ρ.prod volume) := by
    apply hKφ.congr
    filter_upwards with z
    rcases z with ⟨z, x⟩
    rfl
  have hactual :=
    integral_fderiv_convexSetCutoff_of_weightedAdd_leaveOneOut_eq_densityContraction_comp
      s hs hε S hS W O G hWm hOm hGm hOint hGint p q hq hjoint
  have href :=
    integral_fderiv_convexSetCutoff_of_weightedAdd_leaveOneOut_eq_densityContraction_comp
      (ν := γ) s hs hε S hS Wγ O G hWγm hOm hGm hOint hGint p q hq hjointγ
  change
    ((∫ ω, (fderiv ℝ (convexSetCutoff s ε)
        (P (W ω) + (p • O ω + q • G ω)))
        ((-q) • O ω + p • G ω) ∂ρ) -
      ∫ ω, (fderiv ℝ (convexSetCutoff s ε)
        (P (Wγ ω) + (p • O ω + q • G ω)))
        ((-q) • O ω + p • G ω) ∂ρ) = _
  rw [show (∫ ω, (fderiv ℝ (convexSetCutoff s ε)
      (P (W ω) + (p • O ω + q • G ω)))
      ((-q) • O ω + p • G ω) ∂ρ) =
      ∫ z, ∫ x, K ψ (z, x) ∂volume ∂ρ by
        simpa only [P, B, e, ψ, r, K] using hactual,
    show (∫ ω, (fderiv ℝ (convexSetCutoff s ε)
      (P (Wγ ω) + (p • O ω + q • G ω)))
      ((-q) • O ω + p • G ω) ∂ρ) =
      ∫ z, ∫ x, K ψγ (z, x) ∂volume ∂ρ by
        simpa only [P, B, e, γ, ψγ, r, K] using href]
  calc
    (∫ z, ∫ x, K ψ (z, x) ∂volume ∂ρ) -
        ∫ z, ∫ x, K ψγ (z, x) ∂volume ∂ρ =
        (∫ z, K ψ z ∂(ρ.prod volume)) -
          ∫ z, K ψγ z ∂(ρ.prod volume) := by
      rw [integral_integral hKψ, integral_integral hKψγ]
    _ = ∫ z, K ψ z - K ψγ z ∂(ρ.prod volume) := by
      rw [integral_sub hKψ hKψγ]
    _ = ∫ z, K (fun x ↦ ψ x - ψγ x) z ∂(ρ.prod volume) := by
      apply integral_congr_ae
      filter_upwards with z
      dsimp only [K]
      ring
    _ = ∫ z, ∫ x, K (fun x ↦ ψ x - ψγ x) (z, x) ∂volume ∂ρ := by
      exact (integral_integral hKφ').symm

/-- Exact large-angle actual-minus-reference representation for Bentkus's canonical replacement
space.  This is equation (3.14) before applying the induction bound to the conditional cutoff
difference. -/
theorem bentkus_largeAngle_rotationCoordinate_sub_reference_eq_densityContraction
    {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (α : ℝ) (hsin : Real.sin α ≠ 0)
    (s : Set (EuclideanSpace ℝ (Fin d)))
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε) :
    let ρ := bentkusReplacementMeasure μ X
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let UO := bentkusLeaveOneOut
      (fun i ↦ replacementOriginal (d := d) i) k
    let VG := bentkusLeaveOneOut
      (fun i ↦ replacementGaussian (d := d) i) k
    let U := bentkusLeaveOneOut X k
    let ν := μ.map (fun ω ↦ B (U ω))
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let ψ := fun x ↦ ∫ u, convexSetCutoff s ε
      (P (Real.sin α • x + Real.cos α • u)) ∂ν
    let ψγ := fun x ↦ ∫ u, convexSetCutoff s ε
      (P (Real.sin α • x + Real.cos α • u)) ∂γ
    let r := Real.cos α / Real.sin α
    ((∫ ω, (fderiv ℝ (convexSetCutoff s ε)
        ((Real.cos α • UO ω + Real.sin α • VG ω) +
          (Real.cos α • O ω + Real.sin α • G ω)))
        ((-(Real.sin α)) • O ω + Real.cos α • G ω) ∂ρ) -
      ∫ ω, (fderiv ℝ (convexSetCutoff s ε)
        (VG ω + (Real.cos α • O ω + Real.sin α • G ω)))
        ((-(Real.sin α)) • O ω + Real.cos α • G ω) ∂ρ) =
      ∫ z, ∫ x, (ψ x - ψγ x) *
        (standardGaussianDensityD1
            (x - B (G z) - r • B (O z)) (B (O z)) -
          r * standardGaussianDensityD1
            (x - B (G z) - r • B (O z)) (B (G z))) ∂volume ∂ρ := by
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let P := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let UO := bentkusLeaveOneOut
    (fun i ↦ replacementOriginal (d := d) i) k
  let VG := bentkusLeaveOneOut
    (fun i ↦ replacementGaussian (d := d) i) k
  let U := bentkusLeaveOneOut X k
  let W := fun ω ↦ B (Real.cos α • UO ω + Real.sin α • VG ω)
  let Wγ := fun ω ↦ B (VG ω)
  let Z := fun ω ↦ (O ω, G ω)
  let ν := μ.map (fun ω ↦ B (U ω))
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let L := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    Real.sin α • z.1 + Real.cos α • z.2
  let ψ := fun x ↦ ∫ u, convexSetCutoff s ε
    (P (Real.sin α • x + Real.cos α • u)) ∂ν
  let ψγ := fun x ↦ ∫ u, convexSetCutoff s ε
    (P (Real.sin α • x + Real.cos α • u)) ∂γ
  let r := Real.cos α / Real.sin α
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hUm : Measurable U := by
    dsimp only [U, bentkusLeaveOneOut]
    exact Finset.measurable_sum (Finset.univ.erase k) fun i _ ↦ hXm i
  letI : IsProbabilityMeasure ν := by
    dsimp only [ν]
    exact Measure.isProbabilityMeasure_map
      (B.continuous.measurable.comp hUm).aemeasurable
  have hOm : Measurable O := by
    exact (measurable_pi_apply k).comp measurable_fst
  have hGm : Measurable G := by
    exact (measurable_pi_apply k).comp measurable_snd
  have hUOm : Measurable UO := by
    change Measurable (fun z :
        (Fin (n + 1) → EuclideanSpace ℝ (Fin d)) ×
          (Fin (n + 1) → EuclideanSpace ℝ (Fin d)) ↦
      ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase k, z.1 i)
    fun_prop
  have hVGm : Measurable VG := by
    change Measurable (fun z :
        (Fin (n + 1) → EuclideanSpace ℝ (Fin d)) ×
          (Fin (n + 1) → EuclideanSpace ℝ (Fin d)) ↦
      ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase k, z.2 i)
    fun_prop
  have hWm : Measurable W := by
    dsimp only [W]
    fun_prop
  have hWγm : Measurable Wγ := B.continuous.measurable.comp hVGm
  have hOint : Integrable O ρ :=
    (memLp_replacementOriginal hXm hX3 k).integrable (by norm_num)
  have hGint : Integrable G ρ :=
    (memLp_three_replacementGaussian hXm k).integrable (by norm_num)
  have hB : B = bentkusWhiteningCLM S := by
    apply ContinuousLinearMap.ext
    intro x
    exact bentkusWhiteningEquiv_apply S hS x
  have hWlaw : ρ.map W = (γ.prod ν).map L := by
    simpa only [ρ, S, B, UO, VG, U, W, ν, γ, L,
      hB] using
      map_whitenedRotatedLeaveOneOut_eq_map_prod
        hXm hX3 h_indep hX0 hidentity k hk α
  have hpair : ρ.map (fun ω ↦ (W ω, Z ω)) =
      (ρ.map W).prod (ρ.map Z) := by
    simpa only [ρ, S, B, UO, VG, W, O, G, Z,
      hB] using
      map_whitenedRotatedLeaveOneOut_replacementPair_eq_prod hXm k α
  have hjoint : ρ.map (fun ω ↦ (W ω, Z ω)) =
      ((γ.prod ν).map L).prod (ρ.map Z) := by
    rw [hpair, hWlaw]
  have hγmix : (γ.prod γ).map L = γ := by
    simpa only [γ, L] using
      map_prod_stdGaussian_weightedAdd_eq_stdGaussian
        (d := d) (p := Real.cos α) (q := Real.sin α)
          (Real.cos_sq_add_sin_sq α)
  have hγpair : ρ.map (fun ω ↦ (Wγ ω, Z ω)) =
      γ.prod (ρ.map Z) := by
    simpa only [ρ, S, B, Wγ, VG, O, G, Z,
      hB] using
      map_whitened_bentkusLeaveOneOut_replacementGaussian_pair_eq_prod
        hXm hX3 h_indep hX0 hidentity k hk
  have hjointγ : ρ.map (fun ω ↦ (Wγ ω, Z ω)) =
      ((γ.prod γ).map L).prod (ρ.map Z) := by
    rw [hγmix]
    exact hγpair
  have hbase :=
    integral_fderiv_convexSetCutoff_weightedAdd_actual_sub_reference_eq_densityContraction
      s hs hε S hS W Wγ O G hWm hWγm hOm hGm hOint hGint
        (Real.cos α) (Real.sin α) hsin hjoint hjointγ
  have hPB (x : EuclideanSpace ℝ (Fin d)) : P (B x) = x := by
    dsimp only [P, B, e]
    exact (bentkusWhiteningEquiv S hS).symm_apply_apply x
  simpa only [P, B, e, W, Wγ, O, G, UO, VG, ν, γ, ψ, ψγ, r, hPB] using hbase

/-- The conditional cutoff difference has the unit bound needed for product-integrability and
the induction bound needed for the sharp large-angle remainder estimate. -/
theorem bentkus_largeAngle_conditionalCutoff_sub_bounds
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
    (p q : ℝ) (s : Set (EuclideanSpace ℝ (Fin d)))
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε) :
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
    let U := bentkusLeaveOneOut X k
    let ν := μ.map (fun ω ↦ B (U ω))
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let ψ := fun x ↦ ∫ u, convexSetCutoff s ε (P (q • x + p • u)) ∂ν
    let ψγ := fun x ↦ ∫ u, convexSetCutoff s ε (P (q • x + p • u)) ∂γ
    let β := ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
    let D := 8 * C * (d : ℝ) ^ (1 / 4 : ℝ) * β
    Measurable (fun x ↦ ψ x - ψγ x) ∧
      (∀ x, |ψ x - ψγ x| ≤ 1) ∧
      ∀ x, |ψ x - ψγ x| ≤ D := by
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let P := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  let U := bentkusLeaveOneOut X k
  let ν := μ.map (fun ω ↦ B (U ω))
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let ψ := fun x ↦ ∫ u, convexSetCutoff s ε (P (q • x + p • u)) ∂ν
  let ψγ := fun x ↦ ∫ u, convexSetCutoff s ε (P (q • x + p • u)) ∂γ
  let β := ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
  let βrem := ∑ i : Fin n, ∫ ω, ‖X (k.succAbove i) ω‖ ^ 3 ∂μ
  let βwhite := ∑ i : Fin n, ∫ ω,
    ‖bentkusWhiteningCLM S (X (k.succAbove i) ω)‖ ^ 3 ∂μ
  let D := 8 * C * (d : ℝ) ^ (1 / 4 : ℝ) * β
  have hUm : Measurable U := by
    dsimp only [U, bentkusLeaveOneOut]
    exact Finset.measurable_sum (Finset.univ.erase k) fun i _ ↦ hXm i
  letI : IsProbabilityMeasure ν := by
    dsimp only [ν]
    exact Measure.isProbabilityMeasure_map
      (B.continuous.measurable.comp hUm).aemeasurable
  have hψ := measurable_and_abs_integral_convexSetCutoff_affine_le_one
    (ν := ν) s ε P p q
  have hψγ := measurable_and_abs_integral_convexSetCutoff_affine_le_one
    (ν := γ) s ε P p q
  have hψm : Measurable ψ := by simpa only [ψ] using hψ.1
  have hψγm : Measurable ψγ := by simpa only [ψγ] using hψγ.1
  have hψ0 (x) : 0 ≤ ψ x :=
    integral_nonneg fun u ↦ convexSetCutoff_nonneg s ε _
  have hψγ0 (x) : 0 ≤ ψγ x :=
    integral_nonneg fun u ↦ convexSetCutoff_nonneg s ε _
  have hunit : ∀ x, |ψ x - ψγ x| ≤ 1 := by
    intro x
    have hψ1 : ψ x ≤ 1 := by
      simpa only [ψ, abs_of_nonneg (hψ0 x)] using hψ.2 x
    have hψγ1 : ψγ x ≤ 1 := by
      simpa only [ψγ, abs_of_nonneg (hψγ0 x)] using hψγ.2 x
    rw [abs_le]
    constructor <;> linarith [hψ0 x, hψγ0 x]
  have hwhite : βwhite ≤ 8 * βrem := by
    dsimp only [βwhite, βrem]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦
      integral_norm_bentkusWhiteningCLM_leaveOneOut_pow_three_le
        hX3 h_indep hX0 hidentity k hk (hX3 (k.succAbove i))
  have hrem : βrem ≤ β := by
    let m : Fin (n + 1) → ℝ := fun i ↦ ∫ ω, ‖X i ω‖ ^ 3 ∂μ
    have hmk : 0 ≤ m k := integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg _) 3
    have hsplit := Fin.sum_univ_succAbove m k
    dsimp only [βrem, β, m]
    calc
      (∑ i : Fin n, ∫ ω, ‖X (k.succAbove i) ω‖ ^ 3 ∂μ) ≤
          (∫ ω, ‖X k ω‖ ^ 3 ∂μ) +
            ∑ i : Fin n, ∫ ω, ‖X (k.succAbove i) ω‖ ^ 3 ∂μ :=
        le_add_of_nonneg_left hmk
      _ = ∑ i : Fin (n + 1), ∫ ω, ‖X i ω‖ ^ 3 ∂μ := hsplit.symm
  have hfactor : 0 ≤ C * (d : ℝ) ^ (1 / 4 : ℝ) :=
    mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  have hwhiteD :
      C * (d : ℝ) ^ (1 / 4 : ℝ) * βwhite ≤ D := by
    calc
      C * (d : ℝ) ^ (1 / 4 : ℝ) * βwhite ≤
          C * (d : ℝ) ^ (1 / 4 : ℝ) * (8 * βrem) :=
        mul_le_mul_of_nonneg_left hwhite hfactor
      _ = 8 * C * (d : ℝ) ^ (1 / 4 : ℝ) * βrem := by ring
      _ ≤ 8 * C * (d : ℝ) ^ (1 / 4 : ℝ) * β := by
        gcongr
      _ = D := by rfl
  have hD : 0 ≤ D := by
    dsimp only [D, β]
    positivity
  have hBeq (y : EuclideanSpace ℝ (Fin d)) : B y = e y := rfl
  have hνbound (A : Set (EuclideanSpace ℝ (Fin d))) (hA : MeasurableSet A)
      (hAc : Convexity.IsConvexSet ℝ A) :
      |ν.real A - γ.real A| ≤ D := by
    have hbase := bentkusWhitenedLeaveOneOut_error_le_of_induction
      hIH hd hX3 h_indep hX0 k hS A hA hAc
    calc
      |ν.real A - γ.real A| ≤
          C * (d : ℝ) ^ (1 / 4 : ℝ) * βwhite := by
        simpa only [ν, γ, U, S, βwhite, hBeq] using hbase
      _ ≤ D := hwhiteD
  have hsharp (x : EuclideanSpace ℝ (Fin d)) :
      |ψ x - ψγ x| ≤ D := by
    have hcompare := abs_integral_quasiconcave_sub_le_convexDistance
      hD hνbound
      (fun u ↦ convexSetCutoff s ε (P (q • x + p • u)))
      ((measurable_convexSetCutoff s ε).comp (by fun_prop))
      (fun u ↦ convexSetCutoff_nonneg s ε _)
      (fun u ↦ convexSetCutoff_le_one s ε _)
      (by
        intro t
        let A : Set (EuclideanSpace ℝ (Fin d)) :=
          {y | t ≤ convexSetCutoff s ε y}
        have hA : Convexity.IsConvexSet ℝ A :=
          convexSetCutoff_superlevel_isConvexSet hs hε t
        have hadd := isConvexSet_preimage_add_right hA (P (q • x))
        have hpre := isConvexSet_preimage_continuousLinearMap (p • P) hadd
        have heq :
            ((p • P) ⁻¹' {y | y + P (q • x) ∈ A}) =
              {u | t ≤ convexSetCutoff s ε (P (q • x + p • u))} := by
          ext u
          simp only [Set.mem_preimage, Set.mem_setOf_eq, A]
          have harg : (p • P) u + P (q • x) = P (q • x + p • u) := by
            simp only [_root_.smul_apply, map_smul, map_add]
            abel
          rw [harg]
        rw [← heq]
        exact hpre)
    simpa only [ψ, ψγ] using hcompare
  exact ⟨hψm.sub hψγm, hunit, hsharp⟩


/-- Translating Euclidean volume moves the omitted summand from the cutoff into the first
Gaussian-density contraction. -/
private lemma integral_convexSetCutoff_add_mul_standardGaussianDensityD1_eq_sub
    {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (P B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (r r' : EuclideanSpace ℝ (Fin d)) (hPB : P (B r) = r) :
    (∫ u, convexSetCutoff s ε (P u + r) *
        standardGaussianDensityD1 u (B r') ∂volume) =
      ∫ x, convexSetCutoff s ε (P x) *
        standardGaussianDensityD1 (x - B r) (B r') ∂volume := by
  calc
    (∫ u, convexSetCutoff s ε (P u + r) *
        standardGaussianDensityD1 u (B r') ∂volume) =
        ∫ u, convexSetCutoff s ε (P (u + B r)) *
          standardGaussianDensityD1 ((u + B r) - B r) (B r') ∂volume := by
      apply integral_congr_ae
      filter_upwards with u
      rw [map_add, hPB]
      congr 2
      abel
    _ = ∫ x, convexSetCutoff s ε (P x) *
        standardGaussianDensityD1 (x - B r) (B r') ∂volume :=
      integral_add_right_eq_self
        (fun x ↦ convexSetCutoff s ε (P x) *
          standardGaussianDensityD1 (x - B r) (B r')) (B r)

/-- Direct translated-density form of the Gaussian leave-one-out integration-by-parts identity.
The omitted pair is pulled back from its image law to the replacement probability space. -/
theorem integral_fderiv_convexSetCutoff_gaussianLeaveOneOut_eq_neg_translated_D1
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (α : ℝ) {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε) :
    let ρ := bentkusReplacementMeasure μ X
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let e := bentkusWhiteningEquiv S
      (bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
        hX3 h_indep hX0 hidentity k hk)
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let V := bentkusLeaveOneOut
      (fun i ↦ replacementGaussian (d := d) i) k
    let R := bentkusRotated α O G
    let R' := bentkusRotatedDeriv α O G
    (∫ ω, (fderiv ℝ (convexSetCutoff s ε) (V ω + R ω)) (R' ω) ∂ρ) =
      -∫ ω, ∫ x, convexSetCutoff s ε (P x) *
          standardGaussianDensityD1 (x - B (R ω)) (B (R' ω)) ∂volume ∂ρ := by
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let P := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let V := bentkusLeaveOneOut (fun i ↦ replacementGaussian (d := d) i) k
  let R := bentkusRotated α O G
  let R' := bentkusRotatedDeriv α O G
  let Z := fun ω ↦ (O ω, G ω)
  let r := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    Real.cos α • z.1 + Real.sin α • z.2
  let r' := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -(Real.sin α) • z.1 + Real.cos α • z.2
  let τ := ρ.map Z
  let J := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    ∫ u, convexSetCutoff s ε (P u + r z) *
      standardGaussianDensityD1 u (B (r' z)) ∂volume
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hZmeas : Measurable Z := by
    dsimp only [Z, O, G, replacementOriginal, replacementGaussian]
    fun_prop
  have hrmeas : Measurable r := by
    dsimp only [r]
    fun_prop
  have hr'meas : Measurable r' := by
    dsimp only [r']
    fun_prop
  have hJintegrand : Measurable
      (fun p : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
          EuclideanSpace ℝ (Fin d) ↦
        convexSetCutoff s ε (P p.2 + r p.1) *
          standardGaussianDensityD1 p.2 (B (r' p.1))) := by
    have hcut : Measurable
        (fun p : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
            EuclideanSpace ℝ (Fin d) ↦ convexSetCutoff s ε (P p.2 + r p.1)) :=
      (measurable_convexSetCutoff s ε).comp
        ((P.continuous.measurable.comp measurable_snd).add
          (hrmeas.comp measurable_fst))
    have hd1 : Measurable
        (fun p : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
            EuclideanSpace ℝ (Fin d) ↦ standardGaussianDensityD1 p.2 (B (r' p.1))) := by
      unfold standardGaussianDensityD1
      have hBg : Measurable
          (fun p : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
              EuclideanSpace ℝ (Fin d) ↦ B (r' p.1)) :=
        B.continuous.measurable.comp (hr'meas.comp measurable_fst)
      have hinner : Measurable
          (fun p : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
              EuclideanSpace ℝ (Fin d) ↦ inner ℝ p.2 (B (r' p.1))) := by
        change Measurable ((fun q : EuclideanSpace ℝ (Fin d) ×
            EuclideanSpace ℝ (Fin d) ↦ inner ℝ q.1 q.2) ∘
          fun p : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
              EuclideanSpace ℝ (Fin d) ↦ (p.2, B (r' p.1)))
        exact continuous_inner.measurable.comp (measurable_snd.prodMk hBg)
      exact hinner.neg.mul
        (continuous_standardGaussianDensity.measurable.comp measurable_snd)
    exact hcut.mul hd1
  have hJmeas : Measurable J := by
    exact hJintegrand.stronglyMeasurable.integral_prod_right.measurable
  have hmap : (∫ z, J z ∂τ) = ∫ ω, J (Z ω) ∂ρ := by
    dsimp only [τ]
    exact integral_map hZmeas.aemeasurable hJmeas.aestronglyMeasurable
  have htranslate (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
      J z = ∫ x, convexSetCutoff s ε (P x) *
        standardGaussianDensityD1 (x - B (r z)) (B (r' z)) ∂volume := by
    have hPB : P (B (r z)) = r z := by
      dsimp only [P, B, e]
      exact (bentkusWhiteningEquiv S hS).symm_apply_apply (r z)
    simpa only [J] using
      integral_convexSetCutoff_add_mul_standardGaussianDensityD1_eq_sub
        s ε P B (r z) (r' z) hPB
  have hbase :=
    integral_fderiv_convexSetCutoff_gaussianLeaveOneOut_eq_neg_iterated_D1
      hXm hX3 h_indep hX0 hidentity k hk α hs hε
  change (∫ ω, (fderiv ℝ (convexSetCutoff s ε) (V ω + R ω)) (R' ω) ∂ρ) = _
  rw [show (∫ ω, (fderiv ℝ (convexSetCutoff s ε) (V ω + R ω)) (R' ω) ∂ρ) =
      -∫ z, J z ∂τ by simpa only [ρ, S, e, P, B, O, G, V, R, R', Z, r, r', τ, J]
        using hbase,
    hmap]
  congr 1
  apply integral_congr_ae
  filter_upwards with ω
  rw [htranslate]
  rfl

lemma integrable_prod_bounded_mul_standardGaussianDensityD2
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ] {μ : Measure Θ} [SFinite μ]
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφm : Measurable φ) (hφ : ∀ x, |φ x| ≤ 1)
    {h g : Θ → EuclideanSpace ℝ (Fin d)} (hhm : Measurable h) (hgm : Measurable g)
    (hhg : Integrable (fun z ↦
      (‖h z‖ ^ 2 + ‖g z‖ ^ 2) / 2 + ‖h z‖ * ‖g z‖) μ) :
    Integrable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦
      φ p.2 * standardGaussianDensityD2 p.2 (h p.1) (g p.1)) (μ.prod volume) := by
  let F : Θ × EuclideanSpace ℝ (Fin d) → ℝ := fun p ↦
    φ p.2 * standardGaussianDensityD2 p.2 (h p.1) (g p.1)
  have hFm : Measurable F := by
    dsimp only [F]
    unfold standardGaussianDensityD2
    have hx : Measurable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦ p.2) := measurable_snd
    have hh' : Measurable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦ h p.1) :=
      hhm.comp measurable_fst
    have hg' : Measurable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦ g p.1) :=
      hgm.comp measurable_fst
    have hinnerXH : Measurable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦
        inner ℝ p.2 (h p.1)) := by
      change Measurable ((fun q : EuclideanSpace ℝ (Fin d) ×
          EuclideanSpace ℝ (Fin d) ↦ inner ℝ q.1 q.2) ∘
        fun p : Θ × EuclideanSpace ℝ (Fin d) ↦ (p.2, h p.1))
      exact continuous_inner.measurable.comp (hx.prodMk hh')
    have hinnerXG : Measurable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦
        inner ℝ p.2 (g p.1)) := by
      change Measurable ((fun q : EuclideanSpace ℝ (Fin d) ×
          EuclideanSpace ℝ (Fin d) ↦ inner ℝ q.1 q.2) ∘
        fun p : Θ × EuclideanSpace ℝ (Fin d) ↦ (p.2, g p.1))
      exact continuous_inner.measurable.comp (hx.prodMk hg')
    have hinnerHG : Measurable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦
        inner ℝ (h p.1) (g p.1)) := by
      change Measurable ((fun q : EuclideanSpace ℝ (Fin d) ×
          EuclideanSpace ℝ (Fin d) ↦ inner ℝ q.1 q.2) ∘
        fun p : Θ × EuclideanSpace ℝ (Fin d) ↦ (h p.1, g p.1))
      exact continuous_inner.measurable.comp (hh'.prodMk hg')
    exact (hφm.comp hx).mul
      ((((hinnerXH.mul hinnerXG).sub hinnerHG).mul
        (continuous_standardGaussianDensity.measurable.comp hx)))
  apply (integrable_prod_iff hFm.aestronglyMeasurable).2
  constructor
  · filter_upwards with z
    exact (integrable_standardGaussianDensityD2_volume (h z) (g z)).bdd_mul
      hφm.aestronglyMeasurable (by
        filter_upwards with x
        simpa only [Real.norm_eq_abs] using hφ x)
  · have hinnerMeas : AEStronglyMeasurable
        (fun z ↦ ∫ x, ‖F (z, x)‖ ∂volume) μ :=
      hFm.aestronglyMeasurable.norm.integral_prod_right'
    apply hhg.mono' hinnerMeas
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x ↦ norm_nonneg _)]
    calc
      (∫ x, ‖F (z, x)‖ ∂volume) ≤
          ∫ x, |standardGaussianDensityD2 x (h z) (g z)| ∂volume := by
        apply integral_mono
        · exact ((integrable_standardGaussianDensityD2_volume (h z) (g z)).bdd_mul
            hφm.aestronglyMeasurable (by
              filter_upwards with x
              simpa only [Real.norm_eq_abs] using hφ x)).norm
        · exact (integrable_standardGaussianDensityD2_volume (h z) (g z)).abs
        · intro x
          dsimp only [F]
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hφ x)
      _ ≤ (‖h z‖ ^ 2 + ‖g z‖ ^ 2) / 2 + ‖h z‖ * ‖g z‖ :=
        integral_abs_standardGaussianDensityD2_volume_le (h z) (g z)

/-- The linear and quadratic density terms vanish after averaging the omitted
original/Gaussian pair. -/
theorem bentkus_integral_integral_lowOrderDensity_eq_zero
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i)) (hX3 : ∀ i, MemLp (X i) 3 μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (i : Fin n) (α : ℝ) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφm : Measurable φ) (hφ : ∀ x, |φ x| ≤ 1) :
    let ρ := bentkusReplacementMeasure μ X
    let O := replacementOriginal (d := d) i
    let G := replacementGaussian (d := d) i
    let H := fun ω ↦ B (bentkusRotated α O G ω)
    let K := fun ω ↦ B (bentkusRotatedDeriv α O G ω)
    (∫ ω, ∫ x, φ x * standardGaussianDensityD1 x (K ω) ∂volume ∂ρ = 0) ∧
      (∫ ω, ∫ x, φ x * standardGaussianDensityD2 x (H ω) (K ω)
        ∂volume ∂ρ = 0) := by
  let ρ := bentkusReplacementMeasure μ X
  let O := replacementOriginal (d := d) i
  let G := replacementGaussian (d := d) i
  let R := bentkusRotated α O G
  let R' := bentkusRotatedDeriv α O G
  let H := fun ω ↦ B (R ω)
  let K := fun ω ↦ B (R' ω)
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hO3 : MemLp O 3 ρ := memLp_replacementOriginal hXm hX3 i
  have hG3 : MemLp G 3 ρ := memLp_three_replacementGaussian hXm i
  have hR3 : MemLp R 3 ρ := by
    change MemLp ((Real.cos α) • O + (Real.sin α) • G) 3 ρ
    exact (hO3.const_smul (Real.cos α)).add (hG3.const_smul (Real.sin α))
  have hR'3 : MemLp R' 3 ρ := by
    change MemLp ((-(Real.sin α)) • O + (Real.cos α) • G) 3 ρ
    exact (hO3.const_smul (-(Real.sin α))).add (hG3.const_smul (Real.cos α))
  have hH3 : MemLp H 3 ρ := by
    simpa only [H] using hR3.continuousLinearMap_comp B
  have hK3 : MemLp K 3 ρ := by
    simpa only [K] using hR'3.continuousLinearMap_comp B
  have hHm : Measurable H := by
    dsimp only [H, R, O, G, bentkusRotated, replacementOriginal, replacementGaussian]
    fun_prop
  have hKm : Measurable K := by
    dsimp only [K, R', O, G, bentkusRotatedDeriv, replacementOriginal, replacementGaussian]
    fun_prop
  have hD1int := integrable_prod_bounded_mul_standardGaussianDensityD1
    hφm hφ hKm (hK3.integrable (by norm_num))
  have hH2 := hH3.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 3)
  have hK2 := hK3.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 3)
  have hHsq : Integrable (fun ω ↦ ‖H ω‖ ^ 2) ρ := hH2.integrable_norm_pow (by norm_num)
  have hKsq : Integrable (fun ω ↦ ‖K ω‖ ^ 2) ρ := hK2.integrable_norm_pow (by norm_num)
  have hHK : Integrable (fun ω ↦ ‖H ω‖ * ‖K ω‖) ρ :=
    hH2.norm.integrable_mul hK2.norm
  have hquad : Integrable (fun ω ↦
      (‖H ω‖ ^ 2 + ‖K ω‖ ^ 2) / 2 + ‖H ω‖ * ‖K ω‖) ρ :=
    ((hHsq.add hKsq).div_const 2).add hHK
  have hD2int := integrable_prod_bounded_mul_standardGaussianDensityD2
    hφm hφ hHm hKm hquad
  constructor
  · apply integral_integral_eq_zero_of_integral_eq_zero hD1int
    intro x
    change ∫ ω, φ x * standardGaussianDensityD1 x (K ω) ∂ρ = 0
    rw [integral_const_mul]
    have hzero := integral_standardGaussianDensityD1_whitened_replacementRotatedDeriv_eq_zero
      hXm hX3 hX0 B i α x
    simpa only [K, R', O, G, ρ, mul_zero] using congrArg (fun t ↦ φ x * t) hzero
  · apply integral_integral_eq_zero_of_integral_eq_zero hD2int
    intro x
    change ∫ ω, φ x * standardGaussianDensityD2 x (H ω) (K ω) ∂ρ = 0
    rw [integral_const_mul]
    have hzero := integral_standardGaussianDensityD2_whitened_replacementRotated_eq_zero
      hXm hX3 hX0 B i α x
    simpa only [H, K, R, R', O, G, ρ, mul_zero] using
      congrArg (fun t ↦ φ x * t) hzero

end BentkusInduction

open BentkusInduction

/-- The absolute third directional derivative of the standard Gaussian density has the same
dimension-free integral bound as its cubic Hermite contraction. -/
lemma integral_abs_standardGaussianDensityD3_volume_le
    {d : ℕ} (w g : EuclideanSpace ℝ (Fin d)) :
    ∫ x, |standardGaussianDensityD3 x w w g| ∂volume ≤
      (3 + Real.sqrt standardGaussianFourthMoment) * ‖w‖ ^ 2 * ‖g‖ := by
  have hEq :
      (∫ x : EuclideanSpace ℝ (Fin d),
          |gaussianThirdHermiteContraction x w g|
          ∂stdGaussian (EuclideanSpace ℝ (Fin d))) =
        ∫ x, standardGaussianDensityReal x *
          |gaussianThirdHermiteContraction x w g| ∂volume := by
    rw [stdGaussian_eq_withDensity_standardGaussianDensityReal,
      integral_withDensity_eq_integral_toReal_smul]
    · simp only [ENNReal.toReal_ofReal (standardGaussianDensityReal_nonneg _),
        smul_eq_mul]
    · exact measurable_standardGaussianDensityReal.ennreal_ofReal
    · filter_upwards with x
      simp
  calc
    ∫ x, |standardGaussianDensityD3 x w w g| ∂volume =
        ∫ x, standardGaussianDensityReal x *
          |gaussianThirdHermiteContraction x w g| ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      rw [standardGaussianDensityD3_sameDirection,
        ← standardGaussianDensityReal_eq_standardGaussianDensity,
        abs_mul, abs_of_nonneg (standardGaussianDensityReal_nonneg x)]
    _ = ∫ x : EuclideanSpace ℝ (Fin d),
          |gaussianThirdHermiteContraction x w g|
          ∂stdGaussian (EuclideanSpace ℝ (Fin d)) := hEq.symm
    _ ≤ (3 + Real.sqrt standardGaussianFourthMoment) * ‖w‖ ^ 2 * ‖g‖ :=
      integral_abs_gaussianThirdHermiteContraction_le w g

lemma integrable_standardGaussianDensityD3_volume
    {d : ℕ} (w g : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x ↦ standardGaussianDensityD3 x w w g) volume := by
  have hcontract :=
    integrable_gaussianThirdHermiteContraction_stdGaussian w g
  rw [stdGaussian_eq_withDensity_standardGaussianDensityReal] at hcontract
  have hweighted := (integrable_withDensity_iff_integrable_smul'
    measurable_standardGaussianDensityReal.ennreal_ofReal (by simp)).mp hcontract
  simp_rw [ENNReal.toReal_ofReal (standardGaussianDensityReal_nonneg _),
    smul_eq_mul] at hweighted
  have hfun : (fun x ↦ standardGaussianDensityD3 x w w g) =
      fun x ↦ standardGaussianDensityReal x *
        gaussianThirdHermiteContraction x w g := by
    funext x
    rw [standardGaussianDensityD3_sameDirection,
      ← standardGaussianDensityReal_eq_standardGaussianDensity]
  rw [hfun]
  exact hweighted

/-- Bentkus (3.20)--(3.22): multiplying a translated third Gaussian-density contraction by an
arbitrary measurable factor of absolute value at most one costs no more than the universal cubic
Hermite-contraction constant. -/
theorem bentkus_abs_integral_bounded_mul_standardGaussianDensityD3_sub_le
    {d : ℕ} {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφm : AEStronglyMeasurable φ volume) (hφ : ∀ x, |φ x| ≤ 1)
    (a w g : EuclideanSpace ℝ (Fin d)) :
    |∫ x, φ x * standardGaussianDensityD3 (x - a) w w g ∂volume| ≤
      (3 + Real.sqrt standardGaussianFourthMoment) * ‖w‖ ^ 2 * ‖g‖ := by
  have hD3 := integrable_standardGaussianDensityD3_volume w g
  have hD3shift : Integrable
      (fun x ↦ standardGaussianDensityD3 (x - a) w w g) volume :=
    hD3.comp_sub_right a
  have hproduct : Integrable
      (fun x ↦ φ x * standardGaussianDensityD3 (x - a) w w g) volume :=
    hD3shift.bdd_mul hφm (by
      filter_upwards with x
      simpa only [Real.norm_eq_abs] using hφ x)
  calc
    |∫ x, φ x * standardGaussianDensityD3 (x - a) w w g ∂volume| ≤
        ∫ x, |standardGaussianDensityD3 (x - a) w w g| ∂volume := by
      calc
        _ ≤ ∫ x, |φ x * standardGaussianDensityD3 (x - a) w w g| ∂volume :=
          abs_integral_le_integral_abs
        _ ≤ _ := by
          apply integral_mono hproduct.abs hD3shift.abs
          intro x
          change |φ x * standardGaussianDensityD3 (x - a) w w g| ≤
            |standardGaussianDensityD3 (x - a) w w g|
          rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hφ x)
    _ = ∫ x, |standardGaussianDensityD3 x w w g| ∂volume := by
      exact integral_sub_right_eq_self
        (fun x ↦ |standardGaussianDensityD3 x w w g|) a
    _ ≤ (3 + Real.sqrt standardGaussianFourthMoment) * ‖w‖ ^ 2 * ‖g‖ :=
      integral_abs_standardGaussianDensityD3_volume_le w g


namespace BentkusInduction

private lemma standardGaussianDensityD3_smul_second
    {d : ℕ} (x g a : EuclideanSpace ℝ (Fin d)) (c : ℝ) :
    standardGaussianDensityD3 x g (c • g) a =
      c * standardGaussianDensityD3 x g g a := by
  unfold standardGaussianDensityD3
  simp only [real_inner_smul_right, real_inner_smul_left]
  ring

/-- A scalar multiple in one of the repeated Gaussian-density directions is extracted before
applying the dimension-free cubic Hermite bound. -/
private theorem bentkus_abs_integral_bounded_mul_standardGaussianDensityD3_smul_second_le
    {d : ℕ} {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφm : AEStronglyMeasurable φ volume) (hφ : ∀ x, |φ x| ≤ 1)
    (a g l : EuclideanSpace ℝ (Fin d)) (c : ℝ) :
    |∫ x, φ x * standardGaussianDensityD3 (x - a) g (c • g) l ∂volume| ≤
      |c| * (3 + Real.sqrt standardGaussianFourthMoment) * ‖g‖ ^ 2 * ‖l‖ := by
  have hpoint (x : EuclideanSpace ℝ (Fin d)) :
      φ x * standardGaussianDensityD3 (x - a) g (c • g) l =
        c * (φ x * standardGaussianDensityD3 (x - a) g g l) := by
    rw [standardGaussianDensityD3_smul_second]
    ring
  rw [show (fun x ↦ φ x * standardGaussianDensityD3 (x - a) g (c • g) l) =
      fun x ↦ c * (φ x * standardGaussianDensityD3 (x - a) g g l) by
        funext x
        exact hpoint x,
    integral_const_mul, abs_mul]
  have hbase := bentkus_abs_integral_bounded_mul_standardGaussianDensityD3_sub_le
    hφm hφ a g l
  calc
    |c| * |∫ x, φ x * standardGaussianDensityD3 (x - a) g g l ∂volume| ≤
        |c| * ((3 + Real.sqrt standardGaussianFourthMoment) * ‖g‖ ^ 2 * ‖l‖) := by
      gcongr
    _ = |c| * (3 + Real.sqrt standardGaussianFourthMoment) * ‖g‖ ^ 2 * ‖l‖ := by
      ring

private theorem
    bentkus_integral_norm_bounded_mul_standardGaussianDensityD3_smul_second_le
    {d : ℕ} {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφm : AEStronglyMeasurable φ volume) (hφ : ∀ x, |φ x| ≤ 1)
    (a g l : EuclideanSpace ℝ (Fin d)) (c : ℝ) :
    (∫ x, ‖φ x * standardGaussianDensityD3 (x - a) g (c • g) l‖ ∂volume) ≤
      |c| * (3 + Real.sqrt standardGaussianFourthMoment) * ‖g‖ ^ 2 * ‖l‖ := by
  have hD3 := integrable_standardGaussianDensityD3_volume g l
  have hD3shift : Integrable
      (fun x ↦ standardGaussianDensityD3 (x - a) g g l) volume :=
    hD3.comp_sub_right a
  have hbase : Integrable
      (fun x ↦ φ x * standardGaussianDensityD3 (x - a) g g l) volume :=
    hD3shift.bdd_mul hφm (by
      filter_upwards with x
      simpa only [Real.norm_eq_abs] using hφ x)
  have hmono :
      (∫ x, |φ x * standardGaussianDensityD3 (x - a) g g l| ∂volume) ≤
        ∫ x, |standardGaussianDensityD3 (x - a) g g l| ∂volume := by
    apply integral_mono hbase.abs hD3shift.abs
    intro x
    change |φ x * standardGaussianDensityD3 (x - a) g g l| ≤
      |standardGaussianDensityD3 (x - a) g g l|
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hφ x)
  calc
    (∫ x, ‖φ x * standardGaussianDensityD3 (x - a) g (c • g) l‖ ∂volume) =
        |c| * ∫ x, |φ x * standardGaussianDensityD3 (x - a) g g l| ∂volume := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [standardGaussianDensityD3_smul_second, Real.norm_eq_abs,
        abs_mul, abs_mul]
      rw [abs_mul]
      ring
    _ ≤ |c| *
        ∫ x, |standardGaussianDensityD3 (x - a) g g l| ∂volume := by
      gcongr
    _ = |c| * ∫ x, |standardGaussianDensityD3 x g g l| ∂volume := by
      rw [integral_sub_right_eq_self
        (fun x ↦ |standardGaussianDensityD3 x g g l|) a]
    _ ≤ |c| *
        ((3 + Real.sqrt standardGaussianFourthMoment) * ‖g‖ ^ 2 * ‖l‖) := by
      gcongr
      exact integral_abs_standardGaussianDensityD3_volume_le g l
    _ = |c| * (3 + Real.sqrt standardGaussianFourthMoment) * ‖g‖ ^ 2 * ‖l‖ := by
      ring

private lemma contDiff_two_standardGaussianDensityD1
    {d : ℕ} (g : EuclideanSpace ℝ (Fin d)) :
    ContDiff ℝ 2
      (fun y : EuclideanSpace ℝ (Fin d) ↦ standardGaussianDensityD1 y g) := by
  let E := EuclideanSpace ℝ (Fin d)
  have hinner (v : E) : Differentiable ℝ (fun y : E ↦ inner ℝ y v) := by
    have heq : (fun y : E ↦ inner ℝ y v) = innerSL ℝ v := by
      funext y
      exact (real_inner_comm y v).symm
    rw [heq]
    exact (innerSL ℝ v).differentiable
  have hρ : Differentiable ℝ (standardGaussianDensity E) :=
    fun x ↦ (hasFDerivAt_standardGaussianDensity x).differentiableAt
  have hD1diff : Differentiable ℝ
      (fun y : E ↦ standardGaussianDensityD1 y g) := by
    simp only [standardGaussianDensityD1]
    exact (hinner g).neg.mul hρ
  apply (contDiff_succ_iff_fderiv_apply (n := 1)).2
  refine ⟨hD1diff, by simp, ?_⟩
  intro k
  have hD2diff : Differentiable ℝ
      (fun y : E ↦ standardGaussianDensityD2 y g k) := by
    simp only [standardGaussianDensityD2]
    exact (((hinner g).mul (hinner k)).sub
      (differentiable_const (c := inner ℝ g k))).mul hρ
  have hD2cont : ContDiff ℝ 1
      (fun y : E ↦ standardGaussianDensityD2 y g k) := by
    rw [contDiff_one_iff_fderiv]
    refine ⟨hD2diff, ?_⟩
    have hzero : ContDiff ℝ 0
        (fderiv ℝ (fun y : E ↦ standardGaussianDensityD2 y g k)) := by
      rw [contDiff_clm_apply_iff]
      intro l
      have heq : (fun y : E ↦
          fderiv ℝ (fun z : E ↦ standardGaussianDensityD2 z g k) y l) =
          fun y ↦ standardGaussianDensityD3 y g k l := by
        funext y
        exact fderiv_standardGaussianDensityD2_apply y g k l
      rw [heq]
      exact contDiff_zero.mpr (continuous_standardGaussianDensityD3 g k l)
    simpa only [contDiff_zero] using hzero
  have heq : (fun y : E ↦
      fderiv ℝ (fun z : E ↦ standardGaussianDensityD1 z g) y k) =
      fun y ↦ standardGaussianDensityD2 y g k := by
    funext y
    exact fderiv_standardGaussianDensityD1_apply y g k
  rw [heq]
  exact hD2cont

/-- First-order integral Taylor formula for the first Gaussian-density contraction. -/
lemma standardGaussianDensityD1_add_taylor_one
    {d : ℕ} (x a g : EuclideanSpace ℝ (Fin d)) :
    standardGaussianDensityD1 (x + a) g =
      standardGaussianDensityD1 x g +
        ∫ t in (0 : ℝ)..1, standardGaussianDensityD2 (x + t • a) g a := by
  have hf := contDiff_two_standardGaussianDensityD1 g
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := fun y : EuclideanSpace ℝ (Fin d) ↦ standardGaussianDensityD1 y g)
    (x := x) (y := a) (n := 0)
      (fun _ _ ↦ (hf.of_le (by norm_num)).contDiffAt)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    iteratedFDeriv_zero_apply] at ht
  rw [show (0 : ℕ) + 1 = 1 by norm_num] at ht
  simp only [iteratedFDeriv_one_apply,
    fderiv_standardGaussianDensityD1_apply] at ht
  simpa only [pow_zero, one_smul] using ht


/-- First-order integral Taylor formula for the second Gaussian-density contraction. -/
private lemma standardGaussianDensityD2_add_taylor_one
    {d : ℕ} (x a g w : EuclideanSpace ℝ (Fin d)) :
    standardGaussianDensityD2 (x + a) g w =
      standardGaussianDensityD2 x g w +
        ∫ t in (0 : ℝ)..1, standardGaussianDensityD3 (x + t • a) g w a := by
  have hf : ContDiff ℝ 1
      (fun y : EuclideanSpace ℝ (Fin d) ↦ standardGaussianDensityD2 y g w) := by
    have hinner (v : EuclideanSpace ℝ (Fin d)) : Differentiable ℝ
        (fun y : EuclideanSpace ℝ (Fin d) ↦ inner ℝ y v) := by
      have heq : (fun y : EuclideanSpace ℝ (Fin d) ↦ inner ℝ y v) = innerSL ℝ v := by
        funext y
        exact (real_inner_comm y v).symm
      rw [heq]
      exact (innerSL ℝ v).differentiable
    have hρ : Differentiable ℝ
        (standardGaussianDensity (EuclideanSpace ℝ (Fin d))) :=
      fun y ↦ (hasFDerivAt_standardGaussianDensity y).differentiableAt
    have hdiff : Differentiable ℝ
        (fun y : EuclideanSpace ℝ (Fin d) ↦ standardGaussianDensityD2 y g w) := by
      simp only [standardGaussianDensityD2]
      exact (((hinner g).mul (hinner w)).sub
        (differentiable_const (c := inner ℝ g w))).mul hρ
    rw [contDiff_one_iff_fderiv]
    refine ⟨hdiff, ?_⟩
    have hzero : ContDiff ℝ 0
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) ↦
          standardGaussianDensityD2 y g w)) := by
      rw [contDiff_clm_apply_iff]
      intro l
      have heq : (fun y : EuclideanSpace ℝ (Fin d) ↦
          fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) ↦
            standardGaussianDensityD2 z g w) y l) =
          fun y ↦ standardGaussianDensityD3 y g w l := by
        funext y
        exact fderiv_standardGaussianDensityD2_apply y g w l
      rw [heq]
      exact contDiff_zero.mpr (continuous_standardGaussianDensityD3 g w l)
    simpa only [contDiff_zero] using hzero
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := fun y : EuclideanSpace ℝ (Fin d) ↦ standardGaussianDensityD2 y g w)
    (x := x) (y := a) (n := 0) (fun _ _ ↦ hf.contDiffAt)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    iteratedFDeriv_zero_apply] at ht
  rw [show (0 : ℕ) + 1 = 1 by norm_num] at ht
  simp only [iteratedFDeriv_one_apply,
    fderiv_standardGaussianDensityD2_apply] at ht
  simpa only [pow_zero, one_smul] using ht

/-- Two-shift Taylor identity for the first Gaussian-density contraction, with the derivative
frozen before the first shift as in Bentkus (3.28). -/
private lemma standardGaussianDensityD1_twoShift_taylor
    {d : ℕ} (x v w g : EuclideanSpace ℝ (Fin d)) :
    standardGaussianDensityD1 (x + v + w) g -
        standardGaussianDensityD1 (x + v) g -
        standardGaussianDensityD2 x g w =
      ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
        standardGaussianDensityD3
          (x + r • (v + t • w)) g w (v + t • w) := by
  have houter := standardGaussianDensityD1_add_taylor_one (x + v) w g
  have hD2cont : Continuous (fun t : ℝ ↦
      standardGaussianDensityD2 (x + v + t • w) g w) :=
    (continuous_standardGaussianDensityD2 g w).comp (by fun_prop)
  have hconstCont : Continuous (fun _t : ℝ ↦ standardGaussianDensityD2 x g w) :=
    continuous_const
  calc
    standardGaussianDensityD1 (x + v + w) g -
        standardGaussianDensityD1 (x + v) g -
        standardGaussianDensityD2 x g w =
        (∫ t in (0 : ℝ)..1,
          standardGaussianDensityD2 (x + v + t • w) g w) -
          ∫ _t in (0 : ℝ)..1, standardGaussianDensityD2 x g w := by
      rw [houter]
      simp
    _ = ∫ t in (0 : ℝ)..1,
        (standardGaussianDensityD2 (x + v + t • w) g w -
          standardGaussianDensityD2 x g w) := by
      rw [intervalIntegral.integral_sub
        (hD2cont.intervalIntegrable 0 1)
        (hconstCont.intervalIntegrable 0 1)]
    _ = ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
        standardGaussianDensityD3
          (x + r • (v + t • w)) g w (v + t • w) := by
      apply intervalIntegral.integral_congr
      intro t _
      have ht := standardGaussianDensityD2_add_taylor_one x (v + t • w) g w
      change standardGaussianDensityD2 (x + v + t • w) g w -
          standardGaussianDensityD2 x g w =
        ∫ r in (0 : ℝ)..1,
          standardGaussianDensityD3 (x + r • (v + t • w)) g w (v + t • w)
      rw [show x + v + t • w = x + (v + t • w) by abel, ht]
      ring

/-- Integrated form of Bentkus's two-shift density expansion (3.28).  When the second shift is a
scalar multiple of the differentiated direction, the two missing derivatives cost only one
factor of that scalar and one first moment of the combined shift. -/
private theorem bentkus_standardGaussianDensityD1_twoShift_integral_bound
    {d : ℕ} {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφm : Measurable φ) (hφ : ∀ x, |φ x| ≤ 1)
    (v g : EuclideanSpace ℝ (Fin d)) (c : ℝ) :
    |∫ x, φ x *
        (standardGaussianDensityD1 (x + v + c • g) g -
          standardGaussianDensityD1 (x + v) g -
          standardGaussianDensityD2 x g (c • g)) ∂volume| ≤
      |c| * (3 + Real.sqrt standardGaussianFourthMoment) * ‖g‖ ^ 2 *
        (‖v‖ + |c| * ‖g‖) := by
  let E := EuclideanSpace ℝ (Fin d)
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let σ : Measure (ℝ × ℝ) := ν.prod ν
  let a : ℝ → E := fun t ↦ v + t • (c • g)
  let R : (ℝ × ℝ) → E → ℝ := fun p x ↦
    φ x * standardGaussianDensityD3 (x + p.2 • a p.1) g (c • g) (a p.1)
  let F : (ℝ × ℝ) × E → ℝ := fun z ↦ R z.1 z.2
  let L : ℝ := |c| * (3 + Real.sqrt standardGaussianFourthMoment) * ‖g‖ ^ 2 *
    (‖v‖ + |c| * ‖g‖)
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  have haNorm {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
      ‖a t‖ ≤ ‖v‖ + |c| * ‖g‖ := by
    calc
      ‖a t‖ = ‖v + t • (c • g)‖ := rfl
      _ ≤ ‖v‖ + ‖t • (c • g)‖ := norm_add_le _ _
      _ = ‖v‖ + |t| * (|c| * ‖g‖) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖v‖ + |c| * ‖g‖ := by
        have ht0 : 0 ≤ t := ht.1.le
        rw [abs_of_nonneg ht0]
        have hfactor : 0 ≤ |c| * ‖g‖ := mul_nonneg (abs_nonneg c) (norm_nonneg g)
        have hmul := mul_le_mul_of_nonneg_right ht.2 hfactor
        simpa [add_comm] using add_le_add_left (by simpa using hmul) ‖v‖
  have hRmeas : Measurable (Function.uncurry R) := by
    change Measurable (fun z : (ℝ × ℝ) × E ↦
      φ z.2 * standardGaussianDensityD3
        (z.2 + z.1.2 • (v + z.1.1 • (c • g))) g (c • g)
          (v + z.1.1 • (c • g)))
    unfold standardGaussianDensityD3 standardGaussianDensity
    fun_prop
  have hRint (p : ℝ × ℝ) : Integrable (R p) volume := by
    let b : E := a p.1
    have hD3 : Integrable
        (fun x : E ↦ standardGaussianDensityD3 (x - (-(p.2 • b))) g g b) volume :=
      (integrable_standardGaussianDensityD3_volume g b).comp_sub_right (-(p.2 • b))
    have hbase : Integrable
        (fun x : E ↦ φ x *
          standardGaussianDensityD3 (x - (-(p.2 • b))) g g b) volume :=
      hD3.bdd_mul hφm.aestronglyMeasurable (by
        filter_upwards with x
        simpa only [Real.norm_eq_abs] using hφ x)
    have hscaled := hbase.const_mul c
    convert hscaled using 1
    funext x
    dsimp only [R, b]
    rw [standardGaussianDensityD3_smul_second]
    have hx : x + p.2 • a p.1 = x - (-(p.2 • a p.1)) := by abel
    rw [hx]
    ring
  have hRnorm (p : ℝ × ℝ) :
      (∫ x, ‖R p x‖ ∂volume) ≤
        |c| * (3 + Real.sqrt standardGaussianFourthMoment) * ‖g‖ ^ 2 * ‖a p.1‖ := by
    have h :=
      bentkus_integral_norm_bounded_mul_standardGaussianDensityD3_smul_second_le
        hφm.aestronglyMeasurable hφ (-(p.2 • a p.1)) g (a p.1) c
    convert h using 1
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [R]
    have hx : x + p.2 • a p.1 = x - (-(p.2 • a p.1)) := by abel
    rw [hx]
  have hp : ∀ᵐ p : ℝ × ℝ ∂σ,
      p ∈ Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1 := by
    rw [Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioc.prod measurableSet_Ioc)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact ⟨ht, hr⟩
  have hFint : Integrable F (σ.prod volume) := by
    have hFm : AEStronglyMeasurable F (σ.prod volume) :=
      hRmeas.aestronglyMeasurable
    apply (integrable_prod_iff hFm).2
    constructor
    · filter_upwards with p
      exact hRint p
    · have hinnerMeas : AEStronglyMeasurable
          (fun p ↦ ∫ x, ‖F (p, x)‖ ∂volume) σ :=
        hFm.norm.integral_prod_right'
      apply Integrable.of_bound hinnerMeas L
      filter_upwards [hp] with p hp
      rw [Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg fun x ↦ norm_nonneg _)]
      calc
        (∫ x, ‖F (p, x)‖ ∂volume) ≤
            |c| * (3 + Real.sqrt standardGaussianFourthMoment) * ‖g‖ ^ 2 *
              ‖a p.1‖ := hRnorm p
        _ ≤ L := by
          dsimp only [L]
          gcongr
          exact haNorm hp.1
  have hsections : ∀ᵐ x : E ∂volume,
      Integrable (fun p ↦ F (p, x)) σ := by
    have hswapInt := hFint.swap
    have hm : AEStronglyMeasurable (F ∘ Prod.swap) (volume.prod σ) := hswapInt.1
    have hs := ((integrable_prod_iff hm).1 hswapInt).1
    simpa only [Function.comp_apply, Prod.swap_prod_mk] using hs
  have hpoint (x : E) :
      φ x *
          (standardGaussianDensityD1 (x + v + c • g) g -
            standardGaussianDensityD1 (x + v) g -
            standardGaussianDensityD2 x g (c • g)) =
        ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, R (t, r) x := by
    rw [standardGaussianDensityD1_twoShift_taylor x v (c • g) g,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    change φ x * (∫ r in (0 : ℝ)..1,
        standardGaussianDensityD3
          (x + r • (v + t • (c • g))) g (c • g) (v + t • (c • g))) =
      ∫ r in (0 : ℝ)..1, R (t, r) x
    rw [← intervalIntegral.integral_const_mul]
  have hpointProd : ∀ᵐ x : E ∂volume,
      φ x *
          (standardGaussianDensityD1 (x + v + c • g) g -
            standardGaussianDensityD1 (x + v) g -
            standardGaussianDensityD2 x g (c • g)) =
        ∫ p, F (p, x) ∂σ := by
    filter_upwards [hsections] with x hx
    rw [hpoint x]
    simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    change (∫ t, ∫ r, R (t, r) x ∂ν ∂ν) = ∫ p, F (p, x) ∂σ
    rw [← integral_prod (fun p ↦ F (p, x)) hx]
  have hswap :
      (∫ p, ∫ x, F (p, x) ∂volume ∂σ) =
        ∫ x, ∫ p, F (p, x) ∂σ ∂volume :=
    (integral_prod F hFint).symm.trans (integral_prod_symm F hFint)
  have hinnerInt : Integrable (fun p ↦ ∫ x, F (p, x) ∂volume) σ :=
    hFint.integral_prod_left
  have hmass : σ.real Set.univ = 1 := by
    rw [Measure.real_def]
    rw [show (Set.univ : Set (ℝ × ℝ)) =
        (Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ) by simp,
      Measure.prod_prod]
    simp only [ν, Measure.restrict_apply_univ, ENNReal.toReal_mul,
      Real.volume_Ioc, sub_zero]
    simp
  calc
    |∫ x, φ x *
        (standardGaussianDensityD1 (x + v + c • g) g -
          standardGaussianDensityD1 (x + v) g -
          standardGaussianDensityD2 x g (c • g)) ∂volume| =
        |∫ p, ∫ x, F (p, x) ∂volume ∂σ| := by
      congr 1
      calc
        _ = ∫ x, ∫ p, F (p, x) ∂σ ∂volume :=
          integral_congr_ae hpointProd
        _ = _ := hswap.symm
    _ ≤ ∫ p, |∫ x, F (p, x) ∂volume| ∂σ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _p, L ∂σ := by
      apply integral_mono_ae hinnerInt.abs (integrable_const L)
      filter_upwards [hp] with p hp
      change |∫ x, F (p, x) ∂volume| ≤ L
      have hbound :=
        bentkus_abs_integral_bounded_mul_standardGaussianDensityD3_smul_second_le
          hφm.aestronglyMeasurable hφ (-(p.2 • a p.1)) g (a p.1) c
      have hrewrite :
          |∫ x, F (p, x) ∂volume| =
            |∫ x, φ x * standardGaussianDensityD3
              (x - (-(p.2 • a p.1))) g (c • g) (a p.1) ∂volume| := by
        congr 2
        funext x
        dsimp only [F, R]
        have hx : x + p.2 • a p.1 = x - (-(p.2 • a p.1)) := by abel
        rw [hx]
      rw [hrewrite]
      calc
        _ ≤ |c| * (3 + Real.sqrt standardGaussianFourthMoment) * ‖g‖ ^ 2 *
            ‖a p.1‖ := hbound
        _ ≤ L := by
          dsimp only [L]
          gcongr
          exact haNorm hp.1
    _ = L := by simp only [integral_const, hmass, one_smul]
    _ = |c| * (3 + Real.sqrt standardGaussianFourthMoment) * ‖g‖ ^ 2 *
        (‖v‖ + |c| * ‖g‖) := rfl

private theorem bentkus_standardGaussianDensityD1_twoShift_integral_bound_of_bounded
    {d : ℕ} {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφm : Measurable φ) {D : ℝ} (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ D)
    (v g : EuclideanSpace ℝ (Fin d)) (c : ℝ) :
    |∫ x, φ x *
        (standardGaussianDensityD1 (x + v + c • g) g -
          standardGaussianDensityD1 (x + v) g -
          standardGaussianDensityD2 x g (c • g)) ∂volume| ≤
      D * |c| * (3 + Real.sqrt standardGaussianFourthMoment) * ‖g‖ ^ 2 *
        (‖v‖ + |c| * ‖g‖) := by
  rcases hD.eq_or_lt with rfl | hDpos
  · have hφ0 : φ = 0 := by
      funext x
      have hx := hφ x
      simp only [abs_nonpos_iff] at hx
      exact hx
    simp [hφ0]
  · let ψ := fun x ↦ φ x / D
    have hψm : Measurable ψ := hφm.div_const D
    have hψ : ∀ x, |ψ x| ≤ 1 := by
      intro x
      dsimp only [ψ]
      rw [abs_div, abs_of_pos hDpos]
      exact (div_le_one hDpos).2 (hφ x)
    have hbase := bentkus_standardGaussianDensityD1_twoShift_integral_bound
      hψm hψ v g c
    have hfun : (fun x ↦ φ x *
        (standardGaussianDensityD1 (x + v + c • g) g -
          standardGaussianDensityD1 (x + v) g -
          standardGaussianDensityD2 x g (c • g))) =
        fun x ↦ D * (ψ x *
          (standardGaussianDensityD1 (x + v + c • g) g -
            standardGaussianDensityD1 (x + v) g -
            standardGaussianDensityD2 x g (c • g))) := by
      funext x
      dsimp only [ψ]
      field_simp
    rw [hfun, integral_const_mul, abs_mul, abs_of_pos hDpos]
    calc
      D * |∫ x, ψ x *
          (standardGaussianDensityD1 (x + v + c • g) g -
            standardGaussianDensityD1 (x + v) g -
            standardGaussianDensityD2 x g (c • g)) ∂volume| ≤
          D * (|c| * (3 + Real.sqrt standardGaussianFourthMoment) * ‖g‖ ^ 2 *
            (‖v‖ + |c| * ‖g‖)) := by
        gcongr
      _ = D * |c| * (3 + Real.sqrt standardGaussianFourthMoment) * ‖g‖ ^ 2 *
          (‖v‖ + |c| * ‖g‖) := by ring

theorem
    bentkus_integral_standardGaussianDensityD1_twoShift_integral_bound_of_bounded
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ] {ν : Measure Θ}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφm : Measurable φ) {D : ℝ} (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ D)
    {v g : Θ → EuclideanSpace ℝ (Fin d)} (hvm : Measurable v) (hgm : Measurable g)
    (c : ℝ)
    (hvg : Integrable (fun θ ↦ ‖g θ‖ ^ 2 * (‖v θ‖ + |c| * ‖g θ‖)) ν) :
    |∫ θ, (∫ x, φ x *
        (standardGaussianDensityD1 (x + v θ + c • g θ) (g θ) -
          standardGaussianDensityD1 (x + v θ) (g θ) -
          standardGaussianDensityD2 x (g θ) (c • g θ)) ∂volume) ∂ν| ≤
      D * |c| * (3 + Real.sqrt standardGaussianFourthMoment) *
        ∫ θ, ‖g θ‖ ^ 2 * (‖v θ‖ + |c| * ‖g θ‖) ∂ν := by
  let R : Θ → EuclideanSpace ℝ (Fin d) → ℝ := fun θ x ↦ φ x *
    (standardGaussianDensityD1 (x + v θ + c • g θ) (g θ) -
      standardGaussianDensityD1 (x + v θ) (g θ) -
      standardGaussianDensityD2 x (g θ) (c • g θ))
  let K : ℝ := D * |c| * (3 + Real.sqrt standardGaussianFourthMoment)
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hRm : Measurable (Function.uncurry R) := by
    change Measurable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦ φ p.2 *
      (standardGaussianDensityD1 (p.2 + v p.1 + c • g p.1) (g p.1) -
        standardGaussianDensityD1 (p.2 + v p.1) (g p.1) -
        standardGaussianDensityD2 p.2 (g p.1) (c • g p.1)))
    unfold standardGaussianDensityD1 standardGaussianDensityD2 standardGaussianDensity
    fun_prop
  have hinnerMeas : AEStronglyMeasurable (fun θ ↦ ∫ x, R θ x ∂volume) ν :=
    hRm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
  have hmajor : Integrable
      (fun θ ↦ K * (‖g θ‖ ^ 2 * (‖v θ‖ + |c| * ‖g θ‖))) ν :=
    hvg.const_mul K
  have hpoint (θ : Θ) : |∫ x, R θ x ∂volume| ≤
      K * (‖g θ‖ ^ 2 * (‖v θ‖ + |c| * ‖g θ‖)) := by
    have h := bentkus_standardGaussianDensityD1_twoShift_integral_bound_of_bounded
      hφm hD hφ (v θ) (g θ) c
    simpa only [R, K, mul_assoc] using h
  have hinnerInt : Integrable (fun θ ↦ ∫ x, R θ x ∂volume) ν := by
    apply hmajor.mono' hinnerMeas
    filter_upwards with θ
    rw [Real.norm_eq_abs]
    exact hpoint θ
  calc
    |∫ θ, (∫ x, φ x *
        (standardGaussianDensityD1 (x + v θ + c • g θ) (g θ) -
          standardGaussianDensityD1 (x + v θ) (g θ) -
          standardGaussianDensityD2 x (g θ) (c • g θ)) ∂volume) ∂ν| =
        |∫ θ, ∫ x, R θ x ∂volume ∂ν| := rfl
    _ ≤ ∫ θ, |∫ x, R θ x ∂volume| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ θ, K * (‖g θ‖ ^ 2 * (‖v θ‖ + |c| * ‖g θ‖)) ∂ν := by
      exact integral_mono hinnerInt.abs hmajor hpoint
    _ = D * |c| * (3 + Real.sqrt standardGaussianFourthMoment) *
        ∫ θ, ‖g θ‖ ^ 2 * (‖v θ‖ + |c| * ‖g θ‖) ∂ν := by
      rw [integral_const_mul]


/-- The second-order integral Taylor formula for the first standard-Gaussian density
contraction, in the orientation used in Bentkus (3.17)--(3.19). -/
lemma standardGaussianDensityD1_sub_taylor_two
    {d : ℕ} (x h g : EuclideanSpace ℝ (Fin d)) :
    standardGaussianDensityD1 (x - h) g =
      standardGaussianDensityD1 x g - standardGaussianDensityD2 x h g +
        ∫ t in (0 : ℝ)..1, (1 - t) *
          standardGaussianDensityD3 (x - t • h) h h g := by
  have hf := contDiff_two_standardGaussianDensityD1 g
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := fun y : EuclideanSpace ℝ (Fin d) ↦ standardGaussianDensityD1 y g)
    (x := x) (y := -h) (n := 1)
    (fun t _ ↦ hf.contDiffAt)
  rw [show x + -h = x - h by abel] at ht
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    iteratedFDeriv_zero_apply, Nat.factorial_one, pow_one,
    iteratedFDeriv_one_apply] at ht
  rw [fderiv_standardGaussianDensityD1_apply] at ht
  rw [show (1 : ℕ) + 1 = 2 by norm_num] at ht
  have hiter (z : EuclideanSpace ℝ (Fin d)) :
      (iteratedFDeriv ℝ 2
          (fun y : EuclideanSpace ℝ (Fin d) ↦ standardGaussianDensityD1 y g) z)
          (fun _ ↦ -h) = standardGaussianDensityD3 z h h g := by
    rw [(ContDiff.differentiable_iteratedFDeriv (m := 1) (by norm_num) hf z
      ).iteratedFDeriv_succ_apply_left']
    have htail : Fin.tail (fun _ : Fin 2 ↦ -h) = fun _ : Fin 1 ↦ -h := by
      funext i
      rfl
    rw [htail]
    simp only [iteratedFDeriv_one_apply]
    have heq : (fun y : EuclideanSpace ℝ (Fin d) ↦
        fderiv ℝ
          (fun z : EuclideanSpace ℝ (Fin d) ↦ standardGaussianDensityD1 z g) y (-h)) =
        fun y ↦ standardGaussianDensityD2 y g (-h) := by
      funext y
      exact fderiv_standardGaussianDensityD1_apply y g (-h)
    rw [heq, fderiv_standardGaussianDensityD2_apply]
    unfold standardGaussianDensityD3
    simp only [inner_neg_right, inner_neg_left, neg_mul, mul_neg]
    rw [real_inner_comm g h]
    ring
  simp_rw [hiter] at ht
  have hD2neg : standardGaussianDensityD2 x g (-h) =
      -standardGaussianDensityD2 x h g := by
    unfold standardGaussianDensityD2
    simp only [inner_neg_right]
    rw [real_inner_comm g h]
    ring
  rw [hD2neg] at ht
  have hInt :
      (∫ t in (0 : ℝ)..1, (1 - t) •
          standardGaussianDensityD3 (x + t • -h) h h g) =
        ∫ t in (0 : ℝ)..1, (1 - t) *
          standardGaussianDensityD3 (x - t • h) h h g := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [smul_eq_mul]
    congr 2
    module
  rw [hInt] at ht
  convert ht using 1
  all_goals ring

end BentkusInduction

open BentkusInduction

/-- Bentkus (3.19)--(3.23): after the constant, linear, and quadratic terms cancel, the translated
first Gaussian-density contraction has an integrated second-order remainder bounded by one half
of the universal cubic Hermite-contraction constant. -/
theorem bentkus_standardGaussianDensityD1_secondOrderRemainder_integral_bound
    {d : ℕ} {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφm : Measurable φ) (hφ : ∀ x, |φ x| ≤ 1)
    (h g : EuclideanSpace ℝ (Fin d)) :
    |∫ x, φ x *
        (standardGaussianDensityD1 (x - h) g - standardGaussianDensityD1 x g +
          standardGaussianDensityD2 x h g) ∂volume| ≤
      (3 + Real.sqrt standardGaussianFourthMoment) / 2 * ‖h‖ ^ 2 * ‖g‖ := by
  let K : ℝ := (3 + Real.sqrt standardGaussianFourthMoment) * ‖h‖ ^ 2 * ‖g‖
  let R : ℝ → EuclideanSpace ℝ (Fin d) → ℝ := fun t x ↦
    (1 - t) * φ x * standardGaussianDensityD3 (x - t • h) h h g
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hRmeas : Measurable (Function.uncurry R) := by
    have hshift : Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) ↦
        standardGaussianDensityD3 (p.2 - p.1 • h) h h g) :=
      (measurable_standardGaussianDensityD3 h h g).comp (by fun_prop)
    exact ((measurable_const.sub measurable_fst).mul
      (hφm.comp measurable_snd)).mul hshift
  have hD3shift (t : ℝ) : Integrable
      (fun x ↦ standardGaussianDensityD3 (x - t • h) h h g) volume :=
    (integrable_standardGaussianDensityD3_volume h g).comp_sub_right (t • h)
  have hφD3 (t : ℝ) : Integrable
      (fun x ↦ φ x * standardGaussianDensityD3 (x - t • h) h h g) volume :=
    (hD3shift t).bdd_mul hφm.aestronglyMeasurable (by
      filter_upwards with x
      simpa only [Real.norm_eq_abs] using hφ x)
  have hRint (t : ℝ) : Integrable (R t) volume := by
    simpa only [R, mul_assoc] using (hφD3 t).const_mul (1 - t)
  have hinnerBound {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
      (∫ x, ‖R t x‖ ∂volume) ≤ (1 - t) * K := by
    have ht0 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    have hmono :
        (∫ x, |φ x * standardGaussianDensityD3 (x - t • h) h h g|
            ∂volume) ≤
          ∫ x, |standardGaussianDensityD3 (x - t • h) h h g| ∂volume := by
      apply integral_mono (hφD3 t).abs (hD3shift t).abs
      intro x
      change |φ x * standardGaussianDensityD3 (x - t • h) h h g| ≤
        |standardGaussianDensityD3 (x - t • h) h h g|
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hφ x)
    calc
      (∫ x, ‖R t x‖ ∂volume) =
          (1 - t) *
            ∫ x, |φ x * standardGaussianDensityD3 (x - t • h) h h g|
              ∂volume := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        dsimp only [R]
        rw [Real.norm_eq_abs]
        simp only [abs_mul, abs_of_nonneg ht0]
        ring
      _ ≤ (1 - t) *
          ∫ x, |standardGaussianDensityD3 (x - t • h) h h g| ∂volume := by
        gcongr
      _ = (1 - t) *
          ∫ x, |standardGaussianDensityD3 x h h g| ∂volume := by
        rw [integral_sub_right_eq_self
          (fun x ↦ |standardGaussianDensityD3 x h h g|) (t • h)]
      _ ≤ (1 - t) * K := by
        apply mul_le_mul_of_nonneg_left _ ht0
        exact integral_abs_standardGaussianDensityD3_volume_le h g
  have hRprod : Integrable (Function.uncurry R)
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod volume) := by
    letI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
      simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        (inferInstance : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    have hRm : AEStronglyMeasurable (Function.uncurry R)
        ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod volume) :=
      hRmeas.aestronglyMeasurable
    apply (integrable_prod_iff hRm).2
    constructor
    · filter_upwards with t
      exact hRint t
    · have hinnerMeas : AEStronglyMeasurable
          (fun t ↦ ∫ x, ‖R t x‖ ∂volume)
          (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
        hRm.norm.integral_prod_right'
      apply Integrable.of_bound hinnerMeas K
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by simpa using ht
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x ↦ norm_nonneg _)]
      calc
        (∫ x, ‖R t x‖ ∂volume) ≤ (1 - t) * K := hinnerBound ht'
        _ ≤ K := by
          nlinarith [ht'.1.le, ht'.2, hK]
  have hpoint (x : EuclideanSpace ℝ (Fin d)) :
      φ x *
          (standardGaussianDensityD1 (x - h) g - standardGaussianDensityD1 x g +
            standardGaussianDensityD2 x h g) =
        ∫ t in (0 : ℝ)..1, R t x := by
    rw [standardGaussianDensityD1_sub_taylor_two]
    ring_nf
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [R]
    ring
  have hswap :
      (∫ x, ∫ t in (0 : ℝ)..1, R t x ∂volume) =
        ∫ t in (0 : ℝ)..1, ∫ x, R t x ∂volume :=
    (intervalIntegral_integral_swap hRprod).symm
  calc
    |∫ x, φ x *
        (standardGaussianDensityD1 (x - h) g - standardGaussianDensityD1 x g +
          standardGaussianDensityD2 x h g) ∂volume| =
        |∫ t in (0 : ℝ)..1, ∫ x, R t x ∂volume| := by
      congr 1
      calc
        _ = ∫ x, ∫ t in (0 : ℝ)..1, R t x ∂volume := by
          apply integral_congr_ae
          filter_upwards with x
          exact hpoint x
        _ = _ := hswap
    _ ≤ ∫ t in (0 : ℝ)..1, (1 - t) * K := by
      rw [← Real.norm_eq_abs]
      apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
      · filter_upwards with t
        intro ht
        rw [Real.norm_eq_abs]
        exact (abs_integral_le_integral_abs.trans (hinnerBound ht))
      · exact (by fun_prop : Continuous (fun t : ℝ ↦ (1 - t) * K)
          ).intervalIntegrable 0 1
    _ = (3 + Real.sqrt standardGaussianFourthMoment) / 2 * ‖h‖ ^ 2 * ‖g‖ := by
      rw [intervalIntegral.integral_mul_const]
      have ht : (∫ t in (0 : ℝ)..1, 1 - t) = 1 / 2 := by
        calc
          (∫ t in (0 : ℝ)..1, 1 - t) =
              (∫ _t in (0 : ℝ)..1, (1 : ℝ)) -
                ∫ t in (0 : ℝ)..1, t := by
            simpa only [Pi.sub_apply, id_eq] using
              intervalIntegral.integral_sub
                (continuous_const.intervalIntegrable 0 1)
                (continuous_id.intervalIntegrable 0 1)
          _ = 1 / 2 := by
            rw [intervalIntegral.integral_const, integral_id]
            norm_num
      rw [ht]
      dsimp only [K]
      ring
end ProbabilityTheory
