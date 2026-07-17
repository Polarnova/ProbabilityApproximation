/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.Bentkus.GaussianCompanionMoments
import ProbabilityApproximation.Bentkus.CovarianceAlgebra
import ProbabilityApproximation.Bentkus.SmoothingInequality
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fubini interfaces for Bentkus's rotation

This module packages the actual and Gaussian-reference coordinate integrands from Bentkus
(2004), equation (3.12), together with the product-integrability statements that justify
interchanging the angle and replacement-space integrals.
-/

open MeasureTheory InnerProductSpace Matrix Set
open scoped ENNReal MatrixOrder Pointwise RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

universe u

local instance {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

local instance {d : ℕ} :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.ofModule

/-- The coordinate contribution of the actual replacement rotation. -/
def bentkusRotationCoordinateIntegrand {n d : ℕ}
    (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) (k : Fin n)
    (α : ℝ) (ω : (Fin n → EuclideanSpace ℝ (Fin d)) ×
      (Fin n → EuclideanSpace ℝ (Fin d))) : ℝ :=
  (fderiv ℝ (convexSetCutoff s ε)
    (bentkusRotatedSum α
      (fun i ↦ replacementOriginal (d := d) i)
      (fun i ↦ replacementGaussian (d := d) i) ω))
    (bentkusRotatedDeriv α
      (replacementOriginal (d := d) k)
      (replacementGaussian (d := d) k) ω)

/-- The coordinate contribution with a fully Gaussian leave-one-out base. -/
def bentkusGaussianReferenceCoordinateIntegrand {n d : ℕ}
    (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) (k : Fin n)
    (α : ℝ) (ω : (Fin n → EuclideanSpace ℝ (Fin d)) ×
      (Fin n → EuclideanSpace ℝ (Fin d))) : ℝ :=
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let V := bentkusLeaveOneOut
    (fun i ↦ replacementGaussian (d := d) i) k
  (fderiv ℝ (convexSetCutoff s ε)
    (V ω + bentkusRotated α O G ω))
    (bentkusRotatedDeriv α O G ω)

/-- Splitting the rotated full sum at one coordinate gives the rotated leave-one-out base plus
the exposed coordinate. -/
lemma bentkusRotatedSum_eq_leaveOneOut_add
    {n d : ℕ} {Ω : Type*}
    (α : ℝ)
    (X Y : Fin n → Ω → EuclideanSpace ℝ (Fin d))
    (k : Fin n) (ω : Ω) :
    bentkusRotatedSum α X Y ω =
      (Real.cos α • bentkusLeaveOneOut X k ω +
        Real.sin α • bentkusLeaveOneOut Y k ω) +
      bentkusRotated α (X k) (Y k) ω := by
  unfold bentkusRotatedSum bentkusRotated bentkusLeaveOneOut
  rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun i ↦ Real.cos α • X i ω + Real.sin α • Y i ω)
    (Finset.mem_univ k), Finset.sum_add_distrib,
    ← Finset.smul_sum, ← Finset.smul_sum]

/-- Both coordinate integrands are integrable over a bounded angle interval times the canonical
replacement probability space. -/
theorem integrable_bentkusCoordinateIntegrands
    {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ)
    (k : Fin n) {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε)
    (a b : ℝ) :
    let ρ := bentkusReplacementMeasure μ X
    Integrable (Function.uncurry
      (bentkusRotationCoordinateIntegrand s ε k))
      ((volume.restrict (Set.uIoc a b)).prod ρ) ∧
    Integrable (Function.uncurry
      (bentkusGaussianReferenceCoordinateIntegrand s ε k))
      ((volume.restrict (Set.uIoc a b)).prod ρ) := by
  let ρ := bentkusReplacementMeasure μ X
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let I := volume.restrict (Set.uIoc a b)
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  letI : IsFiniteMeasure I := by
    dsimp only [I]
    by_cases hab : a ≤ b
    · rw [Set.uIoc_of_le hab]
      infer_instance
    · rw [Set.uIoc_of_ge (le_of_not_ge hab)]
      infer_instance
  have hO3 : MemLp O 3 ρ := memLp_replacementOriginal hXm hX3 k
  have hG3 : MemLp G 3 ρ := memLp_three_replacementGaussian hXm k
  have hO1 : Integrable (fun ω ↦ ‖O ω‖) ρ :=
    (hO3.integrable (by norm_num)).norm
  have hG1 : Integrable (fun ω ↦ ‖G ω‖) ρ :=
    (hG3.integrable (by norm_num)).norm
  have hmajorρ : Integrable
      (fun ω ↦ (2 / ε) * (‖O ω‖ + ‖G ω‖)) ρ :=
    (hO1.add hG1).const_mul (2 / ε)
  have hmajor : Integrable
      (fun p : ℝ × ((Fin n → EuclideanSpace ℝ (Fin d)) ×
        (Fin n → EuclideanSpace ℝ (Fin d))) ↦
        (2 / ε) * (‖O p.2‖ + ‖G p.2‖)) (I.prod ρ) :=
    hmajorρ.comp_snd I
  have hdir (α : ℝ) (ω) :
      ‖bentkusRotatedDeriv α O G ω‖ ≤ ‖O ω‖ + ‖G ω‖ := by
    change ‖(-(Real.sin α)) • O ω + (Real.cos α) • G ω‖ ≤ _
    calc
      _ ≤ ‖(-(Real.sin α)) • O ω‖ + ‖(Real.cos α) • G ω‖ := norm_add_le _ _
      _ = |Real.sin α| * ‖O ω‖ + |Real.cos α| * ‖G ω‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
      _ ≤ ‖O ω‖ + ‖G ω‖ := by
        exact add_le_add
          (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one α))
          (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one α))
  have hAmeas : Measurable (Function.uncurry
      (bentkusRotationCoordinateIntegrand s ε k)) := by
    have hpos : Measurable (fun p : ℝ × ((Fin n → EuclideanSpace ℝ (Fin d)) ×
        (Fin n → EuclideanSpace ℝ (Fin d))) ↦
        bentkusRotatedSum p.1
          (fun i ↦ replacementOriginal (d := d) i)
          (fun i ↦ replacementGaussian (d := d) i) p.2) := by
      simp only [bentkusRotatedSum, bentkusRotated,
        replacementOriginal, replacementGaussian]
      fun_prop
    have hdirection : Measurable (fun p : ℝ × ((Fin n → EuclideanSpace ℝ (Fin d)) ×
        (Fin n → EuclideanSpace ℝ (Fin d))) ↦
        bentkusRotatedDeriv p.1 O G p.2) := by
      simp only [O, G, bentkusRotatedDeriv,
        replacementOriginal, replacementGaussian]
      fun_prop
    change Measurable (fun p : ℝ × ((Fin n → EuclideanSpace ℝ (Fin d)) ×
        (Fin n → EuclideanSpace ℝ (Fin d))) ↦
      (fderiv ℝ (convexSetCutoff s ε)
        (bentkusRotatedSum p.1
          (fun i ↦ replacementOriginal (d := d) i)
          (fun i ↦ replacementGaussian (d := d) i) p.2))
        (bentkusRotatedDeriv p.1 O G p.2))
    exact ((contDiff_convexSetCutoff hs hε).continuous_fderiv_apply
      (by norm_num)).measurable.comp (hpos.prodMk hdirection)
  have hRmeas : Measurable (Function.uncurry
      (bentkusGaussianReferenceCoordinateIntegrand s ε k)) := by
    have hpos : Measurable (fun p : ℝ × ((Fin n → EuclideanSpace ℝ (Fin d)) ×
        (Fin n → EuclideanSpace ℝ (Fin d))) ↦
        bentkusLeaveOneOut
            (fun i ↦ replacementGaussian (d := d) i) k p.2 +
          bentkusRotated p.1 O G p.2) := by
      simp only [O, G, bentkusLeaveOneOut, bentkusRotated,
        replacementOriginal, replacementGaussian]
      fun_prop
    have hdirection : Measurable (fun p : ℝ × ((Fin n → EuclideanSpace ℝ (Fin d)) ×
        (Fin n → EuclideanSpace ℝ (Fin d))) ↦
        bentkusRotatedDeriv p.1 O G p.2) := by
      simp only [O, G, bentkusRotatedDeriv,
        replacementOriginal, replacementGaussian]
      fun_prop
    change Measurable (fun p : ℝ × ((Fin n → EuclideanSpace ℝ (Fin d)) ×
        (Fin n → EuclideanSpace ℝ (Fin d))) ↦
      (fderiv ℝ (convexSetCutoff s ε)
        (bentkusLeaveOneOut
            (fun i ↦ replacementGaussian (d := d) i) k p.2 +
          bentkusRotated p.1 O G p.2))
        (bentkusRotatedDeriv p.1 O G p.2))
    exact ((contDiff_convexSetCutoff hs hε).continuous_fderiv_apply
      (by norm_num)).measurable.comp (hpos.prodMk hdirection)
  constructor
  · apply hmajor.mono' hAmeas.aestronglyMeasurable
    filter_upwards with p
    rw [Real.norm_eq_abs]
    have happly := ContinuousLinearMap.le_opNorm
      (fderiv ℝ (convexSetCutoff s ε)
        (bentkusRotatedSum p.1
          (fun i ↦ replacementOriginal (d := d) i)
          (fun i ↦ replacementGaussian (d := d) i) p.2))
      (bentkusRotatedDeriv p.1 O G p.2)
    calc
      |bentkusRotationCoordinateIntegrand s ε k p.1 p.2| =
          ‖(fderiv ℝ (convexSetCutoff s ε)
            (bentkusRotatedSum p.1
              (fun i ↦ replacementOriginal (d := d) i)
              (fun i ↦ replacementGaussian (d := d) i) p.2))
            (bentkusRotatedDeriv p.1 O G p.2)‖ := by
        rw [Real.norm_eq_abs]
        rfl
      _ ≤ ‖fderiv ℝ (convexSetCutoff s ε)
            (bentkusRotatedSum p.1
              (fun i ↦ replacementOriginal (d := d) i)
              (fun i ↦ replacementGaussian (d := d) i) p.2)‖ *
          ‖bentkusRotatedDeriv p.1 O G p.2‖ := happly
      _ ≤ (2 / ε) * (‖O p.2‖ + ‖G p.2‖) := by
        exact mul_le_mul
          (norm_fderiv_convexSetCutoff_le hs hε _)
          (hdir p.1 p.2) (norm_nonneg _)
          (div_nonneg (by norm_num) hε.le)

  · apply hmajor.mono' hRmeas.aestronglyMeasurable
    filter_upwards with p
    rw [Real.norm_eq_abs]
    have happly := ContinuousLinearMap.le_opNorm
      (fderiv ℝ (convexSetCutoff s ε)
        (bentkusLeaveOneOut
          (fun i ↦ replacementGaussian (d := d) i) k p.2 +
          bentkusRotated p.1 O G p.2))
      (bentkusRotatedDeriv p.1 O G p.2)
    calc
      |bentkusGaussianReferenceCoordinateIntegrand s ε k p.1 p.2| =
          ‖(fderiv ℝ (convexSetCutoff s ε)
            (bentkusLeaveOneOut
              (fun i ↦ replacementGaussian (d := d) i) k p.2 +
              bentkusRotated p.1 O G p.2))
            (bentkusRotatedDeriv p.1 O G p.2)‖ := by
        rw [Real.norm_eq_abs]
        rfl
      _ ≤ ‖fderiv ℝ (convexSetCutoff s ε)
            (bentkusLeaveOneOut
              (fun i ↦ replacementGaussian (d := d) i) k p.2 +
              bentkusRotated p.1 O G p.2)‖ *
          ‖bentkusRotatedDeriv p.1 O G p.2‖ := happly
      _ ≤ (2 / ε) * (‖O p.2‖ + ‖G p.2‖) := by
        exact mul_le_mul
          (norm_fderiv_convexSetCutoff_le hs hε _)
          (hdir p.1 p.2) (norm_nonneg _)
          (div_nonneg (by norm_num) hε.le)

/-- The expected actual and Gaussian-reference coordinate contributions are interval integrable
as functions of the rotation angle. -/
theorem intervalIntegrable_integral_bentkusCoordinateIntegrands
    {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ)
    (k : Fin n) {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε)
    (a b : ℝ) :
    let ρ := bentkusReplacementMeasure μ X
    IntervalIntegrable (fun α ↦ ∫ ω,
      bentkusRotationCoordinateIntegrand s ε k α ω ∂ρ) volume a b ∧
    IntervalIntegrable (fun α ↦ ∫ ω,
      bentkusGaussianReferenceCoordinateIntegrand s ε k α ω ∂ρ)
      volume a b := by
  let ρ := bentkusReplacementMeasure μ X
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hprod := integrable_bentkusCoordinateIntegrands hXm hX3 k hs hε a b
  constructor
  · rw [intervalIntegrable_iff]
    exact hprod.1.integral_prod_left
  · rw [intervalIntegrable_iff]
    exact hprod.2.integral_prod_left

/-- The interval-integrated actual coordinate is integrable on the replacement space. -/
theorem integrable_intervalIntegral_bentkusRotationCoordinate
    {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ)
    (k : Fin n) {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε)
    {a b : ℝ} (hab : a ≤ b) :
    let ρ := bentkusReplacementMeasure μ X
    Integrable (fun ω ↦ ∫ α in a..b,
      bentkusRotationCoordinateIntegrand s ε k α ω) ρ := by
  let ρ := bentkusReplacementMeasure μ X
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hprod := (integrable_bentkusCoordinateIntegrands
    hXm hX3 k hs hε a b).1
  have hright := hprod.integral_prod_right
  simpa only [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab,
    ρ, Function.uncurry_apply_pair] using hright

/-- The interval-integrated Gaussian-reference coordinate is integrable on the replacement
space. -/
theorem integrable_intervalIntegral_bentkusGaussianReferenceCoordinate
    {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ)
    (k : Fin n) {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε)
    {a b : ℝ} (hab : a ≤ b) :
    let ρ := bentkusReplacementMeasure μ X
    Integrable (fun ω ↦ ∫ α in a..b,
      bentkusGaussianReferenceCoordinateIntegrand s ε k α ω) ρ := by
  let ρ := bentkusReplacementMeasure μ X
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hprod := (integrable_bentkusCoordinateIntegrands
    hXm hX3 k hs hε a b).2
  have hright := hprod.integral_prod_right
  simpa only [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab,
    ρ, Function.uncurry_apply_pair] using hright

/-- Fubini interchange for the actual coordinate contribution. -/
theorem intervalIntegral_integral_bentkusRotationCoordinate_swap
    {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ)
    (k : Fin n) {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε)
    (a b : ℝ) :
    let ρ := bentkusReplacementMeasure μ X
    (∫ α in a..b, ∫ ω,
        bentkusRotationCoordinateIntegrand s ε k α ω ∂ρ) =
      ∫ ω, (∫ α in a..b,
        bentkusRotationCoordinateIntegrand s ε k α ω) ∂ρ := by
  let ρ := bentkusReplacementMeasure μ X
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  exact intervalIntegral_integral_swap
    (integrable_bentkusCoordinateIntegrands hXm hX3 k hs hε a b).1

/-- Fubini interchange for the Gaussian-reference coordinate contribution. -/
theorem intervalIntegral_integral_bentkusGaussianReferenceCoordinate_swap
    {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ)
    (k : Fin n) {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε)
    (a b : ℝ) :
    let ρ := bentkusReplacementMeasure μ X
    (∫ α in a..b, ∫ ω,
        bentkusGaussianReferenceCoordinateIntegrand s ε k α ω ∂ρ) =
      ∫ ω, (∫ α in a..b,
        bentkusGaussianReferenceCoordinateIntegrand s ε k α ω) ∂ρ := by
  let ρ := bentkusReplacementMeasure μ X
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  exact intervalIntegral_integral_swap
    (integrable_bentkusCoordinateIntegrands hXm hX3 k hs hε a b).2

/-- The expected integral of the finite coordinate sum equals the sum of the expected
coordinate integrals, with the angle integral moved outside. -/
theorem integral_sum_intervalIntegral_bentkusRotationCoordinate_eq
    {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ)
    {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε)
    {a b : ℝ} (hab : a ≤ b) :
    let ρ := bentkusReplacementMeasure μ X
    (∫ ω, (∑ k, ∫ α in a..b,
        bentkusRotationCoordinateIntegrand s ε k α ω) ∂ρ) =
      ∑ k, ∫ α in a..b, ∫ ω,
        bentkusRotationCoordinateIntegrand s ε k α ω ∂ρ := by
  let ρ := bentkusReplacementMeasure μ X
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  dsimp only
  rw [MeasureTheory.integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro k _
    exact (intervalIntegral_integral_bentkusRotationCoordinate_swap
      hXm hX3 k hs hε a b).symm
  · intro k _
    exact integrable_intervalIntegral_bentkusRotationCoordinate
      hXm hX3 k hs hε hab

end ProbabilityTheory
