/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.Bentkus.Induction.LargeAngleEstimate
import ProbabilityApproximation.Bentkus.Induction.SmallAngleEstimate

/-!
# Closure of Bentkus's standardized replacement induction

This stable public module combines the small-angle, large-angle, and Gaussian-reference pieces,
composes the smooth replacement estimate with Ball's shell theorem, closes the induction on the
number of summands, and exports the identity-covariance and general convex-set endpoints.
-/

open MeasureTheory InnerProductSpace Matrix Set
open scoped ENNReal MatrixOrder Pointwise RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

universe u

local instance inductionClosureConvexSpace {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

local instance inductionClosureIsModuleConvexSpace {d : ℕ} :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.ofModule

namespace BentkusInduction

set_option maxHeartbeats 2000000

/-- The final angle-integration step in Bentkus (3.30).  Once the conditioned small-angle
remainder has a `cos α` envelope, integration up to `arcsin ε` contributes exactly one factor
of `ε`. -/
private theorem bentkus_smallAngle_integral_le_of_cos_envelope
    {ε K : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {F : ℝ → ℝ}
    (hF : ∀ α ∈ Set.Ioc (0 : ℝ) (Real.arcsin ε), |F α| ≤ K * Real.cos α) :
    |∫ α in (0 : ℝ)..Real.arcsin ε, F α| ≤ K * ε := by
  have harcsin : 0 ≤ Real.arcsin ε := Real.arcsin_nonneg.mpr hε
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ α in (0 : ℝ)..Real.arcsin ε, F α‖ ≤
        ∫ α in (0 : ℝ)..Real.arcsin ε, K * Real.cos α := by
      apply intervalIntegral.norm_integral_le_of_norm_le harcsin
      · filter_upwards with α
        intro hα
        simpa only [Real.norm_eq_abs] using hF α hα
      · exact (continuous_const.mul Real.continuous_cos).intervalIntegrable _ _
    _ = K * ε := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral_cos_zero_arcsin hε hε1]

/-- The integrated small-angle contribution in Bentkus (3.13), normalized to the total
third-moment sum and the original coordinate moment. -/
private theorem bentkus_smallAngle_interval_rotationCoordinate_le
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
    (s : Set (EuclideanSpace ℝ (Fin d)))
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) :
    let ρ := bentkusReplacementMeasure μ X
    let β := ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
    let βk := ∫ ω, ‖X k ω‖ ^ 3 ∂μ
    |∫ α in (0 : ℝ)..Real.arcsin ε, ∫ ω,
        bentkusRotationCoordinateIntegrand s ε k α ω ∂ρ| ≤
      61440 * (d : ℝ) ^ (1 / 4 : ℝ) *
        (1 + C * β / ε) * βk := by
  let ρ := bentkusReplacementMeasure μ X
  let β := ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
  let βk := ∫ ω, ‖X k ω‖ ^ 3 ∂μ
  let βrem := ∑ i : Fin n, ∫ ω, ‖X (k.succAbove i) ω‖ ^ 3 ∂μ
  let βkρ := ∫ ω, ‖replacementOriginal (d := d) k ω‖ ^ 3 ∂ρ
  let K := (61440 / ε) * (d : ℝ) ^ (1 / 4 : ℝ) *
    (1 + C * β / ε) * βk
  have hβrem : βrem ≤ β := by
    exact fin_sum_succAbove_le_sum_univ k
      (fun i ↦ ∫ ω, ‖X i ω‖ ^ 3 ∂μ)
      (fun i ↦ integral_nonneg fun _ ↦ pow_nonneg (norm_nonneg _) _)
  have hβkρ : βkρ = βk := by
    simpa only [βkρ, βk, ρ] using
      integral_norm_pow_replacementOriginal_eq hXm k 3
  have hF : ∀ α ∈ Set.Ioc (0 : ℝ) (Real.arcsin ε),
      |∫ ω, bentkusRotationCoordinateIntegrand s ε k α ω ∂ρ| ≤
        K * Real.cos α := by
    intro α hα
    have hαhalf : α < Real.pi / 2 :=
      hα.2.trans_lt (Real.arcsin_lt_pi_div_two.mpr hε1)
    have hαpi : α < Real.pi := by
      linarith [Real.pi_pos]
    have hsin : 0 < Real.sin α :=
      Real.sin_pos_of_pos_of_lt_pi hα.1 hαpi
    have hcos : 0 < Real.cos α :=
      Real.cos_pos_of_mem_Ioo
        ⟨(neg_lt_zero.mpr (div_pos Real.pi_pos (by norm_num))).trans hα.1,
          hαhalf⟩
    have hpoint := bentkus_smallAngle_rotationCoordinate_le
      hC hIH hd hXm hX3 h_indep hX0 hidentity k hk α hsin hcos
        (closure s) isClosed_closure (closure_isConvexSet hs) hε
    have hpoint' :
        |∫ ω, bentkusRotationCoordinateIntegrand s ε k α ω ∂ρ| ≤
          (61440 / ε ^ 2) * (d : ℝ) ^ (1 / 4 : ℝ) *
            (C * βrem + ε) * Real.cos α * βkρ := by
      simpa only [ρ, βrem, βkρ, bentkusRotationCoordinateIntegrand,
        convexSetCutoff_closure] using hpoint
    calc
      |∫ ω, bentkusRotationCoordinateIntegrand s ε k α ω ∂ρ| ≤
          (61440 / ε ^ 2) * (d : ℝ) ^ (1 / 4 : ℝ) *
            (C * βrem + ε) * Real.cos α * βkρ := hpoint'
      _ ≤ (61440 / ε ^ 2) * (d : ℝ) ^ (1 / 4 : ℝ) *
            (C * β + ε) * Real.cos α * βk := by
        rw [hβkρ]
        gcongr
      _ = K * Real.cos α := by
        dsimp only [K]
        field_simp [ne_of_gt hε]
        ring
  have hsmall := bentkus_smallAngle_integral_le_of_cos_envelope
    hε.le hε1.le hF
  change
    |∫ α in (0 : ℝ)..Real.arcsin ε, ∫ ω,
        bentkusRotationCoordinateIntegrand s ε k α ω ∂ρ| ≤
      61440 * (d : ℝ) ^ (1 / 4 : ℝ) *
        (1 + C * β / ε) * βk
  calc
    |∫ α in (0 : ℝ)..Real.arcsin ε, ∫ ω,
        bentkusRotationCoordinateIntegrand s ε k α ω ∂ρ| ≤ K * ε := hsmall
    _ = 61440 * (d : ℝ) ^ (1 / 4 : ℝ) *
        (1 + C * β / ε) * βk := by
      dsimp only [K]
      field_simp [ne_of_gt hε]

/-- The integrated large-angle actual-minus-Gaussian comparison in Bentkus (3.14), normalized
to the public coordinate integrands and original moments. -/
private theorem bentkus_largeAngle_interval_coordinate_sub_reference_le
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
    (s : Set (EuclideanSpace ℝ (Fin d)))
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let ρ := bentkusReplacementMeasure μ X
    let F := fun α ↦ ∫ ω,
      bentkusRotationCoordinateIntegrand s ε k α ω ∂ρ
    let R := fun α ↦ ∫ ω,
      bentkusGaussianReferenceCoordinateIntegrand s ε k α ω ∂ρ
    let β := ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
    let βk := ∫ ω, ‖X k ω‖ ^ 3 ∂μ
    |∫ α in Real.arcsin ε..Real.pi / 2, F α - R α| ≤
      (16128 * (3 + Real.sqrt standardGaussianFourthMoment)) *
        (d : ℝ) ^ (1 / 4 : ℝ) * (C * β / ε) * βk := by
  let ρ := bentkusReplacementMeasure μ X
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let UO := bentkusLeaveOneOut
    (fun i ↦ replacementOriginal (d := d) i) k
  let VG := bentkusLeaveOneOut
    (fun i ↦ replacementGaussian (d := d) i) k
  let F := fun α ↦ ∫ ω,
    bentkusRotationCoordinateIntegrand s ε k α ω ∂ρ
  let R := fun α ↦ ∫ ω,
    bentkusGaussianReferenceCoordinateIntegrand s ε k α ω ∂ρ
  let Q := fun α ↦
    (∫ ω, (fderiv ℝ (convexSetCutoff s ε)
      ((Real.cos α • UO ω + Real.sin α • VG ω) +
        (Real.cos α • O ω + Real.sin α • G ω)))
      ((-(Real.sin α)) • O ω + Real.cos α • G ω) ∂ρ) -
    ∫ ω, (fderiv ℝ (convexSetCutoff s ε)
      (VG ω + (Real.cos α • O ω + Real.sin α • G ω)))
      ((-(Real.sin α)) • O ω + Real.cos α • G ω) ∂ρ
  let β := ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
  let βk := ∫ ω, ‖X k ω‖ ^ 3 ∂μ
  let βkρ := ∫ ω, ‖O ω‖ ^ 3 ∂ρ
  have hFQ (α : ℝ) : F α - R α = Q α := by
    dsimp only [F, R, Q, bentkusRotationCoordinateIntegrand,
      bentkusGaussianReferenceCoordinateIntegrand, O, G, UO, VG]
    congr 1
    apply integral_congr_ae
    filter_upwards with ω
    rw [bentkusRotatedSum_eq_leaveOneOut_add α
      (fun i ↦ replacementOriginal (d := d) i)
      (fun i ↦ replacementGaussian (d := d) i) k ω]
    rfl
  have hinterval :
      (∫ α in Real.arcsin ε..Real.pi / 2, F α - R α) =
        ∫ α in Real.arcsin ε..Real.pi / 2, Q α := by
    apply intervalIntegral.integral_congr
    intro α _
    exact hFQ α
  have hraw := bentkus_largeAngle_interval_rotationCoordinate_sub_reference_le
    hC hIH hd hXm hX3 h_indep hX0 hidentity k hk s hs hε hε1
  have hraw' :
      |∫ α in Real.arcsin ε..Real.pi / 2, Q α| ≤
        (2016 * (8 * C * (d : ℝ) ^ (1 / 4 : ℝ) * β) *
          (3 + Real.sqrt standardGaussianFourthMoment) * βkρ) / ε := by
    simpa only [Q, ρ, O, G, UO, VG, β, βkρ] using hraw
  have hβkρ : βkρ = βk := by
    simpa only [βkρ, βk, ρ, O] using
      integral_norm_pow_replacementOriginal_eq hXm k 3
  change
    |∫ α in Real.arcsin ε..Real.pi / 2, F α - R α| ≤
      (16128 * (3 + Real.sqrt standardGaussianFourthMoment)) *
        (d : ℝ) ^ (1 / 4 : ℝ) * (C * β / ε) * βk
  rw [hinterval]
  calc
    |∫ α in Real.arcsin ε..Real.pi / 2, Q α| ≤
        (2016 * (8 * C * (d : ℝ) ^ (1 / 4 : ℝ) * β) *
          (3 + Real.sqrt standardGaussianFourthMoment) * βkρ) / ε := hraw'
    _ = (16128 * (3 + Real.sqrt standardGaussianFourthMoment)) *
        (d : ℝ) ^ (1 / 4 : ℝ) * (C * β / ε) * βk := by
      rw [hβkρ]
      ring

/-- The Gaussian-reference contribution on the large-angle interval in Bentkus (3.15), with
the interval length absorbed into the dimension factor. -/
private theorem bentkus_largeAngle_interval_reference_le
    {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hd : 0 < d) (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (s : Set (EuclideanSpace ℝ (Fin d)))
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε) :
    let ρ := bentkusReplacementMeasure μ X
    let R := fun α ↦ ∫ ω,
      bentkusGaussianReferenceCoordinateIntegrand s ε k α ω ∂ρ
    let βk := ∫ ω, ‖X k ω‖ ^ 3 ∂μ
    |∫ α in Real.arcsin ε..Real.pi / 2, R α| ≤
      (896 * (3 + Real.sqrt standardGaussianFourthMoment)) *
        (d : ℝ) ^ (1 / 4 : ℝ) * βk := by
  let ρ := bentkusReplacementMeasure μ X
  let O := replacementOriginal (d := d) k
  let R := fun α ↦ ∫ ω,
    bentkusGaussianReferenceCoordinateIntegrand s ε k α ω ∂ρ
  let βk := ∫ ω, ‖X k ω‖ ^ 3 ∂μ
  let βkρ := ∫ ω, ‖O ω‖ ^ 3 ∂ρ
  let H := 3 + Real.sqrt standardGaussianFourthMoment
  have horder : Real.arcsin ε ≤ Real.pi / 2 :=
    Real.arcsin_le_pi_div_two ε
  have hraw := bentkus_intervalIntegral_gaussianLeaveOneOut_rotationDerivative_le
    hXm hX3 h_indep hX0 hidentity k hk horder hs hε
  have hraw' :
      |∫ α in Real.arcsin ε..Real.pi / 2, R α| ≤
        (Real.pi / 2 - Real.arcsin ε) * (448 * H) * βkρ := by
    simpa only [R, ρ, O, βkρ, H,
      bentkusGaussianReferenceCoordinateIntegrand] using hraw
  have hβkρ : βkρ = βk := by
    simpa only [βkρ, βk, ρ, O] using
      integral_norm_pow_replacementOriginal_eq hXm k 3
  have hH : 0 ≤ H := by
    dsimp only [H]
    positivity
  have hβk : 0 ≤ βk := by
    dsimp only [βk]
    exact integral_nonneg fun _ ↦ pow_nonneg (norm_nonneg _) _
  have hd14 : 1 ≤ (d : ℝ) ^ (1 / 4 : ℝ) :=
    one_le_dimension_rpow_quarter hd
  change
    |∫ α in Real.arcsin ε..Real.pi / 2, R α| ≤
      (896 * H) * (d : ℝ) ^ (1 / 4 : ℝ) * βk
  calc
    |∫ α in Real.arcsin ε..Real.pi / 2, R α| ≤
        (Real.pi / 2 - Real.arcsin ε) * (448 * H) * βkρ := hraw'
    _ ≤ 2 * (448 * H) * βk := by
      rw [hβkρ]
      gcongr
      exact pi_div_two_sub_arcsin_le_two hε.le
    _ = (896 * H) * 1 * βk := by ring
    _ ≤ (896 * H) * (d : ℝ) ^ (1 / 4 : ℝ) * βk := by
      gcongr

/-- The complete one-coordinate rotation estimate obtained by combining Bentkus
(3.13)--(3.15). -/
private theorem bentkus_interval_rotationCoordinate_le
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
    (s : Set (EuclideanSpace ℝ (Fin d)))
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) :
    let ρ := bentkusReplacementMeasure μ X
    let β := ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
    let βk := ∫ ω, ‖X k ω‖ ^ 3 ∂μ
    |∫ α in (0 : ℝ)..Real.pi / 2, ∫ ω,
        bentkusRotationCoordinateIntegrand s ε k α ω ∂ρ| ≤
      (61440 + 17024 *
        (3 + Real.sqrt standardGaussianFourthMoment)) *
        (d : ℝ) ^ (1 / 4 : ℝ) *
        (1 + C * β / ε) * βk := by
  let ρ := bentkusReplacementMeasure μ X
  let F := fun α ↦ ∫ ω,
    bentkusRotationCoordinateIntegrand s ε k α ω ∂ρ
  let R := fun α ↦ ∫ ω,
    bentkusGaussianReferenceCoordinateIntegrand s ε k α ω ∂ρ
  let γ := Real.arcsin ε
  let S := ∫ α in (0 : ℝ)..γ, F α
  let L := ∫ α in γ..Real.pi / 2, F α - R α
  let Q := ∫ α in γ..Real.pi / 2, R α
  let T := ∫ α in (0 : ℝ)..Real.pi / 2, F α
  let β := ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
  let βk := ∫ ω, ‖X k ω‖ ^ 3 ∂μ
  let H := 3 + Real.sqrt standardGaussianFourthMoment
  let d14 := (d : ℝ) ^ (1 / 4 : ℝ)
  let q := C * β / ε
  have hsmall := bentkus_smallAngle_interval_rotationCoordinate_le
    hC hIH hd hXm hX3 h_indep hX0 hidentity k hk s hs hε hε1
  have hlarge := bentkus_largeAngle_interval_coordinate_sub_reference_le
    hC hIH hd hXm hX3 h_indep hX0 hidentity k hk s hs hε hε1.le
  have href := bentkus_largeAngle_interval_reference_le
    hd hXm hX3 h_indep hX0 hidentity k hk s hs hε
  have hsmall' : |S| ≤ 61440 * d14 * (1 + q) * βk := by
    simpa only [S, F, γ, ρ, β, βk, d14, q] using hsmall
  have hlarge' : |L| ≤ (16128 * H) * d14 * q * βk := by
    simpa only [L, F, R, γ, ρ, β, βk, H, d14, q] using hlarge
  have href' : |Q| ≤ (896 * H) * d14 * βk := by
    simpa only [Q, R, γ, ρ, βk, H, d14] using href
  have hintSmall := intervalIntegrable_integral_bentkusCoordinateIntegrands
    hXm hX3 k hs hε (0 : ℝ) γ
  have hintLarge := intervalIntegrable_integral_bentkusCoordinateIntegrands
    hXm hX3 k hs hε γ (Real.pi / 2)
  have hdecomp : T = S + L + Q := by
    exact intervalIntegral_eq_small_add_difference_add_reference
      hintSmall.1 hintLarge.1 hintLarge.2
  have hβ : 0 ≤ β := by
    dsimp only [β]
    positivity
  have hβk : 0 ≤ βk := by
    dsimp only [βk]
    positivity
  have hH : 0 ≤ H := by
    dsimp only [H]
    positivity
  have hd14 : 0 ≤ d14 := by
    dsimp only [d14]
    positivity
  have hq : 0 ≤ q := by
    dsimp only [q]
    exact div_nonneg (mul_nonneg hC hβ) hε.le
  have hthree := bentkus_three_coordinate_pieces
    (S := S) (L := L) (R := Q) (T := T)
    (Ks := 61440) (Kl := 16128 * H) (Kr := 896 * H)
    (d14 := d14) (q := q) (βk := βk)
    (by positivity) (by positivity) hd14 hq hβk hdecomp
      hsmall' hlarge' href'
  change
    |T| ≤ (61440 + 17024 * H) * d14 * (1 + q) * βk
  convert hthree using 1 <;> ring

/-- The exact smooth-test estimate left by Bentkus (3.4)--(3.7), before Lemma 2.1 adds the
Gaussian boundary shells.  The strict branch hypotheses are retained because the proof uses the
leave-one-out induction estimate (3.34). -/
structure bentkusNontrivialSmoothCutoffEstimate (Ks C : ℝ) : Prop where
  bound : ∀ {n d : ℕ} (_hd : 0 < d)
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)),
    (∀ i, Measurable (X i)) →
    (∀ i, MemLp (X i) 3 μ) →
    iIndepFun X μ →
    (∀ i, ∫ ω, X i ω ∂μ = 0) →
    (∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y) →
    bentkusIdentityCovarianceBoundAt.{u} C n →
    (d : ℝ) ^ 3 * C ^ 2 < (n + 1 : ℕ) →
    (∀ k, (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4) →
    ∀ s : Set (EuclideanSpace ℝ (Fin d)),
      MeasurableSet s →
      Convexity.IsConvexSet ℝ s →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        let β := ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
        |∫ x, convexSetCutoff s ε x ∂(μ.map (fun ω ↦ ∑ i, X i ω)) -
            ∫ x, convexSetCutoff s ε x
              ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))| ≤
          Ks * (d : ℝ) ^ (1 / 4 : ℝ) * (β + C * β ^ 2 / ε)

/-- Bentkus's rotation argument supplies the complete smooth-test estimate in the strict
nontrivial induction branch. -/
theorem bentkusNontrivialSmoothCutoffEstimate_of_rotation
    {C : ℝ} (hC : 0 ≤ C) :
    bentkusNontrivialSmoothCutoffEstimate.{u}
      (61440 + 17024 *
        (3 + Real.sqrt standardGaussianFourthMoment)) C := by
  constructor
  intro n d hd Ω _ μ _ X hXm hX3 h_indep hX0 hidentity hIH
    _hcard hsmallMoment s _hsmeas hs ε hε hε1
  let ρ := bentkusReplacementMeasure μ X
  let β := ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
  let βk : Fin (n + 1) → ℝ := fun k ↦ ∫ ω, ‖X k ω‖ ^ 3 ∂μ
  let T : Fin (n + 1) → ℝ := fun k ↦
    ∫ α in (0 : ℝ)..Real.pi / 2, ∫ ω,
      bentkusRotationCoordinateIntegrand s ε k α ω ∂ρ
  let Ks := 61440 + 17024 *
    (3 + Real.sqrt standardGaussianFourthMoment)
  let d14 := (d : ℝ) ^ (1 / 4 : ℝ)
  have hcoord (k : Fin (n + 1)) :
      |T k| ≤ Ks * d14 * (1 + C * β / ε) * βk k := by
    have hk := bentkus_interval_rotationCoordinate_le
      hC hIH hd hXm hX3 h_indep hX0 hidentity k (hsmallMoment k)
        s hs hε hε1
    simpa only [T, Ks, d14, ρ, β, βk] using hk
  have hsum :
      |∑ k, T k| ≤ Ks * d14 * (β + C * β ^ 2 / ε) := by
    exact bentkus_coordinate_bounds_sum
      (T := T) (βk := βk) (K := Ks) (d14 := d14)
      (C := C) (β := β) (ε := ε) rfl hε hcoord
  have hendpoint := integral_convexSetCutoff_endpoint_eq_neg_rotation
    hXm hX3 h_indep hidentity hs hε
  have hendpoint' :
      (∫ x, convexSetCutoff s ε x ∂(μ.map (fun ω ↦ ∑ i, X i ω))) -
          ∫ x, convexSetCutoff s ε x
            ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
        -∫ ω, ∑ k, (∫ α in (0 : ℝ)..Real.pi / 2,
          bentkusRotationCoordinateIntegrand s ε k α ω) ∂ρ := by
    simpa only [ρ, bentkusRotationCoordinateIntegrand] using hendpoint
  have hswap := integral_sum_intervalIntegral_bentkusRotationCoordinate_eq
    hXm hX3 hs hε (a := (0 : ℝ)) (b := Real.pi / 2)
      (by positivity)
  have hswap' :
      (∫ ω, ∑ k, (∫ α in (0 : ℝ)..Real.pi / 2,
          bentkusRotationCoordinateIntegrand s ε k α ω) ∂ρ) =
        ∑ k, T k := by
    simpa only [ρ, T] using hswap
  change
    |(∫ x, convexSetCutoff s ε x ∂(μ.map (fun ω ↦ ∑ i, X i ω))) -
        ∫ x, convexSetCutoff s ε x
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))| ≤
      Ks * d14 * (β + C * β ^ 2 / ε)
  rw [hendpoint', hswap', abs_neg]
  exact hsum

/-- The two exact Gaussian shell inequalities needed by the smoothing step.  This formulation is
kept separate from the smooth replacement estimate because it is Ball's geometric theorem, not a
probabilistic induction lemma. -/
private structure bentkusGaussianShellBound : Prop where
  bound : ∀ {d : ℕ} (_hd : 0 < d)
    (s : Set (EuclideanSpace ℝ (Fin d))),
    MeasurableSet s →
    Convexity.IsConvexSet ℝ s →
    ∀ {ε : ℝ}, 0 ≤ ε →
      (stdGaussian (EuclideanSpace ℝ (Fin d))).real
            (Metric.cthickening ε (closure s) \ s) ≤
          4 * (d : ℝ) ^ (1 / 4 : ℝ) * ε ∧
        (stdGaussian (EuclideanSpace ℝ (Fin d))).real
            (s \ convexInnerParallel s ε) ≤
          4 * (d : ℝ) ^ (1 / 4 : ℝ) * ε

/-- Ball's Gaussian perimeter theorem supplies the exact shell input used by the Bentkus
replacement induction. -/
theorem bentkusGaussianShellBound_of_ball : bentkusGaussianShellBound := by
  constructor
  intro d _hd s _hsmeas hs ε hε
  simpa only [ballGaussianPerimeterConstant] using
    stdGaussian_shell_pair_le_ball hs hε

/-- The sole analytic input still required after the exact probability-space, branch, whitening,
rotation, and parameter reductions.  This is the combined content of Bentkus (3.6), equivalently
the estimates (3.13)--(3.15), in the strict nontrivial branch. -/
structure bentkusNontrivialTaylorEstimate (K C : ℝ) : Prop where
  bound : ∀ {n d : ℕ} (_hd : 0 < d)
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)),
    (∀ i, Measurable (X i)) →
    (∀ i, MemLp (X i) 3 μ) →
    iIndepFun X μ →
    (∀ i, ∫ ω, X i ω ∂μ = 0) →
    (∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y) →
    bentkusIdentityCovarianceBoundAt.{u} C n →
    (d : ℝ) ^ 3 * C ^ 2 < (n + 1 : ℕ) →
    (∀ k, (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4) →
    ∀ A : Set (EuclideanSpace ℝ (Fin d)),
      MeasurableSet A →
      Convexity.IsConvexSet ℝ A →
      let β := ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
      β * Real.sqrt C < 1 →
        |(μ.map (fun ω ↦ ∑ i, X i ω)).real A -
            (stdGaussian (EuclideanSpace ℝ (Fin d))).real A| ≤
          K * (d : ℝ) ^ (1 / 4 : ℝ) *
            (β * Real.sqrt C + β + C * β ^ 2 / (β * Real.sqrt C))

/-- Bentkus (3.3), (3.7), and (3.9) as an exact composition theorem.  Thus the analytic proof of
(3.13)--(3.15) only has to establish `bentkusNontrivialSmoothCutoffEstimate`; the shell theorem is
supplied independently by Ball's Gaussian-perimeter argument. -/
theorem bentkusNontrivialTaylorEstimate_of_smoothCutoff
    {Ks C : ℝ} (hKs : 0 ≤ Ks) (hC : 1 ≤ C)
    (hSmooth : bentkusNontrivialSmoothCutoffEstimate.{u} Ks C)
    (hShell : bentkusGaussianShellBound) :
    bentkusNontrivialTaylorEstimate.{u} (Ks + 4) C := by
  constructor
  intro n d hd Ω _ μ _ X hXm hX3 h_indep hX0 hidentity hIH hcard hsmallMoment
    A hA hAconv
  let β := ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
  change β * Real.sqrt C < 1 →
    |(μ.map (fun ω ↦ ∑ i, X i ω)).real A -
        (stdGaussian (EuclideanSpace ℝ (Fin d))).real A| ≤
      (Ks + 4) * (d : ℝ) ^ (1 / 4 : ℝ) *
        (β * Real.sqrt C + β + C * β ^ 2 / (β * Real.sqrt C))
  intro hscale
  have hβ : 0 < β := thirdMomentSum_pos_of_identityCovariance
    (n := n + 1) (d := d) (Ω := Ω) (μ := μ) (X := X)
    hd hX3 h_indep hX0 hidentity
  have hCpos : 0 < C := (by norm_num : (0 : ℝ) < 1).trans_le hC
  have hsqrt : 0 < Real.sqrt C := Real.sqrt_pos.2 hCpos
  let ε := β * Real.sqrt C
  have hε : 0 < ε := mul_pos hβ hsqrt
  have hOuterSmooth := hSmooth.bound (n := n) (d := d) (Ω := Ω)
    hd μ X hXm hX3 h_indep hX0 hidentity hIH
    hcard hsmallMoment A hA hAconv ε hε hscale
  have hInnerMeas : MeasurableSet (convexInnerParallel A ε) :=
    measurableSet_convexInnerParallel A ε
  have hInnerConv : Convexity.IsConvexSet ℝ (convexInnerParallel A ε) :=
    convexInnerParallel_isConvexSet hAconv ε
  have hInnerSmooth := hSmooth.bound (n := n) (d := d) (Ω := Ω)
    hd μ X hXm hX3 h_indep hX0 hidentity hIH
    hcard hsmallMoment (convexInnerParallel A ε) hInnerMeas hInnerConv ε hε hscale
  have hOuterShell := (hShell.bound (d := d) hd A hA hAconv hε.le).1
  have hInnerShell := (hShell.bound (d := d) hd A hA hAconv hε.le).2
  have hC0 : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans hC
  letI : IsProbabilityMeasure (μ.map (fun ω ↦ ∑ i, X i ω)) :=
    Measure.isProbabilityMeasure_map
      (memLp_finsetSum Finset.univ fun i _ ↦ hX3 i).aemeasurable
  have hcomp := bentkus_oneSet_taylorEstimate_of_smoothCutoff_and_shell
    (Ks := Ks) (C := C) (β := β) (ε := ε) (d := d)
    (ν := μ.map (fun ω ↦ ∑ i, X i ω)) (A := A)
    hKs hC0 hβ.le hε hA hAconv
    hOuterSmooth hInnerSmooth hOuterShell hInnerShell
  dsimp only [ε] at hcomp
  exact hcomp

/-- Once (3.13)--(3.15) are available in the exact combined form above, ordinary induction on the
number of summands closes the complete identity-covariance theorem. -/
theorem bentkusIdentityCovarianceBound_of_nontrivialTaylor
    {K C : ℝ} (hC : 1 ≤ C) (h8C : 8 ≤ C)
    (hKC : K * (2 * Real.sqrt C + 1) ≤ C)
    (hTaylor : bentkusNontrivialTaylorEstimate.{u} K C) :
    BentkusIdentityCovarianceBound.{u} C := by
  have hC0 : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans hC
  have hall : ∀ n, bentkusIdentityCovarianceBoundAt.{u} C n := by
    intro n
    induction n with
    | zero =>
        apply bentkusIdentityCovarianceBoundAt_of_measurable (C := C) (n := 0)
        apply bentkusIdentityCovarianceBoundAt_of_nontrivial
          (C := C) (M := C) (n := 0) hC0 le_rfl h8C
        intro d' hd' Ω' _ μ' _ X' hXm' hX3' h_indep' hX0' hidentity'
          hcard hsmallMoment A hA hAconv
        have hdnonneg : 0 ≤ (d' : ℝ) ^ 3 := pow_nonneg (Nat.cast_nonneg _) _
        have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
        norm_num at hcard
        nlinarith
    | succ n ihn =>
        apply bentkusIdentityCovarianceBoundAt_of_measurable (C := C) (n := n + 1)
        apply bentkusIdentityCovarianceBoundAt_of_nontrivial
          (C := C) (M := C) (n := n + 1) hC0 le_rfl h8C
        intro d' hd' Ω' _ μ' _ X' hXm' hX3' h_indep' hX0' hidentity'
          hcard hsmallMoment A hA hAconv
        apply bentkusIdentity_error_le_of_taylor_estimate
          (K := K) (C := C) (n := n + 1) (d := d') (Ω := Ω')
          (μ := μ') (X := X') hC hKC hd' hX3' h_indep' hX0' hidentity' A
        have hsumMeas : AEMeasurable (fun ω ↦ ∑ i, X' i ω) μ' :=
          (memLp_finsetSum Finset.univ fun i _ ↦ hX3' i).aemeasurable
        letI : IsProbabilityMeasure (μ'.map (fun ω ↦ ∑ i, X' i ω)) :=
          Measure.isProbabilityMeasure_map hsumMeas
        have hΔ1 : |(μ'.map (fun ω ↦ ∑ i, X' i ω)).real A -
            (stdGaussian (EuclideanSpace ℝ (Fin d'))).real A| ≤ 1 :=
          probability_measureReal_abs_sub_le_one
          (μ'.map (fun ω ↦ ∑ i, X' i ω))
          (stdGaussian (EuclideanSpace ℝ (Fin d'))) A
        refine ⟨hΔ1, ?_⟩
        intro hscale
        exact hTaylor.bound (n := n) (d := d') (Ω := Ω')
          hd' μ' X' hXm' hX3' h_indep' hX0' hidentity'
          ihn hcard hsmallMoment A hA hAconv hscale
  intro d n hd Ω _ μ _ X hX3 h_indep hX0 hidentity A hA hAconv
  simpa only [Measure.real_def] using
    (hall n hd μ X hX3 h_indep hX0 hidentity A hA hAconv)

end BentkusInduction

open BentkusInduction

/-- The standardized Bentkus induction admits one absolute constant. -/
theorem exists_bentkus_identity_covariance_constant :
    ∃ C : ℝ, 0 < C ∧ BentkusIdentityCovarianceBound.{u} C := by
  let H := 3 + Real.sqrt standardGaussianFourthMoment
  let Ks := 61440 + 17024 * H
  let K := Ks + 4
  let C := (4 * K + 3) ^ 2
  have hH : 0 ≤ H := by
    dsimp only [H]
    positivity
  have hKs : 0 ≤ Ks := by
    dsimp only [Ks]
    positivity
  have hK4 : 4 ≤ K := by
    dsimp only [K]
    linarith
  have hclosure := bentkus_constant_closure (K := K) hK4
  have hclosure' :
      0 < C ∧ 1 ≤ C ∧ 8 ≤ C ∧
        K * (2 * Real.sqrt C + 1) ≤ C := by
    simpa only [C] using hclosure
  rcases hclosure' with ⟨hCpos, hC1, hC8, hKC⟩
  have hSmooth : bentkusNontrivialSmoothCutoffEstimate.{u} Ks C := by
    simpa only [Ks, H] using
      (bentkusNontrivialSmoothCutoffEstimate_of_rotation
        (C := C) hCpos.le)
  have hTaylor : bentkusNontrivialTaylorEstimate.{u} K C := by
    have h := bentkusNontrivialTaylorEstimate_of_smoothCutoff
      hKs hC1 hSmooth bentkusGaussianShellBound_of_ball
    simpa only [K] using h
  refine ⟨C, hCpos, ?_⟩
  exact bentkusIdentityCovarianceBound_of_nontrivialTaylor
    hC1 hC8 hKC hTaylor

/-- Bentkus's multivariate Berry--Esseen theorem for measurable convex sets. -/
theorem exists_bentkus_convex_set_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d n : ℕ} (_hd : 0 < d)
        {Ω : Type u} [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Fin n → Ω → EuclideanSpace ℝ (Fin d))
        (S : Matrix (Fin d) (Fin d) ℝ),
        (∀ i, MemLp (X i) 3 μ) →
        iIndepFun X μ →
        (∀ i, ∫ ω, X i ω ∂μ = 0) →
        S.PosDef →
        (∀ x y,
          covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y =
            x ⬝ᵥ S *ᵥ y) →
        ∀ A : Set (EuclideanSpace ℝ (Fin d)),
          MeasurableSet A →
          Convexity.IsConvexSet ℝ A →
          |((μ.map (fun ω ↦ ∑ i, X i ω)) A).toReal -
              (multivariateGaussian 0 S A).toReal| ≤
            C * (d : ℝ) ^ (1 / 4 : ℝ) *
              ∑ i, ∫ ω,
                ‖(toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) (X i ω)‖ ^ 3 ∂μ := by
  exact exists_bentkus_convex_set_constant_of_identity_covariance_bound
    exists_bentkus_identity_covariance_constant
end ProbabilityTheory
