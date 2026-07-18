/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.Bentkus.CovarianceAlgebra
import Mathlib.Analysis.Matrix.Order
import Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Geometry.Convex.Set

/-!
# Whitening for the Bentkus covariance reduction

This module proves the linear-algebra and measure-transport facts used to pass from Bentkus's
identity-covariance theorem to arbitrary positive-definite total covariance.
For a covariance matrix `S`, the whitening map is `(CFC.sqrt S)⁻¹`; in particular it is not `S⁻¹`.
Only the total covariance is inverted.  Individual summand covariance matrices may remain singular.
-/

open MeasureTheory InnerProductSpace Matrix
open scoped MatrixOrder RealInnerProductSpace ENNReal

noncomputable section

namespace ProbabilityTheory

universe u

local instance whiteningConvexSpace {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

/-- The inverse positive square root used to whiten a positive-definite covariance matrix. -/
def bentkusWhiteningMatrix {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (CFC.sqrt S)⁻¹

/-- The continuous linear whitening map associated to `S`. -/
def bentkusWhiteningCLM {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  toEuclideanCLM (𝕜 := ℝ) (bentkusWhiteningMatrix S)

/-- The positive square root of a positive-definite matrix is nonsingular. -/
lemma isUnit_det_sqrt_of_posDef {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosDef) : IsUnit (CFC.sqrt S).det := by
  rw [hS.posSemidef.det_sqrt, RCLike.sqrt_of_nonneg hS.det_pos.le]
  exact isUnit_iff_ne_zero.mpr (Real.sqrt_pos.2 hS.det_pos).ne'

/-- The whitening matrix is a left inverse of the positive square root. -/
lemma bentkusWhiteningMatrix_mul_sqrt {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosDef) : bentkusWhiteningMatrix S * CFC.sqrt S = 1 := by
  exact Matrix.nonsing_inv_mul _ (isUnit_det_sqrt_of_posDef S hS)

/-- The whitening matrix is also a right inverse of the positive square root. -/
lemma sqrt_mul_bentkusWhiteningMatrix {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosDef) : CFC.sqrt S * bentkusWhiteningMatrix S = 1 := by
  exact Matrix.mul_nonsing_inv _ (isUnit_det_sqrt_of_posDef S hS)

/-- Conjugating a positive-definite covariance matrix by its whitening matrix gives identity. -/
theorem bentkusWhiteningMatrix_mul_self {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosDef) :
    bentkusWhiteningMatrix S * S * bentkusWhiteningMatrix S = 1 := by
  let R := CFC.sqrt S
  have hR : R * R = S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hdet : IsUnit R.det := isUnit_det_sqrt_of_posDef S hS
  change R⁻¹ * S * R⁻¹ = 1
  rw [← hR]
  calc
    R⁻¹ * (R * R) * R⁻¹ = (R⁻¹ * R) * (R * R⁻¹) := by noncomm_ring
    _ = 1 := by
      rw [Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet]
      simp

/-- The whitening operator is self-adjoint. -/
lemma adjoint_bentkusWhiteningCLM {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) :
    (bentkusWhiteningCLM S).adjoint = bentkusWhiteningCLM S := by
  apply IsSelfAdjoint.adjoint_eq
  let e := toEuclideanCLM (n := Fin d) (𝕜 := ℝ)
  have hT : IsSelfAdjoint (bentkusWhiteningMatrix S) := by
    unfold bentkusWhiteningMatrix
    exact (CFC.sqrt_nonneg S).isSelfAdjoint.isHermitian.inv.isSelfAdjoint
  show star (e (bentkusWhiteningMatrix S)) = e (bentkusWhiteningMatrix S)
  calc
    star (e (bentkusWhiteningMatrix S)) = e (star (bentkusWhiteningMatrix S)) :=
      (map_star e (bentkusWhiteningMatrix S)).symm
    _ = e (bentkusWhiteningMatrix S) := congrArg e hT.star_eq

/-- The whitening map bundled as a continuous linear equivalence. -/
def bentkusWhiteningEquiv {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef) :
    EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d) := by
  let R := CFC.sqrt S
  let T := R⁻¹
  have hdet : IsUnit R.det := isUnit_det_sqrt_of_posDef S hS
  have hTR : T * R = 1 := Matrix.nonsing_inv_mul R hdet
  have hRT : R * T = 1 := Matrix.mul_nonsing_inv R hdet
  exact ContinuousLinearEquiv.equivOfInverse
    (toEuclideanCLM (𝕜 := ℝ) T) (toEuclideanCLM (𝕜 := ℝ) R)
    (fun x ↦ by
      rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul, hRT]
      simp)
    (fun x ↦ by
      rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul, hTR]
      simp)

@[simp]
lemma bentkusWhiteningEquiv_apply {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosDef) (x : EuclideanSpace ℝ (Fin d)) :
    bentkusWhiteningEquiv S hS x = bentkusWhiteningCLM S x := by
  rfl

@[simp]
lemma bentkusWhiteningEquiv_symm_apply {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosDef) (x : EuclideanSpace ℝ (Fin d)) :
    (bentkusWhiteningEquiv S hS).symm x =
      toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x := by
  rfl

/-- Whitening sends the centered Gaussian with covariance `S` to standard Gaussian measure. -/
theorem map_multivariateGaussian_bentkusWhiteningEquiv {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef) :
    (multivariateGaussian 0 S).map (bentkusWhiteningEquiv S hS) =
      stdGaussian (EuclideanSpace ℝ (Fin d)) := by
  rw [multivariateGaussian, Measure.map_map]
  · have hcomp :
        (bentkusWhiteningEquiv S hS :
            EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ∘
            (fun x ↦ 0 + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x) = id := by
      funext x
      simp only [Function.comp_apply, zero_add, id_eq]
      change toEuclideanCLM (𝕜 := ℝ) (bentkusWhiteningMatrix S)
          (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x) = x
      rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
        bentkusWhiteningMatrix_mul_sqrt S hS]
      simp
    rw [hcomp, Measure.map_id]
  · exact (bentkusWhiteningEquiv S hS).continuous.measurable
  · fun_prop

/-- Standard Gaussian transported back through the square root has covariance `S`. -/
theorem map_stdGaussian_bentkusWhiteningEquiv_symm {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map (bentkusWhiteningEquiv S hS).symm =
      multivariateGaussian 0 S := by
  rw [← map_multivariateGaussian_bentkusWhiteningEquiv S hS,
    Measure.map_map]
  · simp
  · exact (bentkusWhiteningEquiv S hS).symm.continuous.measurable
  · exact (bentkusWhiteningEquiv S hS).continuous.measurable

/-- The threefold operator composition `S⁻¹ᐟ² ∘ S ∘ S⁻¹ᐟ²` is the identity. -/
lemma bentkusWhiteningCLM_covariance_comp (d : ℕ)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (x : EuclideanSpace ℝ (Fin d)) :
    bentkusWhiteningCLM S
        (toEuclideanCLM (𝕜 := ℝ) S (bentkusWhiteningCLM S x)) = x := by
  change toEuclideanCLM (𝕜 := ℝ) (bentkusWhiteningMatrix S)
      (toEuclideanCLM (𝕜 := ℝ) S
        (toEuclideanCLM (𝕜 := ℝ) (bentkusWhiteningMatrix S) x)) = x
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul]
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
    bentkusWhiteningMatrix_mul_self S hS]
  simp

/-- The transformed summand family used in the covariance-normalized Bentkus theorem. -/
def bentkusWhitenedSummand {n d : ℕ} {Ω : Type*}
    (S : Matrix (Fin d) (Fin d) ℝ)
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin d))
    (i : Fin n) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  bentkusWhiteningCLM S (X i ω)

/-- Whitening commutes with the finite sum of summands. -/
lemma sum_bentkusWhitenedSummand {n d : ℕ} {Ω : Type*}
    (S : Matrix (Fin d) (Fin d) ℝ)
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)) :
    (fun ω ↦ ∑ i, bentkusWhitenedSummand S X i ω) =
      bentkusWhiteningCLM S ∘ (fun ω ↦ ∑ i, X i ω) := by
  funext ω
  simp only [Function.comp_apply, bentkusWhitenedSummand, map_sum]

/-- A bounded linear image of an `Lᵖ` random vector remains in `Lᵖ`. -/
lemma memLp_bentkusWhiteningCLM_comp
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ≥0∞} (S : Matrix (Fin d) (Fin d) ℝ)
    {Z : Ω → EuclideanSpace ℝ (Fin d)} (hZ : MemLp Z p μ) :
    MemLp (fun ω ↦ bentkusWhiteningCLM S (Z ω)) p μ := by
  apply MemLp.of_le_mul hZ
    ((bentkusWhiteningCLM S).continuous.comp_aestronglyMeasurable
      hZ.aestronglyMeasurable)
  filter_upwards with ω
  exact (bentkusWhiteningCLM S).le_opNorm (Z ω)

/-- The whitened summands retain every `Lᵖ` moment possessed by the original summands. -/
lemma memLp_bentkusWhitenedSummand
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ≥0∞} (S : Matrix (Fin d) (Fin d) ℝ)
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, MemLp (X i) p μ) (i : Fin n) :
    MemLp (bentkusWhitenedSummand S X i) p μ :=
  memLp_bentkusWhiteningCLM_comp S (hX i)

/-- Measurable postcomposition by the whitening operator preserves mutual independence. -/
lemma iIndepFun_bentkusWhitenedSummand
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : Matrix (Fin d) (Fin d) ℝ)
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (h_indep : iIndepFun X μ) :
    iIndepFun (bentkusWhitenedSummand S X) μ := by
  change iIndepFun (fun i ↦ bentkusWhiteningCLM S ∘ X i) μ
  exact h_indep.comp (fun _ ↦ bentkusWhiteningCLM S)
    (fun _ ↦ (bentkusWhiteningCLM S).continuous.measurable)

/-- Centering is preserved by whitening. -/
lemma integral_bentkusWhitenedSummand_eq_zero
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (S : Matrix (Fin d) (Fin d) ℝ)
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, MemLp (X i) 3 μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0) (i : Fin n) :
    ∫ ω, bentkusWhitenedSummand S X i ω ∂μ = 0 := by
  change ∫ ω, bentkusWhiteningCLM S (X i ω) ∂μ = 0
  rw [ContinuousLinearMap.integral_comp_comm _ ((hX i).integrable (by norm_num)),
    h_mean i, map_zero]

/-- Under the stated covariance hypothesis, the whitened sum has identity covariance. -/
theorem covarianceBilin_map_sum_bentkusWhitenedSummand_eq_inner
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, MemLp (X i) 3 μ)
    (hcov : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = x ⬝ᵥ S *ᵥ y)
    (x y : EuclideanSpace ℝ (Fin d)) :
    covarianceBilin
        (μ.map (fun ω ↦ ∑ i, bentkusWhitenedSummand S X i ω)) x y =
      inner ℝ x y := by
  let W : Ω → EuclideanSpace ℝ (Fin d) := fun ω ↦ ∑ i, X i ω
  have hW3 : MemLp W 3 μ :=
    memLp_finsetSum Finset.univ fun i _ ↦ hX i
  have hW2 : MemLp W 2 μ := hW3.mono_exponent (by norm_num)
  have hLaw : MemLp id 2 (μ.map W) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hW2.aemeasurable).2 (by
      simpa only [Function.comp_def, id_eq] using hW2)
  have hmap :
      μ.map (fun ω ↦ ∑ i, bentkusWhitenedSummand S X i ω) =
        (μ.map W).map (bentkusWhiteningCLM S) := by
    rw [sum_bentkusWhitenedSummand S X]
    exact (AEMeasurable.map_map_of_aemeasurable
      (bentkusWhiteningCLM S).continuous.measurable.aemeasurable
      hW2.aemeasurable).symm
  rw [hmap, covarianceBilin_map hLaw, adjoint_bentkusWhiteningCLM,
    hcov, ← inner_toEuclideanCLM]
  rw [← (bentkusWhiteningCLM S).adjoint_inner_right]
  simp only [adjoint_bentkusWhiteningCLM]
  rw [bentkusWhiteningCLM_covariance_comp d S hS]

/-- Image of a set under the whitening equivalence. -/
def bentkusWhitenedSet {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (A : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)) :=
  bentkusWhiteningEquiv S hS '' A

/-- An invertible whitening map preserves measurability of sets. -/
lemma measurableSet_bentkusWhitenedSet {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    {A : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A) :
    MeasurableSet (bentkusWhitenedSet S hS A) := by
  exact (((bentkusWhiteningEquiv S hS).toHomeomorph.toMeasurableEquiv
    ).measurableSet_image).2 hA

/-- An invertible linear whitening map preserves convexity. -/
lemma isConvexSet_bentkusWhitenedSet {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    {A : Set (EuclideanSpace ℝ (Fin d))} (hA : Convexity.IsConvexSet ℝ A) :
    Convexity.IsConvexSet ℝ (bentkusWhitenedSet S hS A) := by
  letI : Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
    Convexity.IsModuleConvexSpace.ofModule
  change Convexity.IsConvexSet ℝ (bentkusWhiteningCLM S '' A)
  apply hA.image
  constructor
  intro w
  rw [Convexity.sConvexComb_eq_sum, Convexity.sConvexComb_eq_sum]
  rw [map_finsuppSum]
  change w.weights.sum (fun m r ↦ bentkusWhiteningCLM S (r • m)) =
    (w.weights.mapDomain (bentkusWhiteningCLM S)).sum (fun m r ↦ r • m)
  rw [Finsupp.sum_mapDomain_index]
  · simp
  · simp
  · simp [add_smul]

/-- The law of the whitened sum is the pushforward of the original sum law by the whitening
equivalence.  Only a.e. measurability, supplied here by `MemLp`, is required. -/
theorem map_sum_bentkusWhitenedSummand
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, MemLp (X i) 3 μ) :
    μ.map (fun ω ↦ ∑ i, bentkusWhitenedSummand S X i ω) =
      (μ.map (fun ω ↦ ∑ i, X i ω)).map (bentkusWhiteningEquiv S hS) := by
  let W : Ω → EuclideanSpace ℝ (Fin d) := fun ω ↦ ∑ i, X i ω
  have hW3 : MemLp W 3 μ :=
    memLp_finsetSum Finset.univ fun i _ ↦ hX i
  rw [sum_bentkusWhitenedSummand S X]
  exact (AEMeasurable.map_map_of_aemeasurable
    (bentkusWhiteningEquiv S hS).continuous.measurable.aemeasurable
    hW3.aemeasurable).symm

/-- The whitened-sum event in the image set is exactly the original-sum event. -/
lemma map_sum_apply_bentkusWhitenedSet
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, MemLp (X i) 3 μ)
    (A : Set (EuclideanSpace ℝ (Fin d))) :
    (μ.map (fun ω ↦ ∑ i, bentkusWhitenedSummand S X i ω))
        (bentkusWhitenedSet S hS A) =
      (μ.map (fun ω ↦ ∑ i, X i ω)) A := by
  rw [map_sum_bentkusWhitenedSummand S hS hX]
  change ((μ.map (fun ω ↦ ∑ i, X i ω)).map
      ((bentkusWhiteningEquiv S hS).toHomeomorph.toMeasurableEquiv))
        ((bentkusWhiteningEquiv S hS).toHomeomorph.toMeasurableEquiv '' A) = _
  rw [MeasurableEquiv.map_apply]
  exact congrArg (μ.map (fun ω ↦ ∑ i, X i ω))
    (Set.preimage_image_eq A (bentkusWhiteningEquiv S hS).injective)

/-- The standard-Gaussian event in the whitened image is exactly the original Gaussian event. -/
lemma stdGaussian_apply_bentkusWhitenedSet {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (A : Set (EuclideanSpace ℝ (Fin d))) :
    stdGaussian (EuclideanSpace ℝ (Fin d)) (bentkusWhitenedSet S hS A) =
      multivariateGaussian 0 S A := by
  rw [← map_multivariateGaussian_bentkusWhiteningEquiv S hS]
  change ((multivariateGaussian 0 S).map
      ((bentkusWhiteningEquiv S hS).toHomeomorph.toMeasurableEquiv))
        ((bentkusWhiteningEquiv S hS).toHomeomorph.toMeasurableEquiv '' A) = _
  rw [MeasurableEquiv.map_apply]
  exact congrArg (multivariateGaussian 0 S)
    (Set.preimage_image_eq A (bentkusWhiteningEquiv S hS).injective)

/-- The normalized theorem proved by Bentkus's induction: total covariance is identity and the
comparison law is standard Gaussian. -/
def BentkusIdentityCovarianceBound (C : ℝ) : Prop :=
  ∀ {d n : ℕ} (_hd : 0 < d)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)),
    (∀ i, MemLp (X i) 3 μ) →
    iIndepFun X μ →
    (∀ i, ∫ ω, X i ω ∂μ = 0) →
    (∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y) →
    ∀ A : Set (EuclideanSpace ℝ (Fin d)),
      MeasurableSet A →
      Convexity.IsConvexSet ℝ A →
      |((μ.map (fun ω ↦ ∑ i, X i ω)) A).toReal -
          (stdGaussian (EuclideanSpace ℝ (Fin d)) A).toReal| ≤
        C * (d : ℝ) ^ (1 / 4 : ℝ) *
          ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ

/-- **Bentkus whitening reduction, at one set.**  Once the identity-covariance estimate has been
proved for the whitened family and the image of `A`, this theorem transports that estimate back to
the original variables and covariance matrix.  This is the reduction described after Theorem 1.1
of Bentkus (2004). -/
theorem bentkus_convex_set_whitening_reduction
    (C : ℝ) {d n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin d))
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (hX : ∀ i, MemLp (X i) 3 μ)
    (A : Set (EuclideanSpace ℝ (Fin d)))
    (hbound :
      |((μ.map (fun ω ↦ ∑ i, bentkusWhitenedSummand S X i ω))
            (bentkusWhitenedSet S hS A)).toReal -
          (stdGaussian (EuclideanSpace ℝ (Fin d))
            (bentkusWhitenedSet S hS A)).toReal| ≤
        C * (d : ℝ) ^ (1 / 4 : ℝ) *
          ∑ i, ∫ ω, ‖bentkusWhitenedSummand S X i ω‖ ^ 3 ∂μ) :
    |((μ.map (fun ω ↦ ∑ i, X i ω)) A).toReal -
        (multivariateGaussian 0 S A).toReal| ≤
      C * (d : ℝ) ^ (1 / 4 : ℝ) *
        ∑ i, ∫ ω,
          ‖(toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) (X i ω)‖ ^ 3 ∂μ := by
  rw [map_sum_apply_bentkusWhitenedSet S hS hX A,
    stdGaussian_apply_bentkusWhitenedSet S hS A] at hbound
  simpa only [bentkusWhitenedSummand, bentkusWhiteningCLM,
    bentkusWhiteningMatrix] using hbound

/-- A dimension-free identity-covariance Bentkus bound transports to the corresponding bound for
an arbitrary positive-definite total covariance by applying the probabilistic estimate in
standardized coordinates. -/
theorem bentkus_convex_set_bound_of_identity_covariance_bound
    (C : ℝ) (hC : BentkusIdentityCovarianceBound.{u} C)
    {d n : ℕ} (hd : 0 < d)
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin d))
    (S : Matrix (Fin d) (Fin d) ℝ)
    (hX : ∀ i, MemLp (X i) 3 μ)
    (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hS : S.PosDef)
    (hcov : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = x ⬝ᵥ S *ᵥ y)
    (A : Set (EuclideanSpace ℝ (Fin d)))
    (hA : MeasurableSet A) (hAconv : Convexity.IsConvexSet ℝ A) :
    |((μ.map (fun ω ↦ ∑ i, X i ω)) A).toReal -
        (multivariateGaussian 0 S A).toReal| ≤
      C * (d : ℝ) ^ (1 / 4 : ℝ) *
        ∑ i, ∫ ω,
          ‖(toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) (X i ω)‖ ^ 3 ∂μ := by
  let W := bentkusWhitenedSummand S X
  let B := bentkusWhitenedSet S hS A
  have hW3 : ∀ i, MemLp (W i) 3 μ := by
    intro i
    simpa only [W] using memLp_bentkusWhitenedSummand S hX i
  have hWindep : iIndepFun W μ := by
    simpa only [W] using iIndepFun_bentkusWhitenedSummand S h_indep
  have hW0 : ∀ i, ∫ ω, W i ω ∂μ = 0 := by
    intro i
    simpa only [W] using integral_bentkusWhitenedSummand_eq_zero S hX hX0 i
  have hWcov : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, W i ω)) x y = inner ℝ x y := by
    intro x y
    simpa only [W] using
      covarianceBilin_map_sum_bentkusWhitenedSummand_eq_inner
        S hS hX hcov x y
  have hBm : MeasurableSet B := by
    simpa only [B] using measurableSet_bentkusWhitenedSet S hS hA
  have hBconv : Convexity.IsConvexSet ℝ B := by
    simpa only [B] using isConvexSet_bentkusWhitenedSet S hS hAconv
  have hbound := hC hd μ W hW3 hWindep hW0 hWcov B hBm hBconv
  exact bentkus_convex_set_whitening_reduction C μ X S hS hX A (by
    simpa only [W, B] using hbound)

/-- An absolute identity-covariance constant yields Bentkus's full positive-definite covariance
theorem by whitening. -/
theorem exists_bentkus_convex_set_constant_of_identity_covariance_bound
    (hidentity : ∃ C : ℝ, 0 < C ∧ BentkusIdentityCovarianceBound.{u} C) :
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
  obtain ⟨C, hC, hidentity⟩ := hidentity
  refine ⟨C, hC, ?_⟩
  intro d n hd Ω _ μ _ X S hX h_indep hX0 hS hcov A hA hAconv
  exact bentkus_convex_set_bound_of_identity_covariance_bound
    C hidentity hd μ X S hX h_indep hX0 hS hcov A hA hAconv

end ProbabilityTheory
