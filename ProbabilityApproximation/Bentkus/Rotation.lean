/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.Bentkus.ProbabilitySpaceTransport
import Mathlib.Probability.Independence.Integration

/-!
# Bentkus rotation and low-order moment cancellation

This module isolates the algebra behind Bentkus (2004), equations (3.4)--(3.5).  If centered
independent vectors `X` and `Y` have matching second bilinear moments, the rotation
`cos α X + sin α Y` is orthogonal in every expected bilinear form to its angular derivative
`-sin α X + cos α Y`.  These are precisely the constant, linear, and quadratic cancellations
used before estimating the third-order Taylor remainder.
-/

open MeasureTheory

noncomputable section

namespace ProbabilityTheory

/-- Rotation from a summand toward its matched Gaussian companion. -/
def bentkusRotated {Ω E : Type*} [AddCommMonoid E] [Module ℝ E]
    (α : ℝ) (X Y : Ω → E) : Ω → E :=
  fun ω ↦ Real.cos α • X ω + Real.sin α • Y ω

/-- Angular derivative of `bentkusRotated`. -/
def bentkusRotatedDeriv {Ω E : Type*} [AddCommGroup E] [Module ℝ E]
    (α : ℝ) (X Y : Ω → E) : Ω → E :=
  fun ω ↦ -(Real.sin α) • X ω + Real.cos α • Y ω

/-- The rotation of two centered integrable vectors is centered. -/
lemma integral_bentkusRotated_eq_zero
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} {X Y : Ω → E}
    (hX : Integrable X μ) (hY : Integrable Y μ)
    (hX0 : ∫ ω, X ω ∂μ = 0) (hY0 : ∫ ω, Y ω ∂μ = 0) (α : ℝ) :
    ∫ ω, bentkusRotated α X Y ω ∂μ = 0 := by
  change ∫ ω, Real.cos α • X ω + Real.sin α • Y ω ∂μ = 0
  have hcos := Integrable.smul (Real.cos α) hX
  change Integrable (fun ω ↦ Real.cos α • X ω) μ at hcos
  have hsin := Integrable.smul (Real.sin α) hY
  change Integrable (fun ω ↦ Real.sin α • Y ω) μ at hsin
  calc
    ∫ ω, Real.cos α • X ω + Real.sin α • Y ω ∂μ =
        (∫ ω, Real.cos α • X ω ∂μ) +
          ∫ ω, Real.sin α • Y ω ∂μ := integral_add hcos hsin
    _ = Real.cos α • (∫ ω, X ω ∂μ) +
          Real.sin α • (∫ ω, Y ω ∂μ) := by
      rw [integral_smul, integral_smul]
    _ = 0 := by rw [hX0, hY0]; simp

/-- The angular derivative of the rotation of two centered integrable vectors is centered. -/
lemma integral_bentkusRotatedDeriv_eq_zero
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} {X Y : Ω → E}
    (hX : Integrable X μ) (hY : Integrable Y μ)
    (hX0 : ∫ ω, X ω ∂μ = 0) (hY0 : ∫ ω, Y ω ∂μ = 0) (α : ℝ) :
    ∫ ω, bentkusRotatedDeriv α X Y ω ∂μ = 0 := by
  change ∫ ω, (-(Real.sin α)) • X ω + Real.cos α • Y ω ∂μ = 0
  have hsin := Integrable.smul (-(Real.sin α)) hX
  change Integrable (fun ω ↦ (-(Real.sin α)) • X ω) μ at hsin
  have hcos := Integrable.smul (Real.cos α) hY
  change Integrable (fun ω ↦ Real.cos α • Y ω) μ at hcos
  calc
    ∫ ω, (-(Real.sin α)) • X ω + Real.cos α • Y ω ∂μ =
        (∫ ω, (-(Real.sin α)) • X ω ∂μ) +
          ∫ ω, Real.cos α • Y ω ∂μ := integral_add hsin hcos
    _ = (-(Real.sin α)) • (∫ ω, X ω ∂μ) +
          Real.cos α • (∫ ω, Y ω ∂μ) := by
      rw [integral_smul, integral_smul]
    _ = 0 := by rw [hX0, hY0]; simp

/-- Pointwise bilinear expansion underlying the quadratic cancellation in Bentkus (3.5). -/
lemma bentkusRotated_bilin_bentkusRotatedDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (α : ℝ) (x y : E) :
    B (Real.cos α • x + Real.sin α • y)
        (-(Real.sin α) • x + Real.cos α • y) =
      (-(Real.cos α * Real.sin α)) * B x x +
        (Real.cos α) ^ 2 * B x y -
        (Real.sin α) ^ 2 * B y x +
        (Real.sin α * Real.cos α) * B y y := by
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  ring

/-- Coordinate expansion of a continuous bilinear form on Euclidean space. -/
lemma bilin_self_eq_sum_basis {d : ℕ}
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (z : EuclideanSpace ℝ (Fin d)) :
    B z z = ∑ i, ∑ j, (z i * z j) *
      B (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ j) := by
  classical
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hz : (∑ i, z i • b i) = z := by
    simpa [b, EuclideanSpace.basisFun_repr] using b.sum_repr z
  calc
    B z z = B (∑ i, z i • b i) (∑ j, z j • b j) := by
      rw [hz]
    _ = ∑ i, ∑ j, (z i * z j) * B (b i) (b j) := by
      simp only [map_sum, map_smul, smul_eq_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [sum_apply]
      simp only [smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, ∑ j, (z i * z j) *
        B (EuclideanSpace.basisFun (Fin d) ℝ i)
          (EuclideanSpace.basisFun (Fin d) ℝ j) := rfl

/-- For a centered square-integrable Euclidean random vector, each uncentered coordinate
second moment is the corresponding entry of the covariance bilinear form of its law. -/
lemma integral_coordinate_mul_eq_covarianceBilin
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {Z : Ω → EuclideanSpace ℝ (Fin d)}
    (hZ : MemLp Z 2 μ) (hZ0 : ∫ ω, Z ω ∂μ = 0) (i j : Fin d) :
    ∫ ω, Z ω i * Z ω j ∂μ =
      covarianceBilin (μ.map Z)
        (EuclideanSpace.basisFun (Fin d) ℝ i)
        (EuclideanSpace.basisFun (Fin d) ℝ j) := by
  have hLaw : MemLp id 2 (μ.map Z) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hZ.aemeasurable).2 (by
      simpa only [Function.comp_def, id_eq] using hZ)
  have hmean : ∫ z, z ∂(μ.map Z) = 0 := by
    calc
      ∫ z, z ∂(μ.map Z) = ∫ ω, Z ω ∂μ := by
        simpa only [Function.comp_def, id_eq] using
          (integral_map hZ.aemeasurable aestronglyMeasurable_id)
      _ = 0 := hZ0
  rw [covarianceBilin_apply hLaw]
  simp only [id_eq, hmean, sub_zero]
  rw [integral_map hZ.aemeasurable (by fun_prop)]
  simp only [EuclideanSpace.basisFun_inner]

/-- A continuous bilinear self-product of a square-integrable finite-dimensional random vector
is integrable. -/
lemma integrable_bilin_self_of_memLp_two
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {d : ℕ} {Z : Ω → EuclideanSpace ℝ (Fin d)}
    (hZ : MemLp Z 2 μ)
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    Integrable (fun ω ↦ B (Z ω) (Z ω)) μ := by
  classical
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hprod (i j : Fin d) : Integrable (fun ω ↦ Z ω i * Z ω j) μ := by
    change Integrable ((fun ω ↦ Z ω i) * (fun ω ↦ Z ω j)) μ
    exact (hZ.eval_piLp i).integrable_mul (hZ.eval_piLp j)
  have hsum : Integrable
      (fun ω ↦ ∑ i, ∑ j, (Z ω i * Z ω j) * B (b i) (b j)) μ :=
    integrable_finsetSum _ fun i _ ↦
      integrable_finsetSum _ fun j _ ↦ (hprod i j).mul_const _
  refine hsum.congr ?_
  filter_upwards [] with ω
  exact (bilin_self_eq_sum_basis B (Z ω)).symm

/-- The expected value of a bilinear self-product is the contraction of the covariance bilinear
form with the matrix coefficients of the chosen bilinear form. -/
lemma integral_bilin_self_eq_sum_covarianceBilin
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {Z : Ω → EuclideanSpace ℝ (Fin d)}
    (hZ : MemLp Z 2 μ) (hZ0 : ∫ ω, Z ω ∂μ = 0)
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    ∫ ω, B (Z ω) (Z ω) ∂μ =
      ∑ i, ∑ j, covarianceBilin (μ.map Z)
        (EuclideanSpace.basisFun (Fin d) ℝ i)
        (EuclideanSpace.basisFun (Fin d) ℝ j) *
          B (EuclideanSpace.basisFun (Fin d) ℝ i)
            (EuclideanSpace.basisFun (Fin d) ℝ j) := by
  classical
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hprod (i j : Fin d) : Integrable (fun ω ↦ Z ω i * Z ω j) μ := by
    change Integrable ((fun ω ↦ Z ω i) * (fun ω ↦ Z ω j)) μ
    exact (hZ.eval_piLp i).integrable_mul (hZ.eval_piLp j)
  calc
    ∫ ω, B (Z ω) (Z ω) ∂μ =
        ∫ ω, ∑ i, ∑ j, (Z ω i * Z ω j) * B (b i) (b j) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact bilin_self_eq_sum_basis B (Z ω)
    _ = ∑ i, ∫ ω, ∑ j, (Z ω i * Z ω j) * B (b i) (b j) ∂μ := by
      rw [integral_finsetSum]
      intro i _
      exact integrable_finsetSum _ fun j _ ↦ (hprod i j).mul_const _
    _ = ∑ i, ∑ j, ∫ ω, (Z ω i * Z ω j) * B (b i) (b j) ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum]
      intro j _
      exact (hprod i j).mul_const _
    _ = ∑ i, ∑ j, covarianceBilin (μ.map Z) (b i) (b j) * B (b i) (b j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_mul_const, integral_coordinate_mul_eq_covarianceBilin hZ hZ0]
    _ = _ := rfl

/-- Centered square-integrable Euclidean vectors with identical covariance bilinear forms have
identical expected values under every continuous bilinear self-product. -/
lemma integral_bilin_self_eq_of_covarianceBilin_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {X Y : Ω → EuclideanSpace ℝ (Fin d)}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hX0 : ∫ ω, X ω ∂μ = 0) (hY0 : ∫ ω, Y ω ∂μ = 0)
    (hcov : ∀ x y, covarianceBilin (μ.map X) x y = covarianceBilin (μ.map Y) x y)
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    ∫ ω, B (X ω) (X ω) ∂μ = ∫ ω, B (Y ω) (Y ω) ∂μ := by
  rw [integral_bilin_self_eq_sum_covarianceBilin hX hX0 B,
    integral_bilin_self_eq_sum_covarianceBilin hY hY0 B]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hcov]

/-- Bentkus (2004), equation (3.5), in its expected-bilinear form.  Independence kills the two
cross terms, while equality of the two self moments kills the remaining pair. -/
theorem integral_bilin_bentkusRotated_bentkusRotatedDeriv_eq_zero
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure Ω} {X Y : Ω → E}
    (hXY : X ⟂ᵢ[μ] Y) (hX : Integrable X μ) (hY : Integrable Y μ)
    (hX0 : ∫ ω, X ω ∂μ = 0) (hY0 : ∫ ω, Y ω ∂μ = 0)
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hXX : Integrable (fun ω ↦ B (X ω) (X ω)) μ)
    (hYY : Integrable (fun ω ↦ B (Y ω) (Y ω)) μ)
    (hmatch : ∫ ω, B (X ω) (X ω) ∂μ = ∫ ω, B (Y ω) (Y ω) ∂μ)
    (α : ℝ) :
    ∫ ω, B (bentkusRotated α X Y ω) (bentkusRotatedDeriv α X Y ω) ∂μ = 0 := by
  have hXYint : Integrable (fun ω ↦ B (X ω) (Y ω)) μ :=
    hXY.integrable_bilin hX hY B
  have hYXint : Integrable (fun ω ↦ B (Y ω) (X ω)) μ :=
    hXY.symm.integrable_bilin hY hX B
  have hcrossXY : ∫ ω, B (X ω) (Y ω) ∂μ = 0 := by
    rw [hXY.integral_bilin hX hY B, hX0, hY0]
    simp
  have hcrossYX : ∫ ω, B (Y ω) (X ω) ∂μ = 0 := by
    rw [hXY.symm.integral_bilin hY hX B, hY0, hX0]
    simp
  have h1 : Integrable
      (fun ω ↦ (-(Real.cos α * Real.sin α)) * B (X ω) (X ω)) μ :=
    hXX.const_mul _
  have h2 : Integrable
      (fun ω ↦ (Real.cos α) ^ 2 * B (X ω) (Y ω)) μ :=
    hXYint.const_mul _
  have h3 : Integrable
      (fun ω ↦ -((Real.sin α) ^ 2 * B (Y ω) (X ω))) μ :=
    (hYXint.const_mul _).neg
  have h4 : Integrable
      (fun ω ↦ (Real.sin α * Real.cos α) * B (Y ω) (Y ω)) μ :=
    hYY.const_mul _
  calc
    ∫ ω, B (bentkusRotated α X Y ω) (bentkusRotatedDeriv α X Y ω) ∂μ =
        ∫ ω,
          (-(Real.cos α * Real.sin α)) * B (X ω) (X ω) +
            (Real.cos α) ^ 2 * B (X ω) (Y ω) -
            (Real.sin α) ^ 2 * B (Y ω) (X ω) +
            (Real.sin α * Real.cos α) * B (Y ω) (Y ω) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact bentkusRotated_bilin_bentkusRotatedDeriv B α (X ω) (Y ω)
    _ = (-(Real.cos α * Real.sin α)) * (∫ ω, B (X ω) (X ω) ∂μ) +
          (Real.cos α) ^ 2 * (∫ ω, B (X ω) (Y ω) ∂μ) -
          (Real.sin α) ^ 2 * (∫ ω, B (Y ω) (X ω) ∂μ) +
          (Real.sin α * Real.cos α) * (∫ ω, B (Y ω) (Y ω) ∂μ) := by
      have hfun :
          (fun ω ↦
            (-(Real.cos α * Real.sin α)) * B (X ω) (X ω) +
              (Real.cos α) ^ 2 * B (X ω) (Y ω) -
              (Real.sin α) ^ 2 * B (Y ω) (X ω) +
              (Real.sin α * Real.cos α) * B (Y ω) (Y ω)) =
            fun ω ↦
              (((-(Real.cos α * Real.sin α)) * B (X ω) (X ω) +
                (Real.cos α) ^ 2 * B (X ω) (Y ω)) +
                -((Real.sin α) ^ 2 * B (Y ω) (X ω))) +
                (Real.sin α * Real.cos α) * B (Y ω) (Y ω) := by
        funext ω
        ring
      rw [hfun]
      calc
        ∫ ω,
            (((-(Real.cos α * Real.sin α)) * B (X ω) (X ω) +
              (Real.cos α) ^ 2 * B (X ω) (Y ω)) +
              -((Real.sin α) ^ 2 * B (Y ω) (X ω))) +
              (Real.sin α * Real.cos α) * B (Y ω) (Y ω) ∂μ =
            (∫ ω,
              ((-(Real.cos α * Real.sin α)) * B (X ω) (X ω) +
                (Real.cos α) ^ 2 * B (X ω) (Y ω)) +
                -((Real.sin α) ^ 2 * B (Y ω) (X ω)) ∂μ) +
              ∫ ω, (Real.sin α * Real.cos α) * B (Y ω) (Y ω) ∂μ :=
          integral_add (h1.add h2 |>.add h3) h4
        _ = ((∫ ω,
                (-(Real.cos α * Real.sin α)) * B (X ω) (X ω) +
                  (Real.cos α) ^ 2 * B (X ω) (Y ω) ∂μ) +
              ∫ ω, -((Real.sin α) ^ 2 * B (Y ω) (X ω)) ∂μ) +
              ∫ ω, (Real.sin α * Real.cos α) * B (Y ω) (Y ω) ∂μ := by
          congr 1
          exact integral_add (h1.add h2) h3
        _ = (((∫ ω, (-(Real.cos α * Real.sin α)) * B (X ω) (X ω) ∂μ) +
                ∫ ω, (Real.cos α) ^ 2 * B (X ω) (Y ω) ∂μ) +
              ∫ ω, -((Real.sin α) ^ 2 * B (Y ω) (X ω)) ∂μ) +
              ∫ ω, (Real.sin α * Real.cos α) * B (Y ω) (Y ω) ∂μ := by
          congr 2
          exact integral_add h1 h2
        _ = _ := by
          rw [integral_const_mul, integral_const_mul, integral_neg,
            integral_const_mul, integral_const_mul]
          ring
    _ = 0 := by rw [hcrossXY, hcrossYX, hmatch]; ring

/-- Bentkus (2004), equation (3.5), realized on the canonical replacement space for one original
summand and its covariance-matched Gaussian companion.  The hypotheses use measurable
representatives; the final setwise theorem transports arbitrary `MemLp` representatives to this
canonical form. -/
theorem integral_bilin_replacementRotated_replacementRotatedDeriv_eq_zero
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i)) (hX3 : ∀ i, MemLp (X i) 3 μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0) (i : Fin n)
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (α : ℝ) :
    ∫ ω,
        B (bentkusRotated α (replacementOriginal (d := d) i)
            (replacementGaussian (d := d) i) ω)
          (bentkusRotatedDeriv α (replacementOriginal (d := d) i)
            (replacementGaussian (d := d) i) ω)
      ∂(bentkusReplacementMeasure μ X) = 0 := by
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure (bentkusReplacementMeasure μ X) := by
    unfold bentkusReplacementMeasure
    infer_instance
  have hX2 : MemLp (replacementOriginal (d := d) i) 2
      (bentkusReplacementMeasure μ X) :=
    memLp_replacementOriginal hXm (fun j ↦ (hX3 j).mono_exponent (by norm_num)) i
  have hY2 : MemLp (replacementGaussian (d := d) i) 2
      (bentkusReplacementMeasure μ X) :=
    (memLp_three_replacementGaussian hXm i).mono_exponent (by norm_num)
  have hXi : Integrable (replacementOriginal (d := d) i)
      (bentkusReplacementMeasure μ X) := hX2.integrable (by norm_num)
  have hYi : Integrable (replacementGaussian (d := d) i)
      (bentkusReplacementMeasure μ X) := hY2.integrable (by norm_num)
  have hXmean : ∫ ω, replacementOriginal (d := d) i ω
      ∂(bentkusReplacementMeasure μ X) = 0 := by
    rw [integral_replacementOriginal_eq hXm i, hX0 i]
  have hYmean : ∫ ω, replacementGaussian (d := d) i ω
      ∂(bentkusReplacementMeasure μ X) = 0 :=
    integral_replacementGaussian_eq_zero hXm i
  have hcov : ∀ x y,
      covarianceBilin
          ((bentkusReplacementMeasure μ X).map (replacementOriginal (d := d) i)) x y =
        covarianceBilin
          ((bentkusReplacementMeasure μ X).map (replacementGaussian (d := d) i)) x y :=
    fun x y ↦
      (covarianceBilin_replacementGaussian_eq_replacementOriginal hXm i x y).symm
  have hmatch :
      ∫ ω, B (replacementOriginal (d := d) i ω)
          (replacementOriginal (d := d) i ω) ∂(bentkusReplacementMeasure μ X) =
        ∫ ω, B (replacementGaussian (d := d) i ω)
          (replacementGaussian (d := d) i ω) ∂(bentkusReplacementMeasure μ X) :=
    integral_bilin_self_eq_of_covarianceBilin_eq hX2 hY2 hXmean hYmean hcov B
  exact integral_bilin_bentkusRotated_bentkusRotatedDeriv_eq_zero
    (indepFun_replacementOriginal_replacementGaussian hXm i i)
    hXi hYi hXmean hYmean B
    (integrable_bilin_self_of_memLp_two hX2 B)
    (integrable_bilin_self_of_memLp_two hY2 B) hmatch α

/-- Pointwise angular derivative of a single Bentkus rotation. -/
lemma hasDerivAt_bentkusRotated_apply
    {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X Y : Ω → E) (ω : Ω) (α : ℝ) :
    HasDerivAt (fun t ↦ bentkusRotated t X Y ω)
      (bentkusRotatedDeriv α X Y ω) α := by
  change HasDerivAt
    ((fun t ↦ Real.cos t • X ω) + fun t ↦ Real.sin t • Y ω)
    (-(Real.sin α) • X ω + Real.cos α • Y ω) α
  exact (Real.hasDerivAt_cos α).smul_const (X ω) |>.add
    ((Real.hasDerivAt_sin α).smul_const (Y ω))

/-- Simultaneous rotation of a finite summand family toward its companion family. -/
def bentkusRotatedSum {n : ℕ} {Ω E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ) (X Y : Fin n → Ω → E) : Ω → E :=
  fun ω ↦ ∑ i, bentkusRotated α (X i) (Y i) ω

/-- Angular derivative of the simultaneous finite rotation. -/
def bentkusRotatedSumDeriv {n : ℕ} {Ω E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ) (X Y : Fin n → Ω → E) : Ω → E :=
  fun ω ↦ ∑ i, bentkusRotatedDeriv α (X i) (Y i) ω

/-- The displayed derivative really is the angular derivative of the simultaneous rotation. -/
lemma hasDerivAt_bentkusRotatedSum_apply
    {n : ℕ} {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X Y : Fin n → Ω → E) (ω : Ω) (α : ℝ) :
    HasDerivAt (fun t ↦ bentkusRotatedSum t X Y ω)
      (bentkusRotatedSumDeriv α X Y ω) α := by
  unfold bentkusRotatedSum bentkusRotatedSumDeriv
  convert HasDerivAt.sum (u := Finset.univ) (fun i _ ↦
    hasDerivAt_bentkusRotated_apply (X i) (Y i) ω α) using 1
  funext t
  simp only [Finset.sum_apply]

/-- At angle zero, the rotation is the original sum. -/
@[simp]
lemma bentkusRotatedSum_zero
    {n : ℕ} {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X Y : Fin n → Ω → E) (ω : Ω) :
    bentkusRotatedSum 0 X Y ω = ∑ i, X i ω := by
  simp [bentkusRotatedSum, bentkusRotated]

/-- At angle `π/2`, the rotation is the companion sum. -/
@[simp]
lemma bentkusRotatedSum_pi_div_two
    {n : ℕ} {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X Y : Fin n → Ω → E) (ω : Ω) :
    bentkusRotatedSum (Real.pi / 2) X Y ω = ∑ i, Y i ω := by
  simp [bentkusRotatedSum, bentkusRotated]

/-- Bentkus's rotation interpolation before expectation: integrating the angular derivative of a
`C¹` test along the simultaneous rotation gives the companion-test value minus the original-test
value.  This is the deterministic calculus identity underlying Bentkus (2004), equation (3.4). -/
theorem intervalIntegral_fderiv_bentkusRotatedSum_eq_sub
    {n : ℕ} {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ)
    (X Y : Fin n → Ω → E) (ω : Ω) :
    (∫ α in (0 : ℝ)..Real.pi / 2,
        (fderiv ℝ φ (bentkusRotatedSum α X Y ω))
          (bentkusRotatedSumDeriv α X Y ω)) =
      φ (∑ i, Y i ω) - φ (∑ i, X i ω) := by
  let F : ℝ → ℝ := fun α ↦ φ (bentkusRotatedSum α X Y ω)
  let F' : ℝ → ℝ := fun α ↦
    (fderiv ℝ φ (bentkusRotatedSum α X Y ω))
      (bentkusRotatedSumDeriv α X Y ω)
  have hrot : ∀ α, HasDerivAt F (F' α) α := by
    intro α
    have hφ' : HasFDerivAt φ (fderiv ℝ φ (bentkusRotatedSum α X Y ω))
        (bentkusRotatedSum α X Y ω) :=
      (hφ.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    simpa only [F, F', Function.comp_def] using
      hφ'.comp_hasDerivAt α (hasDerivAt_bentkusRotatedSum_apply X Y ω α)
  have hrotCont : Continuous (fun α ↦ bentkusRotatedSum α X Y ω) := by
    simp only [bentkusRotatedSum, bentkusRotated]
    fun_prop
  have hrotDerivCont : Continuous (fun α ↦ bentkusRotatedSumDeriv α X Y ω) := by
    simp only [bentkusRotatedSumDeriv, bentkusRotatedDeriv]
    fun_prop
  have hF'cont : Continuous F' := by
    exact (hφ.continuous_fderiv_apply (by norm_num)).comp
      (hrotCont.prodMk hrotDerivCont)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := Real.pi / 2)
    (fun α _ ↦ hrot α) (hF'cont.intervalIntegrable _ _)
  simpa only [F, F', bentkusRotatedSum_zero, bentkusRotatedSum_pi_div_two] using hFTC

/-- Pointwise form of Bentkus (2004), equation (3.4), with Lebesgue integration in the angle.
The derivative of the simultaneous rotation is split into its finitely many summand
contributions. -/
theorem sum_intervalIntegral_fderiv_bentkusRotated_eq_sub
    {n : ℕ} {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ)
    (X Y : Fin n → Ω → E) (ω : Ω) :
    ∑ i, (∫ α in (0 : ℝ)..Real.pi / 2,
        (fderiv ℝ φ (bentkusRotatedSum α X Y ω))
          (bentkusRotatedDeriv α (X i) (Y i) ω)) =
      φ (∑ i, Y i ω) - φ (∑ i, X i ω) := by
  have hsplit (α : ℝ) :
      (fderiv ℝ φ (bentkusRotatedSum α X Y ω))
          (bentkusRotatedSumDeriv α X Y ω) =
        ∑ i, (fderiv ℝ φ (bentkusRotatedSum α X Y ω))
          (bentkusRotatedDeriv α (X i) (Y i) ω) := by
    simp only [bentkusRotatedSumDeriv, map_sum]
  have hcont (i : Fin n) : Continuous (fun α ↦
      (fderiv ℝ φ (bentkusRotatedSum α X Y ω))
        (bentkusRotatedDeriv α (X i) (Y i) ω)) := by
    have hsum : Continuous (fun α ↦ bentkusRotatedSum α X Y ω) := by
      simp only [bentkusRotatedSum, bentkusRotated]
      fun_prop
    have hderiv : Continuous
        (fun α ↦ bentkusRotatedDeriv α (X i) (Y i) ω) := by
      simp only [bentkusRotatedDeriv]
      fun_prop
    exact (hφ.continuous_fderiv_apply (by norm_num)).comp
      (hsum.prodMk hderiv)
  rw [← intervalIntegral.integral_finsetSum (s := Finset.univ)
    (fun i _ ↦ (hcont i).intervalIntegrable _ _)]
  calc
    (∫ α in (0 : ℝ)..Real.pi / 2,
        ∑ i, (fderiv ℝ φ (bentkusRotatedSum α X Y ω))
          (bentkusRotatedDeriv α (X i) (Y i) ω)) =
      ∫ α in (0 : ℝ)..Real.pi / 2,
        (fderiv ℝ φ (bentkusRotatedSum α X Y ω))
          (bentkusRotatedSumDeriv α X Y ω) := by
      apply intervalIntegral.integral_congr
      intro α _
      exact (hsplit α).symm
    _ = _ := intervalIntegral_fderiv_bentkusRotatedSum_eq_sub φ hφ X Y ω

/-- Expected form of the rotation identity.  This is equation (3.4) before normalizing Lebesgue
measure on `[0, π/2]`; the paper's factor `π/2` is exactly the reciprocal density of the uniform
angle. -/
theorem integral_sum_intervalIntegral_fderiv_bentkusRotated_eq
    {n : ℕ} {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ)
    (X Y : Fin n → Ω → E) :
    ∫ ω, ∑ i, (∫ α in (0 : ℝ)..Real.pi / 2,
        (fderiv ℝ φ (bentkusRotatedSum α X Y ω))
          (bentkusRotatedDeriv α (X i) (Y i) ω)) ∂μ =
      ∫ ω, φ (∑ i, Y i ω) - φ (∑ i, X i ω) ∂μ := by
  apply integral_congr_ae
  filter_upwards [] with ω
  exact sum_intervalIntegral_fderiv_bentkusRotated_eq_sub φ hφ X Y ω

end ProbabilityTheory
