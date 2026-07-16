/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.Bentkus.GaussianCompanions
import Mathlib.Probability.Moments.Variance

/-!
# Covariance algebra for the Bentkus leave-one-out argument

This module proves the covariance identities used on original pages 403--404 of Bentkus (2004),
especially the notation surrounding equation (3.2).  For independent square-integrable Euclidean
summands, covariance of a finite subsum is the sum of the individual covariance bilinear forms.
Consequently the covariance of the sum with the `k`th summand removed is total covariance minus
the `k`th covariance.  No individual covariance is assumed invertible.
-/

open MeasureTheory InnerProductSpace Matrix
open scoped RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

/-- Covariance of the law of a Euclidean random vector, evaluated at two directions, is covariance
of the corresponding scalar projections on the original probability space. -/
lemma covarianceBilin_map_apply_eq_cov_projection
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {Z : Ω → EuclideanSpace ℝ (Fin d)} (hZ : MemLp Z 2 μ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    covarianceBilin (μ.map Z) x y =
      cov[fun ω ↦ inner ℝ x (Z ω), fun ω ↦ inner ℝ y (Z ω); μ] := by
  have hLaw : MemLp id 2 (μ.map Z) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hZ.aemeasurable).2 (by
      simpa only [Function.comp_def, id_eq] using hZ)
  rw [covarianceBilin_apply_eq_cov hLaw, covariance_map]
  · rfl
  · fun_prop
  · fun_prop
  · exact hZ.aemeasurable

/-- Covariance bilinear form of a subsum of an independent finite family. -/
theorem covarianceBilin_map_finsetSum_eq_sum
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n d : ℕ} {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, MemLp (X i) 2 μ) (h_indep : iIndepFun X μ)
    (s : Finset (Fin n)) (x y : EuclideanSpace ℝ (Fin d)) :
    covarianceBilin (μ.map (fun ω ↦ ∑ i ∈ s, X i ω)) x y =
      ∑ i ∈ s, covarianceBilin (μ.map (X i)) x y := by
  let P : Fin n → Ω → ℝ := fun i ω ↦ inner ℝ x (X i ω)
  let Q : Fin n → Ω → ℝ := fun i ω ↦ inner ℝ y (X i ω)
  have hP : ∀ i, MemLp (P i) 2 μ := fun i ↦ (hX i).const_inner x
  have hQ : ∀ i, MemLp (Q i) 2 μ := fun i ↦ (hX i).const_inner y
  have hSum : MemLp (fun ω ↦ ∑ i ∈ s, X i ω) 2 μ :=
    memLp_finsetSum s fun i _ ↦ hX i
  rw [covarianceBilin_map_apply_eq_cov_projection hSum]
  have hcovsum :
      cov[fun ω ↦ ∑ i ∈ s, P i ω, fun ω ↦ ∑ j ∈ s, Q j ω; μ] =
        ∑ i ∈ s, ∑ j ∈ s, cov[P i, Q j; μ] :=
    covariance_fun_sum_fun_sum'
      (fun i _ ↦ hP i) (fun j _ ↦ hQ j)
  have hleft : (fun ω ↦ inner ℝ x (∑ i ∈ s, X i ω)) =
      fun ω ↦ ∑ i ∈ s, P i ω := by
    funext ω
    simp only [P, inner_sum]
  have hright : (fun ω ↦ inner ℝ y (∑ i ∈ s, X i ω)) =
      fun ω ↦ ∑ i ∈ s, Q i ω := by
    funext ω
    simp only [Q, inner_sum]
  rw [hleft, hright, hcovsum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · exact (covarianceBilin_map_apply_eq_cov_projection (hX i) x y).symm
  · intro j _ hji
    have hij : i ≠ j := Ne.symm hji
    have hPQ : P i ⟂ᵢ[μ] Q j :=
      (h_indep.indepFun hij).comp (by fun_prop) (by fun_prop)
    exact hPQ.covariance_eq_zero (hP i) (hQ j)
  · exact fun hnot ↦ (hnot hi).elim

/-- Covariance bilinear form of the full independent sum. -/
theorem covarianceBilin_map_sum_eq_sum
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n d : ℕ} {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, MemLp (X i) 2 μ) (h_indep : iIndepFun X μ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y =
      ∑ i, covarianceBilin (μ.map (X i)) x y := by
  simpa using
    covarianceBilin_map_finsetSum_eq_sum hX h_indep Finset.univ x y

/-- Sum of all summands except the `k`th.  This is `Uₖ = S - Xₖ` in Bentkus (2004), (3.2). -/
def bentkusLeaveOneOut {n d : ℕ} {Ω : Type*}
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (k : Fin n) :
    Ω → EuclideanSpace ℝ (Fin d) :=
  fun ω ↦ ∑ i ∈ Finset.univ.erase k, X i ω

/-- Covariance of the full sum decomposes into leave-one-out covariance plus the omitted
summand's covariance. -/
theorem covarianceBilin_map_sum_eq_leaveOneOut_add
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n d : ℕ} {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, MemLp (X i) 2 μ) (h_indep : iIndepFun X μ) (k : Fin n)
    (x y : EuclideanSpace ℝ (Fin d)) :
    covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y =
      covarianceBilin (μ.map (bentkusLeaveOneOut X k)) x y +
        covarianceBilin (μ.map (X k)) x y := by
  rw [covarianceBilin_map_sum_eq_sum hX h_indep,
    show covarianceBilin (μ.map (bentkusLeaveOneOut X k)) x y =
        ∑ i ∈ Finset.univ.erase k, covarianceBilin (μ.map (X i)) x y by
      exact covarianceBilin_map_finsetSum_eq_sum hX h_indep
        (Finset.univ.erase k) x y]
  exact (Finset.sum_erase_add Finset.univ
    (fun i ↦ covarianceBilin (μ.map (X i)) x y) (Finset.mem_univ k)).symm

/-- Covariance matrix of the leave-one-out sum. -/
def bentkusLeaveOneOutCovarianceMatrix
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (k : Fin n) :
    Matrix (Fin d) (Fin d) ℝ :=
  covarianceMatrix (μ.map (bentkusLeaveOneOut X k))

/-- Every leave-one-out covariance matrix is positive semidefinite, with singularity allowed. -/
lemma bentkusLeaveOneOutCovarianceMatrix_posSemidef
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (k : Fin n) :
    (bentkusLeaveOneOutCovarianceMatrix μ X k).PosSemidef :=
  covarianceMatrix_posSemidef _

/-- The leave-one-out covariance matrix recovers the covariance bilinear form. -/
lemma dotProduct_bentkusLeaveOneOutCovarianceMatrix_mulVec
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (k : Fin n)
    (x y : EuclideanSpace ℝ (Fin d)) :
    x ⬝ᵥ bentkusLeaveOneOutCovarianceMatrix μ X k *ᵥ y =
      covarianceBilin (μ.map (bentkusLeaveOneOut X k)) x y :=
  dotProduct_covarianceMatrix_mulVec _ x y

/-- Under identity total covariance, leave-one-out covariance is identity covariance minus the
omitted summand covariance.  This is the matrix `Pₖ² = I - cov Xₖ` used after (3.2). -/
theorem covarianceBilin_leaveOneOut_eq_inner_sub
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n d : ℕ} {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, MemLp (X i) 2 μ) (h_indep : iIndepFun X μ)
    (hidentity : ∀ x y, covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y =
      inner ℝ x y)
    (k : Fin n) (x y : EuclideanSpace ℝ (Fin d)) :
    covarianceBilin (μ.map (bentkusLeaveOneOut X k)) x y =
      inner ℝ x y - covarianceBilin (μ.map (X k)) x y := by
  have hsplit := covarianceBilin_map_sum_eq_leaveOneOut_add hX h_indep k x y
  rw [hidentity x y] at hsplit
  linarith

/-- Matrix form of `Pₖ² = I - cov Xₖ` from Bentkus (2004), page 403. -/
theorem bentkusLeaveOneOutCovarianceMatrix_eq_one_sub
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n d : ℕ} {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, MemLp (X i) 2 μ) (h_indep : iIndepFun X μ)
    (hidentity : ∀ x y, covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y =
      inner ℝ x y)
    (k : Fin n) :
    bentkusLeaveOneOutCovarianceMatrix μ X k =
      (1 : Matrix (Fin d) (Fin d) ℝ) - summandCovarianceMatrix μ X k := by
  ext i j
  have h := covarianceBilin_leaveOneOut_eq_inner_sub hX h_indep hidentity k
    (EuclideanSpace.basisFun (Fin d) ℝ i)
    (EuclideanSpace.basisFun (Fin d) ℝ j)
  rw [← dotProduct_bentkusLeaveOneOutCovarianceMatrix_mulVec,
    ← dotProduct_covarianceMatrix_mulVec (μ.map (X k))] at h
  simpa [summandCovarianceMatrix, dotProduct, mulVec, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left, PiLp.single_apply, Matrix.one_apply] using h

end ProbabilityTheory
