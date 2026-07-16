/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.Bentkus.GaussianCompanionMoments
import ProbabilityApproximation.Bentkus.CovarianceAlgebra

/-!
# Trivial branches in Bentkus's induction

This module closes the two moment-theoretic branches at the beginning of Bentkus (2004),
Section 3, printed page 403.  Identity total covariance forces the sum of second norm moments to
equal the dimension.  Hölder's inequality then gives

`d³ ≤ n (∑ i, E ‖X i‖³)²`.

Consequently the desired probability bound is automatic when `n ≤ d³ M²`.  A separate lemma
turns a large individual second norm moment into the same kind of trivial bound.  The spectral
step which detects that large moment from the leave-one-out inverse remains in the induction
module, while the reusable probability and moment algebra lives here.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace ProbabilityTheory

/-- Finite Hölder inequality in the polynomial form used on Bentkus (2004), printed page 403. -/
lemma sum_sq_cube_le_card_mul_sum_cube_sq {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i ^ 2) ^ 3 ≤ (n : ℝ) * (∑ i, a i ^ 3) ^ 2 := by
  have hholder := Real.inner_le_Lp_mul_Lq_of_nonneg
    (s := Finset.univ) (f := fun i : Fin n ↦ a i ^ 2) (g := fun _ ↦ (1 : ℝ))
    (p := (3 : ℝ) / 2) (q := (3 : ℝ))
    (by exact ⟨by norm_num, by norm_num, by norm_num⟩)
    (fun i _ ↦ sq_nonneg (a i)) (fun _ _ ↦ by norm_num)
  simp only [mul_one, Real.one_rpow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hholder
  have hpow (i : Fin n) : (a i ^ 2) ^ ((3 : ℝ) / 2) = a i ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (ha i)]
    norm_num
  simp_rw [hpow] at hholder
  norm_num at hholder
  have hsum2 : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hsum3 : 0 ≤ ∑ i, a i ^ 3 :=
    Finset.sum_nonneg fun i _ ↦ pow_nonneg (ha i) _
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hcubed := pow_le_pow_left₀ hsum2 hholder 3
  rw [mul_pow] at hcubed
  rw [← Real.rpow_mul_natCast hsum3, ← Real.rpow_mul_natCast hn] at hcubed
  norm_num at hcubed
  simpa [mul_comm] using hcubed

/-- On a probability space, the second norm moment is bounded by the square of the `L³` norm. -/
lemma integral_norm_sq_le_lpNorm_three_sq
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → E}
    (hX3 : MemLp X 3 μ) :
    (∫ ω, ‖X ω‖ ^ 2 ∂μ) ≤ lpNorm X 3 μ ^ 2 := by
  have hX2 : MemLp X 2 μ := hX3.mono_exponent (by norm_num)
  rw [← lpNorm_two_sq_eq_integral_norm_sq hX2]
  exact pow_le_pow_left₀ lpNorm_nonneg
    (lpNorm_mono_exponent_of_isProbabilityMeasure hX3 (by norm_num)) 2

/-- For centered independent summands with identity total covariance, the sum of the individual
second norm moments is exactly the ambient dimension. -/
lemma sum_integral_norm_sq_eq_dimension_of_identityCovariance
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y) :
    (∑ i, ∫ ω, ‖X i ω‖ ^ 2 ∂μ) = d := by
  have hX2 : ∀ i, MemLp (X i) 2 μ :=
    fun i ↦ (hX3 i).mono_exponent (by norm_num)
  calc
    (∑ i, ∫ ω, ‖X i ω‖ ^ 2 ∂μ) =
        ∑ i, ∑ j : Fin d, covarianceMatrix (μ.map (X i)) j j := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_norm_sq_eq_trace_covarianceMatrix (hX2 i) (hX0 i)
    _ = ∑ j : Fin d, ∑ i, covarianceBilin (μ.map (X i))
          (EuclideanSpace.basisFun (Fin d) ℝ j)
          (EuclideanSpace.basisFun (Fin d) ℝ j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      calc
        covarianceMatrix (μ.map (X i)) j j =
            dotProduct (EuclideanSpace.basisFun (Fin d) ℝ j)
              (Matrix.mulVec (covarianceMatrix (μ.map (X i)))
                (EuclideanSpace.basisFun (Fin d) ℝ j)) := by simp
        _ = covarianceBilin (μ.map (X i))
              (EuclideanSpace.basisFun (Fin d) ℝ j)
              (EuclideanSpace.basisFun (Fin d) ℝ j) :=
          dotProduct_covarianceMatrix_mulVec _ _ _
    _ = ∑ j : Fin d, covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω))
          (EuclideanSpace.basisFun (Fin d) ℝ j)
          (EuclideanSpace.basisFun (Fin d) ℝ j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [covarianceBilin_map_sum_eq_sum hX2 h_indep]
    _ = ∑ _j : Fin d, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hidentity]
      simp
    _ = d := by simp

/-- The exact Hölder consequence used for Bentkus's small-cardinality branch. -/
lemma dimension_cube_le_card_mul_thirdMomentSum_sq
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y) :
    (d : ℝ) ^ 3 ≤ (n : ℝ) * (∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ) ^ 2 := by
  let a : Fin n → ℝ := fun i ↦ lpNorm (X i) 3 μ
  have ha (i : Fin n) : 0 ≤ a i := lpNorm_nonneg
  have hsecond : (d : ℝ) ≤ ∑ i, a i ^ 2 := by
    rw [← sum_integral_norm_sq_eq_dimension_of_identityCovariance
      hX3 h_indep hX0 hidentity]
    exact Finset.sum_le_sum fun i _ ↦ integral_norm_sq_le_lpNorm_three_sq (hX3 i)
  have hcube : (d : ℝ) ^ 3 ≤ (∑ i, a i ^ 2) ^ 3 :=
    pow_le_pow_left₀ (Nat.cast_nonneg d) hsecond 3
  calc
    (d : ℝ) ^ 3 ≤ (∑ i, a i ^ 2) ^ 3 := hcube
    _ ≤ (n : ℝ) * (∑ i, a i ^ 3) ^ 2 :=
      sum_sq_cube_le_card_mul_sum_cube_sq a ha
    _ = (n : ℝ) * (∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ) ^ 2 := by
      congr 2
      apply Finset.sum_congr rfl
      intro i _
      exact lpNorm_three_cube_eq_integral_norm_pow_three (hX3 i)

/-- If `n ≤ d³ M²`, identity covariance forces `M ∑ E ‖Xᵢ‖³ ≥ 1`. -/
lemma small_cardinality_thirdMomentSum_lower
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hd : 0 < d) {M : ℝ} (hM : 0 ≤ M)
    (hsmall : (n : ℝ) ≤ (d : ℝ) ^ 3 * M ^ 2)
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y) :
    1 ≤ M * (∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ) := by
  let β : ℝ := ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
  have hβ : 0 ≤ β := Finset.sum_nonneg fun i _ ↦
    integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg _) _
  have hdim := dimension_cube_le_card_mul_thirdMomentSum_sq hX3 h_indep hX0 hidentity
  change (d : ℝ) ^ 3 ≤ (n : ℝ) * β ^ 2 at hdim
  have hchain : (d : ℝ) ^ 3 ≤ (d : ℝ) ^ 3 * (M * β) ^ 2 := by
    calc
      (d : ℝ) ^ 3 ≤ (n : ℝ) * β ^ 2 := hdim
      _ ≤ ((d : ℝ) ^ 3 * M ^ 2) * β ^ 2 := by gcongr
      _ = (d : ℝ) ^ 3 * (M * β) ^ 2 := by ring
  have hd3 : 0 < (d : ℝ) ^ 3 := pow_pos (by exact_mod_cast hd) _
  have hsquare : 1 ≤ (M * β) ^ 2 := by
    apply le_of_mul_le_mul_left (a := (d : ℝ) ^ 3) (by simpa using hchain) hd3
  exact (one_le_sq_iff₀ (mul_nonneg hM hβ)).mp hsquare

/-- The absolute difference between the masses assigned by two probability measures is at most
one, with no measurability hypothesis on the set. -/
lemma probability_measureReal_abs_sub_le_one
    {E : Type*} [MeasurableSpace E]
    (ρ ν : Measure E) [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    (A : Set E) :
    |ρ.real A - ν.real A| ≤ 1 := by
  rw [abs_sub_le_iff]
  constructor <;>
    nlinarith [measureReal_nonneg (μ := ρ) (s := A), measureReal_le_one (μ := ρ) (s := A),
      measureReal_nonneg (μ := ν) (s := A), measureReal_le_one (μ := ν) (s := A)]

/-- Bentkus's small-cardinality branch as a ready-to-use probability-error estimate. -/
theorem probability_error_le_M_mul_thirdMomentSum_of_small_cardinality
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    {ν : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure ν]
    (hd : 0 < d) {M : ℝ} (hM : 0 ≤ M)
    (hsmall : (n : ℝ) ≤ (d : ℝ) ^ 3 * M ^ 2)
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (A : Set (EuclideanSpace ℝ (Fin d))) :
    |(μ.map (fun ω ↦ ∑ i, X i ω)).real A - ν.real A| ≤
      M * (∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ) := by
  letI : IsProbabilityMeasure (μ.map (fun ω ↦ ∑ i, X i ω)) :=
    Measure.isProbabilityMeasure_map (memLp_finsetSum Finset.univ fun i _ ↦ hX3 i).aemeasurable
  exact (probability_measureReal_abs_sub_le_one _ _ A).trans
    (small_cardinality_thirdMomentSum_lower hd hM hsmall hX3 h_indep hX0 hidentity)

/-- A summand whose second norm moment is at least `1/4` has third norm moment at least `1/8`.
This is the moment conversion used after detecting a large individual covariance. -/
lemma large_secondMoment_thirdMoment_lower
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → E}
    (hX3 : MemLp X 3 μ)
    (hlarge : 1 / 4 ≤ ∫ ω, ‖X ω‖ ^ 2 ∂μ) :
    1 ≤ 8 * ∫ ω, ‖X ω‖ ^ 3 ∂μ := by
  have h2le : (∫ ω, ‖X ω‖ ^ 2 ∂μ) ≤ lpNorm X 3 μ ^ 2 :=
    integral_norm_sq_le_lpNorm_three_sq hX3
  have hlp : 1 / 2 ≤ lpNorm X 3 μ := by
    apply (sq_le_sq₀ (by norm_num) lpNorm_nonneg).mp
    norm_num
    linarith
  have hcube := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hlp 3
  rw [lpNorm_three_cube_eq_integral_norm_pow_three hX3] at hcube
  norm_num at hcube ⊢
  linarith

/-- The large-individual-second-moment branch as a probability-error estimate. -/
theorem probability_error_le_eight_mul_thirdMoment_of_large_secondMoment
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → E}
    (hX3 : MemLp X 3 μ) (ν : Measure E) [IsProbabilityMeasure ν]
    (hlarge : 1 / 4 ≤ ∫ ω, ‖X ω‖ ^ 2 ∂μ) (A : Set E) :
    |(μ.map X).real A - ν.real A| ≤ 8 * ∫ ω, ‖X ω‖ ^ 3 ∂μ := by
  letI : IsProbabilityMeasure (μ.map X) :=
    Measure.isProbabilityMeasure_map hX3.aemeasurable
  exact (probability_measureReal_abs_sub_le_one _ _ A).trans
    (large_secondMoment_thirdMoment_lower hX3 hlarge)

end ProbabilityTheory
