/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.Bentkus.AngleCalculus
import ProbabilityApproximation.Bentkus.GaussianCompanionMoments
import ProbabilityApproximation.Bentkus.GaussianDensityDerivatives
import ProbabilityApproximation.Bentkus.GaussianDensityIntegrationByParts
import ProbabilityApproximation.Bentkus.GaussianIntegrationByParts
import ProbabilityApproximation.Bentkus.CutoffDerivativeGaussianIBP
import ProbabilityApproximation.Bentkus.InductionBranches
import ProbabilityApproximation.Bentkus.LeaveOneOutWhitening
import ProbabilityApproximation.Bentkus.ParameterClosure
import ProbabilityApproximation.Bentkus.RotationIntegration
import ProbabilityApproximation.Bentkus.SmoothingInequality
import ProbabilityApproximation.Bentkus.TaylorRemainder
import ProbabilityApproximation.Bentkus.Whitening
import ProbabilityApproximation.ConvexGeometry.GaussianShellCoarea
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.InfinitePi

/-!
# Identity-covariance reduction for Bentkus's induction

This module constructs the canonical replacement space, proves its endpoint and joint-law
identities, transports the induction hypothesis through leave-one-out whitening, and closes the
measurability and elementary branch reductions in Bentkus's Section 3 argument.
-/

open MeasureTheory InnerProductSpace Matrix Set
open scoped ENNReal MatrixOrder Pointwise RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

universe u

local instance identityCovarianceReductionConvexSpace {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

local instance identityCovarianceReductionIsModuleConvexSpace {d : ℕ} :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.ofModule

namespace BentkusInduction

set_option maxHeartbeats 2000000

private abbrev BentkusEuclideanSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

lemma isConvexSet_preimage_continuousLinearMap
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Convexity.ConvexSpace ℝ E] [Convexity.IsModuleConvexSpace ℝ E]
    [Convexity.ConvexSpace ℝ F] [Convexity.IsModuleConvexSpace ℝ F]
    (L : E →L[ℝ] F) {s : Set F} (hs : Convexity.IsConvexSet ℝ s) :
    Convexity.IsConvexSet ℝ (L ⁻¹' s) := by
  refine Convexity.IsConvexSet.of_convexCombPair_mem ?_
  intro a b ha hb hab x hx y hy
  have hmem := hs.convexCombPair_mem hx hy ha hb hab
  change L (Convexity.convexCombPair a b ha hb hab x y) ∈ s
  rw [Convexity.convexCombPair_eq_sum] at hmem ⊢
  simpa only [map_add, map_smul] using hmem

lemma isConvexSet_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Convexity.ConvexSpace ℝ E] [Convexity.IsModuleConvexSpace ℝ E]
    {s : Set E} (hs : Convexity.IsConvexSet ℝ s) :
    Convexity.IsConvexSet ℝ (interior s) := by
  have hsLegacy : Convex ℝ s := by
    rw [convex_iff_add_mem]
    intro x hx y hy a b ha hb hab
    simpa only [Convexity.convexCombPair_eq_sum] using
      hs.convexCombPair_mem hx hy ha hb hab
  refine Convexity.IsConvexSet.of_convexCombPair_mem ?_
  intro a b ha hb hab x hx y hy
  simpa only [Convexity.convexCombPair_eq_sum] using
    hsLegacy.interior hx hy ha hb hab

/-- The square root of a leave-one-out covariance is contractive when the full covariance is
the identity.  This is the operator estimate `‖P‖ ≤ 1` used in Bentkus (3.32). -/
private lemma norm_bentkusWhiteningEquiv_symm_leaveOneOut_apply_le
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin n)
    (hS : (bentkusLeaveOneOutCovarianceMatrix μ X k).PosDef)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖(bentkusWhiteningEquiv
        (bentkusLeaveOneOutCovarianceMatrix μ X k) hS).symm x‖ ≤ ‖x‖ := by
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  let R : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
  have hX2 : ∀ i, MemLp (X i) 2 μ :=
    fun i ↦ (hX3 i).mono_exponent (by norm_num)
  have hRadj : R.adjoint = R := by
    apply IsSelfAdjoint.adjoint_eq
    let e := toEuclideanCLM (n := Fin d) (𝕜 := ℝ)
    have hT : IsSelfAdjoint (CFC.sqrt S) :=
      (CFC.sqrt_nonneg S).isSelfAdjoint
    show star (e (CFC.sqrt S)) = e (CFC.sqrt S)
    calc
      star (e (CFC.sqrt S)) = e (star (CFC.sqrt S)) :=
        (map_star e (CFC.sqrt S)).symm
      _ = e (CFC.sqrt S) := congrArg e hT.star_eq
  have hRsquare (y : EuclideanSpace ℝ (Fin d)) :
      R (R y) = toEuclideanCLM (𝕜 := ℝ) S y := by
    dsimp only [R]
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
      CFC.sqrt_mul_sqrt_self S
        (bentkusLeaveOneOutCovarianceMatrix_posSemidef μ X k).nonneg]
  have hnormsq :
      ‖(bentkusWhiteningEquiv S hS).symm x‖ ^ 2 =
        covarianceBilin (μ.map (bentkusLeaveOneOut X k)) x x := by
    change ‖R x‖ ^ 2 =
      covarianceBilin (μ.map (bentkusLeaveOneOut X k)) x x
    calc
      ‖R x‖ ^ 2 = inner ℝ (R x) (R x) :=
        (real_inner_self_eq_norm_sq (R x)).symm
      _ = inner ℝ x (R.adjoint (R x)) :=
        (R.adjoint_inner_right x (R x)).symm
      _ = inner ℝ x (toEuclideanCLM (𝕜 := ℝ) S x) := by
        rw [hRadj, hRsquare]
      _ = x ⬝ᵥ S *ᵥ x := by
        simpa only using (inner_toEuclideanCLM S x x)
      _ = covarianceBilin (μ.map (bentkusLeaveOneOut X k)) x x :=
        dotProduct_bentkusLeaveOneOutCovarianceMatrix_mulVec μ X k x x
  have hcov :=
    covarianceBilin_leaveOneOut_eq_inner_sub hX2 h_indep hidentity k x x
  have hcovX : 0 ≤ covarianceBilin (μ.map (X k)) x x :=
    covarianceBilin_self_nonneg x
  have hsq :
      ‖(bentkusWhiteningEquiv S hS).symm x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hnormsq, hcov, real_inner_self_eq_norm_sq]
    linarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Operator-norm form of the leave-one-out square-root contraction. -/
lemma norm_bentkusWhiteningEquiv_symm_leaveOneOut_le_one
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin n)
    (hS : (bentkusLeaveOneOutCovarianceMatrix μ X k).PosDef) :
    ‖(bentkusWhiteningEquiv
      (bentkusLeaveOneOutCovarianceMatrix μ X k) hS).symm.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖(bentkusWhiteningEquiv
    (bentkusLeaveOneOutCovarianceMatrix μ X k) hS).symm x‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using
    norm_bentkusWhiteningEquiv_symm_leaveOneOut_apply_le
      hX3 h_indep hidentity k hS x

/-- Operator-norm form of the factor-two leave-one-out whitening estimate. -/
lemma norm_bentkusWhiteningEquiv_leaveOneOut_le_two
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin n) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (hS : (bentkusLeaveOneOutCovarianceMatrix μ X k).PosDef) :
    ‖(bentkusWhiteningEquiv
      (bentkusLeaveOneOutCovarianceMatrix μ X k) hS).toContinuousLinearMap‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖bentkusWhiteningEquiv
    (bentkusLeaveOneOutCovarianceMatrix μ X k) hS x‖ ≤ 2 * ‖x‖
  rw [bentkusWhiteningEquiv_apply]
  exact norm_bentkusWhiteningCLM_leaveOneOut_apply_le_two
    hX3 h_indep hX0 hidentity k hk x

/-- The `n`-summand slice of the standardized Bentkus assertion. -/
def bentkusIdentityCovarianceBoundAt (C : ℝ) (n : ℕ) : Prop :=
  ∀ {d : ℕ} (_hd : 0 < d)
    {Ω : Type u} [MeasurableSpace Ω]
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

/-- The measurable-representative version of one induction slice. -/
private def bentkusIdentityCovarianceBoundAtMeasurable (C : ℝ) (n : ℕ) : Prop :=
  ∀ {d : ℕ} (_hd : 0 < d)
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)),
    (∀ i, Measurable (X i)) →
    (∀ i, MemLp (X i) 3 μ) →
    iIndepFun X μ →
    (∀ i, ∫ ω, X i ω ∂μ = 0) →
    (∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y) →
    ∀ A : Set (EuclideanSpace ℝ (Fin d)),
      MeasurableSet A →
      Convexity.IsConvexSet ℝ A →
      |(μ.map (fun ω ↦ ∑ i, X i ω)).real A -
          (stdGaussian (EuclideanSpace ℝ (Fin d))).real A| ≤
        C * (d : ℝ) ^ (1 / 4 : ℝ) *
          ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ

/-- The family obtained by deleting `k`; `Fin.succAbove` gives the canonical reindexing by
`Fin n`. -/
private def bentkusRemovedFamily {n d : ℕ} {Ω : Type*}
    (k : Fin (n + 1)) (X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)) :
    Fin n → Ω → EuclideanSpace ℝ (Fin d) :=
  fun i ↦ X (k.succAbove i)

private lemma sum_bentkusRemovedFamily_eq_leaveOneOut
    {n d : ℕ} {Ω : Type*}
    (k : Fin (n + 1)) (X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)) :
    (fun ω ↦ ∑ i, bentkusRemovedFamily k X i ω) = bentkusLeaveOneOut X k := by
  funext ω
  change (∑ i : Fin n, X (k.succAbove i) ω) =
    ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase k, X i ω
  have hfull := Fin.sum_univ_succAbove (fun i ↦ X i ω) k
  have herase := Finset.sum_erase_add (Finset.univ : Finset (Fin (n + 1)))
    (fun i ↦ X i ω) (Finset.mem_univ k)
  rw [hfull] at herase
  have heq : X k ω +
      (∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase k, X i ω) =
      X k ω + ∑ i : Fin n, X (k.succAbove i) ω := by
    simpa [add_comm] using herase
  exact (add_left_cancel heq).symm

private lemma memLp_bentkusRemovedFamily
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, MemLp (X i) 3 μ) (k : Fin (n + 1)) :
    ∀ i, MemLp (bentkusRemovedFamily k X i) 3 μ :=
  fun i ↦ hX (k.succAbove i)

private lemma iIndepFun_bentkusRemovedFamily
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : iIndepFun X μ) (k : Fin (n + 1)) :
    iIndepFun (bentkusRemovedFamily k X) μ :=
  iIndepFun.precomp (g := k.succAbove) k.succAbove_right_injective hX

private lemma integral_bentkusRemovedFamily_eq_zero
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, ∫ ω, X i ω ∂μ = 0) (k : Fin (n + 1)) :
    ∀ i, ∫ ω, bentkusRemovedFamily k X i ω ∂μ = 0 :=
  fun i ↦ hX (k.succAbove i)

private lemma iIndepFun_bool_of_indepFun
    {Ω Ε : Type*} [MeasurableSpace Ω] [MeasurableSpace Ε]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f g : Ω → Ε}
    (hfg : f ⟂ᵢ[μ] g) :
    iIndepFun (fun b : Bool ↦ if b then g else f) μ := by
  rw [iIndepFun_iff]
  intro s t ht
  fin_cases s <;> simp_all
  rw [show (⋂ i, t i) = t false ∩ t true by
    ext ω
    simp only [Set.mem_iInter, Set.mem_inter_iff]
    exact Bool.forall_bool]
  rw [hfg.meas_inter ht.1 ht.2]
  exact mul_comm _ _

/-- On the canonical replacement space, the original-coordinate family and the Gaussian-coordinate
family together form one mutually independent family. -/
private lemma iIndepFun_replacementOriginalGaussian
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i)) :
    iIndepFun
      (fun p : Bool × Fin n ↦
        if p.1 then replacementGaussian (d := d) p.2
        else replacementOriginal (d := d) p.2)
      (bentkusReplacementMeasure μ X) := by
  let ρ := bentkusReplacementMeasure μ X
  let O : Fin n → _ → EuclideanSpace ℝ (Fin d) :=
    fun i ↦ replacementOriginal (d := d) i
  let G : Fin n → _ → EuclideanSpace ℝ (Fin d) :=
    fun i ↦ replacementGaussian (d := d) i
  let F : Bool → Fin n → _ → EuclideanSpace ℝ (Fin d) :=
    fun b i ↦ if b then G i else O i
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hblocks :
      (fun ω ↦ fun i ↦ O i ω) ⟂ᵢ[ρ] (fun ω ↦ fun i ↦ G i ω) := by
    simpa only [O, G, replacementOriginal, replacementGaussian, ρ] using
      indepFun_replacement_blocks hXm
  have houter : iIndepFun (fun b ω i ↦ F b i ω) ρ := by
    have h := iIndepFun_bool_of_indepFun hblocks
    convert h using 1
    ext b ω i
    cases b <;> rfl
  have hinner : ∀ b, iIndepFun (F b) ρ := by
    intro b
    cases b
    · change iIndepFun O ρ
      exact iIndepFun_replacementOriginal hXm
    · change iIndepFun G ρ
      exact iIndepFun_replacementGaussian hXm
  have hall := iIndepFun_uncurry'
    (P := ρ) (X := F)
    (by
      intro b i
      cases b
      · exact (measurable_pi_apply i).comp measurable_fst
      · exact (measurable_pi_apply i).comp measurable_snd)
    houter hinner
  simpa only [F, O, G, ρ] using hall

/-- The rotated leave-one-out pair is independent of the omitted original/Gaussian coordinate
pair.  This is the product-law conditioning used in Bentkus (3.36)--(3.41). -/
private theorem indepFun_whitenedRotatedLeaveOneOut_replacementPair
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (k : Fin (n + 1)) (α : ℝ) :
    let ρ := bentkusReplacementMeasure μ X
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let UO := bentkusLeaveOneOut
      (fun i ↦ replacementOriginal (d := d) i) k
    let VG := bentkusLeaveOneOut
      (fun i ↦ replacementGaussian (d := d) i) k
    (fun ω ↦ B (Real.cos α • UO ω + Real.sin α • VG ω)) ⟂ᵢ[ρ]
      (fun ω ↦ (O ω, G ω)) := by
  let ρ := bentkusReplacementMeasure μ X
  let O : Fin (n + 1) → _ → EuclideanSpace ℝ (Fin d) :=
    fun i ↦ replacementOriginal (d := d) i
  let G : Fin (n + 1) → _ → EuclideanSpace ℝ (Fin d) :=
    fun i ↦ replacementGaussian (d := d) i
  let I := Bool × Fin (n + 1)
  let F : I → _ → EuclideanSpace ℝ (Fin d) :=
    fun p ↦ if p.1 then G p.2 else O p.2
  let S : Finset I := Finset.univ.filter (fun p ↦ p.2 ≠ k)
  let T : Finset I := Finset.univ.filter (fun p ↦ p.2 = k)
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro p hpS hpT
    simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at hpS hpT
    exact hpS hpT
  have hFm : ∀ p, Measurable (F p) := by
    intro p
    rcases p with ⟨b, i⟩
    cases b
    · exact (measurable_pi_apply i).comp measurable_fst
    · exact (measurable_pi_apply i).comp measurable_snd
  have hFi : iIndepFun F ρ := by
    dsimp only [F, O, G, ρ]
    exact iIndepFun_replacementOriginalGaussian (μ := μ) (X := X) hXm
  have htuple :
      (fun ω (p : S) ↦ F p ω) ⟂ᵢ[ρ] (fun ω (p : T) ↦ F p ω) :=
    hFi.indepFun_finset S T hST hFm
  have hok : (false, k) ∈ T := by simp [T]
  have hgk : (true, k) ∈ T := by simp [T]
  let ok : T := ⟨(false, k), hok⟩
  let gk : T := ⟨(true, k), hgk⟩
  let combineS : (S → EuclideanSpace ℝ (Fin d)) →
      EuclideanSpace ℝ (Fin d) := fun z ↦ B (∑ p : S,
    if p.1.1 then Real.sin α • z p else Real.cos α • z p)
  let combineT : (T → EuclideanSpace ℝ (Fin d)) →
      EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) :=
    fun z ↦ (z ok, z gk)
  have hcombineSm : Measurable combineS := by
    dsimp only [combineS]
    apply B.continuous.measurable.comp
    apply Finset.measurable_sum Finset.univ
    intro p _
    by_cases hp : p.1.1
    · simp only [hp, if_true]
      change Measurable ((fun x : EuclideanSpace ℝ (Fin d) ↦ Real.sin α • x) ∘
        fun z : S → EuclideanSpace ℝ (Fin d) ↦ z p)
      exact (measurable_const_smul (Real.sin α)).comp (measurable_pi_apply p)
    · simp only [hp]
      change Measurable ((fun x : EuclideanSpace ℝ (Fin d) ↦ Real.cos α • x) ∘
        fun z : S → EuclideanSpace ℝ (Fin d) ↦ z p)
      exact (measurable_const_smul (Real.cos α)).comp (measurable_pi_apply p)
  have hcombineTm : Measurable combineT := by
    dsimp only [combineT]
    fun_prop
  have hcomp := htuple.comp hcombineSm hcombineTm
  have hcombineS (ω) : combineS (fun p : S ↦ F p ω) =
      B (Real.cos α • bentkusLeaveOneOut O k ω +
        Real.sin α • bentkusLeaveOneOut G k ω) := by
    dsimp only [combineS, F, S, bentkusLeaveOneOut]
    have hsub :
        (∑ p : {p // p ∈ (Finset.univ.filter
            (fun p : Bool × Fin (n + 1) ↦ p.2 ≠ k))},
          if p.1.1 then Real.sin α •
              (if p.1.1 then G p.1.2 ω else O p.1.2 ω)
            else Real.cos α •
              (if p.1.1 then G p.1.2 ω else O p.1.2 ω)) =
        (∑ p ∈ (Finset.univ.filter
            (fun p : Bool × Fin (n + 1) ↦ p.2 ≠ k)),
          if p.1 then Real.sin α • (if p.1 then G p.2 ω else O p.2 ω)
            else Real.cos α • (if p.1 then G p.2 ω else O p.2 ω)) := by
      simpa using ((Finset.univ.filter
        (fun p : Bool × Fin (n + 1) ↦ p.2 ≠ k)).sum_attach
          (fun p ↦ if p.1 then Real.sin α •
              (if p.1 then G p.2 ω else O p.2 ω)
            else Real.cos α • (if p.1 then G p.2 ω else O p.2 ω)))
    simp only [ite_apply]
    rw [hsub, Finset.sum_filter, Fintype.sum_prod_type]
    simp only [Fintype.univ_bool, ne_eq, smul_ite, ite_not, Finset.mem_singleton,
      Bool.true_eq_false, not_false_eq_true, Finset.sum_insert, ↓reduceIte,
      Finset.sum_singleton, Bool.false_eq_true]
    have hremove (f : Fin (n + 1) → EuclideanSpace ℝ (Fin d)) :
        (∑ x, if x = k then 0 else f x) = ∑ x ∈ Finset.univ.erase k, f x := by
      calc
        (∑ x, if x = k then 0 else f x) = ∑ x, if x ≠ k then f x else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x = k <;> simp [hx]
        _ = ∑ x ∈ Finset.univ.filter (fun x ↦ x ≠ k), f x :=
          (Finset.sum_filter _ _).symm
        _ = ∑ x ∈ Finset.univ.erase k, f x := by
          congr 1
          ext x
          simp [eq_comm]
    rw [hremove, hremove, ← Finset.smul_sum, ← Finset.smul_sum, add_comm]
  have hcombineT (ω) : combineT (fun p : T ↦ F p ω) = (O k ω, G k ω) := by
    rfl
  change (fun ω ↦ B (Real.cos α • bentkusLeaveOneOut O k ω +
      Real.sin α • bentkusLeaveOneOut G k ω)) ⟂ᵢ[ρ]
    (fun ω ↦ (O k ω, G k ω))
  convert hcomp using 1
  · funext ω
    exact (hcombineS ω).symm
  · funext ω
    exact hcombineT ω

/-- The sum of the matched Gaussian companions has standard Gaussian law when the original total
covariance is the identity.  This is the law-level identification used at the Gaussian endpoint of
Bentkus's rotation. -/
private theorem map_sum_replacementGaussian_eq_stdGaussian
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y) :
    (bentkusReplacementMeasure μ X).map
        (fun ω ↦ ∑ i, replacementGaussian (d := d) i ω) =
      stdGaussian (EuclideanSpace ℝ (Fin d)) := by
  let ρ := bentkusReplacementMeasure μ X
  let O : Fin n → _ → EuclideanSpace ℝ (Fin d) :=
    fun i ↦ replacementOriginal (d := d) i
  let G : Fin n → _ → EuclideanSpace ℝ (Fin d) :=
    fun i ↦ replacementGaussian (d := d) i
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hO2 : ∀ i, MemLp (O i) 2 ρ := fun i ↦
    (memLp_replacementOriginal hXm
      (fun j ↦ (hX3 j).mono_exponent (by norm_num)) i)
  have hG2 : ∀ i, MemLp (G i) 2 ρ := fun i ↦
    (memLp_three_replacementGaussian hXm i).mono_exponent (by norm_num)
  have hOindep : iIndepFun O ρ := iIndepFun_replacementOriginal hXm
  have hGindep : iIndepFun G ρ := iIndepFun_replacementGaussian hXm
  have hOcov (x y : EuclideanSpace ℝ (Fin d)) :
      covarianceBilin (ρ.map (fun ω ↦ ∑ i, O i ω)) x y = inner ℝ x y := by
    rw [covarianceBilin_map_sum_eq_sum hO2 hOindep]
    calc
      (∑ i, covarianceBilin (ρ.map (O i)) x y) =
          ∑ i, covarianceBilin (μ.map (X i)) x y := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show ρ.map (O i) = μ.map (X i) by
          exact map_replacementOriginal hXm i]
      _ = covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y :=
        (covarianceBilin_map_sum_eq_sum
          (fun i ↦ (hX3 i).mono_exponent (by norm_num)) h_indep x y).symm
      _ = inner ℝ x y := hidentity x y
  have hGcov (x y : EuclideanSpace ℝ (Fin d)) :
      covarianceBilin (ρ.map (fun ω ↦ ∑ i, G i ω)) x y = inner ℝ x y := by
    rw [covarianceBilin_map_sum_eq_sum hG2 hGindep]
    calc
      (∑ i, covarianceBilin (ρ.map (G i)) x y) =
          ∑ i, covarianceBilin (ρ.map (O i)) x y := by
        apply Finset.sum_congr rfl
        intro i _
        exact covarianceBilin_replacementGaussian_eq_replacementOriginal hXm i x y
      _ = covarianceBilin (ρ.map (fun ω ↦ ∑ i, O i ω)) x y :=
        (covarianceBilin_map_sum_eq_sum hO2 hOindep x y).symm
      _ = inner ℝ x y := hOcov x y
  have hGlaw : HasGaussianLaw (fun ω ↦ ∑ i, G i ω) ρ := by
    apply iIndepFun.hasGaussianLaw_fun_sum (hX2 := hGindep)
    intro i
    refine ⟨?_⟩
    rw [show ρ.map (G i) = multivariateGaussian 0 (summandCovarianceMatrix μ X i) by
      exact map_replacementGaussian hXm i]
    infer_instance
  letI : IsGaussian (ρ.map (fun ω ↦ ∑ i, G i ω)) := hGlaw.isGaussian_map
  have hGmean : ∫ ω, (∑ i, G i ω) ∂ρ = 0 := by
    rw [integral_finsetSum _ fun i _ ↦
      (memLp_three_replacementGaussian hXm i).integrable (by norm_num)]
    simp only [integral_replacementGaussian_eq_zero hXm, Finset.sum_const_zero]
  have hmean :
      (ρ.map (fun ω ↦ ∑ i, G i ω))[id] =
        (stdGaussian (EuclideanSpace ℝ (Fin d)))[id] := by
    change (∫ x, x ∂(ρ.map (fun ω ↦ ∑ i, G i ω))) =
      ∫ x, x ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
    rw [integral_id_stdGaussian]
    calc
      (∫ x, x ∂(ρ.map (fun ω ↦ ∑ i, G i ω))) =
          ∫ ω, (∑ i, G i ω) ∂ρ := by
        simpa only [Function.comp_apply, id_eq] using
          integral_map hGlaw.aemeasurable aestronglyMeasurable_id
      _ = 0 := hGmean
  change ρ.map (fun ω ↦ ∑ i, G i ω) = _
  apply IsGaussian.ext hmean
  ext x y
  rw [hGcov, covarianceBilin_stdGaussian]
  rfl

/-- The Gaussian companions outside one coordinate have the Gaussian law whose covariance is the
original leave-one-out covariance.  This is the law identification implicit in Bentkus's
definition of `U_k` and `P_k` before (3.13). -/
private theorem map_bentkusLeaveOneOut_replacementGaussian_eq_multivariateGaussian
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (k : Fin (n + 1)) :
    (bentkusReplacementMeasure μ X).map
        (bentkusLeaveOneOut
          (fun i ↦ replacementGaussian (d := d) i) k) =
      multivariateGaussian 0 (bentkusLeaveOneOutCovarianceMatrix μ X k) := by
  let ρ := bentkusReplacementMeasure μ X
  let O : Fin (n + 1) → _ → EuclideanSpace ℝ (Fin d) :=
    fun i ↦ replacementOriginal (d := d) i
  let G : Fin (n + 1) → _ → EuclideanSpace ℝ (Fin d) :=
    fun i ↦ replacementGaussian (d := d) i
  let RO := bentkusRemovedFamily k O
  let RG := bentkusRemovedFamily k G
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hO2 : ∀ i, MemLp (O i) 2 ρ := fun i ↦
    (memLp_replacementOriginal hXm
      (fun j ↦ (hX3 j).mono_exponent (by norm_num)) i)
  have hG2 : ∀ i, MemLp (G i) 2 ρ := fun i ↦
    (memLp_three_replacementGaussian hXm i).mono_exponent (by norm_num)
  have hRO2 : ∀ i, MemLp (RO i) 2 ρ := fun i ↦ hO2 (k.succAbove i)
  have hRG2 : ∀ i, MemLp (RG i) 2 ρ := fun i ↦ hG2 (k.succAbove i)
  have hOindep : iIndepFun O ρ := iIndepFun_replacementOriginal hXm
  have hGindep : iIndepFun G ρ := iIndepFun_replacementGaussian hXm
  have hROindep : iIndepFun RO ρ := iIndepFun_bentkusRemovedFamily hOindep k
  have hRGindep : iIndepFun RG ρ := iIndepFun_bentkusRemovedFamily hGindep k
  have hOcov (x y : EuclideanSpace ℝ (Fin d)) :
      covarianceBilin (ρ.map (bentkusLeaveOneOut O k)) x y =
        covarianceBilin (μ.map (bentkusLeaveOneOut X k)) x y := by
    rw [← sum_bentkusRemovedFamily_eq_leaveOneOut k O,
      ← sum_bentkusRemovedFamily_eq_leaveOneOut k X,
      covarianceBilin_map_sum_eq_sum hRO2 hROindep]
    calc
      (∑ i, covarianceBilin (ρ.map (RO i)) x y) =
          ∑ i, covarianceBilin (μ.map (bentkusRemovedFamily k X i)) x y := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show ρ.map (RO i) = μ.map (bentkusRemovedFamily k X i) by
          exact map_replacementOriginal hXm (k.succAbove i)]
      _ = covarianceBilin
          (μ.map (fun ω ↦ ∑ i, bentkusRemovedFamily k X i ω)) x y :=
        (covarianceBilin_map_sum_eq_sum
          (fun i ↦ (hX3 (k.succAbove i)).mono_exponent (by norm_num))
          (iIndepFun_bentkusRemovedFamily h_indep k) x y).symm
  have hGcov (x y : EuclideanSpace ℝ (Fin d)) :
      covarianceBilin (ρ.map (bentkusLeaveOneOut G k)) x y =
        covarianceBilin (μ.map (bentkusLeaveOneOut X k)) x y := by
    rw [← sum_bentkusRemovedFamily_eq_leaveOneOut k G,
      covarianceBilin_map_sum_eq_sum hRG2 hRGindep]
    calc
      (∑ i, covarianceBilin (ρ.map (RG i)) x y) =
          ∑ i, covarianceBilin (ρ.map (RO i)) x y := by
        apply Finset.sum_congr rfl
        intro i _
        exact covarianceBilin_replacementGaussian_eq_replacementOriginal
          hXm (k.succAbove i) x y
      _ = covarianceBilin (ρ.map (fun ω ↦ ∑ i, RO i ω)) x y :=
        (covarianceBilin_map_sum_eq_sum hRO2 hROindep x y).symm
      _ = covarianceBilin (ρ.map (bentkusLeaveOneOut O k)) x y := by
        rw [sum_bentkusRemovedFamily_eq_leaveOneOut k O]
      _ = covarianceBilin (μ.map (bentkusLeaveOneOut X k)) x y := hOcov x y
  have hGlaw : HasGaussianLaw (bentkusLeaveOneOut G k) ρ := by
    rw [← sum_bentkusRemovedFamily_eq_leaveOneOut k G]
    apply iIndepFun.hasGaussianLaw_fun_sum (hX2 := hRGindep)
    intro i
    refine ⟨?_⟩
    rw [show ρ.map (RG i) =
        multivariateGaussian 0 (summandCovarianceMatrix μ X (k.succAbove i)) by
      exact map_replacementGaussian hXm (k.succAbove i)]
    infer_instance
  letI : IsGaussian (ρ.map (bentkusLeaveOneOut G k)) := hGlaw.isGaussian_map
  have hGmean : ∫ ω, bentkusLeaveOneOut G k ω ∂ρ = 0 := by
    rw [← sum_bentkusRemovedFamily_eq_leaveOneOut k G,
      integral_finsetSum _ fun i _ ↦ (hRG2 i).integrable (by norm_num)]
    apply Finset.sum_eq_zero
    intro i _
    exact integral_replacementGaussian_eq_zero hXm (k.succAbove i)
  have hmean :
      (ρ.map (bentkusLeaveOneOut G k))[id] =
        (multivariateGaussian 0
          (bentkusLeaveOneOutCovarianceMatrix μ X k))[id] := by
    change (∫ x, x ∂(ρ.map (bentkusLeaveOneOut G k))) =
      ∫ x, x ∂(multivariateGaussian 0
        (bentkusLeaveOneOutCovarianceMatrix μ X k))
    rw [integral_id_multivariateGaussian]
    calc
      (∫ x, x ∂(ρ.map (bentkusLeaveOneOut G k))) =
          ∫ ω, bentkusLeaveOneOut G k ω ∂ρ := by
        simpa only [Function.comp_apply, id_eq] using
          integral_map hGlaw.aemeasurable aestronglyMeasurable_id
      _ = 0 := hGmean
  change ρ.map (bentkusLeaveOneOut G k) = _
  apply IsGaussian.ext hmean
  ext x y
  rw [hGcov,
    covarianceBilin_multivariateGaussian
      (bentkusLeaveOneOutCovarianceMatrix_posSemidef μ X k)]
  exact (dotProduct_bentkusLeaveOneOutCovarianceMatrix_mulVec μ X k x y).symm

/-- After the nontrivial-branch leave-one-out whitening, the Gaussian companion sum is exactly
standard Gaussian.  This is the random vector denoted by `N` in Bentkus (3.15). -/
private theorem map_whitened_bentkusLeaveOneOut_replacementGaussian_eq_stdGaussian
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4) :
    (bentkusReplacementMeasure μ X).map
        (fun ω ↦ bentkusWhiteningCLM
          (bentkusLeaveOneOutCovarianceMatrix μ X k)
          (bentkusLeaveOneOut
            (fun i ↦ replacementGaussian (d := d) i) k ω)) =
      stdGaussian (EuclideanSpace ℝ (Fin d)) := by
  let ρ := bentkusReplacementMeasure μ X
  let G : Fin (n + 1) → _ → EuclideanSpace ℝ (Fin d) :=
    fun i ↦ replacementGaussian (d := d) i
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  have hVlaw : ρ.map (bentkusLeaveOneOut G k) = multivariateGaussian 0 S :=
    map_bentkusLeaveOneOut_replacementGaussian_eq_multivariateGaussian
      hXm hX3 h_indep k
  calc
    ρ.map (fun ω ↦ bentkusWhiteningCLM S (bentkusLeaveOneOut G k ω)) =
        (ρ.map (bentkusLeaveOneOut G k)).map (bentkusWhiteningEquiv S hS) := by
      rw [Measure.map_map]
      · rfl
      · exact (bentkusWhiteningEquiv S hS).continuous.measurable
      · dsimp only [G, bentkusLeaveOneOut]
        exact Finset.measurable_sum (Finset.univ.erase k) fun i _ ↦
          (measurable_pi_apply i).comp measurable_snd
    _ = (multivariateGaussian 0 S).map (bentkusWhiteningEquiv S hS) := by
      rw [hVlaw]
    _ = stdGaussian (EuclideanSpace ℝ (Fin d)) :=
      map_multivariateGaussian_bentkusWhiteningEquiv S hS

/-- The whitened Gaussian leave-one-out vector is independent of the omitted original/Gaussian
pair.  This is the independence assertion used when Bentkus conditions the (3.15) remainder on
`X_k,Y_k`. -/
private theorem indepFun_whitened_bentkusLeaveOneOut_replacementGaussian_pair
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (S : Matrix (Fin d) (Fin d) ℝ) (k : Fin (n + 1)) :
    (fun ω ↦ bentkusWhiteningCLM S
        (bentkusLeaveOneOut
          (fun i ↦ replacementGaussian (d := d) i) k ω))
      ⟂ᵢ[bentkusReplacementMeasure μ X]
    (fun ω ↦
      (replacementOriginal (d := d) k ω,
        replacementGaussian (d := d) k ω)) := by
  let ρ := bentkusReplacementMeasure μ X
  let E := EuclideanSpace ℝ (Fin d)
  let H : Bool × Fin (n + 1) → _ → E := fun p ↦
    if p.1 then replacementGaussian (d := d) p.2
    else replacementOriginal (d := d) p.2
  let s : Finset (Bool × Fin (n + 1)) :=
    ({true} : Finset Bool) ×ˢ ((Finset.univ : Finset (Fin (n + 1))).erase k)
  let t : Finset (Bool × Fin (n + 1)) :=
    (Finset.univ : Finset Bool) ×ˢ ({k} : Finset (Fin (n + 1)))
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hHindep : iIndepFun H ρ := by
    simpa only [H, ρ] using iIndepFun_replacementOriginalGaussian hXm
  have hHmeas : ∀ p, Measurable (H p) := by
    intro p
    cases p with
    | mk b i =>
      cases b
      · exact (measurable_pi_apply i).comp measurable_fst
      · exact (measurable_pi_apply i).comp measurable_snd
  have hst : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro p hps hpt
    simp only [s, t, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_univ, true_and] at hps hpt
    exact (Finset.mem_erase.mp hps.2).1 hpt
  have htuple := hHindep.indepFun_finset s t hst hHmeas
  let leftMap : (s → E) → E := fun z ↦
    bentkusWhiteningCLM S
      (∑ j : ↑((Finset.univ : Finset (Fin (n + 1))).erase k),
        z ⟨(true, j), by
          dsimp only [s]
          exact Finset.mem_product.mpr ⟨by simp, j.property⟩⟩)
  let ok : t := ⟨(false, k), by simp [t]⟩
  let gk : t := ⟨(true, k), by simp [t]⟩
  let rightMap : (t → E) → E × E := fun z ↦ (z ok, z gk)
  have hleft : Measurable leftMap := by
    dsimp only [leftMap]
    fun_prop
  have hright : Measurable rightMap := by
    exact Measurable.prod (measurable_pi_apply ok) (measurable_pi_apply gk)
  have hcomp := htuple.comp hleft hright
  convert hcomp using 1
  · funext ω
    dsimp only [Function.comp_apply, leftMap, H]
    congr 1
    change bentkusLeaveOneOut
        (fun i ↦ replacementGaussian (d := d) i) k ω =
      ∑ j : ↑((Finset.univ : Finset (Fin (n + 1))).erase k),
        replacementGaussian (d := d) j ω
    rw [bentkusLeaveOneOut]
    exact (Finset.sum_coe_sort
      ((Finset.univ : Finset (Fin (n + 1))).erase k)
      (fun i ↦ replacementGaussian (d := d) i ω)).symm
  · funext ω
    rfl

/-- The joint law used to condition Bentkus's Gaussian remainder is the product of standard
Gaussian law and the law of the omitted original/Gaussian pair. -/
theorem
    map_whitened_bentkusLeaveOneOut_replacementGaussian_pair_eq_prod
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4) :
    let ρ := bentkusReplacementMeasure μ X
    let N := fun ω ↦ bentkusWhiteningCLM
      (bentkusLeaveOneOutCovarianceMatrix μ X k)
      (bentkusLeaveOneOut
        (fun i ↦ replacementGaussian (d := d) i) k ω)
    let Z := fun ω ↦
      (replacementOriginal (d := d) k ω,
        replacementGaussian (d := d) k ω)
    ρ.map (fun ω ↦ (N ω, Z ω)) =
      (stdGaussian (EuclideanSpace ℝ (Fin d))).prod (ρ.map Z) := by
  let ρ := bentkusReplacementMeasure μ X
  let N := fun ω ↦ bentkusWhiteningCLM
    (bentkusLeaveOneOutCovarianceMatrix μ X k)
    (bentkusLeaveOneOut
      (fun i ↦ replacementGaussian (d := d) i) k ω)
  let Z := fun ω ↦
    (replacementOriginal (d := d) k ω,
      replacementGaussian (d := d) k ω)
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hNmeas : Measurable N := by
    dsimp only [N, bentkusLeaveOneOut, replacementGaussian]
    fun_prop
  have hZmeas : Measurable Z := by
    dsimp only [Z, replacementOriginal, replacementGaussian]
    fun_prop
  have hindep : N ⟂ᵢ[ρ] Z := by
    simpa only [N, Z, ρ] using
      indepFun_whitened_bentkusLeaveOneOut_replacementGaussian_pair
        hXm (bentkusLeaveOneOutCovarianceMatrix μ X k) k
  have hjoint := hindep.map_prod_eq_prod_map_map
    hNmeas.aemeasurable hZmeas.aemeasurable
  have hNlaw : ρ.map N = stdGaussian (EuclideanSpace ℝ (Fin d)) := by
    simpa only [N, ρ] using
      map_whitened_bentkusLeaveOneOut_replacementGaussian_eq_stdGaussian
        hXm hX3 h_indep hX0 hidentity k hk
  rw [hNlaw] at hjoint
  exact hjoint

/-- Fubini disintegration through an exact independent joint-law identity. -/
theorem integral_comp_pair_eq_iterated_of_map_eq_prod
    {Θ Λ Ξ : Type*} [MeasurableSpace Θ] [MeasurableSpace Λ] [MeasurableSpace Ξ]
    {μ : Measure Θ} {ν : Measure Λ} {τ : Measure Ξ}
    [SFinite μ] [SFinite ν] [SFinite τ]
    {N : Θ → Λ} {Z : Θ → Ξ} (hN : Measurable N) (hZ : Measurable Z)
    (hjoint : μ.map (fun ω ↦ (N ω, Z ω)) = ν.prod τ)
    {F : Λ × Ξ → ℝ} (hF : Integrable F (ν.prod τ)) :
    ∫ ω, F (N ω, Z ω) ∂μ = ∫ z, ∫ u, F (u, z) ∂ν ∂τ := by
  have hpair : Measurable (fun ω ↦ (N ω, Z ω)) := hN.prodMk hZ
  have hFmap : AEStronglyMeasurable F (μ.map (fun ω ↦ (N ω, Z ω))) := by
    rw [hjoint]
    exact hF.aestronglyMeasurable
  calc
    (∫ ω, F (N ω, Z ω) ∂μ) =
        ∫ p, F p ∂(μ.map (fun ω ↦ (N ω, Z ω))) := by
      exact (integral_map hpair.aemeasurable hFmap).symm
    _ = ∫ p, F p ∂(ν.prod τ) := by rw [hjoint]
    _ = ∫ p : Ξ × Λ, F p.swap ∂(τ.prod ν) :=
      (integral_prod_swap F).symm
    _ = ∫ z, ∫ u, F (u, z) ∂ν ∂τ := by
      simpa only [Function.comp_apply, Prod.swap_prod_mk] using
        integral_prod (F ∘ Prod.swap) hF.swap

/-- Fubini disintegration when the first coordinate is itself an affine image of a product
measure.  The resulting order is omitted coordinate, affine base, exposed Gaussian coordinate. -/
theorem integral_comp_pair_eq_triple_of_map_eq_mapped_prod
    {Θ A U Z : Type*} [MeasurableSpace Θ] [MeasurableSpace A]
    [MeasurableSpace U] [MeasurableSpace Z]
    {μ : Measure Θ} {ν : Measure A} {γ : Measure U} {τ : Measure Z}
    [SFinite μ] [SFinite ν] [SFinite γ] [SFinite τ]
    {N : Θ → A} {W : Θ → Z} (hN : Measurable N) (hW : Measurable W)
    (M : A × U → A) (hM : Measurable M)
    (hjoint : μ.map (fun ω ↦ (N ω, W ω)) =
      ((ν.prod γ).map M).prod τ)
    {F : A × Z → ℝ}
    (hF : Integrable F
      (((ν.prod γ).map M).prod τ)) :
    ∫ ω, F (N ω, W ω) ∂μ =
      ∫ z, ∫ a, ∫ u, F (M (a, u), z) ∂γ ∂ν ∂τ := by
  have hdisintegrate :=
    integral_comp_pair_eq_iterated_of_map_eq_prod
      hN hW hjoint hF
  rw [hdisintegrate]
  apply integral_congr_ae
  have hfiber := hF.prod_left_ae
  filter_upwards [hfiber] with z hz
  have hcomp : Integrable
      (fun p : A × U ↦ F (M p, z)) (ν.prod γ) := by
    exact hz.comp_measurable hM
  calc
    (∫ a, F (a, z) ∂((ν.prod γ).map M)) =
        ∫ p : A × U, F (M p, z) ∂(ν.prod γ) := by
      exact integral_map hM.aemeasurable hz.aestronglyMeasurable
    _ = ∫ a, ∫ u, F (M (a, u), z) ∂γ ∂ν := by
      simpa only using integral_prod
        (fun p : A × U ↦ F (M p, z)) hcomp

theorem integral_integral_eq_zero_of_integral_eq_zero
    {Θ Λ : Type*} [MeasurableSpace Θ] [MeasurableSpace Λ]
    {μ : Measure Θ} {ν : Measure Λ} [SFinite μ] [SFinite ν]
    {F : Θ × Λ → ℝ} (hF : Integrable F (μ.prod ν))
    (hzero : ∀ x, ∫ ω, F (ω, x) ∂μ = 0) :
    ∫ ω, ∫ x, F (ω, x) ∂ν ∂μ = 0 := by
  calc
    (∫ ω, ∫ x, F (ω, x) ∂ν ∂μ) = ∫ p, F p ∂(μ.prod ν) :=
      integral_integral hF
    _ = ∫ p : Λ × Θ, F p.swap ∂(ν.prod μ) :=
      (integral_prod_swap F).symm
    _ = ∫ x, ∫ ω, F (ω, x) ∂μ ∂ν := by
      simpa only [Function.comp_apply, Prod.swap_prod_mk] using
        integral_prod (F ∘ Prod.swap) hF.swap
    _ = 0 := by simp only [hzero, integral_zero]

/-- The mixed third moment left by the Gaussian-density remainder in Bentkus (3.19)--(3.23) is
uniformly controlled after leave-one-out whitening.  The explicit constant is deliberately
conservative: only its absoluteness is used by the final induction. -/
theorem
    integral_norm_whitened_replacementRotated_sq_mul_norm_whitened_replacementRotatedDeriv_le
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4) (α : ℝ) :
    let ρ := bentkusReplacementMeasure μ X
    let B := bentkusWhiteningCLM (bentkusLeaveOneOutCovarianceMatrix μ X k)
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    (∫ ω, ‖B (bentkusRotated α O G ω)‖ ^ 2 *
        ‖B (bentkusRotatedDeriv α O G ω)‖ ∂ρ) ≤
      896 * ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
  let ρ := bentkusReplacementMeasure μ X
  let B := bentkusWhiteningCLM (bentkusLeaveOneOutCovarianceMatrix μ X k)
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let R := bentkusRotated α O G
  let R' := bentkusRotatedDeriv α O G
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hO3 : MemLp O 3 ρ := memLp_replacementOriginal hXm hX3 k
  have hG3 : MemLp G 3 ρ := memLp_three_replacementGaussian hXm k
  have hupper : Integrable (fun ω ↦ 32 * (‖O ω‖ ^ 3 + ‖G ω‖ ^ 3)) ρ :=
    ((hO3.integrable_norm_pow (by norm_num)).add
      (hG3.integrable_norm_pow (by norm_num))).const_mul 32
  have hpoint (ω) :
      ‖B (R ω)‖ ^ 2 * ‖B (R' ω)‖ ≤
        32 * (‖O ω‖ ^ 3 + ‖G ω‖ ^ 3) := by
    have hB (z : EuclideanSpace ℝ (Fin d)) : ‖B z‖ ≤ 2 * ‖z‖ := by
      exact norm_bentkusWhiteningCLM_leaveOneOut_apply_le_two
        hX3 h_indep hX0 hidentity k hk z
    have hcos : |Real.cos α| ≤ 1 := Real.abs_cos_le_one α
    have hsin : |Real.sin α| ≤ 1 := Real.abs_sin_le_one α
    have hR : ‖R ω‖ ≤ ‖O ω‖ + ‖G ω‖ := by
      dsimp only [R, bentkusRotated]
      calc
        ‖Real.cos α • O ω + Real.sin α • G ω‖ ≤
            ‖Real.cos α • O ω‖ + ‖Real.sin α • G ω‖ := norm_add_le _ _
        _ = |Real.cos α| * ‖O ω‖ + |Real.sin α| * ‖G ω‖ := by
          simp only [norm_smul, Real.norm_eq_abs]
        _ ≤ ‖O ω‖ + ‖G ω‖ := by
          exact add_le_add
            (mul_le_of_le_one_left (norm_nonneg _) hcos)
            (mul_le_of_le_one_left (norm_nonneg _) hsin)
    have hR' : ‖R' ω‖ ≤ ‖O ω‖ + ‖G ω‖ := by
      dsimp only [R', bentkusRotatedDeriv]
      calc
        ‖-(Real.sin α) • O ω + Real.cos α • G ω‖ ≤
            ‖-(Real.sin α) • O ω‖ + ‖Real.cos α • G ω‖ := norm_add_le _ _
        _ = |Real.sin α| * ‖O ω‖ + |Real.cos α| * ‖G ω‖ := by
          simp only [norm_smul, Real.norm_eq_abs, abs_neg]
        _ ≤ ‖O ω‖ + ‖G ω‖ := by
          exact add_le_add
            (mul_le_of_le_one_left (norm_nonneg _) hsin)
            (mul_le_of_le_one_left (norm_nonneg _) hcos)
    have hBR : ‖B (R ω)‖ ≤ 2 * (‖O ω‖ + ‖G ω‖) := (hB _).trans (by gcongr)
    have hBR' : ‖B (R' ω)‖ ≤ 2 * (‖O ω‖ + ‖G ω‖) := (hB _).trans (by gcongr)
    have hsum : 0 ≤ ‖O ω‖ + ‖G ω‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    calc
      ‖B (R ω)‖ ^ 2 * ‖B (R' ω)‖ ≤
          (2 * (‖O ω‖ + ‖G ω‖)) ^ 2 *
            (2 * (‖O ω‖ + ‖G ω‖)) := by gcongr
      _ = 8 * (‖O ω‖ + ‖G ω‖) ^ 3 := by ring
      _ ≤ 32 * (‖O ω‖ ^ 3 + ‖G ω‖ ^ 3) := by
        nlinarith [sq_nonneg (‖O ω‖ - ‖G ω‖),
          mul_nonneg (norm_nonneg (O ω)) (norm_nonneg (G ω)), hsum]
  have hmeas : AEStronglyMeasurable
      (fun ω ↦ ‖B (R ω)‖ ^ 2 * ‖B (R' ω)‖) ρ := by
    dsimp only [R, R', O, G, bentkusRotated, bentkusRotatedDeriv,
      replacementOriginal, replacementGaussian]
    fun_prop
  have hint : Integrable
      (fun ω ↦ ‖B (R ω)‖ ^ 2 * ‖B (R' ω)‖) ρ := by
    apply hupper.mono' hmeas
    filter_upwards with ω
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _))]
    exact hpoint ω
  have hG := integral_norm_pow_three_replacementGaussian_le hXm hX3 hX0 k
  calc
    (∫ ω, ‖B (R ω)‖ ^ 2 * ‖B (R' ω)‖ ∂ρ) ≤
        ∫ ω, 32 * (‖O ω‖ ^ 3 + ‖G ω‖ ^ 3) ∂ρ := by
      exact integral_mono hint hupper hpoint
    _ = 32 * ((∫ ω, ‖O ω‖ ^ 3 ∂ρ) + ∫ ω, ‖G ω‖ ^ 3 ∂ρ) := by
      rw [integral_const_mul, integral_add
        (hO3.integrable_norm_pow (by norm_num))
        (hG3.integrable_norm_pow (by norm_num))]
    _ ≤ 32 * ((∫ ω, ‖O ω‖ ^ 3 ∂ρ) +
        gaussianCompanionThirdMomentConstant * ∫ ω, ‖O ω‖ ^ 3 ∂ρ) := by
      gcongr
    _ = 896 * ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
      norm_num [gaussianCompanionThirdMomentConstant]
      ring

/-- The original endpoint on the canonical replacement space has exactly the law of the user's
original independent sum. -/
private theorem map_sum_replacementOriginal_eq
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i)) (h_indep : iIndepFun X μ) :
    (bentkusReplacementMeasure μ X).map
        (fun ω ↦ ∑ i, replacementOriginal (d := d) i ω) =
      μ.map (fun ω ↦ ∑ i, X i ω) := by
  let ρ := bentkusReplacementMeasure μ X
  let σ := independentLawProduct μ X
  let sumMap : (Fin n → EuclideanSpace ℝ (Fin d)) →
      EuclideanSpace ℝ (Fin d) := fun x ↦ ∑ i, x i
  have hsum : Measurable sumMap := by
    dsimp only [sumMap]
    fun_prop
  have hfst : MeasurePreserving Prod.fst ρ σ := by
    letI : IsProbabilityMeasure σ := isProbabilityMeasure_independentLawProduct hXm
    dsimp only [ρ, σ, bentkusReplacementMeasure]
    exact measurePreserving_fst
  calc
    ρ.map (fun ω ↦ ∑ i, replacementOriginal (d := d) i ω) =
        (ρ.map Prod.fst).map sumMap := by
      rw [Measure.map_map hsum measurable_fst]
      rfl
    _ = σ.map sumMap := by rw [hfst.map_eq]
    _ = μ.map (fun ω ↦ ∑ i, X i ω) :=
      (map_sum_eq_map_sum_independentLawProduct hXm h_indep).symm

/-- The original leave-one-out sum on the replacement space has the user's original
leave-one-out law. -/
private theorem map_bentkusLeaveOneOut_replacementOriginal_eq
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i)) (h_indep : iIndepFun X μ)
    (k : Fin (n + 1)) :
    (bentkusReplacementMeasure μ X).map
        (bentkusLeaveOneOut
          (fun i ↦ replacementOriginal (d := d) i) k) =
      μ.map (bentkusLeaveOneOut X k) := by
  let ρ := bentkusReplacementMeasure μ X
  let σ := independentLawProduct μ X
  let F : (Fin (n + 1) → EuclideanSpace ℝ (Fin d)) →
      EuclideanSpace ℝ (Fin d) := fun z ↦ ∑ i ∈ Finset.univ.erase k, z i
  have hF : Measurable F := by
    dsimp only [F]
    fun_prop
  have hfst : MeasurePreserving Prod.fst ρ σ := by
    letI : IsProbabilityMeasure σ := isProbabilityMeasure_independentLawProduct hXm
    dsimp only [ρ, σ, bentkusReplacementMeasure]
    exact measurePreserving_fst
  have hfamily : μ.map (fun ω i ↦ X i ω) = σ := by
    simpa only [σ] using map_family_eq_independentLawProduct hXm h_indep
  calc
    ρ.map (bentkusLeaveOneOut
        (fun i ↦ replacementOriginal (d := d) i) k) =
        (ρ.map Prod.fst).map F := by
      rw [Measure.map_map hF measurable_fst]
      rfl
    _ = σ.map F := by rw [hfst.map_eq]
    _ = (μ.map (fun ω i ↦ X i ω)).map F := by rw [hfamily]
    _ = μ.map (bentkusLeaveOneOut X k) := by
      rw [Measure.map_map hF (measurable_pi_lambda _ hXm)]
      rfl

/-- The original and Gaussian leave-one-out sums are independent on the canonical replacement
space. -/
private theorem indepFun_bentkusLeaveOneOut_replacementOriginal_gaussian
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i)) (k : Fin (n + 1)) :
    bentkusLeaveOneOut
        (fun i ↦ replacementOriginal (d := d) i) k
      ⟂ᵢ[bentkusReplacementMeasure μ X]
    bentkusLeaveOneOut
        (fun i ↦ replacementGaussian (d := d) i) k := by
  let F : (Fin (n + 1) → EuclideanSpace ℝ (Fin d)) →
      EuclideanSpace ℝ (Fin d) := fun z ↦ ∑ i ∈ Finset.univ.erase k, z i
  have hF : Measurable F := by
    dsimp only [F]
    fun_prop
  have hblocks :=
    (indepFun_replacement_blocks (μ := μ) (X := X) hXm).comp hF hF
  convert hblocks using 1 <;> rfl

/-- The smooth endpoint difference is the expected endpoint difference on Bentkus's canonical
replacement space. -/
private theorem integral_convexSetCutoff_endpoint_eq
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) :
    (∫ x, convexSetCutoff s ε x ∂(μ.map (fun ω ↦ ∑ i, X i ω))) -
        ∫ x, convexSetCutoff s ε x ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ ω,
        (convexSetCutoff s ε
            (∑ i, replacementOriginal (d := d) i ω) -
          convexSetCutoff s ε
            (∑ i, replacementGaussian (d := d) i ω))
        ∂(bentkusReplacementMeasure μ X) := by
  let ρ := bentkusReplacementMeasure μ X
  let O : Fin n → _ → EuclideanSpace ℝ (Fin d) :=
    fun i ↦ replacementOriginal (d := d) i
  let G : Fin n → _ → EuclideanSpace ℝ (Fin d) :=
    fun i ↦ replacementGaussian (d := d) i
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hOmap : ρ.map (fun ω ↦ ∑ i, O i ω) =
      μ.map (fun ω ↦ ∑ i, X i ω) := map_sum_replacementOriginal_eq hXm h_indep
  have hGmap : ρ.map (fun ω ↦ ∑ i, G i ω) =
      stdGaussian (EuclideanSpace ℝ (Fin d)) :=
    map_sum_replacementGaussian_eq_stdGaussian hXm hX3 h_indep hidentity
  have hOmeas : Measurable (fun ω ↦ ∑ i, O i ω) := by
    dsimp only [O, replacementOriginal]
    fun_prop
  have hGmeas : Measurable (fun ω ↦ ∑ i, G i ω) := by
    dsimp only [G, replacementGaussian]
    fun_prop
  have hOintegral :
      (∫ x, convexSetCutoff s ε x ∂(μ.map (fun ω ↦ ∑ i, X i ω))) =
        ∫ ω, convexSetCutoff s ε (∑ i, O i ω) ∂ρ := by
    rw [← hOmap]
    exact integral_map hOmeas.aemeasurable
      (measurable_convexSetCutoff s ε).aestronglyMeasurable
  have hGintegral :
    (∫ x, convexSetCutoff s ε x ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) =
        ∫ ω, convexSetCutoff s ε (∑ i, G i ω) ∂ρ := by
    rw [← hGmap]
    exact integral_map hGmeas.aemeasurable
      (measurable_convexSetCutoff s ε).aestronglyMeasurable
  have hOint : Integrable (fun ω ↦ convexSetCutoff s ε (∑ i, O i ω)) ρ := by
    refine Integrable.of_bound
      ((measurable_convexSetCutoff s ε).comp hOmeas).aestronglyMeasurable 1 ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (convexSetCutoff_nonneg s ε _)]
    exact convexSetCutoff_le_one s ε _
  have hGint : Integrable (fun ω ↦ convexSetCutoff s ε (∑ i, G i ω)) ρ := by
    refine Integrable.of_bound
      ((measurable_convexSetCutoff s ε).comp hGmeas).aestronglyMeasurable 1 ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (convexSetCutoff_nonneg s ε _)]
    exact convexSetCutoff_le_one s ε _
  rw [hOintegral, hGintegral]
  exact (integral_sub hOint hGint).symm

/-- Bentkus (3.4) for the actual cutoff and canonical replacement space, with the sign oriented as
the original-minus-Gaussian smooth error used by the smoothing inequality. -/
theorem integral_convexSetCutoff_endpoint_eq_neg_rotation
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : Convexity.IsConvexSet ℝ s)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ x, convexSetCutoff s ε x ∂(μ.map (fun ω ↦ ∑ i, X i ω))) -
        ∫ x, convexSetCutoff s ε x ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      -∫ ω, ∑ i, (∫ α in (0 : ℝ)..Real.pi / 2,
          (fderiv ℝ (convexSetCutoff s ε)
              (bentkusRotatedSum α
                (fun j ↦ replacementOriginal (d := d) j)
                (fun j ↦ replacementGaussian (d := d) j) ω))
            (bentkusRotatedDeriv α
              (replacementOriginal (d := d) i)
              (replacementGaussian (d := d) i) ω))
        ∂(bentkusReplacementMeasure μ X) := by
  let ρ := bentkusReplacementMeasure μ X
  let O : Fin n → _ → EuclideanSpace ℝ (Fin d) :=
    fun i ↦ replacementOriginal (d := d) i
  let G : Fin n → _ → EuclideanSpace ℝ (Fin d) :=
    fun i ↦ replacementGaussian (d := d) i
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  rw [integral_convexSetCutoff_endpoint_eq hXm hX3 h_indep hidentity s ε]
  have hrot := integral_sum_intervalIntegral_fderiv_bentkusRotated_eq
    ρ (convexSetCutoff s ε) (contDiff_convexSetCutoff hs hε) O G
  change (∫ ω, convexSetCutoff s ε (∑ i, O i ω) -
      convexSetCutoff s ε (∑ i, G i ω) ∂ρ) = -_
  rw [hrot]
  rw [← integral_neg]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by simp only [neg_sub])

/-- The derivative of Bentkus's cutoff, packaged with the exact `NNReal` Lipschitz constant needed
by the reusable Taylor remainder theorem. -/
private lemma lipschitzWith_fderiv_convexSetCutoff
    {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith ⟨8 / ε ^ 2, div_nonneg (by norm_num) (sq_nonneg ε)⟩
      (fderiv ℝ (convexSetCutoff s ε)) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  have h := norm_fderiv_convexSetCutoff_sub_le hs hε x y
  change ‖fderiv ℝ (convexSetCutoff s ε) x -
      fderiv ℝ (convexSetCutoff s ε) y‖ ≤
    (8 / ε ^ 2) * ‖x - y‖
  calc
    ‖fderiv ℝ (convexSetCutoff s ε) x -
        fderiv ℝ (convexSetCutoff s ε) y‖ ≤
      8 * ‖x - y‖ / ε ^ 2 := h
    _ = (8 / ε ^ 2) * ‖x - y‖ := by ring

/-- Bentkus's two-shift Taylor bound specialized to the convex-set cutoff.  This is the exact
pointwise remainder majorant used before moment cancellation in (3.13) and (3.14). -/
private lemma norm_twoShift_convexSetCutoff_remainder_le
    {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε)
    (x v w : EuclideanSpace ℝ (Fin d)) :
    ‖(convexSetCutoff s ε (x + v + w) - convexSetCutoff s ε (x + v)) -
        (fderiv ℝ (convexSetCutoff s ε) x) w‖ ≤
      (8 / ε ^ 2) * ‖w‖ * (‖v‖ + ‖w‖ / 2) := by
  have h := norm_twoShiftTaylorRemainder_le (convexSetCutoff s ε)
    (contDiff_convexSetCutoff hs hε)
    (lipschitzWith_fderiv_convexSetCutoff hs hε) x v w
  change ‖(convexSetCutoff s ε (x + v + w) - convexSetCutoff s ε (x + v)) -
      (fderiv ℝ (convexSetCutoff s ε) x) w‖ ≤
    (8 / ε ^ 2) * ‖w‖ * (‖v‖ + ‖w‖ / 2) at h
  exact h

/-- First-order integral Taylor formula for the standard Gaussian density. -/
lemma standardGaussianDensity_add_taylor_one
    {d : ℕ} (x a : EuclideanSpace ℝ (Fin d)) :
    standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (x + a) =
      standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x +
        ∫ t in (0 : ℝ)..1, standardGaussianDensityD1 (x + t • a) a := by
  have hf : ContDiff ℝ 1
      (standardGaussianDensity (EuclideanSpace ℝ (Fin d))) := by
    rw [contDiff_one_iff_fderiv]
    refine ⟨fun y ↦ (hasFDerivAt_standardGaussianDensity y).differentiableAt, ?_⟩
    have hc : ContDiff ℝ 0
        (fderiv ℝ (standardGaussianDensity (EuclideanSpace ℝ (Fin d)))) := by
      rw [contDiff_clm_apply_iff]
      intro h
      have heq : (fun z : EuclideanSpace ℝ (Fin d) ↦
          (fderiv ℝ (standardGaussianDensity (EuclideanSpace ℝ (Fin d))) z) h) =
          fun z ↦ standardGaussianDensityD1 z h := by
        funext z
        exact fderiv_standardGaussianDensity_apply z h
      rw [heq]
      exact contDiff_zero.mpr (continuous_standardGaussianDensityD1 h)
    exact hc.continuous
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := standardGaussianDensity (EuclideanSpace ℝ (Fin d)))
    (x := x) (y := a) (n := 0) (fun _ _ ↦ hf.contDiffAt)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    iteratedFDeriv_zero_apply] at ht
  rw [show (0 : ℕ) + 1 = 1 by norm_num] at ht
  simp only [iteratedFDeriv_one_apply,
    fderiv_standardGaussianDensity_apply] at ht
  simpa only [pow_zero, one_smul] using ht

/-- Translation of a Gaussian-density integral in the Gaussian coordinate.  This is the
change-of-variables step in Bentkus (3.27), before the density is expanded by (3.28). -/
private lemma integral_mul_standardGaussianDensity_translate
    {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) :
    (∫ u, f (u + v) *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) u ∂volume) =
      ∫ u, f u *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u - v) ∂volume := by
  let g : EuclideanSpace ℝ (Fin d) → ℝ := fun u ↦
    f u * standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u - v)
  have htranslate := integral_add_right_eq_self (μ := volume) g v
  simpa only [g, add_sub_cancel_right] using htranslate

/-- Measure-level density translation for an affine Gaussian coordinate.  Supplying `L v = r`
moves the shift `r` out of the cutoff and into the standard-Gaussian density. -/
theorem integral_fderiv_convexSetCutoff_affine_translate
    {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))} (ε : ℝ)
    (a r x v : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hLv : L v = r) :
    (∫ u, (fderiv ℝ (convexSetCutoff s ε) (a + L u + r)) x
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) =
      ∫ u, (fderiv ℝ (convexSetCutoff s ε) (a + L u)) x *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u - v) ∂volume := by
  let f : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun u ↦ (fderiv ℝ (convexSetCutoff s ε) (a + L u)) x
  have hdensity :
      (∫ u, (fderiv ℝ (convexSetCutoff s ε) (a + L u + r)) x
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) =
        ∫ u, (fderiv ℝ (convexSetCutoff s ε) (a + L u + r)) x *
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) u ∂volume := by
    rw [stdGaussian_eq_withDensity_standardGaussianDensityReal,
      integral_withDensity_eq_integral_toReal_smul]
    · apply integral_congr_ae
      filter_upwards with u
      rw [ENNReal.toReal_ofReal (standardGaussianDensityReal_nonneg _)]
      simp only [smul_eq_mul, standardGaussianDensityReal_eq_standardGaussianDensity]
      ring
    · exact measurable_standardGaussianDensityReal.ennreal_ofReal
    · filter_upwards with u
      simp
  rw [hdensity]
  have htranslate := integral_mul_standardGaussianDensity_translate f v
  rw [show (fun u ↦
      (fderiv ℝ (convexSetCutoff s ε) (a + L u + r)) x *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) u) =
      fun u ↦ f (u + v) *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) u by
      funext u
      dsimp only [f]
      rw [map_add, hLv]
      congr 2
      abel_nf]
  exact htranslate

/-- Shifted form of the cutoff-derivative Gaussian integration-by-parts estimate.  Translating
the density by `b` translates the affine shell base by `-L b`; no Jacobian or norm factor is
introduced.  This is the deterministic estimate inserted into the remainder in Bentkus
(3.30)--(3.32). -/
private theorem convexSetCutoffDirectionalPullback_shifted_D2_shell_bound
    {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hsclosed : IsClosed s) (hs : Convexity.IsConvexSet ℝ s)
    {ε : ℝ} (hε : 0 < ε)
    (a x : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (w h b : EuclideanSpace ℝ (Fin d)) :
    |∫ u, convexSetCutoffDirectionalPullback s ε a x L u *
        standardGaussianDensityD2 (u + b) w h ∂volume| ≤
      ((8 / ε ^ 2) * ‖L‖ * ‖x‖) * ‖h‖ *
        ∫ u in (fun u ↦ (a - L b) + L u) ⁻¹'
            (Metric.cthickening ε s \ interior s),
          |standardGaussianDensityD1 u w| := by
  let a' := a - L b
  let g : EuclideanSpace ℝ (Fin d) → ℝ := fun u ↦
    convexSetCutoffDirectionalPullback s ε a' x L u *
      standardGaussianDensityD2 u w h
  have htranslate := integral_add_right_eq_self (μ := volume) g b
  have hleft :
      (∫ u, convexSetCutoffDirectionalPullback s ε a x L u *
          standardGaussianDensityD2 (u + b) w h ∂volume) =
        ∫ u, convexSetCutoffDirectionalPullback s ε a' x L u *
          standardGaussianDensityD2 u w h ∂volume := by
    calc
      (∫ u, convexSetCutoffDirectionalPullback s ε a x L u *
          standardGaussianDensityD2 (u + b) w h ∂volume) =
          ∫ u, g (u + b) ∂volume := by
        apply integral_congr_ae
        filter_upwards with u
        dsimp only [g, a', convexSetCutoffDirectionalPullback]
        congr 2
        rw [map_add]
        abel_nf
      _ = ∫ u, g u ∂volume := htranslate
      _ = ∫ u, convexSetCutoffDirectionalPullback s ε a' x L u *
          standardGaussianDensityD2 u w h ∂volume := rfl
  rw [hleft]
  simpa only [a'] using
    convexSetCutoffDirectionalPullback_D2_shell_bound
      hsclosed hs hε a' x L w h

/-- The exact shifted second-density term produced by the two-parameter Taylor formula (3.28).
This is Bentkus's integrand in (3.32), before averaging the Taylor parameters and the independent
random shifts. -/
theorem convexSetCutoffDirectionalPullback_twoShift_D2_shell_bound
    {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hsclosed : IsClosed s) (hs : Convexity.IsConvexSet ℝ s)
    {ε : ℝ} (hε : 0 < ε)
    (a x : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (v w : EuclideanSpace ℝ (Fin d)) (t r : ℝ) :
    |∫ u, convexSetCutoffDirectionalPullback s ε a x L u *
        standardGaussianDensityD2
          (u + r • (v + t • w)) w (v + t • w) ∂volume| ≤
      ((8 / ε ^ 2) * ‖L‖ * ‖x‖) * ‖v + t • w‖ *
        ∫ u in
            (fun u ↦
              (a - L (r • (v + t • w))) + L u) ⁻¹'
                (Metric.cthickening ε s \ interior s),
          |standardGaussianDensityD1 u w| := by
  exact convexSetCutoffDirectionalPullback_shifted_D2_shell_bound
    hsclosed hs hε a x L w (v + t • w) (r • (v + t • w))

private theorem integral_fderiv_convexSetCutoff_affineGaussian_eq_neg_D1
    {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε)
    (P B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (r r' : EuclideanSpace ℝ (Fin d)) (hPB : P (B r') = r') :
    (∫ u, (fderiv ℝ (convexSetCutoff s ε) (P u + r)) r' *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) u ∂volume) =
      -∫ u, convexSetCutoff s ε (P u + r) *
        standardGaussianDensityD1 u (B r') ∂volume := by
  let f : EuclideanSpace ℝ (Fin d) → ℝ := fun u ↦ convexSetCutoff s ε (P u + r)
  let C : NNReal := ⟨2 / ε, div_nonneg (by norm_num) hε.le⟩
  have hcutDiff : Differentiable ℝ (convexSetCutoff s ε) :=
    (contDiff_convexSetCutoff hs hε).differentiable (by norm_num)
  have hcutLip : LipschitzWith C (convexSetCutoff s ε) := by
    apply lipschitzWith_of_nnnorm_fderiv_le hcutDiff
    intro x
    change ‖fderiv ℝ (convexSetCutoff s ε) x‖ ≤ 2 / ε
    exact norm_fderiv_convexSetCutoff_le hs hε x
  have haffineLip : LipschitzWith ‖P‖₊ (fun u ↦ P u + r) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    change ‖(P x + r) - (P y + r)‖ ≤ ‖P‖ * ‖x - y‖
    simpa only [add_sub_add_right_eq_sub, ← map_sub] using P.le_opNorm (x - y)
  have hfLip : LipschitzWith (C * ‖P‖₊) f := by
    simpa only [f, Function.comp_def] using hcutLip.comp haffineLip
  have hfDiff : Differentiable ℝ f := by
    dsimp only [f]
    fun_prop
  have hibp := integral_fderiv_mul_standardGaussianDensity_eq_neg hfLip hfDiff (B r')
  have hfderiv (u : EuclideanSpace ℝ (Fin d)) :
      (fderiv ℝ f u) (B r') =
        (fderiv ℝ (convexSetCutoff s ε) (P u + r)) r' := by
    have hT : HasFDerivAt (fun z ↦ P z + r) P u := P.hasFDerivAt.add_const r
    have hcomp := (hcutDiff (P u + r)).hasFDerivAt.comp u hT
    rw [show f = (convexSetCutoff s ε) ∘ (fun z ↦ P z + r) by rfl,
      hcomp.fderiv, ContinuousLinearMap.comp_apply, hPB]
  simpa only [hfderiv, f] using hibp

private theorem integral_fderiv_convexSetCutoff_scaled_stdGaussian_eq_neg_D1
    {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε)
    {q : ℝ} (hq : q ≠ 0) (r h : EuclideanSpace ℝ (Fin d)) :
    (∫ u, (fderiv ℝ (convexSetCutoff s ε) (q • u + r)) h
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) =
      -∫ u, convexSetCutoff s ε (q • u + r) *
        standardGaussianDensityD1 u (q⁻¹ • h) ∂volume := by
  let P : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    q • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))
  let B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    q⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))
  have hPB : P (B h) = h := by
    dsimp only [P, B]
    simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, smul_smul]
    rw [mul_inv_cancel₀ hq, one_smul]
  have hbase := integral_fderiv_convexSetCutoff_affineGaussian_eq_neg_D1
    hs hε P B r h hPB
  have hdensity :
      (∫ u, (fderiv ℝ (convexSetCutoff s ε) (P u + r)) h
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) =
        ∫ u, (fderiv ℝ (convexSetCutoff s ε) (P u + r)) h *
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) u ∂volume := by
    rw [stdGaussian_eq_withDensity_standardGaussianDensityReal,
      integral_withDensity_eq_integral_toReal_smul]
    · apply integral_congr_ae
      filter_upwards with u
      rw [ENNReal.toReal_ofReal (standardGaussianDensityReal_nonneg _)]
      simp only [smul_eq_mul, standardGaussianDensityReal_eq_standardGaussianDensity]
      ring
    · exact measurable_standardGaussianDensityReal.ennreal_ofReal
    · filter_upwards with u
      simp
  rw [show (∫ u, (fderiv ℝ (convexSetCutoff s ε) (q • u + r)) h
      ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) =
      ∫ u, (fderiv ℝ (convexSetCutoff s ε) (P u + r)) h
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) by rfl,
    hdensity, hbase]
  rfl

theorem integral_fderiv_convexSetCutoff_scaled_unwhitening_stdGaussian_eq_neg_D1
    {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    {q : ℝ} (hq : q ≠ 0) (r r' : EuclideanSpace ℝ (Fin d)) :
    let e := bentkusWhiteningEquiv S hS
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
    (∫ u, (fderiv ℝ (convexSetCutoff s ε) (P (q • u) + r)) r'
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) =
      -∫ u, convexSetCutoff s ε (P (q • u) + r) *
        standardGaussianDensityD1 u (q⁻¹ • B r') ∂volume := by
  let e := bentkusWhiteningEquiv S hS
  let P := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  let Pq : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) := q • P
  let Bq : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) := q⁻¹ • B
  have hPB (x : EuclideanSpace ℝ (Fin d)) : P (B x) = x := by
    dsimp only [P, B, e]
    exact (bentkusWhiteningEquiv S hS).symm_apply_apply x
  have hPqBq : Pq (Bq r') = r' := by
    dsimp only [Pq, Bq]
    simp only [_root_.smul_apply, smul_smul, map_smul, hPB]
    rw [inv_mul_cancel₀ hq, one_smul]
  have hbase := integral_fderiv_convexSetCutoff_affineGaussian_eq_neg_D1
    hs hε Pq Bq r r' hPqBq
  have hdensity :
      (∫ u, (fderiv ℝ (convexSetCutoff s ε) (Pq u + r)) r'
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) =
        ∫ u, (fderiv ℝ (convexSetCutoff s ε) (Pq u + r)) r' *
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) u ∂volume := by
    rw [stdGaussian_eq_withDensity_standardGaussianDensityReal,
      integral_withDensity_eq_integral_toReal_smul]
    · apply integral_congr_ae
      filter_upwards with u
      rw [ENNReal.toReal_ofReal (standardGaussianDensityReal_nonneg _)]
      simp only [smul_eq_mul, standardGaussianDensityReal_eq_standardGaussianDensity]
      ring
    · exact measurable_standardGaussianDensityReal.ennreal_ofReal
    · filter_upwards with u
      simp
  change (∫ u, (fderiv ℝ (convexSetCutoff s ε) (P (q • u) + r)) r'
      ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) = _
  rw [show (∫ u, (fderiv ℝ (convexSetCutoff s ε) (P (q • u) + r)) r'
      ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) =
      ∫ u, (fderiv ℝ (convexSetCutoff s ε) (Pq u + r)) r'
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) by
        apply integral_congr_ae
        filter_upwards with u
        dsimp only [Pq]
        rw [_root_.smul_apply, map_smul],
    hdensity, hbase]
  simp_rw [Pq, Bq, _root_.smul_apply, map_smul]
  rfl

/-- First-order Gaussian integration by parts after undoing a positive-definite covariance
whitening.  This is the deterministic identity used in Bentkus (3.16)--(3.19). -/
private theorem integral_fderiv_convexSetCutoff_unwhitening_eq_neg_D1
    {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (r r' : EuclideanSpace ℝ (Fin d)) :
    let e := bentkusWhiteningEquiv S hS
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
    (∫ u, (fderiv ℝ (convexSetCutoff s ε) (P u + r)) r' *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) u ∂volume) =
      -∫ u, convexSetCutoff s ε (P u + r) *
        standardGaussianDensityD1 u (B r') ∂volume := by
  let e := bentkusWhiteningEquiv S hS
  let P := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  let f : EuclideanSpace ℝ (Fin d) → ℝ := fun u ↦ convexSetCutoff s ε (P u + r)
  let C : NNReal := ⟨2 / ε, div_nonneg (by norm_num) hε.le⟩
  have hcutDiff : Differentiable ℝ (convexSetCutoff s ε) :=
    (contDiff_convexSetCutoff hs hε).differentiable (by norm_num)
  have hcutLip : LipschitzWith C (convexSetCutoff s ε) := by
    apply lipschitzWith_of_nnnorm_fderiv_le hcutDiff
    intro x
    change ‖fderiv ℝ (convexSetCutoff s ε) x‖ ≤ 2 / ε
    exact norm_fderiv_convexSetCutoff_le hs hε x
  have haffineLip : LipschitzWith ‖P‖₊ (fun u ↦ P u + r) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    change ‖(P x + r) - (P y + r)‖ ≤ ‖P‖ * ‖x - y‖
    simpa only [add_sub_add_right_eq_sub, ← map_sub] using P.le_opNorm (x - y)
  have hfLip : LipschitzWith (C * ‖P‖₊) f := by
    simpa only [f, Function.comp_def] using hcutLip.comp haffineLip
  have hfDiff : Differentiable ℝ f := by
    dsimp only [f]
    fun_prop
  have hibp := integral_fderiv_mul_standardGaussianDensity_eq_neg hfLip hfDiff (B r')
  have hfderiv (u : EuclideanSpace ℝ (Fin d)) :
      (fderiv ℝ f u) (B r') =
        (fderiv ℝ (convexSetCutoff s ε) (P u + r)) r' := by
    have hT : HasFDerivAt (fun z ↦ P z + r) P u := P.hasFDerivAt.add_const r
    have hcomp := (hcutDiff (P u + r)).hasFDerivAt.comp u hT
    have hPBinv : P (B r') = r' := by
      dsimp only [P, B, e]
      exact (bentkusWhiteningEquiv S hS).symm_apply_apply r'
    rw [show f = (convexSetCutoff s ε) ∘ (fun z ↦ P z + r) by rfl,
      hcomp.fderiv, ContinuousLinearMap.comp_apply, hPBinv]
  simpa only [hfderiv, f, B, P, e] using hibp

/-- Measure-level form of `integral_fderiv_convexSetCutoff_unwhitening_eq_neg_D1`. -/
private theorem integral_fderiv_convexSetCutoff_unwhitening_stdGaussian_eq_neg_D1
    {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (r r' : EuclideanSpace ℝ (Fin d)) :
    let e := bentkusWhiteningEquiv S hS
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
    (∫ u, (fderiv ℝ (convexSetCutoff s ε) (P u + r)) r'
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) =
      -∫ u, convexSetCutoff s ε (P u + r) *
        standardGaussianDensityD1 u (B r') ∂volume := by
  let e := bentkusWhiteningEquiv S hS
  let P := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  have hbase := integral_fderiv_convexSetCutoff_unwhitening_eq_neg_D1
    hs hε S hS r r'
  dsimp only at hbase ⊢
  rw [stdGaussian_eq_withDensity_standardGaussianDensityReal,
    integral_withDensity_eq_integral_toReal_smul] 
  · simp_rw [ENNReal.toReal_ofReal (standardGaussianDensityReal_nonneg _)]
    simpa only [smul_eq_mul, standardGaussianDensityReal_eq_standardGaussianDensity,
      mul_comm, e, P, B] using hbase
  · exact measurable_standardGaussianDensityReal.ennreal_ofReal
  · filter_upwards with x
    simp

/-- The linear Gaussian-density term in Bentkus (3.17) vanishes by centering of the rotated
derivative. -/
theorem integral_standardGaussianDensityD1_whitened_replacementRotatedDeriv_eq_zero
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i)) (hX3 : ∀ i, MemLp (X i) 3 μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (i : Fin n) (α : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ∫ ω, standardGaussianDensityD1 x
        (B (bentkusRotatedDeriv α
          (replacementOriginal (d := d) i)
          (replacementGaussian (d := d) i) ω))
      ∂(bentkusReplacementMeasure μ X) = 0 := by
  let ρ := bentkusReplacementMeasure μ X
  let O := replacementOriginal (d := d) i
  let G := replacementGaussian (d := d) i
  let R' := bentkusRotatedDeriv α O G
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hO3 : MemLp O 3 ρ := memLp_replacementOriginal hXm hX3 i
  have hG3 : MemLp G 3 ρ := memLp_three_replacementGaussian hXm i
  have hOint : Integrable O ρ := hO3.integrable (by norm_num)
  have hGint : Integrable G ρ := hG3.integrable (by norm_num)
  have hO0 : ∫ ω, O ω ∂ρ = 0 := by
    simpa only [O, ρ] using integral_replacementOriginal_eq hXm i |>.trans (hX0 i)
  have hG0 : ∫ ω, G ω ∂ρ = 0 := by
    simpa only [G, ρ] using integral_replacementGaussian_eq_zero hXm i
  have hR'int : Integrable R' ρ := by
    change Integrable ((-(Real.sin α)) • O + (Real.cos α) • G) ρ
    exact (hOint.smul (-(Real.sin α))).add (hGint.smul (Real.cos α))
  have hR'0 : ∫ ω, R' ω ∂ρ = 0 :=
    integral_bentkusRotatedDeriv_eq_zero hOint hGint hO0 hG0 α
  have hBR'int : Integrable (fun ω ↦ B (R' ω)) ρ := B.integrable_comp hR'int
  have hBR'0 : ∫ ω, B (R' ω) ∂ρ = 0 := by
    rw [B.integral_comp_comm hR'int, hR'0, map_zero]
  change ∫ ω, standardGaussianDensityD1 x (B (R' ω)) ∂ρ = 0
  have hinner : ∫ ω, inner ℝ x (B (R' ω)) ∂ρ = 0 := by
    rw [integral_inner hBR'int x, hBR'0]
    simp
  unfold standardGaussianDensityD1
  rw [show (fun ω ↦
      -inner ℝ x (B (R' ω)) * standardGaussianDensity
        (EuclideanSpace ℝ (Fin d)) x) =
      fun ω ↦ (-standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x) *
        inner ℝ x (B (R' ω)) by funext ω; ring,
    integral_const_mul, hinner, mul_zero]

/-- The quadratic Gaussian-density term in Bentkus (3.18) vanishes by covariance matching of
the original summand and its Gaussian companion. -/
theorem integral_standardGaussianDensityD2_whitened_replacementRotated_eq_zero
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i)) (hX3 : ∀ i, MemLp (X i) 3 μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (i : Fin n) (α : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ∫ ω, standardGaussianDensityD2 x
        (B (bentkusRotated α
          (replacementOriginal (d := d) i)
          (replacementGaussian (d := d) i) ω))
        (B (bentkusRotatedDeriv α
          (replacementOriginal (d := d) i)
          (replacementGaussian (d := d) i) ω))
      ∂(bentkusReplacementMeasure μ X) = 0 := by
  let l : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := (innerSL ℝ x).comp B
  let Bprod : EuclideanSpace ℝ (Fin d) →L[ℝ]
      EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    (ContinuousLinearMap.mul ℝ ℝ).bilinearComp l l
  let Binner : EuclideanSpace ℝ (Fin d) →L[ℝ]
      EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp B B
  let Q : EuclideanSpace ℝ (Fin d) →L[ℝ]
      EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x • (Bprod - Binner)
  have hQ := integral_bilin_replacementRotated_replacementRotatedDeriv_eq_zero
    hXm hX3 hX0 i Q α
  rw [show (fun ω ↦ standardGaussianDensityD2 x
      (B (bentkusRotated α
        (replacementOriginal (d := d) i)
        (replacementGaussian (d := d) i) ω))
      (B (bentkusRotatedDeriv α
        (replacementOriginal (d := d) i)
        (replacementGaussian (d := d) i) ω))) =
      fun ω ↦ Q
        (bentkusRotated α
          (replacementOriginal (d := d) i)
          (replacementGaussian (d := d) i) ω)
        (bentkusRotatedDeriv α
          (replacementOriginal (d := d) i)
          (replacementGaussian (d := d) i) ω) by
    funext ω
    dsimp only [Q, Bprod, Binner, l]
    simp only [_root_.smul_apply, _root_.sub_apply,
      ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply]
    unfold standardGaussianDensityD2
    rw [show ((ContinuousLinearMap.mul ℝ ℝ)
        (inner ℝ x (B (bentkusRotated α
          (replacementOriginal (d := d) i)
          (replacementGaussian (d := d) i) ω))))
        (inner ℝ x (B (bentkusRotatedDeriv α
          (replacementOriginal (d := d) i)
          (replacementGaussian (d := d) i) ω))) =
      (inner ℝ x (B (bentkusRotated α
          (replacementOriginal (d := d) i)
          (replacementGaussian (d := d) i) ω))) *
        inner ℝ x (B (bentkusRotatedDeriv α
          (replacementOriginal (d := d) i)
          (replacementGaussian (d := d) i) ω)) by rfl]
    ring]
  exact hQ

/-- Conditioning on the omitted pair and whitening the Gaussian leave-one-out sum converts one
rotation derivative into the translated first-density contraction used in Bentkus (3.17)--(3.19).
-/
theorem integral_fderiv_convexSetCutoff_gaussianLeaveOneOut_eq_neg_iterated_D1
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
    let Z := fun ω ↦ (O ω, G ω)
    let r := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      Real.cos α • z.1 + Real.sin α • z.2
    let r' := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -(Real.sin α) • z.1 + Real.cos α • z.2
    (∫ ω, (fderiv ℝ (convexSetCutoff s ε) (V ω + R ω)) (R' ω) ∂ρ) =
      -∫ z, ∫ u, convexSetCutoff s ε (P u + r z) *
          standardGaussianDensityD1 u (B (r' z)) ∂volume ∂(ρ.map Z) := by
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let P := e.symm.toContinuousLinearMap
  let B := bentkusWhiteningCLM S
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let V := bentkusLeaveOneOut (fun i ↦ replacementGaussian (d := d) i) k
  let N := fun ω ↦ B (V ω)
  let R := bentkusRotated α O G
  let R' := bentkusRotatedDeriv α O G
  let Z := fun ω ↦ (O ω, G ω)
  let r := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    Real.cos α • z.1 + Real.sin α • z.2
  let r' := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -(Real.sin α) • z.1 + Real.cos α • z.2
  let τ := ρ.map Z
  let F : EuclideanSpace ℝ (Fin d) ×
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) → ℝ := fun p ↦
    (fderiv ℝ (convexSetCutoff s ε) (P p.1 + r p.2)) (r' p.2)
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hZmeas : Measurable Z := by
    dsimp only [Z, O, G, replacementOriginal, replacementGaussian]
    fun_prop
  letI : IsProbabilityMeasure τ := by
    dsimp only [τ]
    exact Measure.isProbabilityMeasure_map hZmeas.aemeasurable
  have hNmeas : Measurable N := by
    dsimp only [N, V, B, bentkusLeaveOneOut, replacementGaussian]
    fun_prop
  have hrmeas : Measurable r := by
    dsimp only [r]
    fun_prop
  have hr'meas : Measurable r' := by
    dsimp only [r']
    fun_prop
  have hO3 : MemLp O 3 ρ := memLp_replacementOriginal hXm hX3 k
  have hG3 : MemLp G 3 ρ := memLp_three_replacementGaussian hXm k
  have hR'3 : MemLp R' 3 ρ := by
    change MemLp ((-(Real.sin α)) • O + (Real.cos α) • G) 3 ρ
    exact (hO3.const_smul (-(Real.sin α))).add (hG3.const_smul (Real.cos α))
  have hr'int : Integrable r' τ := by
    apply (integrable_map_measure hr'meas.aestronglyMeasurable hZmeas.aemeasurable).2
    apply (hR'3.integrable (by norm_num)).congr
    filter_upwards with w
    rfl
  have hFmeas : Measurable F := by
    dsimp only [F]
    exact ((contDiff_convexSetCutoff hs hε).continuous_fderiv_apply (by norm_num)).measurable.comp
      (((P.continuous.comp continuous_fst).measurable.add (hrmeas.comp measurable_snd)).prodMk
        (hr'meas.comp measurable_snd))
  have hc : 0 ≤ 2 / ε := div_nonneg (by norm_num) hε.le
  have hmajor : Integrable (fun p : EuclideanSpace ℝ (Fin d) ×
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ↦
      (2 / ε) * ‖r' p.2‖)
      ((stdGaussian (EuclideanSpace ℝ (Fin d))).prod τ) :=
    (hr'int.norm.const_mul (2 / ε)).comp_snd
      (stdGaussian (EuclideanSpace ℝ (Fin d)))
  have hFint : Integrable F
      ((stdGaussian (EuclideanSpace ℝ (Fin d))).prod τ) := by
    apply hmajor.mono' hFmeas.aestronglyMeasurable
    filter_upwards with p
    rw [Real.norm_eq_abs]
    have happly := ContinuousLinearMap.le_opNorm
      (fderiv ℝ (convexSetCutoff s ε) (P p.1 + r p.2)) (r' p.2)
    calc
      |(fderiv ℝ (convexSetCutoff s ε) (P p.1 + r p.2)) (r' p.2)| =
          ‖(fderiv ℝ (convexSetCutoff s ε) (P p.1 + r p.2)) (r' p.2)‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (convexSetCutoff s ε) (P p.1 + r p.2)‖ * ‖r' p.2‖ := happly
      _ ≤ (2 / ε) * ‖r' p.2‖ := by
        exact mul_le_mul_of_nonneg_right
          (norm_fderiv_convexSetCutoff_le hs hε _) (norm_nonneg _)
  have hjoint : ρ.map (fun ω ↦ (N ω, Z ω)) =
      (stdGaussian (EuclideanSpace ℝ (Fin d))).prod τ := by
    simpa only [N, Z, V, B, S, ρ, τ] using
      map_whitened_bentkusLeaveOneOut_replacementGaussian_pair_eq_prod
        hXm hX3 h_indep hX0 hidentity k hk
  have hdisintegrate := integral_comp_pair_eq_iterated_of_map_eq_prod
    hNmeas hZmeas hjoint hFint
  have hPN (w) : P (N w) = V w := by
    change (bentkusWhiteningEquiv S hS).symm
      (bentkusWhiteningCLM S (V w)) = V w
    rw [← bentkusWhiteningEquiv_apply]
    exact (bentkusWhiteningEquiv S hS).symm_apply_apply (V w)
  have hleft : ∫ ω, F (N ω, Z ω) ∂ρ =
      ∫ ω, (fderiv ℝ (convexSetCutoff s ε) (V ω + R ω)) (R' ω) ∂ρ := by
    apply integral_congr_ae
    filter_upwards with w
    dsimp only [F]
    rw [hPN]
    rfl
  have hright (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
      (∫ u, F (u, z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) =
        -∫ u, convexSetCutoff s ε (P u + r z) *
          standardGaussianDensityD1 u (B (r' z)) ∂volume := by
    have h := integral_fderiv_convexSetCutoff_unwhitening_stdGaussian_eq_neg_D1
      hs hε S hS (r z) (r' z)
    dsimp only at h
    have hB : (bentkusWhiteningEquiv S hS).toContinuousLinearMap (r' z) =
        B (r' z) := bentkusWhiteningEquiv_apply S hS (r' z)
    rw [hB] at h
    simpa only [F, P, e] using h
  rw [hleft] at hdisintegrate
  calc
    (∫ ω, (fderiv ℝ (convexSetCutoff s ε) (V ω + R ω)) (R' ω) ∂ρ) =
        ∫ z, ∫ u, F (u, z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ∂τ :=
      hdisintegrate
    _ = ∫ z, -(∫ u, convexSetCutoff s ε (P u + r z) *
          standardGaussianDensityD1 u (B (r' z)) ∂volume) ∂τ := by
      apply integral_congr_ae
      filter_upwards with z
      exact hright z
    _ = -∫ z, ∫ u, convexSetCutoff s ε (P u + r z) *
          standardGaussianDensityD1 u (B (r' z)) ∂volume ∂τ := integral_neg _

/-- One-set composition of the smooth replacement estimate with the two Gaussian shell bounds.
This is the exact interface between Bentkus's analytic (3.6) estimate and Lemma 2.1. -/
theorem bentkus_oneSet_taylorEstimate_of_smoothCutoff_and_shell
    {Ks C β ε : ℝ} (hKs : 0 ≤ Ks) (hC : 0 ≤ C) (hβ : 0 ≤ β) (hε : 0 < ε)
    {d : ℕ} {ν : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure ν]
    {A : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A)
    (hAconv : Convexity.IsConvexSet ℝ A)
    (hOuterSmooth :
      |∫ x, convexSetCutoff A ε x ∂ν -
          ∫ x, convexSetCutoff A ε x
            ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))| ≤
        Ks * (d : ℝ) ^ (1 / 4 : ℝ) * (β + C * β ^ 2 / ε))
    (hInnerSmooth :
      |∫ x, convexSetCutoff (convexInnerParallel A ε) ε x ∂ν -
          ∫ x, convexSetCutoff (convexInnerParallel A ε) ε x
            ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))| ≤
        Ks * (d : ℝ) ^ (1 / 4 : ℝ) * (β + C * β ^ 2 / ε))
    (hOuterShell :
      (stdGaussian (EuclideanSpace ℝ (Fin d))).real
          (Metric.cthickening ε (closure A) \ A) ≤
        4 * (d : ℝ) ^ (1 / 4 : ℝ) * ε)
    (hInnerShell :
      (stdGaussian (EuclideanSpace ℝ (Fin d))).real
          (A \ convexInnerParallel A ε) ≤
        4 * (d : ℝ) ^ (1 / 4 : ℝ) * ε) :
    |ν.real A - (stdGaussian (EuclideanSpace ℝ (Fin d))).real A| ≤
      (Ks + 4) * (d : ℝ) ^ (1 / 4 : ℝ) *
        (ε + β + C * β ^ 2 / ε) := by
  have hsmoothing := bentkus_convexSet_smoothingInequality
    ν (stdGaussian (EuclideanSpace ℝ (Fin d))) hA hAconv hε
  have hsmoothMax :
      max
          |∫ x, convexSetCutoff A ε x ∂ν -
            ∫ x, convexSetCutoff A ε x
              ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))|
          |∫ x, convexSetCutoff (convexInnerParallel A ε) ε x ∂ν -
            ∫ x, convexSetCutoff (convexInnerParallel A ε) ε x
              ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))| ≤
        Ks * (d : ℝ) ^ (1 / 4 : ℝ) * (β + C * β ^ 2 / ε) :=
    max_le hOuterSmooth hInnerSmooth
  have hshellMax :
      max
          ((stdGaussian (EuclideanSpace ℝ (Fin d))).real
            (Metric.cthickening ε (closure A) \ A))
          ((stdGaussian (EuclideanSpace ℝ (Fin d))).real
            (A \ convexInnerParallel A ε)) ≤
        4 * (d : ℝ) ^ (1 / 4 : ℝ) * ε :=
    max_le hOuterShell hInnerShell
  have hdq : 0 ≤ (d : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hquot : 0 ≤ C * β ^ 2 / ε :=
    div_nonneg (mul_nonneg hC (sq_nonneg β)) hε.le
  have hcross1 : 0 ≤ Ks * (d : ℝ) ^ (1 / 4 : ℝ) * ε :=
    mul_nonneg (mul_nonneg hKs hdq) hε.le
  have hcross2 : 0 ≤ 4 * (d : ℝ) ^ (1 / 4 : ℝ) *
      (β + C * β ^ 2 / ε) :=
    mul_nonneg (mul_nonneg (by norm_num) hdq) (add_nonneg hβ hquot)
  calc
    |ν.real A - (stdGaussian (EuclideanSpace ℝ (Fin d))).real A| ≤
        max
            |∫ x, convexSetCutoff A ε x ∂ν -
              ∫ x, convexSetCutoff A ε x
                ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))|
            |∫ x, convexSetCutoff (convexInnerParallel A ε) ε x ∂ν -
              ∫ x, convexSetCutoff (convexInnerParallel A ε) ε x
                ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))| +
          max
            ((stdGaussian (EuclideanSpace ℝ (Fin d))).real
              (Metric.cthickening ε (closure A) \ A))
            ((stdGaussian (EuclideanSpace ℝ (Fin d))).real
              (A \ convexInnerParallel A ε)) := hsmoothing
    _ ≤ Ks * (d : ℝ) ^ (1 / 4 : ℝ) * (β + C * β ^ 2 / ε) +
        4 * (d : ℝ) ^ (1 / 4 : ℝ) * ε := add_le_add hsmoothMax hshellMax
    _ ≤ (Ks + 4) * (d : ℝ) ^ (1 / 4 : ℝ) *
        (ε + β + C * β ^ 2 / ε) := by
      nlinarith


/-- It suffices to prove an induction slice for everywhere-measurable representatives.  `MemLp`
only supplies an almost-everywhere strongly measurable representative, so this lemma performs the
representative change once and transports independence, covariance, laws, means, and third
moments. -/
theorem bentkusIdentityCovarianceBoundAt_of_measurable
    {C : ℝ} {n : ℕ}
    (h : bentkusIdentityCovarianceBoundAtMeasurable.{u} C n) :
    bentkusIdentityCovarianceBoundAt.{u} C n := by
  intro d hd Ω _ μ _ X hX3 h_indep hX0 hidentity A hA hAconv
  let Xm : Fin n → Ω → EuclideanSpace ℝ (Fin d) := fun i ↦
    (hX3 i).aestronglyMeasurable.mk (X i)
  have hXm (i : Fin n) : Measurable (Xm i) :=
    (hX3 i).aestronglyMeasurable.measurable_mk
  have hEq (i : Fin n) : X i =ᵐ[μ] Xm i :=
    (hX3 i).aestronglyMeasurable.ae_eq_mk
  have hsumEq : (fun ω ↦ ∑ i, X i ω) =ᵐ[μ] fun ω ↦ ∑ i, Xm i ω := by
    filter_upwards [ae_all_iff.2 hEq] with ω hω
    exact Finset.sum_congr rfl fun i _ ↦ hω i
  have hXm3 : ∀ i, MemLp (Xm i) 3 μ := fun i ↦ (hX3 i).ae_eq (hEq i)
  have hXmindep : iIndepFun Xm μ := h_indep.congr hEq
  have hXm0 : ∀ i, ∫ ω, Xm i ω ∂μ = 0 := by
    intro i
    calc
      (∫ ω, Xm i ω ∂μ) = ∫ ω, X i ω ∂μ := (integral_congr_ae (hEq i)).symm
      _ = 0 := hX0 i
  have hXmidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, Xm i ω)) x y = inner ℝ x y := by
    intro x y
    rw [← Measure.map_congr hsumEq]
    exact hidentity x y
  have hbound := h hd μ Xm hXm hXm3 hXmindep hXm0 hXmidentity A hA hAconv
  have hmap : μ.map (fun ω ↦ ∑ i, X i ω) = μ.map (fun ω ↦ ∑ i, Xm i ω) :=
    Measure.map_congr hsumEq
  have hmom (i : Fin n) :
      (∫ ω, ‖X i ω‖ ^ 3 ∂μ) = ∫ ω, ‖Xm i ω‖ ^ 3 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hEq i] with ω hω
    rw [hω]
  rw [hmap]
  simpa only [Measure.real_def, hmom] using hbound

/- The induction hypothesis, after the exact leave-one-out reindexing and covariance whitening,
gives the Gaussian comparison used in Bentkus (3.34). -/

private theorem bentkusLeaveOneOut_error_le_of_induction
    {C : ℝ} {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hIH : bentkusIdentityCovarianceBoundAt.{u} C n)
    (hd : 0 < d) (hX3 : ∀ i, MemLp (X i) 3 μ)
    (h_indep : iIndepFun X μ) (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (k : Fin (n + 1))
    (hS : (bentkusLeaveOneOutCovarianceMatrix μ X k).PosDef)
    (A : Set (EuclideanSpace ℝ (Fin d))) (hA : MeasurableSet A)
    (hAconv : Convexity.IsConvexSet ℝ A) :
    |(μ.map (bentkusLeaveOneOut X k)).real A -
        (multivariateGaussian 0 (bentkusLeaveOneOutCovarianceMatrix μ X k)).real A| ≤
      C * (d : ℝ) ^ (1 / 4 : ℝ) *
        ∑ i : Fin n, ∫ ω,
          ‖bentkusWhiteningCLM (bentkusLeaveOneOutCovarianceMatrix μ X k)
            (X (k.succAbove i) ω)‖ ^ 3 ∂μ := by
  let R := bentkusRemovedFamily k X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hR3 : ∀ i, MemLp (R i) 3 μ := memLp_bentkusRemovedFamily hX3 k
  have hRindep : iIndepFun R μ := iIndepFun_bentkusRemovedFamily h_indep k
  have hR0 : ∀ i, ∫ ω, R i ω ∂μ = 0 :=
    integral_bentkusRemovedFamily_eq_zero hX0 k
  have hRcov : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, R i ω)) x y = x ⬝ᵥ S *ᵥ y := by
    intro x y
    rw [show (fun ω ↦ ∑ i, R i ω) = bentkusLeaveOneOut X k by
      exact sum_bentkusRemovedFamily_eq_leaveOneOut k X]
    exact (dotProduct_bentkusLeaveOneOutCovarianceMatrix_mulVec μ X k x y).symm
  have hW3 : ∀ i, MemLp (bentkusWhitenedSummand S R i) 3 μ :=
    memLp_bentkusWhitenedSummand S hR3
  have hWindep : iIndepFun (bentkusWhitenedSummand S R) μ :=
    iIndepFun_bentkusWhitenedSummand S hRindep
  have hW0 : ∀ i, ∫ ω, bentkusWhitenedSummand S R i ω ∂μ = 0 :=
    integral_bentkusWhitenedSummand_eq_zero S hR3 hR0
  have hWcov : ∀ x y,
      covarianceBilin
          (μ.map (fun ω ↦ ∑ i, bentkusWhitenedSummand S R i ω)) x y = inner ℝ x y :=
    covarianceBilin_map_sum_bentkusWhitenedSummand_eq_inner S hS hR3 hRcov
  have hbound := hIH hd μ (bentkusWhitenedSummand S R)
    hW3 hWindep hW0 hWcov (bentkusWhitenedSet S hS A)
    (measurableSet_bentkusWhitenedSet S hS hA)
    (isConvexSet_bentkusWhitenedSet S hS hAconv)
  have htransport := bentkus_convex_set_whitening_reduction
    C μ R S hS hR3 A hbound
  change |(μ.map (bentkusLeaveOneOut X k)).real A -
      (multivariateGaussian 0 S).real A| ≤ _
  rw [← sum_bentkusRemovedFamily_eq_leaveOneOut k X]
  simpa only [Measure.real_def, R, S, bentkusWhitenedSummand,
    bentkusWhiteningCLM, bentkusWhiteningMatrix, bentkusRemovedFamily] using htransport

/-- In the small-individual-second-moment branch, leave-one-out whitening costs at most the
factor `8` in the Lyapunov sum. -/
private theorem bentkusLeaveOneOut_error_le_eight_mul_of_induction
    {C : ℝ} (hC : 0 ≤ C) {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hIH : bentkusIdentityCovarianceBoundAt.{u} C n)
    (hd : 0 < d) (hX3 : ∀ i, MemLp (X i) 3 μ)
    (h_indep : iIndepFun X μ) (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (A : Set (EuclideanSpace ℝ (Fin d))) (hA : MeasurableSet A)
    (hAconv : Convexity.IsConvexSet ℝ A) :
    |(μ.map (bentkusLeaveOneOut X k)).real A -
        (multivariateGaussian 0 (bentkusLeaveOneOutCovarianceMatrix μ X k)).real A| ≤
      8 * C * (d : ℝ) ^ (1 / 4 : ℝ) *
        ∑ i : Fin n, ∫ ω, ‖X (k.succAbove i) ω‖ ^ 3 ∂μ := by
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  have hbase := bentkusLeaveOneOut_error_le_of_induction
    hIH hd hX3 h_indep hX0 k hS A hA hAconv
  have hmom :
      (∑ i : Fin n, ∫ ω, ‖bentkusWhiteningCLM S (X (k.succAbove i) ω)‖ ^ 3 ∂μ) ≤
        8 * ∑ i : Fin n, ∫ ω, ‖X (k.succAbove i) ω‖ ^ 3 ∂μ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦
      integral_norm_bentkusWhiteningCLM_leaveOneOut_pow_three_le
        hX3 h_indep hX0 hidentity k hk (hX3 (k.succAbove i))
  have hfactor : 0 ≤ C * (d : ℝ) ^ (1 / 4 : ℝ) :=
    mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  calc
    |(μ.map (bentkusLeaveOneOut X k)).real A -
        (multivariateGaussian 0 S).real A| ≤
        C * (d : ℝ) ^ (1 / 4 : ℝ) *
          ∑ i : Fin n, ∫ ω, ‖bentkusWhiteningCLM S
            (X (k.succAbove i) ω)‖ ^ 3 ∂μ := by
      simpa only [S] using hbase
    _ ≤ C * (d : ℝ) ^ (1 / 4 : ℝ) *
        (8 * ∑ i : Fin n, ∫ ω, ‖X (k.succAbove i) ω‖ ^ 3 ∂μ) :=
      mul_le_mul_of_nonneg_left hmom hfactor
    _ = 8 * C * (d : ℝ) ^ (1 / 4 : ℝ) *
        ∑ i : Fin n, ∫ ω, ‖X (k.succAbove i) ω‖ ^ 3 ∂μ := by ring

/-- Convex-distance control at two nested sets transfers an outer-shell bound, with the expected
factor two. -/
lemma measureReal_sdiff_le_add_two_mul_of_abs_sub_le
    {E : Type*} [MeasurableSpace E] {ν τ : Measure E} [IsFiniteMeasure ν]
    [IsFiniteMeasure τ] {A B : Set E} (hAB : A ⊆ B) (hA : MeasurableSet A)
    {D : ℝ} (hDA : |ν.real A - τ.real A| ≤ D)
    (hDB : |ν.real B - τ.real B| ≤ D) :
    ν.real (B \ A) ≤ τ.real (B \ A) + 2 * D := by
  rw [measureReal_sdiff (μ := ν) hAB hA,
    measureReal_sdiff (μ := τ) hAB hA]
  have hBupper : ν.real B - τ.real B ≤ D := (le_abs_self _).trans hDB
  have hAlower : τ.real A - ν.real A ≤ D := by
    simpa only [neg_sub] using (neg_le_abs (ν.real A - τ.real A)).trans hDA
  linarith

/-- Two independent standard Gaussians remain standard after an orthogonal scalar combination.
This is the Gaussian side of Bentkus's conditioning argument. -/
theorem map_prod_stdGaussian_weightedAdd_eq_stdGaussian
    {d : ℕ} {p q : ℝ} (hpq : p ^ 2 + q ^ 2 = 1) :
    ((stdGaussian (EuclideanSpace ℝ (Fin d))).prod
      (stdGaussian (EuclideanSpace ℝ (Fin d)))).map
        (fun z ↦ q • z.1 + p • z.2) =
      stdGaussian (EuclideanSpace ℝ (Fin d)) := by
  let γ := stdGaussian (BentkusEuclideanSpace d)
  let L : BentkusEuclideanSpace d × BentkusEuclideanSpace d →L[ℝ]
      BentkusEuclideanSpace d :=
    q • ContinuousLinearMap.fst ℝ (BentkusEuclideanSpace d) (BentkusEuclideanSpace d) +
      p • ContinuousLinearMap.snd ℝ (BentkusEuclideanSpace d) (BentkusEuclideanSpace d)
  have hL (z : BentkusEuclideanSpace d × BentkusEuclideanSpace d) :
      L z = q • z.1 + p • z.2 := rfl
  change (γ.prod γ).map L = γ
  dsimp only [γ, BentkusEuclideanSpace] at *
  apply IsGaussian.ext
  · change (∫ z, z ∂(γ.prod γ).map L) = ∫ z, z ∂γ
    rw [integral_id_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
    have hmean := integral_continuousLinearMap_prod (L := L)
      (IsGaussian.integrable_id (μ := γ)) (IsGaussian.integrable_id (μ := γ))
    have hmeanLeft :
        (∫ x, (L.comp (ContinuousLinearMap.inl ℝ _ _)) x ∂γ) =
          (L.comp (ContinuousLinearMap.inl ℝ _ _)) (∫ x, x ∂γ) := by
      simpa only [id_eq] using
        (L.comp (ContinuousLinearMap.inl ℝ _ _)).integral_comp_comm
          (IsGaussian.integrable_id (μ := γ))
    have hmeanRight :
        (∫ x, (L.comp (ContinuousLinearMap.inr ℝ _ _)) x ∂γ) =
          (L.comp (ContinuousLinearMap.inr ℝ _ _)) (∫ x, x ∂γ) := by
      simpa only [id_eq] using
        (L.comp (ContinuousLinearMap.inr ℝ _ _)).integral_comp_comm
          (IsGaussian.integrable_id (μ := γ))
    rw [hmean, hmeanLeft, hmeanRight, integral_id_stdGaussian]
    rw [map_zero, map_zero, zero_add]
  · ext x y
    have hmapCov := covariance_map_fun
      (μ := γ.prod γ) (Z := L)
      (X := fun z : BentkusEuclideanSpace d ↦ inner ℝ x z)
      (Y := fun z : BentkusEuclideanSpace d ↦ inner ℝ y z)
      (by fun_prop) (by fun_prop) (by fun_prop)
    have htarget2 : MemLp
        (id : BentkusEuclideanSpace d → BentkusEuclideanSpace d) 2
        ((γ.prod γ).map L) :=
      IsGaussian.memLp_two_id
    rw [covarianceBilin_apply_eq_cov htarget2]
    rw [hmapCov]
    let fx : BentkusEuclideanSpace d × BentkusEuclideanSpace d → ℝ :=
      fun z ↦ inner ℝ x z.1
    let gx : BentkusEuclideanSpace d × BentkusEuclideanSpace d → ℝ :=
      fun z ↦ inner ℝ x z.2
    let fy : BentkusEuclideanSpace d × BentkusEuclideanSpace d → ℝ :=
      fun z ↦ inner ℝ y z.1
    let gy : BentkusEuclideanSpace d × BentkusEuclideanSpace d → ℝ :=
      fun z ↦ inner ℝ y z.2
    have hdualx : MemLp (fun z : BentkusEuclideanSpace d ↦ inner ℝ x z) 2 γ := by
      simpa only [coe_innerSL_apply] using
        (IsGaussian.memLp_dual γ (innerSL ℝ x) 2 (by norm_num))
    have hdualy : MemLp (fun z : BentkusEuclideanSpace d ↦ inner ℝ y z) 2 γ := by
      simpa only [coe_innerSL_apply] using
        (IsGaussian.memLp_dual γ (innerSL ℝ y) 2 (by norm_num))
    have hfx : MemLp fx 2 (γ.prod γ) := hdualx.comp_fst γ
    have hgx : MemLp gx 2 (γ.prod γ) := hdualx.comp_snd γ
    have hfy : MemLp fy 2 (γ.prod γ) := hdualy.comp_fst γ
    have hgy : MemLp gy 2 (γ.prod γ) := hdualy.comp_snd γ
    have hcovxx : cov[fx, fy; γ.prod γ] = inner ℝ x y := by
      have hm := covariance_map_fun
        (μ := γ.prod γ) (Z := Prod.fst)
        (X := fun z : BentkusEuclideanSpace d ↦ inner ℝ x z)
        (Y := fun z : BentkusEuclideanSpace d ↦ inner ℝ y z)
        (by fun_prop) (by fun_prop) (by fun_prop)
      rw [measurePreserving_fst.map_eq] at hm
      rw [← hm, ← covarianceBilin_apply_eq_cov (IsGaussian.memLp_two_id (μ := γ)),
        covarianceBilin_stdGaussian]
      rfl
    have hcovyy : cov[gx, gy; γ.prod γ] = inner ℝ x y := by
      have hm := covariance_map_fun
        (μ := γ.prod γ) (Z := Prod.snd)
        (X := fun z : BentkusEuclideanSpace d ↦ inner ℝ x z)
        (Y := fun z : BentkusEuclideanSpace d ↦ inner ℝ y z)
        (by fun_prop) (by fun_prop) (by fun_prop)
      rw [measurePreserving_snd.map_eq] at hm
      rw [← hm, ← covarianceBilin_apply_eq_cov (IsGaussian.memLp_two_id (μ := γ)),
        covarianceBilin_stdGaussian]
      rfl
    have hcovxy : cov[fx, gy; γ.prod γ] = 0 :=
      covariance_fst_snd_prod hdualx hdualy
    have hcovyx : cov[gx, fy; γ.prod γ] = 0 := by
      rw [covariance_comm]
      exact covariance_fst_snd_prod hdualy hdualx
    rw [covarianceBilin_stdGaussian]
    change cov[fun z ↦ inner ℝ x (L z), fun z ↦ inner ℝ y (L z); γ.prod γ] =
      inner ℝ x y
    simp only [hL, inner_add_right, inner_smul_right]
    change cov[(fun z ↦ q * fx z) + fun z ↦ p * gx z,
      (fun z ↦ q * fy z) + fun z ↦ p * gy z; γ.prod γ] = inner ℝ x y
    rw [covariance_add_left (hfx.const_mul q) (hgx.const_mul p)
        ((hfy.const_mul q).add (hgy.const_mul p)),
      covariance_add_right (hfx.const_mul q) (hfy.const_mul q) (hgy.const_mul p),
      covariance_add_right (hgx.const_mul p) (hfy.const_mul q) (hgy.const_mul p),
      covariance_const_mul_left, covariance_const_mul_right]
    simp only [covariance_const_mul_left, covariance_const_mul_right,
      hcovxx, hcovxy, hcovyx, hcovyy]
    calc
      q * (q * inner ℝ x y) + p * (q * 0) +
          (q * (p * 0) + p * (p * inner ℝ x y)) =
          (p ^ 2 + q ^ 2) * inner ℝ x y := by ring
      _ = inner ℝ x y := by rw [hpq, one_mul]

/-- An arbitrary scalar Gaussian combination is a scalar multiple of a standard Gaussian. -/
theorem map_prod_stdGaussian_weightedAdd_eq_map_smul
    {d : ℕ} {p q c : ℝ} (hc : 0 < c) (hpq : p ^ 2 + q ^ 2 = c ^ 2) :
    ((stdGaussian (EuclideanSpace ℝ (Fin d))).prod
      (stdGaussian (EuclideanSpace ℝ (Fin d)))).map
        (fun z ↦ q • z.1 + p • z.2) =
      (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun x ↦ c • x) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let normalize :
      EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) →
        EuclideanSpace ℝ (Fin d) :=
    fun z ↦ (q / c) • z.1 + (p / c) • z.2
  let scale : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun x ↦ c • x
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hnormalized : (p / c) ^ 2 + (q / c) ^ 2 = 1 := by
    field_simp
    nlinarith
  have hlaw : (γ.prod γ).map normalize = γ := by
    simpa only [γ, normalize] using
      map_prod_stdGaussian_weightedAdd_eq_stdGaussian
        (d := d) (p := p / c) (q := q / c) hnormalized
  have hnormalize : Measurable normalize := by
    dsimp only [normalize]
    fun_prop
  have hscale : Measurable scale := by
    dsimp only [scale]
    fun_prop
  change (γ.prod γ).map (fun z ↦ q • z.1 + p • z.2) = γ.map scale
  calc
    (γ.prod γ).map (fun z ↦ q • z.1 + p • z.2) =
        ((γ.prod γ).map normalize).map scale := by
      rw [Measure.map_map hscale hnormalize]
      congr 1
      funext z
      dsimp only [scale, normalize, Function.comp_apply]
      rw [smul_add, smul_smul, smul_smul]
      field_simp
    _ = γ.map scale := by rw [hlaw]

/-- Convex-set distance contracts under a common independent additive noise and a common scalar
multiple.  This is the measure-level conditioning step used in Bentkus (3.31)--(3.34). -/
theorem convexDistance_map_prod_affineNoise_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [Convexity.ConvexSpace ℝ E] [Convexity.IsModuleConvexSpace ℝ E]
    {ν τ κ : Measure E} [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]
    [IsProbabilityMeasure κ] {D : ℝ} (_hD : 0 ≤ D)
    (hbound : ∀ A : Set E, MeasurableSet A → Convexity.IsConvexSet ℝ A →
      |ν.real A - τ.real A| ≤ D)
    (p : ℝ) (A : Set E) (hA : MeasurableSet A)
    (hAconv : Convexity.IsConvexSet ℝ A) :
    |((κ.prod ν).map (fun z : E × E ↦ p • z.2 + z.1)).real A -
        ((κ.prod τ).map (fun z : E × E ↦ p • z.2 + z.1)).real A| ≤ D := by
  let T : E × E → E := fun z ↦ p • z.2 + z.1
  let fiber : E → Set E := fun w ↦ (fun u ↦ p • u + w) ⁻¹' A
  have hT : Measurable T := by
    let LT : E × E →L[ℝ] E :=
      p • ContinuousLinearMap.snd ℝ E E + ContinuousLinearMap.fst ℝ E E
    change Measurable LT
    exact LT.continuous.measurable
  have hfiberMeas (w : E) : MeasurableSet (fiber w) := by
    dsimp only [fiber]
    exact hA.preimage (by fun_prop)
  have hfiberConv (w : E) : Convexity.IsConvexSet ℝ (fiber w) := by
    refine Convexity.IsConvexSet.of_convexCombPair_mem ?_
    intro a b ha hb hab x hx y hy
    change p • x + w ∈ A at hx
    change p • y + w ∈ A at hy
    change p • Convexity.convexCombPair a b ha hb hab x y + w ∈ A
    have hmem := hAconv.convexCombPair_mem hx hy ha hb hab
    rw [Convexity.convexCombPair_eq_sum] at hmem ⊢
    have hw : w = a • w + b • w := by
      calc
        w = (1 : ℝ) • w := (one_smul ℝ w).symm
        _ = (a + b) • w := by rw [hab]
        _ = a • w + b • w := add_smul a b w
    have heq : p • (a • x + b • y) + w =
        a • (p • x + w) + b • (p • y + w) := by
      calc
        p • (a • x + b • y) + w =
            p • (a • x + b • y) + (a • w + b • w) :=
          congrArg (fun z ↦ p • (a • x + b • y) + z) hw
        _ = a • (p • x + w) + b • (p • y + w) := by module
    rw [heq]
    exact hmem
  have hpre : MeasurableSet (T ⁻¹' A) := hA.preimage hT
  let Q : E × E → ℝ := fun z ↦ (T ⁻¹' A).indicator 1 z
  have hQintν : Integrable Q (κ.prod ν) := by
    dsimp only [Q]
    exact (integrable_const (μ := κ.prod ν) (1 : ℝ)).indicator hpre
  have hQintτ : Integrable Q (κ.prod τ) := by
    dsimp only [Q]
    exact (integrable_const (μ := κ.prod τ) (1 : ℝ)).indicator hpre
  have hinnerν (w : E) :
      (∫ u, Q (w, u) ∂ν) = ν.real (fiber w) := by
    rw [← integral_indicator_one (μ := ν) (hfiberMeas w)]
    apply integral_congr_ae
    filter_upwards with u
    rfl
  have hinnerτ (w : E) :
      (∫ u, Q (w, u) ∂τ) = τ.real (fiber w) := by
    rw [← integral_indicator_one (μ := τ) (hfiberMeas w)]
    apply integral_congr_ae
    filter_upwards with u
    rfl
  have hreprν : ((κ.prod ν).map T).real A =
      ∫ w, ν.real (fiber w) ∂κ := by
    rw [map_measureReal_apply hT hA]
    calc
      (κ.prod ν).real (T ⁻¹' A) = ∫ z, Q z ∂(κ.prod ν) := by
        symm
        simpa only [Q] using integral_indicator_one (μ := κ.prod ν) hpre
      _ = ∫ w, ∫ u, Q (w, u) ∂ν ∂κ := by
        have hQintν' : Integrable (Function.uncurry fun w u ↦ Q (w, u)) (κ.prod ν) := by
          apply hQintν.congr
          filter_upwards with z
          rcases z with ⟨w, u⟩
          rfl
        have hfub := integral_integral hQintν'
        change (∫ w, ∫ u, Q (w, u) ∂ν ∂κ) = ∫ z, Q z ∂(κ.prod ν) at hfub
        exact hfub.symm
      _ = ∫ w, ν.real (fiber w) ∂κ := by
        apply integral_congr_ae
        filter_upwards with w
        exact hinnerν w
  have hreprτ : ((κ.prod τ).map T).real A =
      ∫ w, τ.real (fiber w) ∂κ := by
    rw [map_measureReal_apply hT hA]
    calc
      (κ.prod τ).real (T ⁻¹' A) = ∫ z, Q z ∂(κ.prod τ) := by
        symm
        simpa only [Q] using integral_indicator_one (μ := κ.prod τ) hpre
      _ = ∫ w, ∫ u, Q (w, u) ∂τ ∂κ := by
        have hQintτ' : Integrable (Function.uncurry fun w u ↦ Q (w, u)) (κ.prod τ) := by
          apply hQintτ.congr
          filter_upwards with z
          rcases z with ⟨w, u⟩
          rfl
        have hfub := integral_integral hQintτ'
        change (∫ w, ∫ u, Q (w, u) ∂τ ∂κ) = ∫ z, Q z ∂(κ.prod τ) at hfub
        exact hfub.symm
      _ = ∫ w, τ.real (fiber w) ∂κ := by
        apply integral_congr_ae
        filter_upwards with w
        exact hinnerτ w
  have hνint : Integrable (fun w ↦ ν.real (fiber w)) κ := by
    apply hQintν.integral_prod_left.congr
    filter_upwards with w
    exact hinnerν w
  have hτint : Integrable (fun w ↦ τ.real (fiber w)) κ := by
    apply hQintτ.integral_prod_left.congr
    filter_upwards with w
    exact hinnerτ w
  rw [show (fun z : E × E ↦ p • z.2 + z.1) = T by rfl, hreprν, hreprτ,
    ← integral_sub hνint hτint]
  calc
    |∫ w, ν.real (fiber w) - τ.real (fiber w) ∂κ| ≤
        ∫ w, |ν.real (fiber w) - τ.real (fiber w)| ∂κ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _w, D ∂κ := by
      exact integral_mono (hνint.sub hτint).abs (integrable_const D) fun w ↦
        hbound (fiber w) (hfiberMeas w) (hfiberConv w)
    _ = D := by rw [integral_const, probReal_univ, one_smul]

/-- Standard-Gaussian specialization of convex-distance contraction under an orthogonal scalar
mixture. -/
private theorem convexDistance_map_prod_stdGaussian_weightedAdd_le
    {d : ℕ} {ν : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure ν]
    {D p q : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ A : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet A →
      Convexity.IsConvexSet ℝ A →
      |ν.real A - (stdGaussian (EuclideanSpace ℝ (Fin d))).real A| ≤ D)
    (hpq : p ^ 2 + q ^ 2 = 1)
    (A : Set (EuclideanSpace ℝ (Fin d))) (hA : MeasurableSet A)
    (hAconv : Convexity.IsConvexSet ℝ A) :
    |(((stdGaussian (EuclideanSpace ℝ (Fin d))).prod ν).map
          (fun z ↦ q • z.1 + p • z.2)).real A -
        (stdGaussian (EuclideanSpace ℝ (Fin d))).real A| ≤ D := by
  let E := EuclideanSpace ℝ (Fin d)
  let γ := stdGaussian E
  let Q : E → E := fun x ↦ q • x
  let κ := γ.map Q
  let F : E × E → E := fun z ↦ p • z.2 + z.1
  let W : E × E → E := fun z ↦ q • z.1 + p • z.2
  letI : IsProbabilityMeasure κ := Measure.isProbabilityMeasure_map (by fun_prop)
  have hcontract := convexDistance_map_prod_affineNoise_le
    (ν := ν) (τ := γ) (κ := κ) hD hbound p A hA hAconv
  have hκν : κ.prod ν = (γ.prod ν).map (Prod.map Q id) := by
    simpa only [κ, Q, Measure.map_id] using
      Measure.map_prod_map γ ν (by fun_prop : Measurable Q) measurable_id
  have hκγ : κ.prod γ = (γ.prod γ).map (Prod.map Q id) := by
    simpa only [κ, Q, Measure.map_id] using
      Measure.map_prod_map γ γ (by fun_prop : Measurable Q) measurable_id
  have hcomp : F ∘ Prod.map Q id = W := by
    funext z
    change p • z.2 + q • z.1 = q • z.1 + p • z.2
    abel
  have hleft : (κ.prod ν).map F = (γ.prod ν).map W := by
    rw [hκν, Measure.map_map]
    · rw [hcomp]
    · fun_prop
    · fun_prop
  have hright : (κ.prod γ).map F = γ := by
    rw [hκγ, Measure.map_map]
    · rw [hcomp]
      simpa only [W, γ] using
        map_prod_stdGaussian_weightedAdd_eq_stdGaussian (d := d) hpq
    · fun_prop
    · fun_prop
  rw [hleft, hright] at hcontract
  simpa only [W, γ] using hcontract

/-- Bentkus's scalar cutoff profile is nonincreasing. -/
private lemma bentkusProfile_antitone : Antitone bentkusProfile := by
  apply antitone_of_deriv_nonpos differentiable_bentkusProfile
  intro t
  rw [(hasDerivAt_bentkusProfile t).deriv]
  unfold bentkusProfileDeriv
  by_cases h0 : t ≤ 0
  · have hhalf : t - 1 / 2 ≤ 0 := by linarith
    have hone : t - 1 ≤ 0 := by linarith
    rw [max_eq_right h0, max_eq_right hhalf, max_eq_right hone]
    norm_num
  · have ht0 : 0 ≤ t := le_of_not_ge h0
    by_cases hhalf : t ≤ 1 / 2
    · have hhalf' : t - 1 / 2 ≤ 0 := sub_nonpos.mpr hhalf
      have hone : t - 1 ≤ 0 := by linarith
      rw [max_eq_left ht0, max_eq_right hhalf', max_eq_right hone]
      linarith
    · have hhalft : 0 ≤ t - 1 / 2 := by linarith
      by_cases hone : t ≤ 1
      · have hone' : t - 1 ≤ 0 := sub_nonpos.mpr hone
        rw [max_eq_left ht0, max_eq_left hhalft, max_eq_right hone']
        linarith
      · have honet : 0 ≤ t - 1 := by linarith
        rw [max_eq_left ht0, max_eq_left hhalft, max_eq_left honet]
        ring_nf
        exact le_rfl

/-- Distance to a nonempty closed convex set is convex along a two-point convex combination. -/
private lemma infDist_convexComb_le
    {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hsclosed : IsClosed s) (hsne : s.Nonempty) (hs : Convexity.IsConvexSet ℝ s)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (x y : EuclideanSpace ℝ (Fin d)) :
    Metric.infDist (a • x + b • y) s ≤
      a * Metric.infDist x s + b * Metric.infDist y s := by
  let px := metricProjection s hsclosed hsne x
  let py := metricProjection s hsclosed hsne y
  have hpx : px ∈ s := (metricProjection_isNearestPoint s hsclosed hsne x).1
  have hpy : py ∈ s := (metricProjection_isNearestPoint s hsclosed hsne y).1
  have hp : a • px + b • py ∈ s := by
    simpa only [Convexity.convexCombPair_eq_sum] using
      hs.convexCombPair_mem hpx hpy ha hb hab
  calc
    Metric.infDist (a • x + b • y) s ≤
        dist (a • x + b • y) (a • px + b • py) :=
      Metric.infDist_le_dist_of_mem hp
    _ = ‖a • (x - px) + b • (y - py)‖ := by
      rw [dist_eq_norm]
      congr 1
      module
    _ ≤ ‖a • (x - px)‖ + ‖b • (y - py)‖ := norm_add_le _ _
    _ = a * Metric.infDist x s + b * Metric.infDist y s := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb,
        ← dist_eq_norm, ← dist_eq_norm,
        ← infDist_eq_dist_metricProjection s hsclosed hsne x,
        ← infDist_eq_dist_metricProjection s hsclosed hsne y]

/-- Every superlevel of the convex-set cutoff is convex. -/
lemma convexSetCutoff_superlevel_isConvexSet
    {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Convexity.IsConvexSet ℝ {x | t ≤ convexSetCutoff s ε x} := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · by_cases ht : t ≤ 0
    · rw [show {x : EuclideanSpace ℝ (Fin d) |
          t ≤ convexSetCutoff ∅ ε x} = Set.univ by
          ext x
          simp [ht]]
      exact Convexity.IsConvexSet.univ
    · rw [show {x : EuclideanSpace ℝ (Fin d) |
          t ≤ convexSetCutoff ∅ ε x} = ∅ by
          ext x
          simp [ht]]
      exact Convexity.IsConvexSet.empty
  · have hclosed : IsClosed (closure s) := isClosed_closure
    have hne : (closure s).Nonempty := hsne.closure
    have hconv : Convexity.IsConvexSet ℝ (closure s) := closure_isConvexSet hs
    refine Convexity.IsConvexSet.of_convexCombPair_mem ?_
    intro a b ha hb hab x hx y hy
    rw [Convexity.convexCombPair_eq_sum]
    simp only [Set.mem_setOf_eq, convexSetCutoff, if_pos hsne, bentkusCutoff] at hx hy ⊢
    let rx := Metric.infDist x (closure s) / ε
    let ry := Metric.infDist y (closure s) / ε
    let rz := Metric.infDist (a • x + b • y) (closure s) / ε
    have hdist := infDist_convexComb_le hclosed hne hconv ha hb hab x y
    have hratio : rz ≤ a * rx + b * ry := by
      dsimp only [rx, ry, rz]
      calc
        Metric.infDist (a • x + b • y) (closure s) / ε ≤
            (a * Metric.infDist x (closure s) +
              b * Metric.infDist y (closure s)) / ε :=
          (div_le_div_iff_of_pos_right hε).2 hdist
        _ = a * (Metric.infDist x (closure s) / ε) +
            b * (Metric.infDist y (closure s) / ε) := by ring
    have hcombo : a * rx + b * ry ≤ max rx ry := by
      have hxmax : rx ≤ max rx ry := le_max_left _ _
      have hymax : ry ≤ max rx ry := le_max_right _ _
      calc
        a * rx + b * ry ≤ a * max rx ry + b * max rx ry :=
          add_le_add (mul_le_mul_of_nonneg_left hxmax ha)
            (mul_le_mul_of_nonneg_left hymax hb)
        _ = max rx ry := by rw [← add_mul, hab, one_mul]
    have hmax : t ≤ bentkusProfile (max rx ry) := by
      rcases le_total rx ry with hxy | hyx
      · rw [max_eq_right hxy]
        exact hy
      · rw [max_eq_left hyx]
        exact hx
    exact hmax.trans (bentkusProfile_antitone (hratio.trans hcombo))

lemma isConvexSet_preimage_add_right
    {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) (z : EuclideanSpace ℝ (Fin d)) :
    Convexity.IsConvexSet ℝ {x | x + z ∈ s} := by
  refine Convexity.IsConvexSet.of_convexCombPair_mem ?_
  intro a b ha hb hab x hx y hy
  have h := hs.convexCombPair_mem hx hy ha hb hab
  rw [Convexity.convexCombPair_eq_sum] at h ⊢
  change a • x + b • y + z ∈ s
  change a • (x + z) + b • (y + z) ∈ s at h
  have hz : a • (x + z) + b • (y + z) = a • x + b • y + z := by
    rw [smul_add, smul_add]
    calc
      a • x + a • z + (b • y + b • z) =
          a • x + b • y + (a + b) • z := by module
      _ = a • x + b • y + z := by rw [hab, one_smul]
  rwa [hz] at h

/-- Layer cake for a measurable `[0,1]`-valued test whose every superlevel is convex. -/
theorem abs_integral_quasiconcave_sub_le_convexDistance
    {d : ℕ} {ν τ : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]
    {D : ℝ} (_hD : 0 ≤ D)
    (hbound : ∀ A : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet A →
      Convexity.IsConvexSet ℝ A → |ν.real A - τ.real A| ≤ D)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hfm : Measurable f)
    (hfnn : ∀ x, 0 ≤ f x) (hfle : ∀ x, f x ≤ 1)
    (hconv : ∀ t, Convexity.IsConvexSet ℝ {x | t ≤ f x}) :
    |(∫ x, f x ∂ν) - ∫ x, f x ∂τ| ≤ D := by
  let Fν : ℝ → ℝ := fun t ↦ ν.real {x | t ≤ f x}
  let Fτ : ℝ → ℝ := fun t ↦ τ.real {x | t ≤ f x}
  have hfν : Integrable f ν := by
    apply Integrable.of_bound hfm.aestronglyMeasurable 1
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hfnn x)]
    exact hfle x
  have hfτ : Integrable f τ := by
    apply Integrable.of_bound hfm.aestronglyMeasurable 1
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hfnn x)]
    exact hfle x
  have hFνanti : Antitone Fν := by
    intro a b hab
    dsimp only [Fν]
    exact measureReal_mono (fun x hx ↦ hab.trans hx)
  have hFτanti : Antitone Fτ := by
    intro a b hab
    dsimp only [Fτ]
    exact measureReal_mono (fun x hx ↦ hab.trans hx)
  have hFνint : Integrable Fν (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    apply Integrable.of_bound hFνanti.measurable.aestronglyMeasurable 1
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hFτint : Integrable Fτ (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    apply Integrable.of_bound hFτanti.measurable.aestronglyMeasurable 1
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hνrep : (∫ x, f x ∂ν) = ∫ t in Set.Ioc (0 : ℝ) 1, Fν t := by
    simpa only [Fν] using hfν.integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hfnn) (Filter.Eventually.of_forall hfle)
  have hτrep : (∫ x, f x ∂τ) = ∫ t in Set.Ioc (0 : ℝ) 1, Fτ t := by
    simpa only [Fτ] using hfτ.integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hfnn) (Filter.Eventually.of_forall hfle)
  rw [hνrep, hτrep, ← integral_sub hFνint hFτint]
  have hDint : Integrable (fun _t : ℝ ↦ D)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    exact integrableOn_const (C := D)
      (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      (hC := by finiteness)
  calc
    |∫ t in Set.Ioc (0 : ℝ) 1, Fν t - Fτ t| ≤
        ∫ _t in Set.Ioc (0 : ℝ) 1, D := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le hDint
      filter_upwards with t
      rw [Real.norm_eq_abs]
      apply hbound
      · exact measurableSet_le measurable_const hfm
      · exact hconv t
    _ = D := by
      rw [setIntegral_const]
      change (volume (Set.Ioc (0 : ℝ) 1)).toReal * D = D
      rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by norm_num)]
      norm_num

/-- Convex distance controls expectations of Bentkus's quasiconcave cutoff without any loss in
the constant.  This is the layer-cake form of the comparison used in (3.41). -/
private theorem abs_integral_convexSetCutoff_sub_le_convexDistance
    {d : ℕ} {ν τ : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]
    {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ A : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet A →
      Convexity.IsConvexSet ℝ A → |ν.real A - τ.real A| ≤ D)
    (s : Set (EuclideanSpace ℝ (Fin d))) (hs : Convexity.IsConvexSet ℝ s)
    {ε : ℝ} (hε : 0 < ε) :
    |(∫ x, convexSetCutoff s ε x ∂ν) -
        ∫ x, convexSetCutoff s ε x ∂τ| ≤ D := by
  exact abs_integral_quasiconcave_sub_le_convexDistance hD hbound
    (convexSetCutoff s ε) (measurable_convexSetCutoff s ε)
    (convexSetCutoff_nonneg s ε) (convexSetCutoff_le_one s ε)
    (convexSetCutoff_superlevel_isConvexSet hs hε)

private theorem abs_integral_convexSetCutoff_add_sub_le_convexDistance
    {d : ℕ} {ν τ : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]
    {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ A : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet A →
      Convexity.IsConvexSet ℝ A → |ν.real A - τ.real A| ≤ D)
    (s : Set (EuclideanSpace ℝ (Fin d))) (hs : Convexity.IsConvexSet ℝ s)
    {ε : ℝ} (hε : 0 < ε) (z : EuclideanSpace ℝ (Fin d)) :
    |(∫ x, convexSetCutoff s ε (x + z) ∂ν) -
        ∫ x, convexSetCutoff s ε (x + z) ∂τ| ≤ D := by
  apply abs_integral_quasiconcave_sub_le_convexDistance hD hbound
    (fun x ↦ convexSetCutoff s ε (x + z))
  · exact (measurable_convexSetCutoff s ε).comp (by fun_prop)
  · exact fun x ↦ convexSetCutoff_nonneg s ε (x + z)
  · exact fun x ↦ convexSetCutoff_le_one s ε (x + z)
  · intro t
    exact isConvexSet_preimage_add_right
      (convexSetCutoff_superlevel_isConvexSet hs hε t) z

/-- The induction estimate transported to leave-one-out whitening.  This is the normalized
convex-distance comparison that is inserted into Bentkus (3.34) and (3.41). -/
theorem bentkusWhitenedLeaveOneOut_error_le_of_induction
    {C : ℝ} {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hIH : bentkusIdentityCovarianceBoundAt.{u} C n)
    (hd : 0 < d) (hX3 : ∀ i, MemLp (X i) 3 μ)
    (h_indep : iIndepFun X μ) (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (k : Fin (n + 1))
    (hS : (bentkusLeaveOneOutCovarianceMatrix μ X k).PosDef)
    (A : Set (EuclideanSpace ℝ (Fin d))) (hA : MeasurableSet A)
    (hAconv : Convexity.IsConvexSet ℝ A) :
    |(μ.map (fun ω ↦
          bentkusWhiteningEquiv (bentkusLeaveOneOutCovarianceMatrix μ X k) hS
            (bentkusLeaveOneOut X k ω))).real A -
        (stdGaussian (EuclideanSpace ℝ (Fin d))).real A| ≤
      C * (d : ℝ) ^ (1 / 4 : ℝ) *
        ∑ i : Fin n, ∫ ω,
          ‖bentkusWhiteningCLM (bentkusLeaveOneOutCovarianceMatrix μ X k)
            (X (k.succAbove i) ω)‖ ^ 3 ∂μ := by
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  let e := bentkusWhiteningEquiv S hS
  let U := bentkusLeaveOneOut X k
  have hUaeMeas : AEMeasurable U μ :=
    (memLp_finsetSum (Finset.univ.erase k) fun i _ ↦ hX3 i).aemeasurable
  have hmapU :
      μ.map (fun ω ↦ e (U ω)) = (μ.map U).map e := by
    exact (AEMeasurable.map_map_of_aemeasurable
      e.continuous.measurable.aemeasurable hUaeMeas).symm
  have hpreMeas : MeasurableSet (e ⁻¹' A) := hA.preimage e.continuous.measurable
  have hpreConv : Convexity.IsConvexSet ℝ (e ⁻¹' A) :=
    isConvexSet_preimage_continuousLinearMap e.toContinuousLinearMap hAconv
  have hbase := bentkusLeaveOneOut_error_le_of_induction
    hIH hd hX3 h_indep hX0 k hS (e ⁻¹' A) hpreMeas hpreConv
  have hgauss := map_multivariateGaussian_bentkusWhiteningEquiv S hS
  change |(μ.map (fun ω ↦ e (U ω))).real A -
      (stdGaussian (EuclideanSpace ℝ (Fin d))).real A| ≤ _
  rw [hmapU, ← hgauss,
    map_measureReal_apply e.continuous.measurable hA,
    map_measureReal_apply e.continuous.measurable hA]
  simpa only [S, U] using hbase

/-- Joint law of the whitened Gaussian and original leave-one-out sums.  The Gaussian coordinate
is placed first so the subsequent scalar-mixture contraction has the form `q V + p U`. -/
private theorem map_whitened_bentkusLeaveOneOut_gaussian_original_pair_eq_prod
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4) :
    let ρ := bentkusReplacementMeasure μ X
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let UO := bentkusLeaveOneOut
      (fun i ↦ replacementOriginal (d := d) i) k
    let VG := bentkusLeaveOneOut
      (fun i ↦ replacementGaussian (d := d) i) k
    let U := bentkusLeaveOneOut X k
    ρ.map (fun ω ↦ (e (VG ω), e (UO ω))) =
      (stdGaussian (EuclideanSpace ℝ (Fin d))).prod
        (μ.map (fun ω ↦ e (U ω))) := by
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let UO := bentkusLeaveOneOut
    (fun i ↦ replacementOriginal (d := d) i) k
  let VG := bentkusLeaveOneOut
    (fun i ↦ replacementGaussian (d := d) i) k
  let U := bentkusLeaveOneOut X k
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hUOmeas : Measurable UO := by
    change Measurable (fun z :
        (Fin (n + 1) → EuclideanSpace ℝ (Fin d)) ×
          (Fin (n + 1) → EuclideanSpace ℝ (Fin d)) ↦
      ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase k, z.1 i)
    fun_prop
  have hVGmeas : Measurable VG := by
    change Measurable (fun z :
        (Fin (n + 1) → EuclideanSpace ℝ (Fin d)) ×
          (Fin (n + 1) → EuclideanSpace ℝ (Fin d)) ↦
      ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase k, z.2 i)
    fun_prop
  have hUmeas : Measurable U := by
    dsimp only [U, bentkusLeaveOneOut]
    exact Finset.measurable_sum (Finset.univ.erase k) fun i _ ↦ hXm i
  have hindep : (e ∘ VG) ⟂ᵢ[ρ] (e ∘ UO) := by
    have hbase :=
      (indepFun_bentkusLeaveOneOut_replacementOriginal_gaussian
        (μ := μ) (X := X) hXm k).symm.comp
          e.continuous.measurable e.continuous.measurable
    simpa only [UO, VG, ρ] using hbase
  have hjoint := hindep.map_prod_eq_prod_map_map
    (e.continuous.measurable.comp hVGmeas).aemeasurable
    (e.continuous.measurable.comp hUOmeas).aemeasurable
  have hVlaw : ρ.map (fun ω ↦ e (VG ω)) =
      stdGaussian (EuclideanSpace ℝ (Fin d)) := by
    simpa only [ρ, S, e, VG, bentkusWhiteningEquiv_apply] using
      map_whitened_bentkusLeaveOneOut_replacementGaussian_eq_stdGaussian
        hXm hX3 h_indep hX0 hidentity k hk
  have hUlaw : ρ.map (fun ω ↦ e (UO ω)) = μ.map (fun ω ↦ e (U ω)) := by
    calc
      ρ.map (fun ω ↦ e (UO ω)) = (ρ.map UO).map e := by
        rw [Measure.map_map e.continuous.measurable hUOmeas]
        rfl
      _ = (μ.map U).map e := by
        rw [show ρ.map UO = μ.map U by
          simpa only [ρ, UO, U] using
            map_bentkusLeaveOneOut_replacementOriginal_eq hXm h_indep k]
      _ = μ.map (fun ω ↦ e (U ω)) := by
        rw [Measure.map_map e.continuous.measurable hUmeas]
        rfl
  change ρ.map (fun ω ↦ (e (VG ω), e (UO ω))) =
      (ρ.map (fun ω ↦ e (VG ω))).prod (ρ.map (fun ω ↦ e (UO ω))) at hjoint
  rw [hVlaw, hUlaw] at hjoint
  simpa only using hjoint

theorem map_whitenedRotatedLeaveOneOut_eq_map_prod
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4) (α : ℝ) :
    let ρ := bentkusReplacementMeasure μ X
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let B := bentkusWhiteningCLM S
    let UO := bentkusLeaveOneOut
      (fun i ↦ replacementOriginal (d := d) i) k
    let VG := bentkusLeaveOneOut
      (fun i ↦ replacementGaussian (d := d) i) k
    let U := bentkusLeaveOneOut X k
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let ν := μ.map (fun ω ↦ B (U ω))
    let L : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) →
        EuclideanSpace ℝ (Fin d) := fun z ↦
      Real.sin α • z.1 + Real.cos α • z.2
    ρ.map (fun ω ↦ B (Real.cos α • UO ω + Real.sin α • VG ω)) =
      (γ.prod ν).map L := by
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  let B := bentkusWhiteningCLM S
  let UO := bentkusLeaveOneOut
    (fun i ↦ replacementOriginal (d := d) i) k
  let VG := bentkusLeaveOneOut
    (fun i ↦ replacementGaussian (d := d) i) k
  let U := bentkusLeaveOneOut X k
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let ν := μ.map (fun ω ↦ B (U ω))
  let L : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) := fun z ↦
    Real.sin α • z.1 + Real.cos α • z.2
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  have hpair := map_whitened_bentkusLeaveOneOut_gaussian_original_pair_eq_prod
    hXm hX3 h_indep hX0 hidentity k hk
  have hpair' : ρ.map (fun ω ↦ (B (VG ω), B (UO ω))) = γ.prod ν := by
    simpa only [ρ, S, B, UO, VG, U, γ, ν, bentkusWhiteningEquiv_apply] using hpair
  have hpairMeas : Measurable (fun ω ↦ (B (VG ω), B (UO ω))) := by
    dsimp only [B, UO, VG, bentkusLeaveOneOut,
      replacementOriginal, replacementGaussian]
    fun_prop
  have hLmeas : Measurable L := by
    dsimp only [L]
    fun_prop
  change ρ.map (fun ω ↦ B (Real.cos α • UO ω + Real.sin α • VG ω)) =
    (γ.prod ν).map L
  rw [← hpair']
  rw [Measure.map_map hLmeas hpairMeas]
  congr 1
  funext ω
  dsimp only [L, Function.comp_apply]
  rw [map_add, map_smul, map_smul]
  abel

theorem map_whitenedRotatedLeaveOneOut_replacementPair_eq_prod
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i)) (k : Fin (n + 1)) (α : ℝ) :
    let ρ := bentkusReplacementMeasure μ X
    let B := bentkusWhiteningCLM (bentkusLeaveOneOutCovarianceMatrix μ X k)
    let UO := bentkusLeaveOneOut
      (fun i ↦ replacementOriginal (d := d) i) k
    let VG := bentkusLeaveOneOut
      (fun i ↦ replacementGaussian (d := d) i) k
    let W := fun ω ↦ B (Real.cos α • UO ω + Real.sin α • VG ω)
    let Z := fun ω ↦
      (replacementOriginal (d := d) k ω, replacementGaussian (d := d) k ω)
    ρ.map (fun ω ↦ (W ω, Z ω)) = (ρ.map W).prod (ρ.map Z) := by
  let ρ := bentkusReplacementMeasure μ X
  let B := bentkusWhiteningCLM (bentkusLeaveOneOutCovarianceMatrix μ X k)
  let UO := bentkusLeaveOneOut
    (fun i ↦ replacementOriginal (d := d) i) k
  let VG := bentkusLeaveOneOut
    (fun i ↦ replacementGaussian (d := d) i) k
  let W := fun ω ↦ B (Real.cos α • UO ω + Real.sin α • VG ω)
  let Z := fun ω ↦
    (replacementOriginal (d := d) k ω, replacementGaussian (d := d) k ω)
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hWm : Measurable W := by
    dsimp only [W, UO, VG, bentkusLeaveOneOut,
      replacementOriginal, replacementGaussian]
    fun_prop
  have hZm : Measurable Z := by
    dsimp only [Z, replacementOriginal, replacementGaussian]
    fun_prop
  have hindep : W ⟂ᵢ[ρ] Z := by
    simpa only [W, Z, B, UO, VG, ρ] using
      indepFun_whitenedRotatedLeaveOneOut_replacementPair
        (μ := μ) (X := X) hXm B k α
  exact hindep.map_prod_eq_prod_map_map hWm.aemeasurable hZm.aemeasurable

/-- The exact product-law representation used at the start of Bentkus (3.27).  The whitened
Gaussian leave-one-out coordinate is split into two independent half-variance standard
Gaussians; the rotated leave-one-out vector remains independent of the omitted
original/Gaussian pair. -/
theorem map_splitGaussian_whitenedRotatedLeaveOneOut_replacementPair_eq_prod
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4) (α : ℝ) :
    let ρ := bentkusReplacementMeasure μ X
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let B := bentkusWhiteningCLM S
    let UO := bentkusLeaveOneOut
      (fun i ↦ replacementOriginal (d := d) i) k
    let VG := bentkusLeaveOneOut
      (fun i ↦ replacementGaussian (d := d) i) k
    let U := bentkusLeaveOneOut X k
    let Z := fun ω ↦
      (replacementOriginal (d := d) k ω, replacementGaussian (d := d) k ω)
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let ν := μ.map (fun ω ↦ B (U ω))
    let τ := ρ.map Z
    let θ := (Real.sqrt 2)⁻¹
    let splitRotate :
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
            EuclideanSpace ℝ (Fin d) →
          EuclideanSpace ℝ (Fin d) :=
      fun z ↦
        Real.sin α • (θ • z.1.1 + θ • z.1.2) + Real.cos α • z.2
    ρ.map (fun ω ↦
        (B (Real.cos α • UO ω + Real.sin α • VG ω), Z ω)) =
      (((γ.prod γ).prod ν).map splitRotate).prod τ := by
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  let B := bentkusWhiteningCLM S
  let UO := bentkusLeaveOneOut
    (fun i ↦ replacementOriginal (d := d) i) k
  let VG := bentkusLeaveOneOut
    (fun i ↦ replacementGaussian (d := d) i) k
  let U := bentkusLeaveOneOut X k
  let Z := fun ω ↦
    (replacementOriginal (d := d) k ω, replacementGaussian (d := d) k ω)
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let ν := μ.map (fun ω ↦ B (U ω))
  let τ := ρ.map Z
  let θ := (Real.sqrt 2)⁻¹
  let split :
      EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) →
        EuclideanSpace ℝ (Fin d) :=
    fun z ↦ θ • z.1 + θ • z.2
  let rotate :
      EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) →
        EuclideanSpace ℝ (Fin d) :=
    fun z ↦ Real.sin α • z.1 + Real.cos α • z.2
  let splitRotate :
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
          EuclideanSpace ℝ (Fin d) →
        EuclideanSpace ℝ (Fin d) :=
    fun z ↦
      Real.sin α • (θ • z.1.1 + θ • z.1.2) + Real.cos α • z.2
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hθpos : 0 < θ := by
    dsimp only [θ]
    exact inv_pos.mpr (Real.sqrt_pos.2 (by norm_num))
  have hθsq : θ ^ 2 + θ ^ 2 = 1 := by
    have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 :=
      Real.sq_sqrt (by norm_num)
    dsimp only [θ]
    field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
    nlinarith
  have hsplitLaw : (γ.prod γ).map split = γ := by
    simpa only [γ, split] using
      map_prod_stdGaussian_weightedAdd_eq_stdGaussian (d := d) hθsq
  have hsplitMeas : Measurable split := by
    dsimp only [split]
    fun_prop
  have hrotateMeas : Measurable rotate := by
    dsimp only [rotate]
    fun_prop
  have hsplitRotateMeas : Measurable splitRotate := by
    dsimp only [splitRotate]
    fun_prop
  have hsource :
      (γ.prod ν).map rotate = ((γ.prod γ).prod ν).map splitRotate := by
    have hprod :
        ((γ.prod γ).map split).prod ν =
          ((γ.prod γ).prod ν).map (Prod.map split id) := by
      simpa only [Measure.map_id] using
        Measure.map_prod_map (γ.prod γ) ν hsplitMeas measurable_id
    calc
      (γ.prod ν).map rotate =
          (((γ.prod γ).map split).prod ν).map rotate := by rw [hsplitLaw]
      _ = (((γ.prod γ).prod ν).map (Prod.map split id)).map rotate := by rw [hprod]
      _ = ((γ.prod γ).prod ν).map splitRotate := by
        rw [Measure.map_map hrotateMeas (hsplitMeas.prodMap measurable_id)]
        rfl
  have hpair :=
    map_whitenedRotatedLeaveOneOut_replacementPair_eq_prod
      (μ := μ) (X := X) hXm k α
  have hleave :=
    map_whitenedRotatedLeaveOneOut_eq_map_prod
      hXm hX3 h_indep hX0 hidentity k hk α
  change ρ.map (fun ω ↦
      (B (Real.cos α • UO ω + Real.sin α • VG ω), Z ω)) =
    (((γ.prod γ).prod ν).map splitRotate).prod τ
  rw [show ρ.map (fun ω ↦
      (B (Real.cos α • UO ω + Real.sin α • VG ω), Z ω)) =
      (ρ.map (fun ω ↦
        B (Real.cos α • UO ω + Real.sin α • VG ω))).prod τ by
      simpa only [ρ, S, B, UO, VG, Z, τ] using hpair,
    show ρ.map (fun ω ↦
      B (Real.cos α • UO ω + Real.sin α • VG ω)) =
      (γ.prod ν).map rotate by
      simpa only [ρ, S, B, UO, VG, U, γ, ν, rotate] using hleave,
    hsource]

/-- Integral form of
`map_splitGaussian_whitenedRotatedLeaveOneOut_replacementPair_eq_prod`.  It exposes, in order,
the two independent standard Gaussians, the whitened original leave-one-out law, and the omitted
coordinate pair.  This is the conditioning interface consumed by the density translation in
Bentkus (3.27). -/
private theorem integral_splitGaussian_whitenedRotatedLeaveOneOut_replacementPair_eq
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4) (α : ℝ)
    (F : EuclideanSpace ℝ (Fin d) ×
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) → ℝ) :
    let ρ := bentkusReplacementMeasure μ X
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let B := bentkusWhiteningCLM S
    let UO := bentkusLeaveOneOut
      (fun i ↦ replacementOriginal (d := d) i) k
    let VG := bentkusLeaveOneOut
      (fun i ↦ replacementGaussian (d := d) i) k
    let U := bentkusLeaveOneOut X k
    let Z := fun ω ↦
      (replacementOriginal (d := d) k ω, replacementGaussian (d := d) k ω)
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let ν := μ.map (fun ω ↦ B (U ω))
    let τ := ρ.map Z
    let θ := (Real.sqrt 2)⁻¹
    let splitRotate :
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
            EuclideanSpace ℝ (Fin d) →
          EuclideanSpace ℝ (Fin d) :=
      fun z ↦
        Real.sin α • (θ • z.1.1 + θ • z.1.2) + Real.cos α • z.2
    Integrable F
      (((((γ.prod γ).prod ν).map splitRotate).prod τ)) →
    (∫ ω, F
        (B (Real.cos α • UO ω + Real.sin α • VG ω), Z ω) ∂ρ) =
      ∫ a, ∫ z, F (splitRotate a, z) ∂τ ∂((γ.prod γ).prod ν) := by
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  let B := bentkusWhiteningCLM S
  let UO := bentkusLeaveOneOut
    (fun i ↦ replacementOriginal (d := d) i) k
  let VG := bentkusLeaveOneOut
    (fun i ↦ replacementGaussian (d := d) i) k
  let U := bentkusLeaveOneOut X k
  let Z := fun ω ↦
    (replacementOriginal (d := d) k ω, replacementGaussian (d := d) k ω)
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let ν := μ.map (fun ω ↦ B (U ω))
  let τ := ρ.map Z
  let θ := (Real.sqrt 2)⁻¹
  let splitRotate :
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
          EuclideanSpace ℝ (Fin d) →
        EuclideanSpace ℝ (Fin d) :=
    fun z ↦
      Real.sin α • (θ • z.1.1 + θ • z.1.2) + Real.cos α • z.2
  let pairMap := fun ω ↦
    (B (Real.cos α • UO ω + Real.sin α • VG ω), Z ω)
  let source := (γ.prod γ).prod ν
  let liftMap := Prod.map splitRotate
    (id : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) →
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
  change Integrable F ((source.map splitRotate).prod τ) →
    (∫ ω, F (pairMap ω) ∂ρ) =
      ∫ a, ∫ z, F (splitRotate a, z) ∂τ ∂source
  intro hFint
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hpairMap : Measurable pairMap := by
    dsimp only [pairMap, UO, VG, Z, bentkusLeaveOneOut,
      replacementOriginal, replacementGaussian]
    fun_prop
  have hsplitRotate : Measurable splitRotate := by
    dsimp only [splitRotate]
    fun_prop
  have hliftMap : Measurable liftMap :=
    hsplitRotate.prodMap measurable_id
  have hjoint : ρ.map pairMap = (source.map splitRotate).prod τ := by
    simpa only [ρ, S, B, UO, VG, U, Z, γ, ν, τ, θ, splitRotate, source, pairMap] using
      map_splitGaussian_whitenedRotatedLeaveOneOut_replacementPair_eq_prod
        hXm hX3 h_indep hX0 hidentity k hk α
  have hprodMap :
      (source.map splitRotate).prod τ = (source.prod τ).map liftMap := by
    simpa only [Measure.map_id, liftMap] using
      Measure.map_prod_map source τ hsplitRotate measurable_id
  have hFmap : AEStronglyMeasurable F (ρ.map pairMap) := by
    rw [hjoint]
    exact hFint.aestronglyMeasurable
  have hFintMap : Integrable F ((source.prod τ).map liftMap) := by
    rw [← hprodMap]
    exact hFint
  have hFsource : Integrable (F ∘ liftMap) (source.prod τ) := by
    exact hFintMap.comp_aemeasurable hliftMap.aemeasurable
  calc
    (∫ ω, F
        (B (Real.cos α • UO ω + Real.sin α • VG ω), Z ω) ∂ρ) =
        ∫ p, F p ∂(ρ.map pairMap) := by
      exact (integral_map hpairMap.aemeasurable hFmap).symm
    _ = ∫ p, F p ∂((source.map splitRotate).prod τ) := by rw [hjoint]
    _ = ∫ p, F p ∂((source.prod τ).map liftMap) := by rw [hprodMap]
    _ = ∫ p, (F ∘ liftMap) p ∂(source.prod τ) := by
      exact integral_map hliftMap.aemeasurable hFintMap.aestronglyMeasurable
    _ = ∫ a, ∫ z, F (splitRotate a, z) ∂τ ∂source := by
      simpa only [Function.comp_apply, liftMap, Prod.map_apply, id_eq] using
        integral_prod (F ∘ liftMap) hFsource

/-- Bentkus's induction comparison after whitening and rotation of the leave-one-out pair.  This
is the probability-distance core common to (3.34) and (3.41). -/
private theorem bentkus_whitenedRotatedLeaveOneOut_error_le_of_induction
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
    (α : ℝ) (A : Set (EuclideanSpace ℝ (Fin d))) (hA : MeasurableSet A)
    (hAconv : Convexity.IsConvexSet ℝ A) :
    let ρ := bentkusReplacementMeasure μ X
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let UO := bentkusLeaveOneOut
      (fun i ↦ replacementOriginal (d := d) i) k
    let VG := bentkusLeaveOneOut
      (fun i ↦ replacementGaussian (d := d) i) k
    |(ρ.map (fun ω ↦ e
          (Real.cos α • UO ω + Real.sin α • VG ω))).real A -
        (stdGaussian (EuclideanSpace ℝ (Fin d))).real A| ≤
      C * (d : ℝ) ^ (1 / 4 : ℝ) *
        ∑ i : Fin n, ∫ ω,
          ‖bentkusWhiteningCLM S (X (k.succAbove i) ω)‖ ^ 3 ∂μ := by
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let UO := bentkusLeaveOneOut
    (fun i ↦ replacementOriginal (d := d) i) k
  let VG := bentkusLeaveOneOut
    (fun i ↦ replacementGaussian (d := d) i) k
  let U := bentkusLeaveOneOut X k
  let ν := μ.map (fun ω ↦ e (U ω))
  let D := C * (d : ℝ) ^ (1 / 4 : ℝ) *
    ∑ i : Fin n, ∫ ω, ‖bentkusWhiteningCLM S (X (k.succAbove i) ω)‖ ^ 3 ∂μ
  let Z := fun ω ↦ (e (VG ω), e (UO ω))
  let W := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    Real.sin α • z.1 + Real.cos α • z.2
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hUmeas : Measurable U := by
    dsimp only [U, bentkusLeaveOneOut]
    exact Finset.measurable_sum (Finset.univ.erase k) fun i _ ↦ hXm i
  letI : IsProbabilityMeasure ν := by
    dsimp only [ν]
    exact Measure.isProbabilityMeasure_map (e.continuous.measurable.comp hUmeas).aemeasurable
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hbound (B : Set (EuclideanSpace ℝ (Fin d))) (hBm : MeasurableSet B)
      (hBc : Convexity.IsConvexSet ℝ B) :
      |ν.real B - (stdGaussian (EuclideanSpace ℝ (Fin d))).real B| ≤ D := by
    simpa only [ν, D, S, e, U] using
      bentkusWhitenedLeaveOneOut_error_le_of_induction
        hIH hd hX3 h_indep hX0 k hS B hBm hBc
  have hcontract := convexDistance_map_prod_stdGaussian_weightedAdd_le
    (ν := ν) (D := D) (p := Real.cos α) (q := Real.sin α)
    hD hbound (Real.cos_sq_add_sin_sq α) A hA hAconv
  have hpair : ρ.map Z =
      (stdGaussian (EuclideanSpace ℝ (Fin d))).prod ν := by
    simpa only [ρ, S, e, UO, VG, U, ν, Z] using
      map_whitened_bentkusLeaveOneOut_gaussian_original_pair_eq_prod
        hXm hX3 h_indep hX0 hidentity k hk
  have hZmeas : Measurable Z := by
    dsimp only [Z, UO, VG, bentkusLeaveOneOut,
      replacementOriginal, replacementGaussian]
    fun_prop
  have hWmeas : Measurable W := by
    dsimp only [W]
    fun_prop
  have hrotLaw :
      ρ.map (fun ω ↦ e (Real.cos α • UO ω + Real.sin α • VG ω)) =
        ((stdGaussian (EuclideanSpace ℝ (Fin d))).prod ν).map W := by
    have hfun : (fun ω ↦ e (Real.cos α • UO ω + Real.sin α • VG ω)) =
        W ∘ Z := by
      funext ω
      dsimp only [W, Z, Function.comp_apply]
      rw [map_add, map_smul, map_smul]
      abel
    rw [hfun, ← Measure.map_map hWmeas hZmeas, hpair]
  rw [← hrotLaw] at hcontract
  simpa only [ρ, S, e, UO, VG, D, W] using hcontract

/-- The layer-cake consequence of the rotated leave-one-out convex-distance estimate.  This is
Bentkus (3.41) for the concrete smooth cutoff. -/
private theorem bentkus_whitenedRotatedLeaveOneOut_cutoff_add_error_le_of_induction
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
    (α : ℝ) (s : Set (EuclideanSpace ℝ (Fin d)))
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε)
    (z : EuclideanSpace ℝ (Fin d)) :
    let ρ := bentkusReplacementMeasure μ X
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let UO := bentkusLeaveOneOut
      (fun i ↦ replacementOriginal (d := d) i) k
    let VG := bentkusLeaveOneOut
      (fun i ↦ replacementGaussian (d := d) i) k
    let R := fun ω ↦ e (Real.cos α • UO ω + Real.sin α • VG ω)
    |(∫ x, convexSetCutoff s ε (x + z) ∂(ρ.map R)) -
        ∫ x, convexSetCutoff s ε (x + z)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))| ≤
      C * (d : ℝ) ^ (1 / 4 : ℝ) *
        ∑ i : Fin n, ∫ ω,
          ‖bentkusWhiteningCLM S (X (k.succAbove i) ω)‖ ^ 3 ∂μ := by
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let UO := bentkusLeaveOneOut
    (fun i ↦ replacementOriginal (d := d) i) k
  let VG := bentkusLeaveOneOut
    (fun i ↦ replacementGaussian (d := d) i) k
  let R := fun ω ↦ e (Real.cos α • UO ω + Real.sin α • VG ω)
  let ν := ρ.map R
  let D := C * (d : ℝ) ^ (1 / 4 : ℝ) *
    ∑ i : Fin n, ∫ ω, ‖bentkusWhiteningCLM S (X (k.succAbove i) ω)‖ ^ 3 ∂μ
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hRmeas : Measurable R := by
    dsimp only [R, UO, VG, bentkusLeaveOneOut,
      replacementOriginal, replacementGaussian]
    fun_prop
  letI : IsProbabilityMeasure ν := by
    dsimp only [ν]
    exact Measure.isProbabilityMeasure_map hRmeas.aemeasurable
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hbound (A : Set (EuclideanSpace ℝ (Fin d))) (hA : MeasurableSet A)
      (hAc : Convexity.IsConvexSet ℝ A) :
      |ν.real A - (stdGaussian (EuclideanSpace ℝ (Fin d))).real A| ≤ D := by
    simpa only [ν, R, D, ρ, S, e, UO, VG] using
      bentkus_whitenedRotatedLeaveOneOut_error_le_of_induction
        hC hIH hd hXm hX3 h_indep hX0 hidentity k hk α A hA hAc
  have hcut := abs_integral_convexSetCutoff_add_sub_le_convexDistance
    hD hbound s hs hε z
  simpa only [ν, R, D, ρ, S, e, UO, VG] using hcut

private theorem bentkus_whitenedRotatedLeaveOneOut_cutoff_error_le_of_induction
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
    (α : ℝ) (s : Set (EuclideanSpace ℝ (Fin d)))
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε) :
    let ρ := bentkusReplacementMeasure μ X
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let UO := bentkusLeaveOneOut
      (fun i ↦ replacementOriginal (d := d) i) k
    let VG := bentkusLeaveOneOut
      (fun i ↦ replacementGaussian (d := d) i) k
    let R := fun ω ↦ e (Real.cos α • UO ω + Real.sin α • VG ω)
    |(∫ x, convexSetCutoff s ε x ∂(ρ.map R)) -
        ∫ x, convexSetCutoff s ε x
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))| ≤
      C * (d : ℝ) ^ (1 / 4 : ℝ) *
        ∑ i : Fin n, ∫ ω,
          ‖bentkusWhiteningCLM S (X (k.succAbove i) ω)‖ ^ 3 ∂μ := by
  simpa only [add_zero] using
    bentkus_whitenedRotatedLeaveOneOut_cutoff_add_error_le_of_induction
      hC hIH hd hXm hX3 h_indep hX0 hidentity k hk α s hs hε
        (0 : EuclideanSpace ℝ (Fin d))

/-- A Gaussian shell bound plus the rotated leave-one-out convex-distance estimate controls the
corresponding shell of the non-Gaussian mixture.  This is the `J₇ + J₈` probability step in
Bentkus (3.31). -/
private theorem bentkus_whitenedRotatedLeaveOneOut_outerShell_le_of_induction
    {C G : ℝ} (hC : 0 ≤ C) {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hIH : bentkusIdentityCovarianceBoundAt.{u} C n)
    (hd : 0 < d) (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (α : ℝ) (A : Set (EuclideanSpace ℝ (Fin d))) (hA : MeasurableSet A)
    (hAconv : Convexity.IsConvexSet ℝ A) {δ : ℝ} (hδ : 0 ≤ δ)
    (hGaussian :
      (stdGaussian (EuclideanSpace ℝ (Fin d))).real
          (Metric.cthickening δ (closure A) \ A) ≤ G) :
    let ρ := bentkusReplacementMeasure μ X
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let UO := bentkusLeaveOneOut
      (fun i ↦ replacementOriginal (d := d) i) k
    let VG := bentkusLeaveOneOut
      (fun i ↦ replacementGaussian (d := d) i) k
    let R := fun ω ↦ e (Real.cos α • UO ω + Real.sin α • VG ω)
    (ρ.map R).real (Metric.cthickening δ (closure A) \ A) ≤
      G + 2 * (C * (d : ℝ) ^ (1 / 4 : ℝ) *
        ∑ i : Fin n, ∫ ω,
          ‖bentkusWhiteningCLM S (X (k.succAbove i) ω)‖ ^ 3 ∂μ) := by
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let UO := bentkusLeaveOneOut
    (fun i ↦ replacementOriginal (d := d) i) k
  let VG := bentkusLeaveOneOut
    (fun i ↦ replacementGaussian (d := d) i) k
  let R := fun ω ↦ e (Real.cos α • UO ω + Real.sin α • VG ω)
  let ν := ρ.map R
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let D := C * (d : ℝ) ^ (1 / 4 : ℝ) *
    ∑ i : Fin n, ∫ ω, ‖bentkusWhiteningCLM S (X (k.succAbove i) ω)‖ ^ 3 ∂μ
  let B := Metric.cthickening δ (closure A)
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hRmeas : Measurable R := by
    dsimp only [R, UO, VG, bentkusLeaveOneOut,
      replacementOriginal, replacementGaussian]
    fun_prop
  letI : IsProbabilityMeasure ν := by
    dsimp only [ν]
    exact Measure.isProbabilityMeasure_map hRmeas.aemeasurable
  have hbound (T : Set (EuclideanSpace ℝ (Fin d))) (hTm : MeasurableSet T)
      (hTc : Convexity.IsConvexSet ℝ T) : |ν.real T - γ.real T| ≤ D := by
    simpa only [ν, γ, D, R, ρ, S, e, UO, VG] using
      bentkus_whitenedRotatedLeaveOneOut_error_le_of_induction
        hC hIH hd hXm hX3 h_indep hX0 hidentity k hk α T hTm hTc
  have hAB : A ⊆ B := by
    dsimp only [B]
    exact subset_closure.trans (Metric.self_subset_cthickening (closure A))
  have hBm : MeasurableSet B := by
    dsimp only [B]
    exact measurableSet_cthickening (closure A) δ
  have hBc : Convexity.IsConvexSet ℝ B := by
    dsimp only [B]
    exact cthickening_isConvexSet (closure_isConvexSet hAconv) hδ
  have hshell := measureReal_sdiff_le_add_two_mul_of_abs_sub_le
    (ν := ν) (τ := γ) hAB hA (hbound A hA hAconv) (hbound B hBm hBc)
  calc
    ν.real (B \ A) ≤ γ.real (B \ A) + 2 * D := hshell
    _ ≤ G + 2 * D := by
      simpa only [γ, B, add_comm] using add_le_add_right hGaussian (2 * D)


/-- The induction hypothesis controls an outer shell of the original leave-one-out sum by the
matching Gaussian shell plus twice the convex-distance error. -/
private theorem bentkusLeaveOneOut_outerShell_le_of_induction
    {C : ℝ} (hC : 0 ≤ C) {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hIH : bentkusIdentityCovarianceBoundAt.{u} C n)
    (hd : 0 < d) (hX3 : ∀ i, MemLp (X i) 3 μ)
    (h_indep : iIndepFun X μ) (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (A : Set (EuclideanSpace ℝ (Fin d))) (hA : MeasurableSet A)
    (hAconv : Convexity.IsConvexSet ℝ A) {ε : ℝ} (hε : 0 ≤ ε) :
    (μ.map (bentkusLeaveOneOut X k)).real
        (Metric.cthickening ε (closure A) \ A) ≤
      (multivariateGaussian 0 (bentkusLeaveOneOutCovarianceMatrix μ X k)).real
          (Metric.cthickening ε (closure A) \ A) +
        16 * C * (d : ℝ) ^ (1 / 4 : ℝ) *
          ∑ i : Fin n, ∫ ω, ‖X (k.succAbove i) ω‖ ^ 3 ∂μ := by
  let ν := μ.map (bentkusLeaveOneOut X k)
  let τ := multivariateGaussian 0 (bentkusLeaveOneOutCovarianceMatrix μ X k)
  let B := Metric.cthickening ε (closure A)
  let D := 8 * C * (d : ℝ) ^ (1 / 4 : ℝ) *
    ∑ i : Fin n, ∫ ω, ‖X (k.succAbove i) ω‖ ^ 3 ∂μ
  letI : IsFiniteMeasure ν := μ.isFiniteMeasure_map (bentkusLeaveOneOut X k)
  have hS : (bentkusLeaveOneOutCovarianceMatrix μ X k).PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  letI : IsProbabilityMeasure τ := by
    dsimp only [τ]
    infer_instance
  have hbase (T : Set (EuclideanSpace ℝ (Fin d))) (hTm : MeasurableSet T)
      (hTc : Convexity.IsConvexSet ℝ T) : |ν.real T - τ.real T| ≤ D := by
    simpa only [ν, τ, D] using
      bentkusLeaveOneOut_error_le_eight_mul_of_induction
        hC hIH hd hX3 h_indep hX0 hidentity k hk T hTm hTc
  have hAB : A ⊆ B := by
    dsimp only [B]
    exact subset_closure.trans (Metric.self_subset_cthickening (closure A))
  have hBm : MeasurableSet B := by
    dsimp only [B]
    exact measurableSet_cthickening (closure A) ε
  have hBc : Convexity.IsConvexSet ℝ B := by
    dsimp only [B]
    exact cthickening_isConvexSet (closure_isConvexSet hAconv) hε
  have hshell := measureReal_sdiff_le_add_two_mul_of_abs_sub_le
    (ν := ν) (τ := τ) hAB hA (hbase A hA hAconv) (hbase B hBm hBc)
  simpa only [ν, τ, B, D] using hshell.trans_eq (by ring)

/-- The small-cardinality branch, with the dimension factor and the eventual induction constant
already inserted. -/
private theorem bentkusIdentity_error_le_of_small_cardinality
    {C M : ℝ} (hM : 0 ≤ M) (hMC : M ≤ C)
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hd : 0 < d)
    (hsmall : (n : ℝ) ≤ (d : ℝ) ^ 3 * M ^ 2)
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (A : Set (EuclideanSpace ℝ (Fin d))) :
    |(μ.map (fun ω ↦ ∑ i, X i ω)).real A -
        (stdGaussian (EuclideanSpace ℝ (Fin d))).real A| ≤
      C * (d : ℝ) ^ (1 / 4 : ℝ) *
        ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ := by
  let β := ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
  have hβ : 0 ≤ β := Finset.sum_nonneg fun i _ ↦
    integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg _) _
  have hdim : 1 ≤ (d : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hd) (by norm_num)
  have hbase := probability_error_le_M_mul_thirdMomentSum_of_small_cardinality
    (M := M) (X := X) (ν := stdGaussian (EuclideanSpace ℝ (Fin d)))
    hd hM hsmall hX3 h_indep hX0 hidentity A
  change _ ≤ C * (d : ℝ) ^ (1 / 4 : ℝ) * β
  calc
    |(μ.map (fun ω ↦ ∑ i, X i ω)).real A -
        (stdGaussian (EuclideanSpace ℝ (Fin d))).real A| ≤ M * β := hbase
    _ ≤ C * (d : ℝ) ^ (1 / 4 : ℝ) * β := by
      have hC : 0 ≤ C := hM.trans hMC
      have hfactor : M ≤ C * (d : ℝ) ^ (1 / 4 : ℝ) := by
        calc
          M ≤ C := hMC
          _ ≤ C * (d : ℝ) ^ (1 / 4 : ℝ) := by nlinarith
      exact mul_le_mul_of_nonneg_right hfactor hβ

/-- Identity total covariance in positive dimension forces the Lyapunov third-moment sum to be
strictly positive. -/
lemma thirdMomentSum_pos_of_identityCovariance
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hd : 0 < d) (hX3 : ∀ i, MemLp (X i) 3 μ)
    (h_indep : iIndepFun X μ) (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y) :
    0 < ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ := by
  let β := ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
  have hβ : 0 ≤ β := Finset.sum_nonneg fun i _ ↦
    integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg _) _
  have hdim := dimension_cube_le_card_mul_thirdMomentSum_sq
    hX3 h_indep hX0 hidentity
  change (d : ℝ) ^ 3 ≤ (n : ℝ) * β ^ 2 at hdim
  have hd3 : 0 < (d : ℝ) ^ 3 := pow_pos (by exact_mod_cast hd) _
  change 0 < β
  by_contra hnot
  have hzero : β = 0 := le_antisymm (le_of_not_gt hnot) hβ
  rw [hzero] at hdim
  norm_num at hdim
  linarith

/-- The exact (3.9)--(3.10) closure at one convex set.  All probability and moment side
conditions needed by `bentkus_parameter_closure` are discharged here; the sole remaining premise
is the small-smoothing-scale Taylor estimate. -/
theorem bentkusIdentity_error_le_of_taylor_estimate
    {K C : ℝ} (hC : 1 ≤ C) (hKC : K * (2 * Real.sqrt C + 1) ≤ C)
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hd : 0 < d) (hX3 : ∀ i, MemLp (X i) 3 μ)
    (h_indep : iIndepFun X μ) (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (A : Set (EuclideanSpace ℝ (Fin d)))
    (hTaylor :
      let β := ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
      |(μ.map (fun ω ↦ ∑ i, X i ω)).real A -
          (stdGaussian (EuclideanSpace ℝ (Fin d))).real A| ≤ 1 ∧
      (β * Real.sqrt C < 1 →
        |(μ.map (fun ω ↦ ∑ i, X i ω)).real A -
            (stdGaussian (EuclideanSpace ℝ (Fin d))).real A| ≤
          K * (d : ℝ) ^ (1 / 4 : ℝ) *
            (β * Real.sqrt C + β + C * β ^ 2 / (β * Real.sqrt C)))) :
    |(μ.map (fun ω ↦ ∑ i, X i ω)).real A -
        (stdGaussian (EuclideanSpace ℝ (Fin d))).real A| ≤
      C * (d : ℝ) ^ (1 / 4 : ℝ) *
        ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ := by
  let β := ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
  let Δ := |(μ.map (fun ω ↦ ∑ i, X i ω)).real A -
    (stdGaussian (EuclideanSpace ℝ (Fin d))).real A|
  have hβ : 0 < β := thirdMomentSum_pos_of_identityCovariance
    hd hX3 h_indep hX0 hidentity
  have hdreal : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have ht := hTaylor
  change Δ ≤ C * (d : ℝ) ^ (1 / 4 : ℝ) * β
  exact bentkus_parameter_closure hC hKC hdreal hβ ht.1 ht.2

/-- The large-individual-second-moment branch, with the full Lyapunov sum and the dimension factor
already inserted. -/
private theorem bentkusIdentity_error_le_of_large_secondMoment
    {C : ℝ} (hC : 8 ≤ C)
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hd : 0 < d) (hX3 : ∀ i, MemLp (X i) 3 μ)
    (k : Fin n) (hk : 1 / 4 ≤ ∫ ω, ‖X k ω‖ ^ 2 ∂μ)
    (A : Set (EuclideanSpace ℝ (Fin d))) :
    |(μ.map (fun ω ↦ ∑ i, X i ω)).real A -
        (stdGaussian (EuclideanSpace ℝ (Fin d))).real A| ≤
      C * (d : ℝ) ^ (1 / 4 : ℝ) *
        ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ := by
  let β := ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ
  have hβ : 0 ≤ β := Finset.sum_nonneg fun i _ ↦
    integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg _) _
  have hdim : 1 ≤ (d : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hd) (by norm_num)
  have hk3nonneg : 0 ≤ ∫ ω, ‖X k ω‖ ^ 3 ∂μ :=
    integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg _) _
  have hksum : (∫ ω, ‖X k ω‖ ^ 3 ∂μ) ≤ β := by
    dsimp only [β]
    exact Finset.single_le_sum
      (f := fun i : Fin n ↦ ∫ ω, ‖X i ω‖ ^ 3 ∂μ) (s := Finset.univ)
      (fun (i : Fin n) _ ↦ integral_nonneg (μ := μ) fun ω ↦
        pow_nonneg (norm_nonneg (X i ω)) 3) (Finset.mem_univ k)
  letI : IsProbabilityMeasure (μ.map (fun ω ↦ ∑ i, X i ω)) :=
    Measure.isProbabilityMeasure_map
      (memLp_finsetSum Finset.univ fun i _ ↦ hX3 i).aemeasurable
  have hprob := probability_measureReal_abs_sub_le_one
    (μ.map (fun ω ↦ ∑ i, X i ω))
    (stdGaussian (EuclideanSpace ℝ (Fin d))) A
  have hkLower := large_secondMoment_thirdMoment_lower (hX3 k) hk
  change _ ≤ C * (d : ℝ) ^ (1 / 4 : ℝ) * β
  calc
    |(μ.map (fun ω ↦ ∑ i, X i ω)).real A -
        (stdGaussian (EuclideanSpace ℝ (Fin d))).real A| ≤ 1 := hprob
    _ ≤ 8 * (∫ ω, ‖X k ω‖ ^ 3 ∂μ) := hkLower
    _ ≤ C * (d : ℝ) ^ (1 / 4 : ℝ) * β := by
      have hCd : 8 ≤ C * (d : ℝ) ^ (1 / 4 : ℝ) := by
        nlinarith
      calc
        8 * (∫ ω, ‖X k ω‖ ^ 3 ∂μ) ≤ 8 * β :=
          mul_le_mul_of_nonneg_left hksum (by norm_num)
        _ ≤ (C * (d : ℝ) ^ (1 / 4 : ℝ)) * β :=
          mul_le_mul_of_nonneg_right hCd hβ
        _ = C * (d : ℝ) ^ (1 / 4 : ℝ) * β := rfl

/-- A complete logical split of one induction slice into Bentkus's two trivial branches and the
nontrivial Taylor branch.  The latter premise contains exactly the strict inequalities left after
the two branch eliminations. -/
theorem bentkusIdentityCovarianceBoundAt_of_nontrivial
    {C M : ℝ} (hM : 0 ≤ M) (hMC : M ≤ C) (h8C : 8 ≤ C) {n : ℕ}
    (hmain :
      ∀ {d : ℕ} (_hd : 0 < d)
        {Ω : Type u} [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)),
        (∀ i, Measurable (X i)) →
        (∀ i, MemLp (X i) 3 μ) →
        iIndepFun X μ →
        (∀ i, ∫ ω, X i ω ∂μ = 0) →
        (∀ x y,
          covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y) →
        (d : ℝ) ^ 3 * M ^ 2 < (n : ℝ) →
        (∀ k, (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4) →
        ∀ A : Set (EuclideanSpace ℝ (Fin d)),
          MeasurableSet A →
          Convexity.IsConvexSet ℝ A →
          |(μ.map (fun ω ↦ ∑ i, X i ω)).real A -
              (stdGaussian (EuclideanSpace ℝ (Fin d))).real A| ≤
            C * (d : ℝ) ^ (1 / 4 : ℝ) *
              ∑ i, ∫ ω, ‖X i ω‖ ^ 3 ∂μ) :
    bentkusIdentityCovarianceBoundAtMeasurable.{u} C n := by
  intro d hd Ω _ μ _ X hXm hX3 h_indep hX0 hidentity A hA hAconv
  by_cases hsmall : (n : ℝ) ≤ (d : ℝ) ^ 3 * M ^ 2
  · exact bentkusIdentity_error_le_of_small_cardinality
      hM hMC hd hsmall hX3 h_indep hX0 hidentity A
  · have hnlarge : (d : ℝ) ^ 3 * M ^ 2 < (n : ℝ) := lt_of_not_ge hsmall
    by_cases hlarge : ∃ k, 1 / 4 ≤ ∫ ω, ‖X k ω‖ ^ 2 ∂μ
    · obtain ⟨k, hk⟩ := hlarge
      exact bentkusIdentity_error_le_of_large_secondMoment h8C hd hX3 k hk A
    · have hsmallMoment : ∀ k, (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4 := by
        intro k
        exact lt_of_not_ge fun hk ↦ hlarge ⟨k, hk⟩
      exact hmain hd μ X hXm hX3 h_indep hX0 hidentity hnlarge hsmallMoment A hA hAconv

end BentkusInduction

end ProbabilityTheory
