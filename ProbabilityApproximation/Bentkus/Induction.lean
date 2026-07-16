/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.Bentkus.GaussianCompanionMoments
import ProbabilityApproximation.Bentkus.GaussianDensityDerivatives
import ProbabilityApproximation.Bentkus.GaussianDensityIntegrationByParts
import ProbabilityApproximation.Bentkus.GaussianIntegrationByParts
import ProbabilityApproximation.Bentkus.CutoffDerivativeGaussianIBP
import ProbabilityApproximation.Bentkus.InductionBranches
import ProbabilityApproximation.Bentkus.LeaveOneOutWhitening
import ProbabilityApproximation.Bentkus.ParameterClosure
import ProbabilityApproximation.Bentkus.SmoothingInequality
import ProbabilityApproximation.Bentkus.TaylorRemainder
import ProbabilityApproximation.Bentkus.Whitening
import ProbabilityApproximation.ConvexGeometry.GaussianShell
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.InfinitePi

/-!
# Bentkus's standardized replacement induction

This module implements Section 3 of V. Bentkus, *A Lyapunov type bound in `R^d`*, printed
pp. 403--410.  The proof first treats the identity-total-covariance problem and only afterwards
uses the whitening reduction from `ProbabilityApproximation.Bentkus.Whitening`.
-/

open MeasureTheory InnerProductSpace Matrix Set
open scoped ENNReal MatrixOrder RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

universe u

local instance bentkusConvexSpace {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

local instance bentkusIsModuleConvexSpace {d : ℕ} :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.ofModule

private abbrev BentkusEuclideanSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

private lemma isConvexSet_preimage_continuousLinearMap
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

/-- The `n`-summand slice of the standardized Bentkus assertion. -/
private def bentkusIdentityCovarianceBoundAt (C : ℝ) (n : ℕ) : Prop :=
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
    · simp only [hp, if_false]
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
    congr 1
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
private theorem
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
private theorem integral_comp_pair_eq_iterated_of_map_eq_prod
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

private theorem integral_integral_eq_zero_of_integral_eq_zero
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
private theorem
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
private theorem integral_convexSetCutoff_endpoint_eq_neg_rotation
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
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_smul]
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

private theorem integral_fderiv_convexSetCutoff_scaled_unwhitening_stdGaussian_eq_neg_D1
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
private theorem integral_standardGaussianDensityD1_whitened_replacementRotatedDeriv_eq_zero
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
private theorem integral_standardGaussianDensityD2_whitened_replacementRotated_eq_zero
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
private theorem integral_fderiv_convexSetCutoff_gaussianLeaveOneOut_eq_neg_iterated_D1
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
private theorem bentkus_oneSet_taylorEstimate_of_smoothCutoff_and_shell
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

section

set_option maxHeartbeats 2000000

/-- It suffices to prove an induction slice for everywhere-measurable representatives.  `MemLp`
only supplies an almost-everywhere strongly measurable representative, so this lemma performs the
representative change once and transports independence, covariance, laws, means, and third
moments. -/
private theorem bentkusIdentityCovarianceBoundAt_of_measurable
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
private lemma measureReal_sdiff_le_add_two_mul_of_abs_sub_le
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
private theorem map_prod_stdGaussian_weightedAdd_eq_stdGaussian
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

/-- Convex-set distance contracts under a common independent additive noise and a common scalar
multiple.  This is the measure-level conditioning step used in Bentkus (3.31)--(3.34). -/
private theorem convexDistance_map_prod_affineNoise_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [Convexity.ConvexSpace ℝ E] [Convexity.IsModuleConvexSpace ℝ E]
    {ν τ κ : Measure E} [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]
    [IsProbabilityMeasure κ] {D : ℝ} (hD : 0 ≤ D)
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
private lemma convexSetCutoff_superlevel_isConvexSet
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

private lemma isConvexSet_preimage_add_right
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
private theorem abs_integral_quasiconcave_sub_le_convexDistance
    {d : ℕ} {ν τ : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]
    {D : ℝ} (hD : 0 ≤ D)
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
private theorem bentkusWhitenedLeaveOneOut_error_le_of_induction
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

private theorem map_whitenedRotatedLeaveOneOut_eq_map_prod
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

private theorem map_whitenedRotatedLeaveOneOut_replacementPair_eq_prod
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
private lemma thirdMomentSum_pos_of_identityCovariance
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
private theorem bentkusIdentity_error_le_of_taylor_estimate
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
private theorem bentkusIdentityCovarianceBoundAt_of_nontrivial
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

/-- The first standard-Gaussian density contraction has its expected dimension-free `L¹`
bound. -/
private lemma integral_abs_standardGaussianDensityD1_volume_le
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
private lemma integrable_standardGaussianDensityD2_volume
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
private lemma integral_abs_standardGaussianDensityD2_volume_le
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

private lemma integrable_prod_bounded_mul_standardGaussianDensityD1
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
private lemma integrable_prod_bounded_mul_standardGaussianDensityD1_sub
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
private theorem integral_fderiv_convexSetCutoff_gaussianLeaveOneOut_eq_neg_translated_D1
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

private lemma integrable_prod_bounded_mul_standardGaussianDensityD2
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
private theorem bentkus_integral_integral_lowOrderDensity_eq_zero
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
private lemma standardGaussianDensityD1_add_taylor_one
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

private theorem
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

/-- The two mixed moments in Bentkus (3.39)--(3.40), after leave-one-out whitening.  The constants
are deliberately inherited from the already proved rotation-moment estimate. -/
private theorem bentkus_whitened_coordinate_twoShift_moments_le
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (r : ℝ) (hr : 0 ≤ r) :
    let ρ := bentkusReplacementMeasure μ X
    let B := bentkusWhiteningCLM (bentkusLeaveOneOutCovarianceMatrix μ X k)
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    (∫ ω, ‖B (O ω)‖ ^ 2 * (‖B (G ω)‖ + r * ‖B (O ω)‖) ∂ρ) ≤
        (896 + 8 * r) * ∫ ω, ‖O ω‖ ^ 3 ∂ρ ∧
      (∫ ω, ‖B (G ω)‖ ^ 2 * (r * ‖B (O ω)‖ + ‖B (G ω)‖) ∂ρ) ≤
        (896 * r + 216) * ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
  let ρ := bentkusReplacementMeasure μ X
  let B := bentkusWhiteningCLM (bentkusLeaveOneOutCovarianceMatrix μ X k)
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hO3 : MemLp O 3 ρ := memLp_replacementOriginal hXm hX3 k
  have hG3 : MemLp G 3 ρ := memLp_three_replacementGaussian hXm k
  have hBO3 : MemLp (fun ω ↦ B (O ω)) 3 ρ :=
    memLp_bentkusWhiteningCLM_comp _ hO3
  have hBG3 : MemLp (fun ω ↦ B (G ω)) 3 ρ :=
    memLp_bentkusWhiteningCLM_comp _ hG3
  have hBO3int : Integrable (fun ω ↦ ‖B (O ω)‖ ^ 3) ρ :=
    hBO3.integrable_norm_pow (by norm_num)
  have hBG3int : Integrable (fun ω ↦ ‖B (G ω)‖ ^ 3) ρ :=
    hBG3.integrable_norm_pow (by norm_num)
  have hcubic (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 * b ≤ a ^ 3 + b ^ 3 := by
    by_cases hab : b ≤ a
    · calc
        a ^ 2 * b ≤ a ^ 2 * a := mul_le_mul_of_nonneg_left hab (sq_nonneg a)
        _ ≤ a ^ 3 + b ^ 3 := by
          rw [show a ^ 2 * a = a ^ 3 by ring]
          exact le_add_of_nonneg_right (pow_nonneg hb 3)
    · have hab' : a ≤ b := le_of_not_ge hab
      calc
        a ^ 2 * b ≤ b ^ 2 * b := by gcongr
        _ ≤ a ^ 3 + b ^ 3 := by
          rw [show b ^ 2 * b = b ^ 3 by ring]
          exact le_add_of_nonneg_left (pow_nonneg ha 3)
  have hOGint : Integrable (fun ω ↦ ‖B (O ω)‖ ^ 2 * ‖B (G ω)‖) ρ := by
    apply (hBO3int.add hBG3int).mono'
      ((hBO3.aestronglyMeasurable.norm.pow 2).mul hBG3.aestronglyMeasurable.norm)
    filter_upwards with ω
    change |‖B (O ω)‖ ^ 2 * ‖B (G ω)‖| ≤
      ‖B (O ω)‖ ^ 3 + ‖B (G ω)‖ ^ 3
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _))]
    exact hcubic _ _ (norm_nonneg _) (norm_nonneg _)
  have hGOint : Integrable (fun ω ↦ ‖B (G ω)‖ ^ 2 * ‖B (O ω)‖) ρ := by
    apply (hBG3int.add hBO3int).mono'
      ((hBG3.aestronglyMeasurable.norm.pow 2).mul hBO3.aestronglyMeasurable.norm)
    filter_upwards with ω
    change |‖B (G ω)‖ ^ 2 * ‖B (O ω)‖| ≤
      ‖B (G ω)‖ ^ 3 + ‖B (O ω)‖ ^ 3
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _))]
    exact hcubic _ _ (norm_nonneg _) (norm_nonneg _)
  have hOG : (∫ ω, ‖B (O ω)‖ ^ 2 * ‖B (G ω)‖ ∂ρ) ≤
      896 * ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
    simpa only [ρ, B, O, G, bentkusRotated, bentkusRotatedDeriv,
      Real.cos_zero, Real.sin_zero, one_smul, zero_smul, zero_add, add_zero, neg_zero,
      map_add, map_zero] using
      (integral_norm_whitened_replacementRotated_sq_mul_norm_whitened_replacementRotatedDeriv_le
        hXm hX3 h_indep hX0 hidentity k hk 0)
  have hGO : (∫ ω, ‖B (G ω)‖ ^ 2 * ‖B (O ω)‖ ∂ρ) ≤
      896 * ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
    simpa only [ρ, B, O, G, bentkusRotated, bentkusRotatedDeriv,
      Real.cos_pi_div_two, Real.sin_pi_div_two, one_smul, zero_smul, add_zero,
      zero_add, neg_one_smul, norm_neg, map_add, map_zero, map_neg] using
      (integral_norm_whitened_replacementRotated_sq_mul_norm_whitened_replacementRotatedDeriv_le
        hXm hX3 h_indep hX0 hidentity k hk (Real.pi / 2))
  have hBO : (∫ ω, ‖B (O ω)‖ ^ 3 ∂ρ) ≤
      8 * ∫ ω, ‖O ω‖ ^ 3 ∂ρ :=
    integral_norm_bentkusWhiteningCLM_leaveOneOut_pow_three_le
      hX3 h_indep hX0 hidentity k hk hO3
  have hBGbase : (∫ ω, ‖B (G ω)‖ ^ 3 ∂ρ) ≤
      8 * ∫ ω, ‖G ω‖ ^ 3 ∂ρ :=
    integral_norm_bentkusWhiteningCLM_leaveOneOut_pow_three_le
      hX3 h_indep hX0 hidentity k hk hG3
  have hGcomp := integral_norm_pow_three_replacementGaussian_le hXm hX3 hX0 k
  have hBG : (∫ ω, ‖B (G ω)‖ ^ 3 ∂ρ) ≤
      216 * ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
    calc
      _ ≤ 8 * ∫ ω, ‖G ω‖ ^ 3 ∂ρ := hBGbase
      _ ≤ 8 * (gaussianCompanionThirdMomentConstant *
          ∫ ω, ‖O ω‖ ^ 3 ∂ρ) := by gcongr
      _ = 216 * ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
        norm_num [gaussianCompanionThirdMomentConstant]
        ring
  constructor
  · calc
      (∫ ω, ‖B (O ω)‖ ^ 2 * (‖B (G ω)‖ + r * ‖B (O ω)‖) ∂ρ) =
          (∫ ω, ‖B (O ω)‖ ^ 2 * ‖B (G ω)‖ ∂ρ) +
            r * ∫ ω, ‖B (O ω)‖ ^ 3 ∂ρ := by
        rw [← integral_const_mul, ← integral_add hOGint (hBO3int.const_mul r)]
        apply integral_congr_ae
        filter_upwards with ω
        ring
      _ ≤ 896 * (∫ ω, ‖O ω‖ ^ 3 ∂ρ) +
          r * (8 * ∫ ω, ‖O ω‖ ^ 3 ∂ρ) :=
        add_le_add hOG (mul_le_mul_of_nonneg_left hBO hr)
      _ = (896 + 8 * r) * ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by ring
  · calc
      (∫ ω, ‖B (G ω)‖ ^ 2 * (r * ‖B (O ω)‖ + ‖B (G ω)‖) ∂ρ) =
          r * (∫ ω, ‖B (G ω)‖ ^ 2 * ‖B (O ω)‖ ∂ρ) +
            ∫ ω, ‖B (G ω)‖ ^ 3 ∂ρ := by
        rw [← integral_const_mul, ← integral_add (hGOint.const_mul r) hBG3int]
        apply integral_congr_ae
        filter_upwards with ω
        ring
      _ ≤ r * (896 * ∫ ω, ‖O ω‖ ^ 3 ∂ρ) +
          216 * ∫ ω, ‖O ω‖ ^ 3 ∂ρ :=
        add_le_add (mul_le_mul_of_nonneg_left hGO hr) hBG
      _ = (896 * r + 216) * ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by ring

/-- Analytic remainder budget in Bentkus (3.37)--(3.40), at one angle.  The statement preserves
the decisive `cos α / (sin α)²` dependence. -/
private theorem bentkus_largeAngle_twoShiftDensityRemainders_le
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφm : Measurable φ)
    {D : ℝ} (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ D)
    (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    let ρ := bentkusReplacementMeasure μ X
    let B := bentkusWhiteningCLM (bentkusLeaveOneOutCovarianceMatrix μ X k)
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let r := p / q
    |∫ ω, (∫ x, φ x *
        (standardGaussianDensityD1 (x + (-(B (G ω))) + (-r) • B (O ω)) (B (O ω)) -
          standardGaussianDensityD1 (x + (-(B (G ω)))) (B (O ω)) -
          standardGaussianDensityD2 x (B (O ω)) ((-r) • B (O ω)))
        ∂volume) ∂ρ| +
      r * |∫ ω, (∫ x, φ x *
        (standardGaussianDensityD1 (x + ((-r) • B (O ω)) + (-1 : ℝ) • B (G ω))
            (B (G ω)) -
          standardGaussianDensityD1 (x + ((-r) • B (O ω))) (B (G ω)) -
          standardGaussianDensityD2 x (B (G ω)) ((-1 : ℝ) • B (G ω)))
        ∂volume) ∂ρ| ≤
      2016 * D * (3 + Real.sqrt standardGaussianFourthMoment) *
        (p / q ^ 2) * ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
  let ρ := bentkusReplacementMeasure μ X
  let B := bentkusWhiteningCLM (bentkusLeaveOneOutCovarianceMatrix μ X k)
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let r := p / q
  let K : ℝ := 3 + Real.sqrt standardGaussianFourthMoment
  let βk : ℝ := ∫ ω, ‖O ω‖ ^ 3 ∂ρ
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hr : 0 ≤ r := div_nonneg hp0 hq0.le
  have hrAbs : |r| = r := abs_of_nonneg hr
  have hO3 : MemLp O 3 ρ := memLp_replacementOriginal hXm hX3 k
  have hG3 : MemLp G 3 ρ := memLp_three_replacementGaussian hXm k
  have hBO3 : MemLp (fun ω ↦ B (O ω)) 3 ρ :=
    memLp_bentkusWhiteningCLM_comp _ hO3
  have hBG3 : MemLp (fun ω ↦ B (G ω)) 3 ρ :=
    memLp_bentkusWhiteningCLM_comp _ hG3
  have hOm : Measurable O := by
    exact (measurable_pi_apply k).comp measurable_fst
  have hGm : Measurable G := by
    exact (measurable_pi_apply k).comp measurable_snd
  have hBOm : Measurable (fun ω ↦ B (O ω)) := B.continuous.measurable.comp hOm
  have hBGm : Measurable (fun ω ↦ B (G ω)) := B.continuous.measurable.comp hGm
  have hcubic (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 * b ≤ a ^ 3 + b ^ 3 := by
    by_cases hab : b ≤ a
    · calc
        a ^ 2 * b ≤ a ^ 2 * a := mul_le_mul_of_nonneg_left hab (sq_nonneg a)
        _ ≤ a ^ 3 + b ^ 3 := by
          rw [show a ^ 2 * a = a ^ 3 by ring]
          exact le_add_of_nonneg_right (pow_nonneg hb 3)
    · have hab' : a ≤ b := le_of_not_ge hab
      calc
        a ^ 2 * b ≤ b ^ 2 * b := by gcongr
        _ ≤ a ^ 3 + b ^ 3 := by
          rw [show b ^ 2 * b = b ^ 3 by ring]
          exact le_add_of_nonneg_left (pow_nonneg ha 3)
  have hBO3int : Integrable (fun ω ↦ ‖B (O ω)‖ ^ 3) ρ :=
    hBO3.integrable_norm_pow (by norm_num)
  have hBG3int : Integrable (fun ω ↦ ‖B (G ω)‖ ^ 3) ρ :=
    hBG3.integrable_norm_pow (by norm_num)
  have hfirstInt : Integrable
      (fun ω ↦ ‖B (O ω)‖ ^ 2 * (‖-(B (G ω))‖ + |-r| * ‖B (O ω)‖)) ρ := by
    have hmajor : Integrable (fun ω ↦
        (1 + r) * ‖B (O ω)‖ ^ 3 + ‖B (G ω)‖ ^ 3) ρ :=
      (hBO3int.const_mul (1 + r)).add hBG3int
    have hm : AEStronglyMeasurable
        (fun ω ↦ ‖B (O ω)‖ ^ 2 * (‖-(B (G ω))‖ + |-r| * ‖B (O ω)‖)) ρ := by
      exact (hBO3.aestronglyMeasurable.norm.pow 2).mul
        (hBG3.aestronglyMeasurable.neg.norm.add
          (hBO3.aestronglyMeasurable.norm.const_mul |-r|))
    apply hmajor.mono' hm
    filter_upwards with ω
    simp only [norm_neg, abs_neg, hrAbs]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hmixed := hcubic ‖B (O ω)‖ ‖B (G ω)‖ (norm_nonneg _) (norm_nonneg _)
    nlinarith [mul_nonneg hr (pow_nonneg (norm_nonneg (B (O ω))) 3)]
  have hsecondInt : Integrable
      (fun ω ↦ ‖B (G ω)‖ ^ 2 *
        (‖(-r) • B (O ω)‖ + |(-1 : ℝ)| * ‖B (G ω)‖)) ρ := by
    have hmajor : Integrable (fun ω ↦
        r * ‖B (O ω)‖ ^ 3 + (r + 1) * ‖B (G ω)‖ ^ 3) ρ :=
      (hBO3int.const_mul r).add (hBG3int.const_mul (r + 1))
    have hm : AEStronglyMeasurable (fun ω ↦ ‖B (G ω)‖ ^ 2 *
        (‖(-r) • B (O ω)‖ + |(-1 : ℝ)| * ‖B (G ω)‖)) ρ := by
      exact (hBG3.aestronglyMeasurable.norm.pow 2).mul
        ((hBO3.aestronglyMeasurable.const_smul (-r)).norm.add
          (hBG3.aestronglyMeasurable.norm.const_mul |(-1 : ℝ)|))
    apply hmajor.mono' hm
    filter_upwards with ω
    simp only [norm_smul, Real.norm_eq_abs, abs_neg, hrAbs, abs_one, one_mul]
    rw [abs_of_nonneg (by positivity)]
    have hmixed := hcubic ‖B (G ω)‖ ‖B (O ω)‖ (norm_nonneg _) (norm_nonneg _)
    nlinarith [mul_nonneg hr (pow_nonneg (norm_nonneg (B (O ω))) 3),
      mul_nonneg hr (pow_nonneg (norm_nonneg (B (G ω))) 3)]
  have hfirst :=
    bentkus_integral_standardGaussianDensityD1_twoShift_integral_bound_of_bounded
      hφm hD hφ (v := fun ω ↦ -(B (G ω))) (g := fun ω ↦ B (O ω))
      hBGm.neg hBOm (-r) hfirstInt
  have hsecond :=
    bentkus_integral_standardGaussianDensityD1_twoShift_integral_bound_of_bounded
      hφm hD hφ (v := fun ω ↦ (-r) • B (O ω)) (g := fun ω ↦ B (G ω))
      (by
        change Measurable ((-r) • (fun ω ↦ B (O ω)))
        exact hBOm.const_smul (-r))
      hBGm (-1) hsecondInt
  have hmom := bentkus_whitened_coordinate_twoShift_moments_le
    hXm hX3 h_indep hX0 hidentity k hk r hr
  have hfirst' :
      |∫ ω, (∫ x, φ x *
        (standardGaussianDensityD1 (x + (-(B (G ω))) + (-r) • B (O ω)) (B (O ω)) -
          standardGaussianDensityD1 (x + (-(B (G ω)))) (B (O ω)) -
          standardGaussianDensityD2 x (B (O ω)) ((-r) • B (O ω))) ∂volume) ∂ρ| ≤
        D * r * K * ((896 + 8 * r) * βk) := by
    calc
      _ ≤ D * r * K *
          ∫ ω, ‖B (O ω)‖ ^ 2 * (‖B (G ω)‖ + r * ‖B (O ω)‖) ∂ρ := by
        simpa only [abs_neg, hrAbs, norm_neg, K, mul_assoc] using hfirst
      _ ≤ D * r * K * ((896 + 8 * r) * βk) := by
        gcongr
        simpa only [βk, ρ, B, O, G] using hmom.1
  have hsecond' :
      |∫ ω, (∫ x, φ x *
        (standardGaussianDensityD1 (x + ((-r) • B (O ω)) + (-1 : ℝ) • B (G ω))
            (B (G ω)) -
          standardGaussianDensityD1 (x + ((-r) • B (O ω))) (B (G ω)) -
          standardGaussianDensityD2 x (B (G ω)) ((-1 : ℝ) • B (G ω))) ∂volume) ∂ρ| ≤
        D * K * ((896 * r + 216) * βk) := by
    calc
      _ ≤ D * K *
          ∫ ω, ‖B (G ω)‖ ^ 2 * (r * ‖B (O ω)‖ + ‖B (G ω)‖) ∂ρ := by
        simpa only [abs_neg, hrAbs, abs_one, norm_smul, Real.norm_eq_abs,
          one_mul, K, mul_assoc] using hsecond
      _ ≤ D * K * ((896 * r + 216) * βk) := by
        gcongr
        simpa only [βk, ρ, B, O, G] using hmom.2
  have hβk : 0 ≤ βk := integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg _) 3
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hrle : r ≤ 1 / q := by
    dsimp only [r]
    exact (div_le_div_iff_of_pos_right hq0).2 hp1
  have hcoef : r * (1112 + 904 * r) ≤ 2016 * (p / q ^ 2) := by
    have h1112 : (1112 : ℝ) ≤ 1112 / q := by
      apply (le_div_iff₀ hq0).2
      nlinarith
    have h904 : 904 * r ≤ 904 / q := by
      calc
        904 * r ≤ 904 * (1 / q) := by gcongr
        _ = 904 / q := by ring
    calc
      r * (1112 + 904 * r) ≤ r * (2016 / q) := by
        gcongr
        calc
          1112 + 904 * r ≤ 1112 / q + 904 / q := add_le_add h1112 h904
          _ = 2016 / q := by ring
      _ = 2016 * (p / q ^ 2) := by
        dsimp only [r]
        field_simp
  calc
    |∫ ω, (∫ x, φ x *
        (standardGaussianDensityD1 (x + (-(B (G ω))) + (-r) • B (O ω)) (B (O ω)) -
          standardGaussianDensityD1 (x + (-(B (G ω)))) (B (O ω)) -
          standardGaussianDensityD2 x (B (O ω)) ((-r) • B (O ω))) ∂volume) ∂ρ| +
      r * |∫ ω, (∫ x, φ x *
        (standardGaussianDensityD1 (x + ((-r) • B (O ω)) + (-1 : ℝ) • B (G ω))
            (B (G ω)) -
          standardGaussianDensityD1 (x + ((-r) • B (O ω))) (B (G ω)) -
          standardGaussianDensityD2 x (B (G ω)) ((-1 : ℝ) • B (G ω))) ∂volume) ∂ρ| ≤
        D * r * K * ((896 + 8 * r) * βk) +
          r * (D * K * ((896 * r + 216) * βk)) :=
      add_le_add hfirst' (mul_le_mul_of_nonneg_left hsecond' hr)
    _ = D * K * (r * (1112 + 904 * r)) * βk := by ring
    _ ≤ D * K * (2016 * (p / q ^ 2)) * βk := by gcongr
    _ = 2016 * D * (3 + Real.sqrt standardGaussianFourthMoment) *
        (p / q ^ 2) * ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
      dsimp only [K, βk]
      ring

/-- The second-order integral Taylor formula for the first standard-Gaussian density
contraction, in the orientation used in Bentkus (3.17)--(3.19). -/
private lemma standardGaussianDensityD1_sub_taylor_two
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

/-- The pointwise Gaussian-density remainder estimate remains valid after conditioning on an
arbitrary measurable parameter.  This is the Fubini step used for the omitted pair
`(X_k,Y_k)` in Bentkus (3.15). -/
private theorem
    bentkus_integral_standardGaussianDensityD1_secondOrderRemainder_le
    {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφm : Measurable φ) (hφ : ∀ x, |φ x| ≤ 1)
    {h g : Ξ → EuclideanSpace ℝ (Fin d)}
    (hh : Measurable h) (hg : Measurable g)
    (hhg : Integrable (fun z ↦ ‖h z‖ ^ 2 * ‖g z‖) ν) :
    |∫ z, (∫ x, φ x *
        (standardGaussianDensityD1 (x - h z) (g z) -
          standardGaussianDensityD1 x (g z) +
          standardGaussianDensityD2 x (h z) (g z)) ∂volume) ∂ν| ≤
      (3 + Real.sqrt standardGaussianFourthMoment) / 2 *
        ∫ z, ‖h z‖ ^ 2 * ‖g z‖ ∂ν := by
  let c : ℝ := (3 + Real.sqrt standardGaussianFourthMoment) / 2
  let R : Ξ → EuclideanSpace ℝ (Fin d) → ℝ := fun z x ↦ φ x *
    (standardGaussianDensityD1 (x - h z) (g z) -
      standardGaussianDensityD1 x (g z) +
      standardGaussianDensityD2 x (h z) (g z))
  have hRm : Measurable (Function.uncurry R) := by
    change Measurable (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ φ p.2 *
      (standardGaussianDensityD1 (p.2 - h p.1) (g p.1) -
        standardGaussianDensityD1 p.2 (g p.1) +
        standardGaussianDensityD2 p.2 (h p.1) (g p.1)))
    unfold standardGaussianDensityD1 standardGaussianDensityD2
    have hx : Measurable (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ p.2) := measurable_snd
    have hh' : Measurable (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ h p.1) :=
      hh.comp measurable_fst
    have hg' : Measurable (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ g p.1) :=
      hg.comp measurable_fst
    have hshift : Measurable
        (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ p.2 - h p.1) := hx.sub hh'
    have hinnerShift : Measurable
        (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ inner ℝ (p.2 - h p.1) (g p.1)) :=
      by
        change Measurable
          ((fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
              inner ℝ q.1 q.2) ∘
            fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ (p.2 - h p.1, g p.1))
        exact continuous_inner.measurable.comp (hshift.prodMk hg')
    have hinnerXG : Measurable
        (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ inner ℝ p.2 (g p.1)) :=
      by
        change Measurable
          ((fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
              inner ℝ q.1 q.2) ∘
            fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ (p.2, g p.1))
        exact continuous_inner.measurable.comp (hx.prodMk hg')
    have hinnerXH : Measurable
        (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ inner ℝ p.2 (h p.1)) :=
      by
        change Measurable
          ((fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
              inner ℝ q.1 q.2) ∘
            fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ (p.2, h p.1))
        exact continuous_inner.measurable.comp (hx.prodMk hh')
    have hinnerHG : Measurable
        (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ inner ℝ (h p.1) (g p.1)) :=
      by
        change Measurable
          ((fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
              inner ℝ q.1 q.2) ∘
            fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦ (h p.1, g p.1))
        exact continuous_inner.measurable.comp (hh'.prodMk hg')
    have hdensityShift : Measurable
        (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (p.2 - h p.1)) :=
      continuous_standardGaussianDensity.measurable.comp hshift
    have hdensityX : Measurable
        (fun p : Ξ × EuclideanSpace ℝ (Fin d) ↦
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) p.2) :=
      continuous_standardGaussianDensity.measurable.comp hx
    exact (hφm.comp hx).mul
      (((hinnerShift.neg.mul hdensityShift).sub (hinnerXG.neg.mul hdensityX)).add
        (((hinnerXH.mul hinnerXG).sub hinnerHG).mul hdensityX))
  have hinnerMeas : AEStronglyMeasurable (fun z ↦ ∫ x, R z x ∂volume) ν :=
    hRm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
  have hc : 0 ≤ c := by
    dsimp only [c]
    positivity
  have hmajorant : Integrable (fun z ↦ c * (‖h z‖ ^ 2 * ‖g z‖)) ν :=
    hhg.const_mul c
  have hpoint (z : Ξ) : |∫ x, R z x ∂volume| ≤
      c * (‖h z‖ ^ 2 * ‖g z‖) := by
    simpa only [R, c, mul_assoc] using
      bentkus_standardGaussianDensityD1_secondOrderRemainder_integral_bound
        hφm hφ (h z) (g z)
  have hinnerInt : Integrable (fun z ↦ ∫ x, R z x ∂volume) ν := by
    apply hmajorant.mono' hinnerMeas
    filter_upwards with z
    rw [Real.norm_eq_abs]
    exact hpoint z
  calc
    |∫ z, (∫ x, φ x *
        (standardGaussianDensityD1 (x - h z) (g z) -
          standardGaussianDensityD1 x (g z) +
          standardGaussianDensityD2 x (h z) (g z)) ∂volume) ∂ν| =
        |∫ z, ∫ x, R z x ∂volume ∂ν| := rfl
    _ ≤ ∫ z, |∫ x, R z x ∂volume| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ z, c * (‖h z‖ ^ 2 * ‖g z‖) ∂ν := by
      exact integral_mono hinnerInt.abs hmajorant hpoint
    _ = (3 + Real.sqrt standardGaussianFourthMoment) / 2 *
        ∫ z, ‖h z‖ ^ 2 * ‖g z‖ ∂ν := by
      rw [integral_const_mul]

/-- Bentkus (3.15), at a fixed coordinate and angle, after the constant, linear, and quadratic
terms have been removed.  The remaining Gaussian-density contribution is bounded by the third
moment of the original omitted summand. -/
private theorem bentkus_replacementRotated_D1_secondOrderRemainder_le
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (α : ℝ) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφm : Measurable φ) (hφ : ∀ x, |φ x| ≤ 1) :
    let ρ := bentkusReplacementMeasure μ X
    let B := bentkusWhiteningCLM (bentkusLeaveOneOutCovarianceMatrix μ X k)
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let H := fun ω ↦ B (bentkusRotated α O G ω)
    let K := fun ω ↦ B (bentkusRotatedDeriv α O G ω)
    |∫ ω, (∫ x, φ x *
        (standardGaussianDensityD1 (x - H ω) (K ω) -
          standardGaussianDensityD1 x (K ω) +
          standardGaussianDensityD2 x (H ω) (K ω)) ∂volume) ∂ρ| ≤
      448 * (3 + Real.sqrt standardGaussianFourthMoment) *
        ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  let B := bentkusWhiteningCLM S
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let R := bentkusRotated α O G
  let R' := bentkusRotatedDeriv α O G
  let H := fun ω ↦ B (R ω)
  let K := fun ω ↦ B (R' ω)
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hO3 : MemLp O 3 ρ := memLp_replacementOriginal hXm hX3 k
  have hG3 : MemLp G 3 ρ := memLp_three_replacementGaussian hXm k
  have hR3 : MemLp R 3 ρ := by
    change MemLp ((Real.cos α) • O + (Real.sin α) • G) 3 ρ
    exact (hO3.const_smul (Real.cos α)).add (hG3.const_smul (Real.sin α))
  have hR'3 : MemLp R' 3 ρ := by
    change MemLp ((-(Real.sin α)) • O + (Real.cos α) • G) 3 ρ
    exact (hO3.const_smul (-(Real.sin α))).add (hG3.const_smul (Real.cos α))
  have hH3 : MemLp H 3 ρ := by
    simpa only [H, B, S] using memLp_bentkusWhiteningCLM_comp S hR3
  have hK3 : MemLp K 3 ρ := by
    simpa only [K, B, S] using memLp_bentkusWhiteningCLM_comp S hR'3
  letI : ENNReal.HolderTriple 3 3 (3 / 2) := by
    constructor
    have hdiv : (3 / 2 : ℝ≥0∞) ≠ 0 :=
      ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩
    have hinvdiv : (3 / 2 : ℝ≥0∞)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hdiv
    rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) hinvdiv,
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    norm_num
  have hHsq : MemLp (fun ω ↦ ‖H ω‖ * ‖H ω‖) (3 / 2 : ℝ≥0∞) ρ := by
    exact hH3.norm.mul hH3.norm
  letI : ENNReal.HolderTriple (3 / 2) 3 1 := by
    constructor
    have hdiv : (3 / 2 : ℝ≥0∞) ≠ 0 :=
      ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩
    have hinvdiv : (3 / 2 : ℝ≥0∞)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hdiv
    rw [← ENNReal.toReal_eq_toReal_iff'
        (ENNReal.add_ne_top.mpr ⟨hinvdiv, by finiteness⟩) (by norm_num),
      ENNReal.toReal_add hinvdiv (by finiteness)]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_ofNat,
      ENNReal.toReal_one]
    norm_num
  have hmix : Integrable (fun ω ↦ ‖H ω‖ ^ 2 * ‖K ω‖) ρ := by
    have hprod := hHsq.integrable_mul hK3.norm
    refine hprod.congr ?_
    filter_upwards with ω
    simp only [Pi.mul_apply, pow_two]
  have hHmeas : Measurable H := by
    dsimp only [H, R, O, G, B, bentkusRotated,
      replacementOriginal, replacementGaussian]
    fun_prop
  have hKmeas : Measurable K := by
    dsimp only [K, R', O, G, B, bentkusRotatedDeriv,
      replacementOriginal, replacementGaussian]
    fun_prop
  have hrem := bentkus_integral_standardGaussianDensityD1_secondOrderRemainder_le
    (d := d) (ν := ρ) hφm hφ hHmeas hKmeas hmix
  have hmixed :=
    integral_norm_whitened_replacementRotated_sq_mul_norm_whitened_replacementRotatedDeriv_le
      hXm hX3 h_indep hX0 hidentity k hk α
  have hc : 0 ≤ (3 + Real.sqrt standardGaussianFourthMoment) / 2 := by positivity
  calc
    |∫ ω, (∫ x, φ x *
        (standardGaussianDensityD1 (x - H ω) (K ω) -
          standardGaussianDensityD1 x (K ω) +
          standardGaussianDensityD2 x (H ω) (K ω)) ∂volume) ∂ρ| ≤
        (3 + Real.sqrt standardGaussianFourthMoment) / 2 *
          ∫ ω, ‖H ω‖ ^ 2 * ‖K ω‖ ∂ρ := hrem
    _ ≤ (3 + Real.sqrt standardGaussianFourthMoment) / 2 *
        (896 * ∫ ω, ‖O ω‖ ^ 3 ∂ρ) :=
      mul_le_mul_of_nonneg_left (by simpa only [H, K, R, R', B, S, O, G, ρ] using hmixed) hc
    _ = 448 * (3 + Real.sqrt standardGaussianFourthMoment) *
        ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by ring

/-- Bentkus (3.15) at a fixed coordinate and angle.  Gaussian integration by parts, translation,
and equality of the first two moments reduce the full rotation derivative to the cubic density
remainder. -/
private theorem bentkus_gaussianLeaveOneOut_rotationDerivative_le
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
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let V := bentkusLeaveOneOut
      (fun i ↦ replacementGaussian (d := d) i) k
    let R := bentkusRotated α O G
    let R' := bentkusRotatedDeriv α O G
    |∫ ω, (fderiv ℝ (convexSetCutoff s ε) (V ω + R ω)) (R' ω) ∂ρ| ≤
      448 * (3 + Real.sqrt standardGaussianFourthMoment) *
        ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
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
  let H := fun ω ↦ B (R ω)
  let K := fun ω ↦ B (R' ω)
  let φ := fun x ↦ convexSetCutoff s ε (P x)
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hφm : Measurable φ :=
    (measurable_convexSetCutoff s ε).comp P.continuous.measurable
  have hφ : ∀ x, |φ x| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (convexSetCutoff_nonneg s ε (P x))]
    exact convexSetCutoff_le_one s ε (P x)
  have hO3 : MemLp O 3 ρ := memLp_replacementOriginal hXm hX3 k
  have hG3 : MemLp G 3 ρ := memLp_three_replacementGaussian hXm k
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
  have hKint : Integrable K ρ := hK3.integrable (by norm_num)
  have hshift : Integrable (fun p : _ × EuclideanSpace ℝ (Fin d) ↦
      φ p.2 * standardGaussianDensityD1 (p.2 - H p.1) (K p.1))
      (ρ.prod volume) :=
    integrable_prod_bounded_mul_standardGaussianDensityD1_sub
      hφm hφ hHm hKm hKint
  have hlinear : Integrable (fun p : _ × EuclideanSpace ℝ (Fin d) ↦
      φ p.2 * standardGaussianDensityD1 p.2 (K p.1)) (ρ.prod volume) :=
    integrable_prod_bounded_mul_standardGaussianDensityD1 hφm hφ hKm hKint
  have hH2 := hH3.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 3)
  have hK2 := hK3.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 3)
  have hHsq : Integrable (fun ω ↦ ‖H ω‖ ^ 2) ρ :=
    hH2.integrable_norm_pow (by norm_num)
  have hKsq : Integrable (fun ω ↦ ‖K ω‖ ^ 2) ρ :=
    hK2.integrable_norm_pow (by norm_num)
  have hHK : Integrable (fun ω ↦ ‖H ω‖ * ‖K ω‖) ρ :=
    hH2.norm.integrable_mul hK2.norm
  have hquadMajor : Integrable (fun ω ↦
      (‖H ω‖ ^ 2 + ‖K ω‖ ^ 2) / 2 + ‖H ω‖ * ‖K ω‖) ρ :=
    ((hHsq.add hKsq).div_const 2).add hHK
  have hquadratic : Integrable (fun p : _ × EuclideanSpace ℝ (Fin d) ↦
      φ p.2 * standardGaussianDensityD2 p.2 (H p.1) (K p.1))
      (ρ.prod volume) :=
    integrable_prod_bounded_mul_standardGaussianDensityD2
      hφm hφ hHm hKm hquadMajor
  have hremainder : Integrable (fun p : _ × EuclideanSpace ℝ (Fin d) ↦
      φ p.2 *
        (standardGaussianDensityD1 (p.2 - H p.1) (K p.1) -
          standardGaussianDensityD1 p.2 (K p.1) +
          standardGaussianDensityD2 p.2 (H p.1) (K p.1)))
      (ρ.prod volume) := by
    apply ((hshift.sub hlinear).add hquadratic).congr
    filter_upwards with p
    change (φ p.2 * standardGaussianDensityD1 (p.2 - H p.1) (K p.1) -
        φ p.2 * standardGaussianDensityD1 p.2 (K p.1)) +
        φ p.2 * standardGaussianDensityD2 p.2 (H p.1) (K p.1) = _
    ring
  let Ishift := ∫ ω, ∫ x, φ x *
    standardGaussianDensityD1 (x - H ω) (K ω) ∂volume ∂ρ
  let Ilinear := ∫ ω, ∫ x, φ x *
    standardGaussianDensityD1 x (K ω) ∂volume ∂ρ
  let Iquadratic := ∫ ω, ∫ x, φ x *
    standardGaussianDensityD2 x (H ω) (K ω) ∂volume ∂ρ
  let Iremainder := ∫ ω, ∫ x, φ x *
    (standardGaussianDensityD1 (x - H ω) (K ω) -
      standardGaussianDensityD1 x (K ω) +
      standardGaussianDensityD2 x (H ω) (K ω)) ∂volume ∂ρ
  have hshiftProd : Ishift = ∫ p, φ p.2 *
      standardGaussianDensityD1 (p.2 - H p.1) (K p.1) ∂(ρ.prod volume) := by
    simpa only [Ishift] using integral_integral hshift
  have hlinearProd : Ilinear = ∫ p, φ p.2 *
      standardGaussianDensityD1 p.2 (K p.1) ∂(ρ.prod volume) := by
    simpa only [Ilinear] using integral_integral hlinear
  have hquadraticProd : Iquadratic = ∫ p, φ p.2 *
      standardGaussianDensityD2 p.2 (H p.1) (K p.1) ∂(ρ.prod volume) := by
    simpa only [Iquadratic] using integral_integral hquadratic
  have hdecomp : Iremainder = Ishift - Ilinear + Iquadratic := by
    calc
      Iremainder = ∫ p, φ p.2 *
          (standardGaussianDensityD1 (p.2 - H p.1) (K p.1) -
            standardGaussianDensityD1 p.2 (K p.1) +
            standardGaussianDensityD2 p.2 (H p.1) (K p.1))
          ∂(ρ.prod volume) := integral_integral hremainder
      _ = ∫ p, (φ p.2 * standardGaussianDensityD1 (p.2 - H p.1) (K p.1) -
            φ p.2 * standardGaussianDensityD1 p.2 (K p.1)) +
            φ p.2 * standardGaussianDensityD2 p.2 (H p.1) (K p.1)
          ∂(ρ.prod volume) := by
        apply integral_congr_ae
        filter_upwards with p
        ring
      _ = (∫ p, φ p.2 * standardGaussianDensityD1 (p.2 - H p.1) (K p.1)
            ∂(ρ.prod volume) -
          ∫ p, φ p.2 * standardGaussianDensityD1 p.2 (K p.1)
            ∂(ρ.prod volume)) +
          ∫ p, φ p.2 * standardGaussianDensityD2 p.2 (H p.1) (K p.1)
            ∂(ρ.prod volume) := by
        calc
          _ = (∫ p, φ p.2 * standardGaussianDensityD1 (p.2 - H p.1) (K p.1) -
                φ p.2 * standardGaussianDensityD1 p.2 (K p.1) ∂(ρ.prod volume)) +
              ∫ p, φ p.2 * standardGaussianDensityD2 p.2 (H p.1) (K p.1)
                ∂(ρ.prod volume) :=
            integral_add (hshift.sub hlinear) hquadratic
          _ = _ := by rw [integral_sub hshift hlinear]
      _ = Ishift - Ilinear + Iquadratic := by
        rw [← hshiftProd, ← hlinearProd, ← hquadraticProd]
  have hlow := bentkus_integral_integral_lowOrderDensity_eq_zero
    hXm hX3 hX0 B k α hφm hφ
  have hlinear0 : Ilinear = 0 := by
    simpa only [Ilinear, K, R', O, G, ρ] using hlow.1
  have hquadratic0 : Iquadratic = 0 := by
    simpa only [Iquadratic, H, K, R, R', O, G, ρ] using hlow.2
  have hIeq : Ishift = Iremainder := by
    rw [hdecomp, hlinear0, hquadratic0]
    ring
  have hrem := bentkus_replacementRotated_D1_secondOrderRemainder_le
    hXm hX3 h_indep hX0 hidentity k hk α hφm hφ
  have hB : B = bentkusWhiteningCLM S := by
    apply ContinuousLinearMap.ext
    intro x
    exact bentkusWhiteningEquiv_apply S hS x
  have hrem' : |Iremainder| ≤
      448 * (3 + Real.sqrt standardGaussianFourthMoment) *
        ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
    simpa only [Iremainder, H, K, R, R', hB, S, O, G, ρ] using hrem
  have hderiv :=
    integral_fderiv_convexSetCutoff_gaussianLeaveOneOut_eq_neg_translated_D1
      hXm hX3 h_indep hX0 hidentity k hk α hs hε
  have hderiv' :
      (∫ ω, (fderiv ℝ (convexSetCutoff s ε) (V ω + R ω)) (R' ω) ∂ρ) =
        -Ishift := by
    simpa only [Ishift, φ, H, K, ρ, S, e, P, B, O, G, V, R, R'] using hderiv
  change
    |∫ ω, (fderiv ℝ (convexSetCutoff s ε) (V ω + R ω)) (R' ω) ∂ρ| ≤
      448 * (3 + Real.sqrt standardGaussianFourthMoment) *
        ∫ ω, ‖O ω‖ ^ 3 ∂ρ
  rw [hderiv', abs_neg, hIeq]
  exact hrem'

/-- The Gaussian-reference term in Bentkus (3.12)--(3.15), integrated over an arbitrary ordered
angle interval. -/
private theorem bentkus_intervalIntegral_gaussianLeaveOneOut_rotationDerivative_le
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    {a b : ℝ} (hab : a ≤ b) {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε) :
    let ρ := bentkusReplacementMeasure μ X
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let V := bentkusLeaveOneOut
      (fun i ↦ replacementGaussian (d := d) i) k
    |∫ α in a..b, ∫ ω,
        (fderiv ℝ (convexSetCutoff s ε)
          (V ω + bentkusRotated α O G ω))
          (bentkusRotatedDeriv α O G ω) ∂ρ| ≤
      (b - a) * (448 * (3 + Real.sqrt standardGaussianFourthMoment)) *
        ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
  let ρ := bentkusReplacementMeasure μ X
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let V := bentkusLeaveOneOut (fun i ↦ replacementGaussian (d := d) i) k
  let M := (448 * (3 + Real.sqrt standardGaussianFourthMoment)) *
    ∫ ω, ‖O ω‖ ^ 3 ∂ρ
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity
  have hpoint (α : ℝ) :
      ‖∫ ω, (fderiv ℝ (convexSetCutoff s ε)
          (V ω + bentkusRotated α O G ω))
          (bentkusRotatedDeriv α O G ω) ∂ρ‖ ≤ M := by
    rw [Real.norm_eq_abs]
    simpa only [M, ρ, O, G, V, mul_assoc] using
      bentkus_gaussianLeaveOneOut_rotationDerivative_le
        hXm hX3 h_indep hX0 hidentity k hk α hs hε
  change
    |∫ α in a..b, ∫ ω,
        (fderiv ℝ (convexSetCutoff s ε)
          (V ω + bentkusRotated α O G ω))
          (bentkusRotatedDeriv α O G ω) ∂ρ| ≤
      (b - a) * (448 * (3 + Real.sqrt standardGaussianFourthMoment)) *
        ∫ ω, ‖O ω‖ ^ 3 ∂ρ
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ α in a..b, ∫ ω,
        (fderiv ℝ (convexSetCutoff s ε)
          (V ω + bentkusRotated α O G ω))
          (bentkusRotatedDeriv α O G ω) ∂ρ‖ ≤ M * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun α _ ↦ hpoint α
    _ = (b - a) * M := by
      rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      ring
    _ = (b - a) * (448 * (3 + Real.sqrt standardGaussianFourthMoment)) *
        ∫ ω, ‖O ω‖ ^ 3 ∂ρ := by
      dsimp only [M]
      ring

/-- The exact smooth-test estimate left by Bentkus (3.4)--(3.7), before Lemma 2.1 adds the
Gaussian boundary shells.  The strict branch hypotheses are retained because the proof uses the
leave-one-out induction estimate (3.34). -/
private structure bentkusNontrivialSmoothCutoffEstimate (Ks C : ℝ) : Prop where
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

/-- The sole analytic input still required after the exact probability-space, branch, whitening,
rotation, and parameter reductions.  This is the combined content of Bentkus (3.6), equivalently
the estimates (3.13)--(3.15), in the strict nontrivial branch. -/
private structure bentkusNontrivialTaylorEstimate (K C : ℝ) : Prop where
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
private theorem bentkusNontrivialTaylorEstimate_of_smoothCutoff
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
private theorem bentkusIdentityCovarianceBound_of_nontrivialTaylor
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

end

end ProbabilityTheory
