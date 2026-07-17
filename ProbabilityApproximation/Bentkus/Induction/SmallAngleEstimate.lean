/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.Bentkus.Induction.SplitGaussianShell

/-!
# Small-angle estimate in Bentkus's replacement rotation

This module formalizes Bentkus (3.27)--(3.35): the split-Gaussian law, low-order cancellation,
two-shift second-density remainders, their product-space Fubini exchanges, and the final
one-coordinate small-angle estimate.
-/

open MeasureTheory InnerProductSpace Matrix Set
open scoped ENNReal MatrixOrder Pointwise RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

universe u

local instance smallAngleEstimateConvexSpace {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

local instance smallAngleEstimateIsModuleConvexSpace {d : ℕ} :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.ofModule

namespace BentkusInduction

set_option maxHeartbeats 2000000

/-- Reassociation of the two half-Gaussians exposes one Gaussian coordinate for density
translation and leaves the other inside the split-Gaussian base law. -/
private theorem bentkus_splitGaussianBase_add_law
    {d : ℕ} {ν : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure ν]
    (P : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (α : ℝ) :
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let θ := (Real.sqrt 2)⁻¹
    let p := Real.cos α
    let s := Real.sin α
    let q := θ * s
    let T := ((γ.map (fun y ↦ q • y)).prod ν).map
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        p • z.2 + z.1)
    let L := q • P
    ((T.map P).prod γ).map
        (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
          z.1 + L z.2) =
      ((γ.prod γ).prod ν).map
        (fun z : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
            EuclideanSpace ℝ (Fin d) ↦
          P (p • z.2 + q • z.1.1 + q • z.1.2)) := by
  let E := EuclideanSpace ℝ (Fin d)
  let γ := stdGaussian E
  let θ := (Real.sqrt 2)⁻¹
  let p := Real.cos α
  let s := Real.sin α
  let q := θ * s
  let T := ((γ.map (fun y ↦ q • y)).prod ν).map
    (fun z : E × E ↦ p • z.2 + z.1)
  let L := q • P
  let scale : E → E := fun y ↦ q • y
  let affine : E × E → E := fun z ↦ p • z.2 + z.1
  let baseMap : E × E → E := fun z ↦ P (p • z.2 + q • z.1)
  let reorder : (E × E) × E → (E × E) × E :=
    fun z ↦ ((z.1.1, z.2), z.1.2)
  let addMap : E × E → E := fun z ↦ z.1 + L z.2
  have hscale : Measurable scale := by
    dsimp only [scale]
    fun_prop
  have haffine : Measurable affine := by
    dsimp only [affine]
    fun_prop
  have hbaseMap : Measurable baseMap := by
    dsimp only [baseMap]
    fun_prop
  have haddMap : Measurable addMap := by
    dsimp only [addMap]
    fun_prop
  have hreorder : Measurable reorder := by
    dsimp only [reorder]
    fun_prop
  have hreorderLaw :
      ((γ.prod γ).prod ν).map reorder = (γ.prod ν).prod γ := by
    have hAssoc₁ :=
      measurePreserving_prodAssoc γ γ ν
    have hSwap : MeasurePreserving
        (Prod.map id Prod.swap)
        (γ.prod (γ.prod ν)) (γ.prod (ν.prod γ)) :=
      (MeasurePreserving.id γ).prod Measure.measurePreserving_swap
    have hAssoc₂ : MeasurePreserving
        (MeasurableEquiv.prodAssoc.symm :
          E × E × E ≃ᵐ (E × E) × E)
        (γ.prod (ν.prod γ)) ((γ.prod ν).prod γ) :=
      (measurePreserving_prodAssoc γ ν γ).symm MeasurableEquiv.prodAssoc
    have hcomp := hAssoc₂.comp (hSwap.comp hAssoc₁)
    have hmap := hcomp.map_eq
    change ((γ.prod γ).prod ν).map
      (fun z : (E × E) × E ↦ ((z.1.1, z.2), z.1.2)) =
        (γ.prod ν).prod γ at hmap
    simpa only [reorder] using hmap
  have hbaseLaw : T.map P = (γ.prod ν).map baseMap := by
    have hprod :
        (γ.map scale).prod ν = (γ.prod ν).map (Prod.map scale id) := by
      simpa only [Measure.map_id] using
        Measure.map_prod_map γ ν hscale measurable_id
    dsimp only [T]
    rw [hprod, Measure.map_map haffine (hscale.prodMap measurable_id),
      Measure.map_map P.continuous.measurable
        (haffine.comp (hscale.prodMap measurable_id))]
    congr 1
  change ((T.map P).prod γ).map addMap =
    ((γ.prod γ).prod ν).map
      (fun z : (E × E) × E ↦ P (p • z.2 + q • z.1.1 + q • z.1.2))
  rw [hbaseLaw]
  have hprod :
      (((γ.prod ν).map baseMap).prod γ) =
        ((γ.prod ν).prod γ).map (Prod.map baseMap id) := by
    simpa only [Measure.map_id] using
      Measure.map_prod_map (γ.prod ν) γ hbaseMap measurable_id
  rw [hprod, Measure.map_map haddMap (hbaseMap.prodMap measurable_id),
    ← hreorderLaw, Measure.map_map
      (haddMap.comp (hbaseMap.prodMap measurable_id)) hreorder]
  congr 1
  funext z
  dsimp only [addMap, baseMap, reorder, L, Function.comp_apply, Prod.map_apply, id_eq]
  rw [map_add, map_smul]
  simp only [_root_.smul_apply, map_add, map_smul]

/-- Joint-law form of the small-angle split: the rotated leave-one-out vector is an independent
sum of the split-Gaussian base and one exposed Gaussian coordinate, and remains independent of
the omitted original/Gaussian pair. -/
private theorem bentkus_smallAngle_splitBase_replacementPair_eq_prod
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (α : ℝ) :
    let ρ := bentkusReplacementMeasure μ X
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
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
    let p := Real.cos α
    let s := Real.sin α
    let q := θ * s
    let T := ((γ.map (fun y ↦ q • y)).prod ν).map
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        p • z.2 + z.1)
    let L := q • P
    let addMap := fun z :
        EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦ z.1 + L z.2
    ρ.map (fun ω ↦ (p • UO ω + s • VG ω, Z ω)) =
      (((T.map P).prod γ).map addMap).prod τ := by
  let E := EuclideanSpace ℝ (Fin d)
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
    hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let P := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  let UO := bentkusLeaveOneOut
    (fun i ↦ replacementOriginal (d := d) i) k
  let VG := bentkusLeaveOneOut
    (fun i ↦ replacementGaussian (d := d) i) k
  let U := bentkusLeaveOneOut X k
  let Z := fun ω ↦
    (replacementOriginal (d := d) k ω, replacementGaussian (d := d) k ω)
  let γ := stdGaussian E
  let ν := μ.map (fun ω ↦ B (U ω))
  let τ := ρ.map Z
  let θ := (Real.sqrt 2)⁻¹
  let p := Real.cos α
  let s := Real.sin α
  let q := θ * s
  let T := ((γ.map (fun y ↦ q • y)).prod ν).map
    (fun z : E × E ↦ p • z.2 + z.1)
  let L := q • P
  let addMap := fun z : E × E ↦ z.1 + L z.2
  let source := (γ.prod γ).prod ν
  let splitRotate : (E × E) × E → E := fun z ↦
    s • (θ • z.1.1 + θ • z.1.2) + p • z.2
  let W := fun ω ↦ B (p • UO ω + s • VG ω)
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hB : B = bentkusWhiteningCLM S := by
    apply ContinuousLinearMap.ext
    intro x
    exact bentkusWhiteningEquiv_apply S hS x
  have hUmeas : Measurable U := by
    dsimp only [U, bentkusLeaveOneOut]
    exact Finset.measurable_sum (Finset.univ.erase k) fun i _ ↦ hXm i
  letI : IsProbabilityMeasure ν := by
    dsimp only [ν]
    exact Measure.isProbabilityMeasure_map
      (B.continuous.measurable.comp hUmeas).aemeasurable
  have hZmeas : Measurable Z := by
    dsimp only [Z, replacementOriginal, replacementGaussian]
    fun_prop
  letI : IsProbabilityMeasure τ := by
    dsimp only [τ]
    exact Measure.isProbabilityMeasure_map hZmeas.aemeasurable
  have hbaseAdd :
      ((T.map P).prod γ).map addMap =
        source.map (fun z : (E × E) × E ↦
          P (p • z.2 + q • z.1.1 + q • z.1.2)) := by
    simpa only [γ, θ, p, s, q, T, L, addMap, source] using
      bentkus_splitGaussianBase_add_law (ν := ν) P α
  have hsplitMeas : Measurable splitRotate := by
    dsimp only [splitRotate]
    fun_prop
  have hleaveLaw :
      (source.map splitRotate).map P = ((T.map P).prod γ).map addMap := by
    rw [Measure.map_map P.continuous.measurable hsplitMeas, hbaseAdd]
    congr 1
    funext z
    dsimp only [splitRotate, Function.comp_apply]
    rw [smul_add, smul_smul, smul_smul]
    dsimp only [q]
    simp only [map_add, map_smul]
    rw [mul_comm s θ]
    abel
  have hpair := map_splitGaussian_whitenedRotatedLeaveOneOut_replacementPair_eq_prod
    hXm hX3 h_indep hX0 hidentity k hk α
  have hWmeas : Measurable W := by
    dsimp only [W, UO, VG, bentkusLeaveOneOut,
      replacementOriginal, replacementGaussian]
    fun_prop
  have hpairP : Measurable (Prod.map P id : E × (E × E) → E × (E × E)) :=
    P.continuous.measurable.prodMap measurable_id
  have hprodMap :
      ((source.map splitRotate).prod τ).map (Prod.map P id) =
        ((source.map splitRotate).map P).prod τ := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map (source.map splitRotate) τ
        P.continuous.measurable measurable_id).symm
  change ρ.map (fun ω ↦ (p • UO ω + s • VG ω, Z ω)) =
    (((T.map P).prod γ).map addMap).prod τ
  calc
    ρ.map (fun ω ↦ (p • UO ω + s • VG ω, Z ω)) =
        (ρ.map (fun ω ↦ (W ω, Z ω))).map (Prod.map P id) := by
      rw [Measure.map_map hpairP (hWmeas.prodMk hZmeas)]
      congr 1
      funext ω
      dsimp only [W, Function.comp_apply, Prod.map_apply, id_eq, P, B, e]
      apply Prod.ext
      · exact ((bentkusWhiteningEquiv S hS).symm_apply_apply _).symm
      · rfl
    _ = ((source.map splitRotate).prod τ).map (Prod.map P id) := by
      rw [show ρ.map (fun ω ↦ (W ω, Z ω)) =
          (source.map splitRotate).prod τ by
        simpa only [ρ, S, hB, UO, VG, U, Z, γ, ν, τ, θ, p, s,
          splitRotate, source, W] using hpair]
    _ = ((source.map splitRotate).map P).prod τ := hprodMap
    _ = (((T.map P).prod γ).map addMap).prod τ := by rw [hleaveLaw]

/-- Exact affine-shift algebra used in the small-angle Gaussian translation. -/
private lemma bentkus_smallAngle_shift_relations
    {d : ℕ}
    (e : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (α : ℝ) (hsin : 0 < Real.sin α)
    (O G : EuclideanSpace ℝ (Fin d)) :
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
    let θ := (Real.sqrt 2)⁻¹
    let p := Real.cos α
    let s := Real.sin α
    let L := (θ * s) • P
    let vO := -((1 / θ) • B G)
    let wO := -((p / (θ * s)) • B O)
    L vO = -s • G ∧
      L wO = -p • O ∧
      L (-(vO + wO)) = p • O + s • G := by
  let P := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  let θ := (Real.sqrt 2)⁻¹
  let p := Real.cos α
  let s := Real.sin α
  let L := (θ * s) • P
  let vO := -((1 / θ) • B G)
  let wO := -((p / (θ * s)) • B O)
  have hθ : θ ≠ 0 := by
    dsimp only [θ]
    exact inv_ne_zero (Real.sqrt_ne_zero'.2 (by norm_num))
  have hs : s ≠ 0 := by
    simpa only [s] using hsin.ne'
  have hPB (x : EuclideanSpace ℝ (Fin d)) : P (B x) = x := by
    dsimp only [P, B]
    exact e.symm_apply_apply x
  have hv : L vO = -s • G := by
    dsimp only [L, vO]
    simp only [_root_.smul_apply, map_neg, map_smul, hPB, smul_smul]
    congr 1
    field_simp [hθ]
    simp only [neg_smul]
  have hw : L wO = -p • O := by
    dsimp only [L, wO]
    simp only [_root_.smul_apply, map_neg, map_smul, hPB, smul_smul]
    congr 1
    field_simp [hθ, hs]
    simp only [neg_smul]
  refine ⟨hv, hw, ?_⟩
  rw [map_neg, map_add, hv, hw]
  module

/-- The two first-density terms in the small-angle expansion cancel by covariance matching. -/
private theorem bentkus_smallAngle_D1_pair_cancel
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (k : Fin (n + 1))
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (α : ℝ) (hsin : 0 < Real.sin α)
    (A : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (a u : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    let ρ := bentkusReplacementMeasure μ X
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let θ := (Real.sqrt 2)⁻¹
    let p := Real.cos α
    let s := Real.sin α
    let wO := fun ω ↦ -((p / (θ * s)) • B (O ω))
    let wG := fun ω ↦ -((1 / θ) • B (G ω))
    Integrable (fun ω ↦
        (-s) * (convexSetCutoffDirectionalPullback A ε a (O ω) L u *
          standardGaussianDensityD1 u (wO ω)) +
        p * (convexSetCutoffDirectionalPullback A ε a (G ω) L u *
          standardGaussianDensityD1 u (wG ω))) ρ ∧
      (∫ ω,
        (-s) * (convexSetCutoffDirectionalPullback A ε a (O ω) L u *
          standardGaussianDensityD1 u (wO ω)) +
        p * (convexSetCutoffDirectionalPullback A ε a (G ω) L u *
          standardGaussianDensityD1 u (wG ω)) ∂ρ) = 0 := by
  let ρ := bentkusReplacementMeasure μ X
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let θ := (Real.sqrt 2)⁻¹
  let p := Real.cos α
  let s := Real.sin α
  let wO := fun ω ↦ -((p / (θ * s)) • B (O ω))
  let wG := fun ω ↦ -((1 / θ) • B (G ω))
  let ell : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    fderiv ℝ (convexSetCutoff A ε) (a + L u)
  let m : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    (-standardGaussianDensity (EuclideanSpace ℝ (Fin d)) u) •
      ((innerSL ℝ u).comp B)
  let Q : EuclideanSpace ℝ (Fin d) →L[ℝ]
      EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    (ContinuousLinearMap.mul ℝ ℝ).bilinearComp ell m
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hO2 : MemLp O 2 ρ :=
    (memLp_replacementOriginal hXm hX3 k).mono_exponent (by norm_num)
  have hG2 : MemLp G 2 ρ :=
    (memLp_three_replacementGaussian hXm k).mono_exponent (by norm_num)
  have hO0 : ∫ ω, O ω ∂ρ = 0 := by
    simpa only [O, ρ] using
      (integral_replacementOriginal_eq hXm k).trans (hX0 k)
  have hG0 : ∫ ω, G ω ∂ρ = 0 := by
    simpa only [G, ρ] using integral_replacementGaussian_eq_zero hXm k
  have hcov : ∀ x y,
      covarianceBilin (ρ.map O) x y = covarianceBilin (ρ.map G) x y := by
    intro x y
    simpa only [O, G, ρ] using
      (covarianceBilin_replacementGaussian_eq_replacementOriginal hXm k x y).symm
  have hmatch := integral_bilin_self_eq_of_covarianceBilin_eq
    hO2 hG2 hO0 hG0 hcov Q
  have hOint := integrable_bilin_self_of_memLp_two hO2 Q
  have hGint := integrable_bilin_self_of_memLp_two hG2 Q
  have hθ : θ ≠ 0 := by
    dsimp only [θ]
    exact inv_ne_zero (Real.sqrt_ne_zero'.2 (by norm_num))
  have hs : s ≠ 0 := by
    simpa only [s] using hsin.ne'
  have hQapply (x y : EuclideanSpace ℝ (Fin d)) :
      Q x y = ell x *
        (-standardGaussianDensity (EuclideanSpace ℝ (Fin d)) u *
          inner ℝ u (B y)) := by
    rfl
  have hpoint (ω) :
      (-s) * (convexSetCutoffDirectionalPullback A ε a (O ω) L u *
          standardGaussianDensityD1 u (wO ω)) +
        p * (convexSetCutoffDirectionalPullback A ε a (G ω) L u *
          standardGaussianDensityD1 u (wG ω)) =
        (p / θ) * (Q (O ω) (O ω) - Q (G ω) (G ω)) := by
    rw [hQapply, hQapply]
    dsimp only [convexSetCutoffDirectionalPullback, wO, wG, ell]
    unfold standardGaussianDensityD1
    simp only [inner_neg_right, inner_smul_right, neg_mul, neg_neg]
    field_simp [hθ, hs]
    ring
  constructor
  · apply ((hOint.sub hGint).const_mul (p / θ)).congr
    filter_upwards with ω
    exact (hpoint ω).symm
  · calc
      (∫ ω,
        (-s) * (convexSetCutoffDirectionalPullback A ε a (O ω) L u *
          standardGaussianDensityD1 u (wO ω)) +
        p * (convexSetCutoffDirectionalPullback A ε a (G ω) L u *
          standardGaussianDensityD1 u (wG ω)) ∂ρ) =
          ∫ ω, (p / θ) * (Q (O ω) (O ω) - Q (G ω) (G ω)) ∂ρ := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = (p / θ) *
          ((∫ ω, Q (O ω) (O ω) ∂ρ) - ∫ ω, Q (G ω) (G ω) ∂ρ) := by
        rw [integral_const_mul, integral_sub hOint hGint]
      _ = 0 := by rw [hmatch, sub_self, mul_zero]

/-- The two zeroth-order density terms in the small-angle expansion vanish separately:
the differentiated omitted coordinate is centered and is independent of the coordinate on which
the translated density depends. -/
private theorem bentkus_smallAngle_zeroOrder_pair_cancel
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (k : Fin (n + 1))
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (α : ℝ) (hsin : 0 < Real.sin α)
    (A : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (a u : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    let ρ := bentkusReplacementMeasure μ X
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let θ := (Real.sqrt 2)⁻¹
    let p := Real.cos α
    let s := Real.sin α
    let vO := fun ω ↦ -((1 / θ) • B (G ω))
    let vG := fun ω ↦ -((p / (θ * s)) • B (O ω))
    Integrable (fun ω ↦
        (-s) * (convexSetCutoffDirectionalPullback A ε a (O ω) L u *
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + vO ω)) +
        p * (convexSetCutoffDirectionalPullback A ε a (G ω) L u *
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + vG ω))) ρ ∧
      (∫ ω,
        (-s) * (convexSetCutoffDirectionalPullback A ε a (O ω) L u *
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + vO ω)) +
        p * (convexSetCutoffDirectionalPullback A ε a (G ω) L u *
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + vG ω)) ∂ρ) = 0 := by
  let ρ := bentkusReplacementMeasure μ X
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let θ := (Real.sqrt 2)⁻¹
  let p := Real.cos α
  let s := Real.sin α
  let vO := fun ω ↦ -((1 / θ) • B (G ω))
  let vG := fun ω ↦ -((p / (θ * s)) • B (O ω))
  let ell : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    fderiv ℝ (convexSetCutoff A ε) (a + L u)
  let densityO := fun ω ↦
    standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + vO ω)
  let densityG := fun ω ↦
    standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + vG ω)
  let c := standardGaussianDensityNormalization (EuclideanSpace ℝ (Fin d))
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hOm : Measurable O := by
    exact (measurable_pi_apply k).comp measurable_fst
  have hGm : Measurable G := by
    exact (measurable_pi_apply k).comp measurable_snd
  have hOint : Integrable O ρ :=
    (memLp_replacementOriginal hXm hX3 k).integrable (by norm_num)
  have hGint : Integrable G ρ :=
    (memLp_three_replacementGaussian hXm k).integrable (by norm_num)
  have hO0 : ∫ ω, O ω ∂ρ = 0 := by
    simpa only [O, ρ] using
      (integral_replacementOriginal_eq hXm k).trans (hX0 k)
  have hG0 : ∫ ω, G ω ∂ρ = 0 := by
    simpa only [G, ρ] using integral_replacementGaussian_eq_zero hXm k
  have hOG : O ⟂ᵢ[ρ] G := by
    simpa only [O, G, ρ] using
      indepFun_replacementOriginal_replacementGaussian hXm k k
  have hellOm : Measurable (fun ω ↦ ell (O ω)) :=
    ell.continuous.measurable.comp hOm
  have hellGm : Measurable (fun ω ↦ ell (G ω)) :=
    ell.continuous.measurable.comp hGm
  have hdensityOm : Measurable densityO := by
    exact continuous_standardGaussianDensity.measurable.comp (by
      dsimp only [vO]
      exact measurable_const.add
        ((B.continuous.measurable.comp hGm).const_smul (1 / θ)).neg)
  have hdensityGm : Measurable densityG := by
    exact continuous_standardGaussianDensity.measurable.comp (by
      dsimp only [vG]
      exact measurable_const.add
        ((B.continuous.measurable.comp hOm).const_smul (p / (θ * s))).neg)
  have hc : 0 ≤ c := by
    dsimp only [c, standardGaussianDensityNormalization]
    positivity
  have hdensity_le (x : EuclideanSpace ℝ (Fin d)) :
      ‖standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x‖ ≤ c := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · unfold standardGaussianDensity
      exact mul_le_of_le_one_right hc
        (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖x‖]))
    · unfold standardGaussianDensity
      positivity
  have hdensityOint : Integrable densityO ρ := by
    apply Integrable.of_bound hdensityOm.aestronglyMeasurable c
    filter_upwards with ω
    exact hdensity_le _
  have hdensityGint : Integrable densityG ρ := by
    apply Integrable.of_bound hdensityGm.aestronglyMeasurable c
    filter_upwards with ω
    exact hdensity_le _
  have hellOint : Integrable (fun ω ↦ ell (O ω)) ρ :=
    ell.integrable_comp hOint
  have hellGint : Integrable (fun ω ↦ ell (G ω)) ρ :=
    ell.integrable_comp hGint
  have hindO :
      (fun ω ↦ ell (O ω)) ⟂ᵢ[ρ] densityO := by
    have hcomp := hOG.comp ell.continuous.measurable
      (continuous_standardGaussianDensity.measurable.comp (by
        change Measurable (fun y : EuclideanSpace ℝ (Fin d) ↦
          u + -((1 / θ) • B y))
        fun_prop))
    convert hcomp using 1 <;> funext ω <;> rfl
  have hindG :
      (fun ω ↦ ell (G ω)) ⟂ᵢ[ρ] densityG := by
    have hcomp := hOG.symm.comp ell.continuous.measurable
      (continuous_standardGaussianDensity.measurable.comp (by
        change Measurable (fun x : EuclideanSpace ℝ (Fin d) ↦
          u + -((p / (θ * s)) • B x))
        fun_prop))
    convert hcomp using 1 <;> funext ω <;> rfl
  have hellO0 : ∫ ω, ell (O ω) ∂ρ = 0 := by
    rw [ell.integral_comp_comm hOint, hO0, map_zero]
  have hellG0 : ∫ ω, ell (G ω) ∂ρ = 0 := by
    rw [ell.integral_comp_comm hGint, hG0, map_zero]
  have htermOint : Integrable (fun ω ↦ ell (O ω) * densityO ω) ρ :=
    hindO.integrable_mul hellOint hdensityOint
  have htermGint : Integrable (fun ω ↦ ell (G ω) * densityG ω) ρ :=
    hindG.integrable_mul hellGint hdensityGint
  have htermO : ∫ ω, ell (O ω) * densityO ω ∂ρ = 0 := by
    rw [hindO.integral_fun_mul_eq_mul_integral
      hellOm.aestronglyMeasurable hdensityOm.aestronglyMeasurable, hellO0, zero_mul]
  have htermG : ∫ ω, ell (G ω) * densityG ω ∂ρ = 0 := by
    rw [hindG.integral_fun_mul_eq_mul_integral
      hellGm.aestronglyMeasurable hdensityGm.aestronglyMeasurable, hellG0, zero_mul]
  have hpoint (ω) :
      convexSetCutoffDirectionalPullback A ε a (O ω) L u * densityO ω =
        ell (O ω) * densityO ω := rfl
  have hpointG (ω) :
      convexSetCutoffDirectionalPullback A ε a (G ω) L u * densityG ω =
        ell (G ω) * densityG ω := rfl
  have hpairInt : Integrable (fun ω ↦
      (-s) * (ell (O ω) * densityO ω) +
        p * (ell (G ω) * densityG ω)) ρ :=
    (htermOint.const_mul (-s)).add (htermGint.const_mul p)
  constructor
  · apply hpairInt.congr
    filter_upwards with ω
    rw [hpoint, hpointG]
  · calc
      (∫ ω,
        (-s) * (convexSetCutoffDirectionalPullback A ε a (O ω) L u *
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + vO ω)) +
        p * (convexSetCutoffDirectionalPullback A ε a (G ω) L u *
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + vG ω)) ∂ρ) =
          ∫ ω, (-s) * (ell (O ω) * densityO ω) +
            p * (ell (G ω) * densityG ω) ∂ρ := by
        apply integral_congr_ae
        filter_upwards with ω
        rw [hpoint, hpointG]
      _ = (-s) * (∫ ω, ell (O ω) * densityO ω ∂ρ) +
          p * (∫ ω, ell (G ω) * densityG ω ∂ρ) := by
        rw [integral_add (htermOint.const_mul (-s)) (htermGint.const_mul p),
          integral_const_mul, integral_const_mul]
      _ = 0 := by rw [htermO, htermG]; ring

/-- The complete low-order group in the small-angle density expansion vanishes on the law of
the omitted original/Gaussian pair.  This packages the two centered zeroth-order terms and the
matched-covariance first-order pair in the exact form consumed by the Taylor decomposition. -/
private theorem bentkus_smallAngle_lowOrder_pair_cancel
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (k : Fin (n + 1))
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (α : ℝ) (hsin : 0 < Real.sin α)
    (A : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (a u : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    let ρ := bentkusReplacementMeasure μ X
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let Z := fun ω ↦ (O ω, G ω)
    let τ := ρ.map Z
    let θ := (Real.sqrt 2)⁻¹
    let p := Real.cos α
    let s := Real.sin α
    let vO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((1 / θ) • B z.2)
    let wO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((p / (θ * s)) • B z.1)
    let cancel := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      (((-s) * (convexSetCutoffDirectionalPullback A ε a z.1 L u *
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + vO z)) +
        p * (convexSetCutoffDirectionalPullback A ε a z.2 L u *
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + wO z))) +
      ((-s) * (convexSetCutoffDirectionalPullback A ε a z.1 L u *
          standardGaussianDensityD1 u (wO z)) +
        p * (convexSetCutoffDirectionalPullback A ε a z.2 L u *
          standardGaussianDensityD1 u (vO z))))
    Integrable cancel τ ∧ (∫ z, cancel z ∂τ) = 0 := by
  let ρ := bentkusReplacementMeasure μ X
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let Z := fun ω ↦ (O ω, G ω)
  let τ := ρ.map Z
  let θ := (Real.sqrt 2)⁻¹
  let p := Real.cos α
  let s := Real.sin α
  let vO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -((1 / θ) • B z.2)
  let wO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -((p / (θ * s)) • B z.1)
  let zero := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    (-s) * (convexSetCutoffDirectionalPullback A ε a z.1 L u *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + vO z)) +
      p * (convexSetCutoffDirectionalPullback A ε a z.2 L u *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + wO z))
  let linear := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    (-s) * (convexSetCutoffDirectionalPullback A ε a z.1 L u *
        standardGaussianDensityD1 u (wO z)) +
      p * (convexSetCutoffDirectionalPullback A ε a z.2 L u *
        standardGaussianDensityD1 u (vO z))
  let cancel := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    zero z + linear z
  have hZmeas : Measurable Z := by
    dsimp only [Z, O, G]
    exact ((measurable_pi_apply k).comp measurable_fst).prodMk
      ((measurable_pi_apply k).comp measurable_snd)
  have hzeromeas : Measurable zero := by
    dsimp only [zero, vO, wO, convexSetCutoffDirectionalPullback]
    apply Measurable.add
    · apply Measurable.const_mul
      apply Measurable.mul
      · fun_prop
      · exact continuous_standardGaussianDensity.measurable.comp (by fun_prop)
    · apply Measurable.const_mul
      apply Measurable.mul
      · fun_prop
      · exact continuous_standardGaussianDensity.measurable.comp (by fun_prop)
  have hlinearmeas : Measurable linear := by
    dsimp only [linear, vO, wO, convexSetCutoffDirectionalPullback,
      standardGaussianDensityD1]
    fun_prop
  have hzeroρ := bentkus_smallAngle_zeroOrder_pair_cancel
    hXm hX3 hX0 k B α hsin A ε a u L
  have hlinearρ := bentkus_smallAngle_D1_pair_cancel
    hXm hX3 hX0 k B α hsin A ε a u L
  have hzero : Integrable zero τ := by
    apply (integrable_map_measure hzeromeas.aestronglyMeasurable
      hZmeas.aemeasurable).2
    apply hzeroρ.1.congr
    filter_upwards with ω
    rfl
  have hlinear : Integrable linear τ := by
    apply (integrable_map_measure hlinearmeas.aestronglyMeasurable
      hZmeas.aemeasurable).2
    apply hlinearρ.1.congr
    filter_upwards with ω
    rfl
  have hzero0 : ∫ z, zero z ∂τ = 0 := by
    rw [integral_map hZmeas.aemeasurable hzeromeas.aestronglyMeasurable]
    simpa only [zero, vO, wO, Z, O, G, ρ, τ, θ, p, s,
      Function.comp_apply, Prod.fst, Prod.snd] using hzeroρ.2
  have hlinear0 : ∫ z, linear z ∂τ = 0 := by
    rw [integral_map hZmeas.aemeasurable hlinearmeas.aestronglyMeasurable]
    simpa only [linear, vO, wO, Z, O, G, ρ, τ, θ, p, s,
      Function.comp_apply, Prod.fst, Prod.snd] using hlinearρ.2
  constructor
  · exact hzero.add hlinear
  · rw [integral_add hzero hlinear, hzero0, hlinear0, add_zero]


/-- Three third moments dominate the cubic expression obtained by multiplying one direction
norm by the `L¹` majorant for a second Gaussian-density contraction. -/
private lemma integrable_norm_mul_D2_major_of_memLp_three
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ] {μ : Measure Θ}
    [IsFiniteMeasure μ]
    {x h g : Θ → EuclideanSpace ℝ (Fin d)}
    (hx3 : MemLp x 3 μ) (hh3 : MemLp h 3 μ) (hg3 : MemLp g 3 μ) :
    Integrable (fun z ↦
      ‖x z‖ * ((‖h z‖ ^ 2 + ‖g z‖ ^ 2) / 2 + ‖h z‖ * ‖g z‖)) μ := by
  let M : Θ → ℝ := fun z ↦
    2 * ‖x z‖ ^ 3 + ‖h z‖ ^ 3 + ‖g z‖ ^ 3
  have hxint : Integrable (fun z ↦ ‖x z‖ ^ 3) μ :=
    hx3.integrable_norm_pow (by norm_num)
  have hhint : Integrable (fun z ↦ ‖h z‖ ^ 3) μ :=
    hh3.integrable_norm_pow (by norm_num)
  have hgint : Integrable (fun z ↦ ‖g z‖ ^ 3) μ :=
    hg3.integrable_norm_pow (by norm_num)
  have hMint : Integrable M μ := (hxint.const_mul 2).add hhint |>.add hgint
  apply hMint.mono'
  · have hsum :=
      (hh3.aestronglyMeasurable.norm.pow 2).add
        (hg3.aestronglyMeasurable.norm.pow 2)
    have hquadratic := (hsum.const_mul (1 / 2)).add
      (hh3.aestronglyMeasurable.norm.mul hg3.aestronglyMeasurable.norm)
    apply (hx3.aestronglyMeasurable.norm.mul hquadratic).congr
    filter_upwards with z
    simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply]
    ring_nf
  · filter_upwards with z
    let a := ‖x z‖
    let b := ‖h z‖
    let c := ‖g z‖
    have ha : 0 ≤ a := norm_nonneg _
    have hb : 0 ≤ b := norm_nonneg _
    have hc : 0 ≤ c := norm_nonneg _
    have hab : a * b ^ 2 ≤ a ^ 3 + b ^ 3 := by
      rcases le_total a b with hab | hba
      · calc
          a * b ^ 2 ≤ b * b ^ 2 :=
            mul_le_mul_of_nonneg_right hab (sq_nonneg b)
          _ = b ^ 3 := by ring
          _ ≤ a ^ 3 + b ^ 3 := le_add_of_nonneg_left (pow_nonneg ha 3)
      · calc
          a * b ^ 2 ≤ a * a ^ 2 :=
            mul_le_mul_of_nonneg_left ((sq_le_sq₀ hb ha).2 hba) ha
          _ = a ^ 3 := by ring
          _ ≤ a ^ 3 + b ^ 3 := le_add_of_nonneg_right (pow_nonneg hb 3)
    have hac : a * c ^ 2 ≤ a ^ 3 + c ^ 3 := by
      rcases le_total a c with hac | hca
      · calc
          a * c ^ 2 ≤ c * c ^ 2 :=
            mul_le_mul_of_nonneg_right hac (sq_nonneg c)
          _ = c ^ 3 := by ring
          _ ≤ a ^ 3 + c ^ 3 := le_add_of_nonneg_left (pow_nonneg ha 3)
      · calc
          a * c ^ 2 ≤ a * a ^ 2 :=
            mul_le_mul_of_nonneg_left ((sq_le_sq₀ hc ha).2 hca) ha
          _ = a ^ 3 := by ring
          _ ≤ a ^ 3 + c ^ 3 := le_add_of_nonneg_right (pow_nonneg hc 3)
    have hbc : b * c ≤ (b ^ 2 + c ^ 2) / 2 := by
      nlinarith [sq_nonneg (b - c)]
    have hq :
        (b ^ 2 + c ^ 2) / 2 + b * c ≤ b ^ 2 + c ^ 2 := by
      linarith
    have hnonneg :
        0 ≤ a * ((b ^ 2 + c ^ 2) / 2 + b * c) := by positivity
    rw [Real.norm_eq_abs]
    calc
      |a * ((b ^ 2 + c ^ 2) / 2 + b * c)| =
          a * ((b ^ 2 + c ^ 2) / 2 + b * c) := abs_of_nonneg hnonneg
      _ ≤
          a * (b ^ 2 + c ^ 2) := mul_le_mul_of_nonneg_left hq ha
      _ = a * b ^ 2 + a * c ^ 2 := by ring
      _ ≤ (a ^ 3 + b ^ 3) + (a ^ 3 + c ^ 3) := add_le_add hab hac
      _ = M z := by
        dsimp only [M, a, b, c]
        ring

/-- Product-integrability of a parameter-dependent, translated second Gaussian-density
contraction.  The multiplier may depend on both the parameter and Euclidean coordinates; only a
measurable pointwise envelope and the corresponding quadratic moment majorant are required. -/
private lemma integrable_prod_parametric_mul_standardGaussianDensityD2_add
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ] {μ : Measure Θ} [SFinite μ]
    {φ : Θ × EuclideanSpace ℝ (Fin d) → ℝ} (hφm : Measurable φ)
    {b h g : Θ → EuclideanSpace ℝ (Fin d)}
    (hbm : Measurable b) (hhm : Measurable h) (hgm : Measurable g)
    {D : Θ → ℝ} (hD : ∀ z, 0 ≤ D z)
    (hφ : ∀ z u, |φ (z, u)| ≤ D z)
    (hmajor : Integrable (fun z ↦
      D z * ((‖h z‖ ^ 2 + ‖g z‖ ^ 2) / 2 + ‖h z‖ * ‖g z‖)) μ) :
    Integrable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦
      φ p * standardGaussianDensityD2
        (p.2 + b p.1) (h p.1) (g p.1)) (μ.prod volume) := by
  let F : Θ × EuclideanSpace ℝ (Fin d) → ℝ := fun p ↦
    φ p * standardGaussianDensityD2
      (p.2 + b p.1) (h p.1) (g p.1)
  have hFm : Measurable F := by
    dsimp only [F]
    unfold standardGaussianDensityD2
    have hy : Measurable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦
        p.2 + b p.1) := measurable_snd.add (hbm.comp measurable_fst)
    have hh' : Measurable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦ h p.1) :=
      hhm.comp measurable_fst
    have hg' : Measurable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦ g p.1) :=
      hgm.comp measurable_fst
    have hi₁ : Measurable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦
        inner ℝ (p.2 + b p.1) (h p.1)) :=
      continuous_inner.measurable.comp (hy.prodMk hh')
    have hi₂ : Measurable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦
        inner ℝ (p.2 + b p.1) (g p.1)) :=
      continuous_inner.measurable.comp (hy.prodMk hg')
    have hi₃ : Measurable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦
        inner ℝ (h p.1) (g p.1)) :=
      continuous_inner.measurable.comp (hh'.prodMk hg')
    exact hφm.mul (((hi₁.mul hi₂).sub hi₃).mul
      (continuous_standardGaussianDensity.measurable.comp hy))
  apply (integrable_prod_iff hFm.aestronglyMeasurable).2
  constructor
  · filter_upwards with z
    have hD2 : Integrable (fun u : EuclideanSpace ℝ (Fin d) ↦
        standardGaussianDensityD2 (u + b z) (h z) (g z)) volume := by
      have hbase :=
        (integrable_standardGaussianDensityD2_volume (h z) (g z)
          ).comp_sub_right (-b z)
      simpa only [sub_neg_eq_add] using hbase
    exact hD2.bdd_mul
      (hφm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (by
        filter_upwards with u
        change |φ (z, u)| ≤ D z
        exact hφ z u)
  · have hinnerMeas : AEStronglyMeasurable
        (fun z ↦ ∫ u, ‖F (z, u)‖ ∂volume) μ :=
      hFm.aestronglyMeasurable.norm.integral_prod_right'
    apply hmajor.mono' hinnerMeas
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun u ↦ norm_nonneg _)]
    let Q := (‖h z‖ ^ 2 + ‖g z‖ ^ 2) / 2 + ‖h z‖ * ‖g z‖
    have hD2 : Integrable (fun u : EuclideanSpace ℝ (Fin d) ↦
        standardGaussianDensityD2 (u + b z) (h z) (g z)) volume := by
      have hbase :=
        (integrable_standardGaussianDensityD2_volume (h z) (g z)
          ).comp_sub_right (-b z)
      simpa only [sub_neg_eq_add] using hbase
    calc
      (∫ u, ‖F (z, u)‖ ∂volume) ≤
          D z * ∫ u,
            |standardGaussianDensityD2 (u + b z) (h z) (g z)| ∂volume := by
        rw [← integral_const_mul]
        apply integral_mono
        · exact (hD2.bdd_mul
            (hφm.comp (measurable_const.prodMk measurable_id)
              ).aestronglyMeasurable (by
                filter_upwards with u
                change |φ (z, u)| ≤ D z
                exact hφ z u)).norm
        · exact hD2.abs.const_mul (D z)
        · intro u
          dsimp only [F]
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (hφ z u) (abs_nonneg _)
      _ = D z * ∫ u,
          |standardGaussianDensityD2 u (h z) (g z)| ∂volume := by
        congr 1
        exact integral_add_right_eq_self
          (fun u ↦ |standardGaussianDensityD2 u (h z) (g z)|) (b z)
      _ ≤ D z * Q := by
        exact mul_le_mul_of_nonneg_left
          (integral_abs_standardGaussianDensityD2_volume_le (h z) (g z))
          (hD z)

/-- Uniform translated-shell control converts the pointwise two-shift `D²` estimate into its
average over the random affine base.  The norm factors are left exact for the subsequent
replacement-pair moment estimate. -/
private theorem
    integral_abs_convexSetCutoffDirectionalPullback_twoShift_D2_le_of_uniform_shell
    {d : ℕ} {ν : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure ν]
    {s : Set (EuclideanSpace ℝ (Fin d))}
    (hsclosed : IsClosed s) (hs : Convexity.IsConvexSet ℝ s)
    {ε : ℝ} (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (v w : EuclideanSpace ℝ (Fin d)) (t r : ℝ)
    {J : ℝ} (hJ : 0 ≤ J)
    (hshell : ∀ z, ν.real ((fun a ↦ a + z) ⁻¹'
      (Metric.cthickening ε s \ interior s)) ≤ J) :
    (∫ a, |∫ u, convexSetCutoffDirectionalPullback s ε a x L u *
        standardGaussianDensityD2
          (u + r • (v + t • w)) w (v + t • w) ∂volume| ∂ν) ≤
      (((8 / ε ^ 2) * ‖L‖ * ‖x‖) * ‖v + t • w‖) *
        (J * ‖w‖) := by
  let E := EuclideanSpace ℝ (Fin d)
  let h : E := v + t • w
  let b : E := r • h
  let K : ℝ := ((8 / ε ^ 2) * ‖L‖ * ‖x‖) * ‖h‖
  let M : ℝ := (2 / ε) * ‖x‖
  let shell : Set E := Metric.cthickening ε s \ interior s
  let F : E → E := fun a ↦ a - L b
  let R : E × E → ℝ := fun p ↦
    convexSetCutoffDirectionalPullback s ε p.1 x L p.2 *
      standardGaussianDensityD2 (p.2 + b) w h
  let Q : E × E → ℝ := fun p ↦
    shell.indicator (fun _ ↦ |standardGaussianDensityD1 p.2 w|)
      (F p.1 + L p.2)
  have hshellMeas : MeasurableSet shell := by
    dsimp only [shell]
    exact (Metric.isClosed_cthickening.sdiff isOpen_interior).measurableSet
  have hFmeas : Measurable F := by
    dsimp only [F]
    fun_prop
  have hcutMeas : Measurable (fun p : E × E ↦
      convexSetCutoffDirectionalPullback s ε p.1 x L p.2) := by
    dsimp only [convexSetCutoffDirectionalPullback]
    exact ((contDiff_convexSetCutoff hs hε).continuous_fderiv_apply (by norm_num)
      ).measurable.comp
        ((measurable_fst.add
          (L.continuous.measurable.comp measurable_snd)).prodMk measurable_const)
  have hD2Meas : Measurable (fun p : E × E ↦
      standardGaussianDensityD2 (p.2 + b) w h) :=
    (continuous_standardGaussianDensityD2 w h).measurable.comp
      (measurable_snd.add measurable_const)
  have hRmeas : Measurable R := by
    dsimp only [R]
    exact hcutMeas.mul hD2Meas
  have hD2shift : Integrable
      (fun u : E ↦ standardGaussianDensityD2 (u + b) w h) volume := by
    have hb := (integrable_standardGaussianDensityD2_volume w h).comp_sub_right (-b)
    simpa only [sub_neg_eq_add] using hb
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity
  have hmajor : Integrable
      (fun p : E × E ↦ M * |standardGaussianDensityD2 (p.2 + b) w h|)
      (ν.prod volume) :=
    (hD2shift.abs.const_mul M).comp_snd ν
  have hRint : Integrable R (ν.prod volume) := by
    apply hmajor.mono' hRmeas.aestronglyMeasurable
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul]
    have happly := ContinuousLinearMap.le_opNorm
      (fderiv ℝ (convexSetCutoff s ε) (p.1 + L p.2)) x
    have hcut :
        |convexSetCutoffDirectionalPullback s ε p.1 x L p.2| ≤ M := by
      dsimp only [convexSetCutoffDirectionalPullback, M]
      rw [← Real.norm_eq_abs]
      calc
        ‖(fderiv ℝ (convexSetCutoff s ε) (p.1 + L p.2)) x‖ ≤
            ‖fderiv ℝ (convexSetCutoff s ε) (p.1 + L p.2)‖ * ‖x‖ := happly
        _ ≤ (2 / ε) * ‖x‖ := by
          exact mul_le_mul_of_nonneg_right
            (norm_fderiv_convexSetCutoff_le hs hε _) (norm_nonneg x)
    exact mul_le_mul_of_nonneg_right hcut (abs_nonneg _)
  have hinnerInt : Integrable
      (fun a ↦ ∫ u, R (a, u) ∂volume) ν :=
    hRint.integral_prod_left
  have hjoint : MeasurableSet
      ((fun p : E × E ↦ F p.1 + L p.2) ⁻¹' shell) :=
    hshellMeas.preimage
      ((hFmeas.comp measurable_fst).add
        (L.continuous.measurable.comp measurable_snd))
  have hQint : Integrable Q (ν.prod volume) := by
    have hbase : Integrable
        (fun p : E × E ↦ |standardGaussianDensityD1 p.2 w|)
        (ν.prod volume) :=
      (integrable_standardGaussianDensityD1_volume w).abs.comp_snd ν
    exact hbase.indicator hjoint
  have hQinnerInt : Integrable (fun a ↦ ∫ u, Q (a, u) ∂volume) ν :=
    hQint.integral_prod_left
  have hfiber (a : E) :
      MeasurableSet ((fun u ↦ F a + L u) ⁻¹' shell) :=
    hshellMeas.preimage (continuous_const.add L.continuous).measurable
  have hQfiber (a : E) :
      (∫ u, Q (a, u) ∂volume) =
        ∫ u in (fun u ↦ F a + L u) ⁻¹' shell,
          |standardGaussianDensityD1 u w| := by
    rw [← integral_indicator (hfiber a)]
    rfl
  have hshellF (u : E) :
      ν.real ((fun a ↦ F a + L u) ⁻¹' shell) ≤ J := by
    have hu := hshell (L u - L b)
    simpa only [F, shell, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hu
  have haverage :
      (∫ a, ∫ u in (fun u ↦ F a + L u) ⁻¹' shell,
          |standardGaussianDensityD1 u w| ∂volume ∂ν) ≤ J * ‖w‖ :=
    integral_setIntegral_abs_standardGaussianDensityD1_le_of_uniform_shell
      F hFmeas L shell hshellMeas w hJ hshellF
  have hpoint (a : E) :
      |∫ u, R (a, u) ∂volume| ≤ K * ∫ u, Q (a, u) ∂volume := by
    have hbase :=
      convexSetCutoffDirectionalPullback_twoShift_D2_shell_bound
        hsclosed hs hε a x L v w t r
    rw [hQfiber a]
    simpa only [R, F, shell, h, b, K] using hbase
  calc
    (∫ a, |∫ u, convexSetCutoffDirectionalPullback s ε a x L u *
        standardGaussianDensityD2
          (u + r • (v + t • w)) w (v + t • w) ∂volume| ∂ν) =
        ∫ a, |∫ u, R (a, u) ∂volume| ∂ν := rfl
    _ ≤ ∫ a, K * ∫ u, Q (a, u) ∂volume ∂ν := by
      exact integral_mono hinnerInt.abs (hQinnerInt.const_mul K) hpoint
    _ = K * ∫ a, ∫ u, Q (a, u) ∂volume ∂ν := by
      rw [integral_const_mul]
    _ = K * ∫ a, ∫ u in (fun u ↦ F a + L u) ⁻¹' shell,
          |standardGaussianDensityD1 u w| ∂volume ∂ν := by
      congr 1
      apply integral_congr_ae
      filter_upwards with a
      exact hQfiber a
    _ ≤ K * (J * ‖w‖) := by
      exact mul_le_mul_of_nonneg_left haverage (by
        dsimp only [K, h]
        positivity)
    _ = (((8 / ε ^ 2) * ‖L‖ * ‖x‖) * ‖v + t • w‖) *
        (J * ‖w‖) := rfl

/-- The uniform shell estimate for the split Gaussian base inserted into the averaged `D²`
remainder.  This is the probability-to-analysis composition in Bentkus (3.32)--(3.34), before
the omitted-coordinate moment bounds are applied. -/
private theorem
    bentkus_splitGaussianBase_average_twoShift_D2_le_of_induction
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
    (α : ℝ) (hcos : 0 < Real.cos α)
    (A : Set (EuclideanSpace ℝ (Fin d))) (hAclosed : IsClosed A)
    (hAconv : Convexity.IsConvexSet ℝ A) {ε : ℝ} (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (v w : EuclideanSpace ℝ (Fin d)) (t r : ℝ) :
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let U := bentkusLeaveOneOut X k
    let ν := μ.map (fun ω ↦ e (U ω))
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let θ := (Real.sqrt 2)⁻¹
    let p := Real.cos α
    let q := θ * Real.sin α
    let c := Real.sqrt (p ^ 2 + q ^ 2)
    let T := ((γ.map (fun y ↦ q • y)).prod ν).map
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        p • z.2 + z.1)
    let D := C * (d : ℝ) ^ (1 / 4 : ℝ) *
      ∑ i : Fin n, ∫ ω,
        ‖bentkusWhiteningCLM S (X (k.succAbove i) ω)‖ ^ 3 ∂μ
    let J := ballGaussianPerimeterConstant d *
      (‖e.toContinuousLinearMap‖ * ε / c) + 4 * D
    (∫ a, |∫ u, convexSetCutoffDirectionalPullback A ε a x L u *
        standardGaussianDensityD2
          (u + r • (v + t • w)) w (v + t • w) ∂volume|
      ∂(T.map e.symm)) ≤
      (((8 / ε ^ 2) * ‖L‖ * ‖x‖) * ‖v + t • w‖) *
        (J * ‖w‖) := by
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let U := bentkusLeaveOneOut X k
  let ν := μ.map (fun ω ↦ e (U ω))
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let θ := (Real.sqrt 2)⁻¹
  let p := Real.cos α
  let q := θ * Real.sin α
  let c := Real.sqrt (p ^ 2 + q ^ 2)
  let T := ((γ.map (fun y ↦ q • y)).prod ν).map
    (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      p • z.2 + z.1)
  let D := C * (d : ℝ) ^ (1 / 4 : ℝ) *
    ∑ i : Fin n, ∫ ω,
      ‖bentkusWhiteningCLM S (X (k.succAbove i) ω)‖ ^ 3 ∂μ
  let J := ballGaussianPerimeterConstant d *
    (‖e.toContinuousLinearMap‖ * ε / c) + 4 * D
  have hUmeas : Measurable U := by
    dsimp only [U, bentkusLeaveOneOut]
    exact Finset.measurable_sum (Finset.univ.erase k) fun i _ ↦ hXm i
  letI : IsProbabilityMeasure ν := by
    dsimp only [ν]
    exact Measure.isProbabilityMeasure_map
      (e.continuous.measurable.comp hUmeas).aemeasurable
  letI : IsProbabilityMeasure (γ.map (fun y ↦ q • y)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure T := by
    dsimp only [T]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (T.map e.symm) :=
    Measure.isProbabilityMeasure_map e.symm.continuous.measurable.aemeasurable
  have hp : 0 < p := by
    simpa only [p] using hcos
  have hc : 0 < c := by
    dsimp only [c]
    exact Real.sqrt_pos.2 (by
      have hp2 : 0 < p ^ 2 := sq_pos_of_pos hp
      nlinarith [sq_nonneg q])
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hJ : 0 ≤ J := by
    dsimp only [J]
    exact add_nonneg
      (mul_nonneg (by
        unfold ballGaussianPerimeterConstant
        positivity)
        (div_nonneg
          (mul_nonneg (norm_nonneg e.toContinuousLinearMap) hε.le) hc.le))
      (mul_nonneg (by norm_num) hD)
  have hshell : ∀ z, (T.map e.symm).real ((fun a ↦ a + z) ⁻¹'
      (Metric.cthickening ε A \ interior A)) ≤ J := by
    simpa only [S, hS, e, U, ν, γ, θ, p, q, c, T, D, J] using
      bentkus_splitGaussianBase_uniform_translated_closedShell_le_of_induction
        hC hIH hd hXm hX3 h_indep hX0 hidentity k hk α hcos
          A hAclosed hAconv hε.le
  simpa only [S, hS, e, U, ν, γ, θ, p, q, c, T, D, J] using
    integral_abs_convexSetCutoffDirectionalPullback_twoShift_D2_le_of_uniform_shell
      (ν := T.map e.symm) hAclosed hAconv hε x L v w t r hJ hshell

/-- Dimension-normalized form of the averaged two-shift `D²` estimate. -/
private theorem
    bentkus_splitGaussianBase_average_twoShift_D2_normalized_le_of_induction
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
    (α : ℝ) (hcos : 0 < Real.cos α)
    (A : Set (EuclideanSpace ℝ (Fin d))) (hAclosed : IsClosed A)
    (hAconv : Convexity.IsConvexSet ℝ A) {ε : ℝ} (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (v w : EuclideanSpace ℝ (Fin d)) (t r : ℝ) :
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let U := bentkusLeaveOneOut X k
    let ν := μ.map (fun ω ↦ e (U ω))
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let θ := (Real.sqrt 2)⁻¹
    let p := Real.cos α
    let q := θ * Real.sin α
    let T := ((γ.map (fun y ↦ q • y)).prod ν).map
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        p • z.2 + z.1)
    let β := ∑ i : Fin n, ∫ ω, ‖X (k.succAbove i) ω‖ ^ 3 ∂μ
    let J := 32 * (d : ℝ) ^ (1 / 4 : ℝ) * (C * β + ε)
    (∫ a, |∫ u, convexSetCutoffDirectionalPullback A ε a x L u *
        standardGaussianDensityD2
          (u + r • (v + t • w)) w (v + t • w) ∂volume|
      ∂(T.map e.symm)) ≤
      (((8 / ε ^ 2) * ‖L‖ * ‖x‖) * ‖v + t • w‖) *
        (J * ‖w‖) := by
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let U := bentkusLeaveOneOut X k
  let ν := μ.map (fun ω ↦ e (U ω))
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let θ := (Real.sqrt 2)⁻¹
  let p := Real.cos α
  let q := θ * Real.sin α
  let T := ((γ.map (fun y ↦ q • y)).prod ν).map
    (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      p • z.2 + z.1)
  let β := ∑ i : Fin n, ∫ ω, ‖X (k.succAbove i) ω‖ ^ 3 ∂μ
  let J := 32 * (d : ℝ) ^ (1 / 4 : ℝ) * (C * β + ε)
  have hUmeas : Measurable U := by
    dsimp only [U, bentkusLeaveOneOut]
    exact Finset.measurable_sum (Finset.univ.erase k) fun i _ ↦ hXm i
  letI : IsProbabilityMeasure ν := by
    dsimp only [ν]
    exact Measure.isProbabilityMeasure_map
      (e.continuous.measurable.comp hUmeas).aemeasurable
  letI : IsProbabilityMeasure (γ.map (fun y ↦ q • y)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure T := by
    dsimp only [T]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (T.map e.symm) :=
    Measure.isProbabilityMeasure_map e.symm.continuous.measurable.aemeasurable
  have hβ : 0 ≤ β := by
    dsimp only [β]
    exact Finset.sum_nonneg fun i _ ↦
      integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg _) 3
  have hJ : 0 ≤ J := by
    dsimp only [J]
    positivity
  have hshell : ∀ z, (T.map e.symm).real ((fun a ↦ a + z) ⁻¹'
      (Metric.cthickening ε A \ interior A)) ≤ J := by
    simpa only [S, hS, e, U, ν, γ, θ, p, q, T, β, J] using
      bentkus_splitGaussianBase_uniform_translated_closedShell_normalized_le_of_induction
        hC hIH hd hXm hX3 h_indep hX0 hidentity k hk α hcos
          A hAclosed hAconv hε.le
  simpa only [S, hS, e, U, ν, γ, θ, p, q, T, β, J] using
    integral_abs_convexSetCutoffDirectionalPullback_twoShift_D2_le_of_uniform_shell
      (ν := T.map e.symm) hAclosed hAconv hε x L v w t r hJ hshell

/-- Integration of a pointwise averaged two-shift estimate over an auxiliary random pair. -/
private theorem integral_pair_average_twoShift_D2_le
    {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    {τ : Measure Z} {ν : Measure (EuclideanSpace ℝ (Fin d))}
    [SFinite τ] [SFinite ν]
    {A : Set (EuclideanSpace ℝ (Fin d))}
    (hAconv : Convexity.IsConvexSet ℝ A)
    {ε c J t r : ℝ} (hε : 0 < ε) (hc : 0 ≤ c) (hJ : 0 ≤ J)
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (x v w : Z → EuclideanSpace ℝ (Fin d))
    (hx : Measurable x) (hv : Measurable v) (hw : Measurable w)
    (hfactor : Integrable (fun z ↦
      c * ‖L‖ * ‖x z‖ * ‖v z + t • w z‖ * ‖w z‖) τ)
    (hbound : ∀ z,
      (∫ a, |∫ u, convexSetCutoffDirectionalPullback A ε a (x z) L u *
          standardGaussianDensityD2
            (u + r • (v z + t • w z)) (w z) (v z + t • w z) ∂volume| ∂ν) ≤
        (((8 / ε ^ 2) * ‖L‖ * ‖x z‖) * ‖v z + t • w z‖) *
          (J * ‖w z‖)) :
    (∫ z, c * ∫ a,
      |∫ u, convexSetCutoffDirectionalPullback A ε a (x z) L u *
        standardGaussianDensityD2
          (u + r • (v z + t • w z)) (w z) (v z + t • w z) ∂volume| ∂ν ∂τ) ≤
      (8 / ε ^ 2) * J *
        ∫ z, c * ‖L‖ * ‖x z‖ * ‖v z + t • w z‖ * ‖w z‖ ∂τ := by
  let H : (Z × EuclideanSpace ℝ (Fin d)) ×
      EuclideanSpace ℝ (Fin d) → ℝ := fun p ↦
    convexSetCutoffDirectionalPullback A ε p.1.2 (x p.1.1) L p.2 *
      standardGaussianDensityD2
        (p.2 + r • (v p.1.1 + t • w p.1.1))
        (w p.1.1) (v p.1.1 + t • w p.1.1)
  let f : Z → ℝ := fun z ↦
    c * ∫ a, |∫ u, H ((z, a), u) ∂volume| ∂ν
  let factor : Z → ℝ := fun z ↦
    c * ‖L‖ * ‖x z‖ * ‖v z + t • w z‖ * ‖w z‖
  let K : ℝ := (8 / ε ^ 2) * J
  have hHmeas : Measurable H := by
    dsimp only [H, convexSetCutoffDirectionalPullback]
    have hpos : Measurable (fun p : (Z × EuclideanSpace ℝ (Fin d)) ×
        EuclideanSpace ℝ (Fin d) ↦ p.1.2 + L p.2) := by
      fun_prop
    have hdir : Measurable (fun p : (Z × EuclideanSpace ℝ (Fin d)) ×
        EuclideanSpace ℝ (Fin d) ↦ x p.1.1) :=
      hx.comp (measurable_fst.comp measurable_fst)
    have hcut : Measurable (fun p : (Z × EuclideanSpace ℝ (Fin d)) ×
        EuclideanSpace ℝ (Fin d) ↦
        (fderiv ℝ (convexSetCutoff A ε) (p.1.2 + L p.2)) (x p.1.1)) := by
      exact ((contDiff_convexSetCutoff hAconv hε).continuous_fderiv_apply
        (by norm_num)).measurable.comp (hpos.prodMk hdir)
    have hD2 : Measurable (fun p : (Z × EuclideanSpace ℝ (Fin d)) ×
        EuclideanSpace ℝ (Fin d) ↦
        standardGaussianDensityD2
          (p.2 + r • (v p.1.1 + t • w p.1.1))
          (w p.1.1) (v p.1.1 + t • w p.1.1)) := by
      unfold standardGaussianDensityD2
      have hy : Measurable (fun p : (Z × EuclideanSpace ℝ (Fin d)) ×
          EuclideanSpace ℝ (Fin d) ↦
          p.2 + r • (v p.1.1 + t • w p.1.1)) := by
        fun_prop
      have hw' : Measurable (fun p : (Z × EuclideanSpace ℝ (Fin d)) ×
          EuclideanSpace ℝ (Fin d) ↦ w p.1.1) :=
        hw.comp (measurable_fst.comp measurable_fst)
      have hvw : Measurable (fun p : (Z × EuclideanSpace ℝ (Fin d)) ×
          EuclideanSpace ℝ (Fin d) ↦ v p.1.1 + t • w p.1.1) := by
        fun_prop
      have hi₁ : Measurable (fun p : (Z × EuclideanSpace ℝ (Fin d)) ×
          EuclideanSpace ℝ (Fin d) ↦
          inner ℝ
            (p.2 + r • (v p.1.1 + t • w p.1.1)) (w p.1.1)) :=
        continuous_inner.measurable.comp (hy.prodMk hw')
      have hi₂ : Measurable (fun p : (Z × EuclideanSpace ℝ (Fin d)) ×
          EuclideanSpace ℝ (Fin d) ↦
          inner ℝ
            (p.2 + r • (v p.1.1 + t • w p.1.1))
            (v p.1.1 + t • w p.1.1)) :=
        continuous_inner.measurable.comp (hy.prodMk hvw)
      have hi₃ : Measurable (fun p : (Z × EuclideanSpace ℝ (Fin d)) ×
          EuclideanSpace ℝ (Fin d) ↦
          inner ℝ (w p.1.1) (v p.1.1 + t • w p.1.1)) :=
        continuous_inner.measurable.comp (hw'.prodMk hvw)
      exact ((hi₁.mul hi₂).sub hi₃).mul
        (continuous_standardGaussianDensity.measurable.comp hy)
    exact hcut.mul hD2
  have hinnerMeas : StronglyMeasurable (fun z : Z ↦
      ∫ a, |∫ u, H ((z, a), u) ∂volume| ∂ν) := by
    have hu : StronglyMeasurable (fun p :
        Z × EuclideanSpace ℝ (Fin d) ↦
        ∫ u, H (p, u) ∂volume) :=
      hHmeas.stronglyMeasurable.integral_prod_right'
    have hua : StronglyMeasurable (fun p :
        Z × EuclideanSpace ℝ (Fin d) ↦
        |∫ u, H (p, u) ∂volume|) := by
      simpa only [Real.norm_eq_abs] using hu.norm
    exact hua.integral_prod_right' (ν := ν)
  have hfMeas : AEStronglyMeasurable f τ :=
    hinnerMeas.const_mul c |>.aestronglyMeasurable
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hfactorNonneg (z : Z) : 0 ≤ factor z := by
    dsimp only [factor]
    positivity
  have hgInt : Integrable (fun z ↦ K * factor z) τ := by
    exact hfactor.const_mul K
  have hpoint (z : Z) : f z ≤ K * factor z := by
    dsimp only [f, factor, K]
    calc
      c * (∫ a, |∫ u, H ((z, a), u) ∂volume| ∂ν) ≤
          c * ((((8 / ε ^ 2) * ‖L‖ * ‖x z‖) *
            ‖v z + t • w z‖) * (J * ‖w z‖)) := by
        exact mul_le_mul_of_nonneg_left (by
          simpa only [H] using hbound z) hc
      _ = (8 / ε ^ 2) * J *
          (c * ‖L‖ * ‖x z‖ * ‖v z + t • w z‖ * ‖w z‖) := by ring
  have hfInt : Integrable f τ := by
    apply hgInt.mono' hfMeas
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hpoint z
    · dsimp only [f]
      positivity
  calc
    (∫ z, c * ∫ a,
        |∫ u, convexSetCutoffDirectionalPullback A ε a (x z) L u *
          standardGaussianDensityD2
            (u + r • (v z + t • w z)) (w z) (v z + t • w z)
          ∂volume| ∂ν ∂τ) =
        ∫ z, f z ∂τ := rfl
    _ ≤ ∫ z, K * factor z ∂τ :=
      integral_mono hfInt hgInt hpoint
    _ = K * ∫ z, factor z ∂τ := by rw [integral_const_mul]
    _ = (8 / ε ^ 2) * J *
        ∫ z, c * ‖L‖ * ‖x z‖ * ‖v z + t • w z‖ * ‖w z‖ ∂τ := rfl

/-- Scalar bookkeeping for the original-coordinate remainder in the small-angle argument. -/
private lemma bentkus_smallAngle_original_factor_le
    {θ s p t a b ell v w : ℝ}
    (hθ : 0 < θ) (hs : 0 < s) (hs1 : s ≤ 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hell : 0 ≤ ell)
    (hv0 : 0 ≤ v) (hw0 : 0 ≤ w)
    (hθinv : 1 / θ ≤ 2)
    (hell_le : ell ≤ θ * s)
    (hv_le : v ≤ 2 / θ * b)
    (hw_le : w ≤ 2 * p / (θ * s) * a) :
    s * ell * a * (v + t * w) * w ≤
      8 * p * (a ^ 2 * b + a ^ 3) := by
  have hθ0 : 0 ≤ θ := hθ.le
  have hs0 : 0 ≤ s := hs.le
  have hθs : 0 < θ * s := mul_pos hθ hs
  calc
    s * ell * a * (v + t * w) * w ≤
        s * (θ * s) * a *
          ((2 / θ * b) + t * (2 * p / (θ * s) * a)) *
            (2 * p / (θ * s) * a) := by
      gcongr
    _ = (4 * p * s / θ) * (a ^ 2 * b) +
        (4 * p ^ 2 * t / θ) * a ^ 3 := by
      field_simp [ne_of_gt hθ, ne_of_gt hs]
      ring
    _ ≤ 8 * p * (a ^ 2 * b + a ^ 3) := by
      have hab : 0 ≤ a ^ 2 * b := mul_nonneg (sq_nonneg a) hb
      have ha3 : 0 ≤ a ^ 3 := pow_nonneg ha 3
      have hfirst : 4 * p * s / θ ≤ 8 * p := by
        calc
          4 * p * s / θ = 4 * p * s * (1 / θ) := by field_simp
          _ ≤ 4 * p * 1 * 2 := by gcongr
          _ = 8 * p := by ring
      have hsecond : 4 * p ^ 2 * t / θ ≤ 8 * p := by
        calc
          4 * p ^ 2 * t / θ = 4 * p ^ 2 * t * (1 / θ) := by field_simp
          _ ≤ 4 * p * 1 * 2 := by
            gcongr
            nlinarith
          _ = 8 * p := by ring
      nlinarith

/-- Scalar bookkeeping for the Gaussian-coordinate remainder in the small-angle argument. -/
private lemma bentkus_smallAngle_gaussian_factor_le
    {θ s p t a b ell v w : ℝ}
    (hθ : 0 < θ) (hs : 0 < s) (hs1 : s ≤ 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hell : 0 ≤ ell)
    (hv0 : 0 ≤ v) (hw0 : 0 ≤ w)
    (hθinv : 1 / θ ≤ 2)
    (hell_le : ell ≤ θ * s)
    (hv_le : v ≤ 2 * p / (θ * s) * a)
    (hw_le : w ≤ 2 / θ * b) :
    p * ell * b * (v + t * w) * w ≤
      8 * p * (b ^ 2 * a + b ^ 3) := by
  have hθ0 : 0 ≤ θ := hθ.le
  have hs0 : 0 ≤ s := hs.le
  have hθs : 0 < θ * s := mul_pos hθ hs
  calc
    p * ell * b * (v + t * w) * w ≤
        p * (θ * s) * b *
          ((2 * p / (θ * s) * a) + t * (2 / θ * b)) *
            (2 / θ * b) := by
      gcongr
    _ = (4 * p ^ 2 / θ) * (b ^ 2 * a) +
        (4 * p * s * t / θ) * b ^ 3 := by
      field_simp [ne_of_gt hθ, ne_of_gt hs]
      ring
    _ ≤ 8 * p * (b ^ 2 * a + b ^ 3) := by
      have hba : 0 ≤ b ^ 2 * a := mul_nonneg (sq_nonneg b) ha
      have hb3 : 0 ≤ b ^ 3 := pow_nonneg hb 3
      have hfirst : 4 * p ^ 2 / θ ≤ 8 * p := by
        calc
          4 * p ^ 2 / θ = 4 * p ^ 2 * (1 / θ) := by field_simp
          _ ≤ 4 * p * 2 := by
            gcongr
            nlinarith
          _ = 8 * p := by ring
      have hsecond : 4 * p * s * t / θ ≤ 8 * p := by
        calc
          4 * p * s * t / θ = 4 * p * s * t * (1 / θ) := by field_simp
          _ ≤ 4 * p * 1 * 1 * 2 := by gcongr
          _ = 8 * p := by ring
      nlinarith

/-- The replacement-pair moment estimate for the two small-angle density remainders.  The first
coordinate costs `16` before the Hessian factor `8`; the Gaussian companion costs `224`.
These are the explicit moment constants behind `128 + 1792 = 1920`. -/
private theorem bentkus_smallAngle_twoShift_moment_factors_integrable_and_le
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (α : ℝ) (hsin : 0 < Real.sin α) (hcos : 0 ≤ Real.cos α)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    let ρ := bentkusReplacementMeasure μ X
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let θ := (Real.sqrt 2)⁻¹
    let p := Real.cos α
    let s := Real.sin α
    let L := (θ * s) • P
    let vO := fun ω ↦ -((1 / θ) • B (G ω))
    let wO := fun ω ↦ -((p / (θ * s)) • B (O ω))
    let vG := fun ω ↦ -((p / (θ * s)) • B (O ω))
    let wG := fun ω ↦ -((1 / θ) • B (G ω))
    let βk := ∫ ω, ‖O ω‖ ^ 3 ∂ρ
    (Integrable (fun ω ↦
        s * ‖L‖ * ‖O ω‖ * ‖vO ω + t • wO ω‖ * ‖wO ω‖) ρ ∧
      Integrable (fun ω ↦
        p * ‖L‖ * ‖G ω‖ * ‖vG ω + t • wG ω‖ * ‖wG ω‖) ρ) ∧
    ((∫ ω, s * ‖L‖ * ‖O ω‖ * ‖vO ω + t • wO ω‖ * ‖wO ω‖ ∂ρ) ≤
        16 * p * βk ∧
      (∫ ω, p * ‖L‖ * ‖G ω‖ * ‖vG ω + t • wG ω‖ * ‖wG ω‖ ∂ρ) ≤
        224 * p * βk) := by
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
  let θ := (Real.sqrt 2)⁻¹
  let p := Real.cos α
  let s := Real.sin α
  let L := (θ * s) • P
  let vO := fun ω ↦ -((1 / θ) • B (G ω))
  let wO := fun ω ↦ -((p / (θ * s)) • B (O ω))
  let vG := fun ω ↦ -((p / (θ * s)) • B (O ω))
  let wG := fun ω ↦ -((1 / θ) • B (G ω))
  let βk := ∫ ω, ‖O ω‖ ^ 3 ∂ρ
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hXm
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ, bentkusReplacementMeasure]
    infer_instance
  have hp : 0 ≤ p := by simpa only [p] using hcos
  have hp1 : p ≤ 1 := by
    dsimp only [p]
    exact Real.cos_le_one α
  have hs : 0 < s := by simpa only [s] using hsin
  have hs1 : s ≤ 1 := by
    dsimp only [s]
    exact Real.sin_le_one α
  have hθ : 0 < θ := by
    dsimp only [θ]
    exact inv_pos.mpr (Real.sqrt_pos.2 (by norm_num))
  have hθinv : 1 / θ ≤ 2 := by
    dsimp only [θ]
    rw [one_div, inv_inv]
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hPnorm : ‖P‖ ≤ 1 := by
    simpa only [P, e, S] using
      norm_bentkusWhiteningEquiv_symm_leaveOneOut_le_one
        hX3 h_indep hidentity k hS
  have hBnorm : ‖B‖ ≤ 2 := by
    simpa only [B, e, S] using
      norm_bentkusWhiteningEquiv_leaveOneOut_le_two
        hX3 h_indep hX0 hidentity k hk hS
  have hLnorm : ‖L‖ ≤ θ * s := by
    dsimp only [L]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hθ.le hs.le)]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hPnorm (mul_nonneg hθ.le hs.le)
  have hBapply (x : EuclideanSpace ℝ (Fin d)) : ‖B x‖ ≤ 2 * ‖x‖ := by
    calc
      ‖B x‖ ≤ ‖B‖ * ‖x‖ := ContinuousLinearMap.le_opNorm B x
      _ ≤ 2 * ‖x‖ :=
        mul_le_mul_of_nonneg_right hBnorm (norm_nonneg x)
  have hO3 : MemLp O 3 ρ := memLp_replacementOriginal hXm hX3 k
  have hG3 : MemLp G 3 ρ := memLp_three_replacementGaussian hXm k
  have hO2 : MemLp O 2 ρ := hO3.mono_exponent (by norm_num)
  have hG2 : MemLp G 2 ρ := hG3.mono_exponent (by norm_num)
  have hO1 : MemLp O 1 ρ := hO3.mono_exponent (by norm_num)
  have hBO3 : MemLp (fun ω ↦ B (O ω)) 3 ρ :=
    hO3.continuousLinearMap_comp B
  have hBG3 : MemLp (fun ω ↦ B (G ω)) 3 ρ :=
    hG3.continuousLinearMap_comp B
  have hO3int : Integrable (fun ω ↦ ‖O ω‖ ^ 3) ρ :=
    hO3.integrable_norm_pow (by norm_num)
  have hG3int : Integrable (fun ω ↦ ‖G ω‖ ^ 3) ρ :=
    hG3.integrable_norm_pow (by norm_num)
  have hcubic (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      a ^ 2 * b ≤ a ^ 3 + b ^ 3 := by
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
  have hOGint : Integrable (fun ω ↦ ‖O ω‖ ^ 2 * ‖G ω‖) ρ := by
    apply (hO3int.add hG3int).mono'
      ((hO3.aestronglyMeasurable.norm.pow 2).mul hG3.aestronglyMeasurable.norm)
    filter_upwards with ω
    change |‖O ω‖ ^ 2 * ‖G ω‖| ≤ ‖O ω‖ ^ 3 + ‖G ω‖ ^ 3
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _))]
    exact hcubic _ _ (norm_nonneg _) (norm_nonneg _)
  have hGOint : Integrable (fun ω ↦ ‖G ω‖ ^ 2 * ‖O ω‖) ρ := by
    apply (hG3int.add hO3int).mono'
      ((hG3.aestronglyMeasurable.norm.pow 2).mul hO3.aestronglyMeasurable.norm)
    filter_upwards with ω
    change |‖G ω‖ ^ 2 * ‖O ω‖| ≤ ‖G ω‖ ^ 3 + ‖O ω‖ ^ 3
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _))]
    exact hcubic _ _ (norm_nonneg _) (norm_nonneg _)
  have hOG : (∫ ω, ‖O ω‖ ^ 2 * ‖G ω‖ ∂ρ) ≤ βk := by
    simpa only [O, G, ρ, βk] using
      integral_norm_sq_replacementOriginal_mul_norm_replacementGaussian_le
        hXm hX3 hX0 k
  have hGOeq :
      (∫ ω, ‖G ω‖ ^ 2 * ‖O ω‖ ∂ρ) =
        (∫ ω, ‖G ω‖ ^ 2 ∂ρ) * ∫ ω, ‖O ω‖ ∂ρ := by
    have hind : (fun ω ↦ ‖G ω‖ ^ 2) ⟂ᵢ[ρ] (fun ω ↦ ‖O ω‖) := by
      change ((fun z : EuclideanSpace ℝ (Fin d) ↦ ‖z‖ ^ 2) ∘ G) ⟂ᵢ[ρ]
        ((fun z : EuclideanSpace ℝ (Fin d) ↦ ‖z‖) ∘ O)
      exact (indepFun_replacementOriginal_replacementGaussian hXm k k).symm.comp
        (by fun_prop) (by fun_prop)
    exact hind.integral_fun_mul_eq_mul_integral
      (hG2.aestronglyMeasurable.norm.pow 2)
      hO1.aestronglyMeasurable.norm
  have hGO : (∫ ω, ‖G ω‖ ^ 2 * ‖O ω‖ ∂ρ) ≤ βk := by
    rw [hGOeq]
    simpa only [O, G, ρ, βk] using
      integral_norm_sq_replacementGaussian_mul_integral_norm_replacementOriginal_le
        hXm hX3 hX0 k
  have hG3le : (∫ ω, ‖G ω‖ ^ 3 ∂ρ) ≤ 27 * βk := by
    have hbase := integral_norm_pow_three_replacementGaussian_le hXm hX3 hX0 k
    simpa only [gaussianCompanionThirdMomentConstant, O, G, ρ, βk] using hbase
  have hvO_le (ω) : ‖vO ω‖ ≤ 2 / θ * ‖G ω‖ := by
    dsimp only [vO]
    rw [norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (by norm_num) hθ.le)]
    calc
      (1 / θ) * ‖B (G ω)‖ ≤ (1 / θ) * (2 * ‖G ω‖) := by
        exact mul_le_mul_of_nonneg_left (hBapply _)
          (div_nonneg (by norm_num) hθ.le)
      _ = 2 / θ * ‖G ω‖ := by ring
  have hwO_le (ω) : ‖wO ω‖ ≤ 2 * p / (θ * s) * ‖O ω‖ := by
    dsimp only [wO]
    rw [norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hp (mul_nonneg hθ.le hs.le))]
    calc
      (p / (θ * s)) * ‖B (O ω)‖ ≤
          (p / (θ * s)) * (2 * ‖O ω‖) := by
        exact mul_le_mul_of_nonneg_left (hBapply _)
          (div_nonneg hp (mul_nonneg hθ.le hs.le))
      _ = 2 * p / (θ * s) * ‖O ω‖ := by ring
  have hvG_le (ω) : ‖vG ω‖ ≤ 2 * p / (θ * s) * ‖O ω‖ := by
    simpa only [vG, wO] using hwO_le ω
  have hwG_le (ω) : ‖wG ω‖ ≤ 2 / θ * ‖G ω‖ := by
    simpa only [wG, vO] using hvO_le ω
  have hvOm : AEStronglyMeasurable vO ρ := by
    apply Measurable.aestronglyMeasurable
    dsimp only [vO, G, replacementGaussian]
    fun_prop
  have hwOm : AEStronglyMeasurable wO ρ := by
    apply Measurable.aestronglyMeasurable
    dsimp only [wO, O, replacementOriginal]
    fun_prop
  have hvGm : AEStronglyMeasurable vG ρ := by
    apply Measurable.aestronglyMeasurable
    dsimp only [vG, O, replacementOriginal]
    fun_prop
  have hwGm : AEStronglyMeasurable wG ρ := by
    apply Measurable.aestronglyMeasurable
    dsimp only [wG, G, replacementGaussian]
    fun_prop
  let M₁ := fun ω ↦ 8 * p * (‖O ω‖ ^ 2 * ‖G ω‖ + ‖O ω‖ ^ 3)
  let M₂ := fun ω ↦ 8 * p * (‖G ω‖ ^ 2 * ‖O ω‖ + ‖G ω‖ ^ 3)
  have hM₁int : Integrable M₁ ρ :=
    (hOGint.add hO3int).const_mul (8 * p)
  have hM₂int : Integrable M₂ ρ :=
    (hGOint.add hG3int).const_mul (8 * p)
  have hpoint₁ (ω) :
      s * ‖L‖ * ‖O ω‖ * ‖vO ω + t • wO ω‖ * ‖wO ω‖ ≤ M₁ ω := by
    have hadd :
        ‖vO ω + t • wO ω‖ ≤ ‖vO ω‖ + t * ‖wO ω‖ := by
      calc
        ‖vO ω + t • wO ω‖ ≤ ‖vO ω‖ + ‖t • wO ω‖ := norm_add_le _ _
        _ = ‖vO ω‖ + t * ‖wO ω‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    calc
      s * ‖L‖ * ‖O ω‖ * ‖vO ω + t • wO ω‖ * ‖wO ω‖ ≤
          s * ‖L‖ * ‖O ω‖ *
            (‖vO ω‖ + t * ‖wO ω‖) * ‖wO ω‖ := by gcongr
      _ ≤ 8 * p * (‖O ω‖ ^ 2 * ‖G ω‖ + ‖O ω‖ ^ 3) :=
        bentkus_smallAngle_original_factor_le
          hθ hs hs1 hp hp1 ht ht1
          (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
          (norm_nonneg _) (norm_nonneg _) hθinv hLnorm
          (hvO_le ω) (hwO_le ω)
      _ = M₁ ω := rfl
  have hpoint₂ (ω) :
      p * ‖L‖ * ‖G ω‖ * ‖vG ω + t • wG ω‖ * ‖wG ω‖ ≤ M₂ ω := by
    have hadd :
        ‖vG ω + t • wG ω‖ ≤ ‖vG ω‖ + t * ‖wG ω‖ := by
      calc
        ‖vG ω + t • wG ω‖ ≤ ‖vG ω‖ + ‖t • wG ω‖ := norm_add_le _ _
        _ = ‖vG ω‖ + t * ‖wG ω‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    calc
      p * ‖L‖ * ‖G ω‖ * ‖vG ω + t • wG ω‖ * ‖wG ω‖ ≤
          p * ‖L‖ * ‖G ω‖ *
            (‖vG ω‖ + t * ‖wG ω‖) * ‖wG ω‖ := by gcongr
      _ ≤ 8 * p * (‖G ω‖ ^ 2 * ‖O ω‖ + ‖G ω‖ ^ 3) :=
        bentkus_smallAngle_gaussian_factor_le
          hθ hs hs1 hp hp1 ht ht1
          (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
          (norm_nonneg _) (norm_nonneg _) hθinv hLnorm
          (hvG_le ω) (hwG_le ω)
      _ = M₂ ω := rfl
  have hleft₁ : Integrable
      (fun ω ↦ s * ‖L‖ * ‖O ω‖ *
        ‖vO ω + t • wO ω‖ * ‖wO ω‖) ρ := by
    apply hM₁int.mono'
    · exact (((hO3.aestronglyMeasurable.norm.const_mul (s * ‖L‖)).mul
          (hvOm.add (hwOm.const_smul t)).norm).mul hwOm.norm)
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hpoint₁ ω
  have hleft₂ : Integrable
      (fun ω ↦ p * ‖L‖ * ‖G ω‖ *
        ‖vG ω + t • wG ω‖ * ‖wG ω‖) ρ := by
    apply hM₂int.mono'
    · exact (((hG3.aestronglyMeasurable.norm.const_mul (p * ‖L‖)).mul
          (hvGm.add (hwGm.const_smul t)).norm).mul hwGm.norm)
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hpoint₂ ω
  refine ⟨⟨hleft₁, hleft₂⟩, ?_⟩
  constructor
  · calc
      (∫ ω, s * ‖L‖ * ‖O ω‖ *
          ‖vO ω + t • wO ω‖ * ‖wO ω‖ ∂ρ) ≤
          ∫ ω, M₁ ω ∂ρ := integral_mono hleft₁ hM₁int hpoint₁
      _ = 8 * p *
          ((∫ ω, ‖O ω‖ ^ 2 * ‖G ω‖ ∂ρ) +
            ∫ ω, ‖O ω‖ ^ 3 ∂ρ) := by
        dsimp only [M₁]
        rw [integral_const_mul, integral_add hOGint hO3int]
      _ ≤ 8 * p * (βk + βk) := by gcongr
      _ = 16 * p * βk := by ring
  · calc
      (∫ ω, p * ‖L‖ * ‖G ω‖ *
          ‖vG ω + t • wG ω‖ * ‖wG ω‖ ∂ρ) ≤
          ∫ ω, M₂ ω ∂ρ := integral_mono hleft₂ hM₂int hpoint₂
      _ = 8 * p *
          ((∫ ω, ‖G ω‖ ^ 2 * ‖O ω‖ ∂ρ) +
            ∫ ω, ‖G ω‖ ^ 3 ∂ρ) := by
        dsimp only [M₂]
        rw [integral_const_mul, integral_add hGOint hG3int]
      _ ≤ 8 * p * (βk + 27 * βk) := by gcongr
      _ = 224 * p * βk := by ring

/-- The numerical part of the small-angle replacement-pair moment estimate. -/
private theorem bentkus_smallAngle_twoShift_moment_factors_le
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (α : ℝ) (hsin : 0 < Real.sin α) (hcos : 0 ≤ Real.cos α)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    let ρ := bentkusReplacementMeasure μ X
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let θ := (Real.sqrt 2)⁻¹
    let p := Real.cos α
    let s := Real.sin α
    let L := (θ * s) • P
    let vO := fun ω ↦ -((1 / θ) • B (G ω))
    let wO := fun ω ↦ -((p / (θ * s)) • B (O ω))
    let vG := fun ω ↦ -((p / (θ * s)) • B (O ω))
    let wG := fun ω ↦ -((1 / θ) • B (G ω))
    let βk := ∫ ω, ‖O ω‖ ^ 3 ∂ρ
    (∫ ω, s * ‖L‖ * ‖O ω‖ * ‖vO ω + t • wO ω‖ * ‖wO ω‖ ∂ρ) ≤
        16 * p * βk ∧
      (∫ ω, p * ‖L‖ * ‖G ω‖ * ‖vG ω + t • wG ω‖ * ‖wG ω‖ ∂ρ) ≤
        224 * p * βk := by
  exact (bentkus_smallAngle_twoShift_moment_factors_integrable_and_le
    hXm hX3 h_indep hX0 hidentity k hk α hsin hcos t ht ht1).2

/-- Integrability of the two small-angle moment factors on the omitted-pair law. -/
private theorem bentkus_smallAngle_pairFactors_integrable
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (α : ℝ) (hsin : 0 < Real.sin α) (hcos : 0 ≤ Real.cos α)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    let ρ := bentkusReplacementMeasure μ X
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let Z := fun ω ↦ (O ω, G ω)
    let τ := ρ.map Z
    let θ := (Real.sqrt 2)⁻¹
    let p := Real.cos α
    let s := Real.sin α
    let L := (θ * s) • P
    let vO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((1 / θ) • B z.2)
    let wO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((p / (θ * s)) • B z.1)
    let vG := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((p / (θ * s)) • B z.1)
    let wG := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((1 / θ) • B z.2)
    Integrable (fun z ↦
        s * ‖L‖ * ‖z.1‖ * ‖vO z + t • wO z‖ * ‖wO z‖) τ ∧
      Integrable (fun z ↦
        p * ‖L‖ * ‖z.2‖ * ‖vG z + t • wG z‖ * ‖wG z‖) τ := by
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
  let Z := fun ω ↦ (O ω, G ω)
  let τ := ρ.map Z
  let θ := (Real.sqrt 2)⁻¹
  let p := Real.cos α
  let s := Real.sin α
  let L := (θ * s) • P
  let vO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -((1 / θ) • B z.2)
  let wO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -((p / (θ * s)) • B z.1)
  let vG := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -((p / (θ * s)) • B z.1)
  let wG := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -((1 / θ) • B z.2)
  have hZmeas : Measurable Z := by
    dsimp only [Z, O, G, replacementOriginal, replacementGaussian]
    fun_prop
  have hbase :=
    (bentkus_smallAngle_twoShift_moment_factors_integrable_and_le
      hXm hX3 h_indep hX0 hidentity k hk α hsin hcos t ht ht1).1
  constructor
  · apply (integrable_map_measure (by fun_prop) hZmeas.aemeasurable).2
    apply hbase.1.congr
    filter_upwards with ω
    rfl
  · apply (integrable_map_measure (by fun_prop) hZmeas.aemeasurable).2
    apply hbase.2.congr
    filter_upwards with ω
    rfl

/-- Numerical small-angle moment bounds transported to the omitted-pair law. -/
private theorem bentkus_smallAngle_pairFactors_le
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (α : ℝ) (hsin : 0 < Real.sin α) (hcos : 0 ≤ Real.cos α)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    let ρ := bentkusReplacementMeasure μ X
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let Z := fun ω ↦ (O ω, G ω)
    let τ := ρ.map Z
    let θ := (Real.sqrt 2)⁻¹
    let p := Real.cos α
    let s := Real.sin α
    let L := (θ * s) • P
    let vO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((1 / θ) • B z.2)
    let wO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((p / (θ * s)) • B z.1)
    let vG := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((p / (θ * s)) • B z.1)
    let wG := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((1 / θ) • B z.2)
    let βk := ∫ ω, ‖O ω‖ ^ 3 ∂ρ
    (∫ z, s * ‖L‖ * ‖z.1‖ * ‖vO z + t • wO z‖ * ‖wO z‖ ∂τ) ≤
        16 * p * βk ∧
      (∫ z, p * ‖L‖ * ‖z.2‖ * ‖vG z + t • wG z‖ * ‖wG z‖ ∂τ) ≤
        224 * p * βk := by
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
  let Z := fun ω ↦ (O ω, G ω)
  let τ := ρ.map Z
  let θ := (Real.sqrt 2)⁻¹
  let p := Real.cos α
  let s := Real.sin α
  let L := (θ * s) • P
  let vO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -((1 / θ) • B z.2)
  let wO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -((p / (θ * s)) • B z.1)
  let vG := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -((p / (θ * s)) • B z.1)
  let wG := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -((1 / θ) • B z.2)
  let βk := ∫ ω, ‖O ω‖ ^ 3 ∂ρ
  have hZmeas : Measurable Z := by
    dsimp only [Z, O, G, replacementOriginal, replacementGaussian]
    fun_prop
  have hbase := bentkus_smallAngle_twoShift_moment_factors_le
    hXm hX3 h_indep hX0 hidentity k hk α hsin hcos t ht ht1
  constructor
  · rw [integral_map hZmeas.aemeasurable (by fun_prop)]
    simpa only [ρ, S, hS, e, P, B, O, G, Z, τ, θ, p, s, L, vO, wO, βk,
      Function.comp_apply, Prod.fst, Prod.snd] using hbase.1
  · rw [integral_map hZmeas.aemeasurable (by fun_prop)]
    simpa only [ρ, S, hS, e, P, B, O, G, Z, τ, θ, p, s, L, vG, wG, βk,
      Function.comp_apply, Prod.fst, Prod.snd] using hbase.2

/-- Joint product-integrability of a small-angle two-shift `D²` kernel over both Taylor
parameters.  The interval parameters are kept in the product measure so that all later Fubini
exchanges follow from one absolute-integrability witness. -/
private theorem integrable_smallAngle_twoShift_D2_kernel
    {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    {τ : Measure Z} [IsProbabilityMeasure τ]
    {κ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure κ]
    {A : Set (EuclideanSpace ℝ (Fin d))}
    (hAconv : Convexity.IsConvexSet ℝ A)
    {ε : ℝ} (hε : 0 < ε)
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (c : ℝ) (hc : 0 ≤ c)
    (x v w : Z → EuclideanSpace ℝ (Fin d))
    (hxm : Measurable x) (hvm : Measurable v) (hwm : Measurable w)
    (hx3 : MemLp x 3 τ) (hv3 : MemLp v 3 τ) (hw3 : MemLp w 3 τ) :
    let I := volume.restrict (Set.uIoc (0 : ℝ) 1)
    Integrable (fun q :
        ((((ℝ × ℝ) × Z) × EuclideanSpace ℝ (Fin d)) ×
          EuclideanSpace ℝ (Fin d)) ↦
      c * convexSetCutoffDirectionalPullback A ε q.1.2
          (x q.1.1.2) L q.2 *
        standardGaussianDensityD2
          (q.2 + q.1.1.1.2 •
            (v q.1.1.2 + q.1.1.1.1 • w q.1.1.2))
          (w q.1.1.2)
          (v q.1.1.2 + q.1.1.1.1 • w q.1.1.2))
      ((((I.prod I).prod τ).prod κ).prod volume) := by
  let E := EuclideanSpace ℝ (Fin d)
  let I := volume.restrict (Set.uIoc (0 : ℝ) 1)
  let σ := I.prod I
  let η := (σ.prod τ).prod κ
  letI : IsFiniteMeasure I := by
    dsimp only [I]
    simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      (inferInstance : IsFiniteMeasure
        (volume.restrict (Set.Ioc (0 : ℝ) 1)))
  have htI : MemLp (fun t : ℝ ↦ t) ∞ I := by
    apply memLp_top_of_bound measurable_id.aestronglyMeasurable 1
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    change |t| ≤ 1
    rw [abs_of_nonneg ht'.1.le]
    exact ht'.2
  have htσ : MemLp (fun q : ℝ × ℝ ↦ q.1) ∞ σ := by
    simpa only [σ] using htI.comp_fst I
  have htστ : MemLp (fun q : (ℝ × ℝ) × Z ↦ q.1.1) ∞ (σ.prod τ) := by
    simpa only [σ] using htσ.comp_fst τ
  have hxστ : MemLp (fun q : (ℝ × ℝ) × Z ↦ x q.2) 3 (σ.prod τ) := by
    simpa only [σ] using hx3.comp_snd σ
  have hvστ : MemLp (fun q : (ℝ × ℝ) × Z ↦ v q.2) 3 (σ.prod τ) := by
    simpa only [σ] using hv3.comp_snd σ
  have hwστ : MemLp (fun q : (ℝ × ℝ) × Z ↦ w q.2) 3 (σ.prod τ) := by
    simpa only [σ] using hw3.comp_snd σ
  have htwστ : MemLp
      (fun q : (ℝ × ℝ) × Z ↦ q.1.1 • w q.2) 3 (σ.prod τ) := by
    have hraw := hwστ.smul (r := 3) htστ
    apply hraw.congr_norm (by fun_prop)
    filter_upwards with q
    rfl
  have hcombστ : MemLp
      (fun q : (ℝ × ℝ) × Z ↦ v q.2 + q.1.1 • w q.2) 3 (σ.prod τ) :=
    hvστ.add htwστ
  have hxη : MemLp
      (fun q : ((ℝ × ℝ) × Z) × E ↦ x q.1.2) 3 η := by
    simpa only [η] using hxστ.comp_fst κ
  have hwη : MemLp
      (fun q : ((ℝ × ℝ) × Z) × E ↦ w q.1.2) 3 η := by
    simpa only [η] using hwστ.comp_fst κ
  have hcombη : MemLp
      (fun q : ((ℝ × ℝ) × Z) × E ↦
        v q.1.2 + q.1.1.1 • w q.1.2) 3 η := by
    simpa only [η] using hcombστ.comp_fst κ
  have hcubic := integrable_norm_mul_D2_major_of_memLp_three
    hxη hwη hcombη
  have hmajor : Integrable (fun q : ((ℝ × ℝ) × Z) × E ↦
      (c * (2 / ε) * ‖x q.1.2‖) *
        ((‖w q.1.2‖ ^ 2 +
            ‖v q.1.2 + q.1.1.1 • w q.1.2‖ ^ 2) / 2 +
          ‖w q.1.2‖ *
            ‖v q.1.2 + q.1.1.1 • w q.1.2‖)) η := by
    apply (hcubic.const_mul (c * (2 / ε))).congr
    filter_upwards with q
    ring
  have hcutMeas : Measurable (fun q :
      ((((ℝ × ℝ) × Z) × E) × E) ↦
      c * convexSetCutoffDirectionalPullback A ε q.1.2
        (x q.1.1.2) L q.2) := by
    dsimp only [η, convexSetCutoffDirectionalPullback]
    have hpos : Measurable (fun q :
        (((ℝ × ℝ) × Z) × E) × E ↦ q.1.2 + L q.2) := by
      fun_prop
    have hdir : Measurable (fun q :
        (((ℝ × ℝ) × Z) × E) × E ↦ x q.1.1.2) := by
      fun_prop
    exact measurable_const.mul
      (((contDiff_convexSetCutoff hAconv hε).continuous_fderiv_apply
        (by norm_num)).measurable.comp (hpos.prodMk hdir))
  have hcutBound (q : ((ℝ × ℝ) × Z) × E) (u : E) :
      |c * convexSetCutoffDirectionalPullback A ε q.2
          (x q.1.2) L u| ≤ c * (2 / ε) * ‖x q.1.2‖ := by
    rw [abs_mul, abs_of_nonneg hc]
    have hcut :
        |convexSetCutoffDirectionalPullback A ε q.2
            (x q.1.2) L u| ≤ (2 / ε) * ‖x q.1.2‖ := by
      rw [← Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm
        (fderiv ℝ (convexSetCutoff A ε) (q.2 + L u)) (x q.1.2)).trans
          (mul_le_mul_of_nonneg_right
            (norm_fderiv_convexSetCutoff_le hAconv hε _)
            (norm_nonneg _))
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcut hc
  apply integrable_prod_parametric_mul_standardGaussianDensityD2_add
    (μ := η)
    (φ := fun q : (((ℝ × ℝ) × Z) × E) × E ↦
      c * convexSetCutoffDirectionalPullback A ε q.1.2
        (x q.1.1.2) L q.2)
    (b := fun q : ((ℝ × ℝ) × Z) × E ↦
      q.1.1.2 • (v q.1.2 + q.1.1.1 • w q.1.2))
    (h := fun q : ((ℝ × ℝ) × Z) × E ↦ w q.1.2)
    (g := fun q : ((ℝ × ℝ) × Z) × E ↦
      v q.1.2 + q.1.1.1 • w q.1.2)
    (D := fun q : ((ℝ × ℝ) × Z) × E ↦
      c * (2 / ε) * ‖x q.1.2‖)
    hcutMeas (by fun_prop) (by fun_prop) (by fun_prop)
    (fun q ↦ by positivity) hcutBound hmajor

/-- Joint measurability of the signed two-shift `D²` kernel in the Taylor parameters, omitted
pair, affine base, and exposed Gaussian coordinate. -/
private theorem measurable_smallAngle_twoShift_D2_kernel
    {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (A : Set (EuclideanSpace ℝ (Fin d)))
    (hAconv : Convexity.IsConvexSet ℝ A) {ε : ℝ} (hε : 0 < ε)
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (c : ℝ)
    (x v w : Z → EuclideanSpace ℝ (Fin d))
    (hxm : Measurable x) (hvm : Measurable v) (hwm : Measurable w) :
    Measurable (fun q :
        (ℝ × ℝ) ×
          (Z × (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) ↦
      c * (convexSetCutoffDirectionalPullback A ε q.2.2.1 (x q.2.1) L q.2.2.2 *
        standardGaussianDensityD2
          (q.2.2.2 + q.1.2 • (v q.2.1 + q.1.1 • w q.2.1))
          (w q.2.1) (v q.2.1 + q.1.1 • w q.2.1))) := by
  have hcut : Measurable (fun q :
      (ℝ × ℝ) ×
        (Z × (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) ↦
      convexSetCutoffDirectionalPullback A ε q.2.2.1 (x q.2.1) L q.2.2.2) := by
    dsimp only [convexSetCutoffDirectionalPullback]
    exact ((contDiff_convexSetCutoff hAconv hε).continuous_fderiv_apply
      (by norm_num)).measurable.comp
        (((by fun_prop : Measurable (fun q :
            (ℝ × ℝ) ×
              (Z × (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) ↦
            q.2.2.1 + L q.2.2.2))).prodMk
          (hxm.comp (measurable_fst.comp measurable_snd)))
  have hD2 : Measurable (fun q :
      (ℝ × ℝ) ×
        (Z × (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) ↦
      standardGaussianDensityD2
        (q.2.2.2 + q.1.2 • (v q.2.1 + q.1.1 • w q.2.1))
        (w q.2.1) (v q.2.1 + q.1.1 • w q.2.1)) := by
    simp only [standardGaussianDensityD2, standardGaussianDensity]
    fun_prop
  exact measurable_const.mul (hcut.mul hD2)

/-- Absolute integrability transported from a fully left-associated fourfold product to the
corresponding fully right-associated product. -/
private theorem integrable_fourfold_reassociate
    {T Z A U : Type*} [MeasurableSpace T] [MeasurableSpace Z]
    [MeasurableSpace A] [MeasurableSpace U]
    {σ : Measure T} {τ : Measure Z} {κ : Measure A} {υ : Measure U}
    [SFinite σ] [SFinite τ] [SFinite κ] [SFinite υ]
    (F : T × (Z × (A × U)) → ℝ) (hFm : Measurable F)
    (hF : Integrable (fun q : (((T × Z) × A) × U) ↦
      F (q.1.1.1, (q.1.1.2, (q.1.2, q.2))))
      ((((σ.prod τ).prod κ).prod υ))) :
    Integrable F (σ.prod (τ.prod (κ.prod υ))) := by
  have hAssoc :=
    (measurePreserving_prodAssoc σ τ (κ.prod υ)).comp
      (measurePreserving_prodAssoc (σ.prod τ) κ υ)
  apply (hAssoc.integrable_comp hFm.aestronglyMeasurable).mp
  simpa only [Function.comp_def, MeasurableEquiv.prodAssoc,
    MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply] using hF

/-- Fubini normalization for the two Taylor parameters and the three probability coordinates.
The hypothesis is absolute integrability on the right-associated product; the conclusion is the
precise order exchange used in the small-angle remainder identity. -/
private theorem integral_twoInterval_triple_swap
    {Z A U : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace U]
    {τ : Measure Z} {κ : Measure A} {υ : Measure U}
    [SFinite τ] [SFinite κ] [SFinite υ]
    (R : ℝ → ℝ → Z → A → U → ℝ)
    (hR : let I := volume.restrict (Set.uIoc (0 : ℝ) 1)
      Integrable (fun q : (ℝ × ℝ) × (Z × (A × U)) ↦
        R q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2)
        ((I.prod I).prod (τ.prod (κ.prod υ)))) :
    (∫ a, (∫ u, (∫ z,
        (∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
          R t r z a u) ∂τ) ∂υ) ∂κ) =
      ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
        (∫ z, (∫ a, (∫ u, R t r z a u ∂υ) ∂κ) ∂τ) := by
  let I := volume.restrict (Set.uIoc (0 : ℝ) 1)
  let σ := I.prod I
  let baseMeasure := τ.prod (κ.prod υ)
  let F : (ℝ × ℝ) × (Z × (A × U)) → ℝ := fun q ↦
    R q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2
  have hF : Integrable F (σ.prod baseMeasure) := by
    simpa only [I, σ, baseMeasure, F] using hR
  let G : ℝ × ℝ → ℝ := fun tr ↦
    ∫ y, F (tr, y) ∂baseMeasure
  let G' : ℝ × ℝ → ℝ := fun tr ↦
    ∫ z, ∫ a, ∫ u, R tr.1 tr.2 z a u ∂υ ∂κ ∂τ
  have hG : Integrable G σ := by
    simpa only [G] using hF.integral_prod_left
  have hGG' : G =ᵐ[σ] G' := by
    have hsections := hF.prod_right_ae
    filter_upwards [hsections] with tr htr
    dsimp only [G, G', F, baseMeasure]
    rw [integral_prod (fun y : Z × (A × U) ↦
      R tr.1 tr.2 y.1 y.2.1 y.2.2) htr]
    apply integral_congr_ae
    filter_upwards [htr.prod_right_ae] with z hz
    rw [integral_prod
      (fun y : A × U ↦ R tr.1 tr.2 z y.1 y.2) hz]
  have hG' : Integrable G' σ := hG.congr hGG'
  have htarget :
      (∫ q, F q ∂(σ.prod baseMeasure)) =
        ∫ t, ∫ r, ∫ z, ∫ a, ∫ u,
          R t r z a u ∂υ ∂κ ∂τ ∂I ∂I := by
    calc
      (∫ q, F q ∂(σ.prod baseMeasure)) = ∫ tr, G tr ∂σ := by
        simpa only [G] using integral_prod F hF
      _ = ∫ tr, G' tr ∂σ := integral_congr_ae hGG'
      _ = ∫ t, ∫ r, G' (t, r) ∂I ∂I := by
        simpa only [σ] using integral_prod G' hG'
      _ = ∫ t, ∫ r, ∫ z, ∫ a, ∫ u,
          R t r z a u ∂υ ∂κ ∂τ ∂I ∂I := rfl
  let H : Z × (A × U) → ℝ := fun y ↦
    ∫ tr, F (tr, y) ∂σ
  let H' : Z × (A × U) → ℝ := fun y ↦
    ∫ t, ∫ r, R t r y.1 y.2.1 y.2.2 ∂I ∂I
  have hH : Integrable H baseMeasure := by
    simpa only [H] using hF.integral_prod_right
  have hHH' : H =ᵐ[baseMeasure] H' := by
    have hsections := hF.prod_left_ae
    filter_upwards [hsections] with y hy
    dsimp only [H, H', F, σ]
    exact integral_prod (fun tr : ℝ × ℝ ↦
      R tr.1 tr.2 y.1 y.2.1 y.2.2) hy
  have hH' : Integrable H' baseMeasure := hH.congr hHH'
  let J : A × U → ℝ := fun au ↦
    ∫ z, H' (z, au) ∂τ
  have hJ : Integrable J (κ.prod υ) := by
    simpa only [J] using hH'.integral_prod_right
  have hsource :
      (∫ a, ∫ u, ∫ z, ∫ t, ∫ r,
          R t r z a u ∂I ∂I ∂τ ∂υ ∂κ) =
        ∫ q, F q ∂(σ.prod baseMeasure) := by
    calc
      (∫ a, ∫ u, ∫ z, ∫ t, ∫ r,
          R t r z a u ∂I ∂I ∂τ ∂υ ∂κ) =
          ∫ au, J au ∂(κ.prod υ) := by
        rw [integral_prod J hJ]
      _ = ∫ y, H' y ∂baseMeasure := by
        simpa only [J, baseMeasure] using
          (integral_prod_symm H' hH').symm
      _ = ∫ y, H y ∂baseMeasure := by
        exact integral_congr_ae hHH'.symm
      _ = ∫ q, F q ∂(σ.prod baseMeasure) := by
        simpa only [H] using (integral_prod_symm F hF).symm
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simpa only [I, Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
    hsource.trans htarget

/-- Left-associated input form of `integral_twoInterval_triple_swap`. -/
private theorem integral_twoInterval_triple_swap_of_left
    {Z A U : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace U]
    {τ : Measure Z} {κ : Measure A} {υ : Measure U}
    [SFinite τ] [SFinite κ] [SFinite υ]
    (R : ℝ → ℝ → Z → A → U → ℝ)
    (hRm : Measurable (fun q : (ℝ × ℝ) × (Z × (A × U)) ↦
      R q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2))
    (hR : let I := volume.restrict (Set.uIoc (0 : ℝ) 1)
      Integrable (fun q : ((((ℝ × ℝ) × Z) × A) × U) ↦
        R q.1.1.1.1 q.1.1.1.2 q.1.1.2 q.1.2 q.2)
        ((((I.prod I).prod τ).prod κ).prod υ)) :
    (∫ a, (∫ u, (∫ z,
        (∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
          R t r z a u) ∂τ) ∂υ) ∂κ) =
      ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
        (∫ z, (∫ a, (∫ u, R t r z a u ∂υ) ∂κ) ∂τ) := by
  let I := volume.restrict (Set.uIoc (0 : ℝ) 1)
  let F : (ℝ × ℝ) × (Z × (A × U)) → ℝ := fun q ↦
    R q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2
  have hright : Integrable F
      ((I.prod I).prod (τ.prod (κ.prod υ))) := by
    apply integrable_fourfold_reassociate F hRm
    simpa only [F, I] using hR
  exact integral_twoInterval_triple_swap R (by
    simpa only [F, I] using hright)

/-- Integrating an absolutely integrable five-coordinate kernel over its two interval
coordinates leaves an absolutely integrable function of the remaining three coordinates. -/
private theorem integrable_twoInterval_integral_of_integrable_left
    {Z A U : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace U]
    {τ : Measure Z} {κ : Measure A} {υ : Measure U}
    [SFinite τ] [SFinite κ] [SFinite υ]
    (R : ℝ → ℝ → Z → A → U → ℝ)
    (hRm : Measurable (fun q : (ℝ × ℝ) × (Z × (A × U)) ↦
      R q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2))
    (hR : let I := volume.restrict (Set.uIoc (0 : ℝ) 1)
      Integrable (fun q : ((((ℝ × ℝ) × Z) × A) × U) ↦
        R q.1.1.1.1 q.1.1.1.2 q.1.1.2 q.1.2 q.2)
        ((((I.prod I).prod τ).prod κ).prod υ)) :
    Integrable (fun q : Z × (A × U) ↦
      ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
        R t r q.1 q.2.1 q.2.2)
      (τ.prod (κ.prod υ)) := by
  let I := volume.restrict (Set.uIoc (0 : ℝ) 1)
  let F : (ℝ × ℝ) × (Z × (A × U)) → ℝ := fun q ↦
    R q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2
  have hright : Integrable F
      ((I.prod I).prod (τ.prod (κ.prod υ))) := by
    apply integrable_fourfold_reassociate F hRm
    simpa only [F, I] using hR
  let H : Z × (A × U) → ℝ := fun y ↦
    ∫ tr, F (tr, y) ∂(I.prod I)
  have hH : Integrable H (τ.prod (κ.prod υ)) := by
    simpa only [H] using hright.integral_prod_right
  apply hH.congr
  have hsections := hright.prod_left_ae
  filter_upwards [hsections] with y hy
  dsimp only [H, F]
  rw [integral_prod (fun tr : ℝ × ℝ ↦
    R tr.1 tr.2 y.1 y.2.1 y.2.2) hy]
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [I, Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- Joint product-integrability of the two exact small-angle remainder kernels over both Taylor
parameters, the omitted pair, the affine base, and the exposed Gaussian coordinate. -/
private theorem bentkus_smallAngle_D2_remainderKernels_integrable
    {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (α : ℝ) (hsin : 0 < Real.sin α)
    (A : Set (EuclideanSpace ℝ (Fin d)))
    (hAconv : Convexity.IsConvexSet ℝ A) {ε : ℝ} (hε : 0 < ε)
    :
    let ρ := bentkusReplacementMeasure μ X
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
    let U := bentkusLeaveOneOut X k
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let Z := fun ω ↦ (O ω, G ω)
    let τ := ρ.map Z
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let ν := μ.map (fun ω ↦ e (U ω))
    let θ := (Real.sqrt 2)⁻¹
    let p := Real.cos α
    let s := Real.sin α
    let q := θ * s
    let T := ((γ.map (fun y ↦ q • y)).prod ν).map
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        p • z.2 + z.1)
    let L := q • P
    let vO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((1 / θ) • B z.2)
    let wO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((p / (θ * s)) • B z.1)
    let vG := wO
    let wG := vO
    let I := volume.restrict (Set.uIoc (0 : ℝ) 1)
    Integrable (fun y :
        ((((ℝ × ℝ) ×
          (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) ×
          EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d)) ↦
      convexSetCutoffDirectionalPullback A ε y.1.2 y.1.1.2.1 L y.2 *
        standardGaussianDensityD2
          (y.2 + y.1.1.1.2 •
            (vO y.1.1.2 + y.1.1.1.1 • wO y.1.1.2))
          (wO y.1.1.2)
          (vO y.1.1.2 + y.1.1.1.1 • wO y.1.1.2))
      ((((I.prod I).prod τ).prod (T.map P)).prod volume) ∧
    Integrable (fun y :
        ((((ℝ × ℝ) ×
          (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) ×
          EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d)) ↦
      convexSetCutoffDirectionalPullback A ε y.1.2 y.1.1.2.2 L y.2 *
        standardGaussianDensityD2
          (y.2 + y.1.1.1.2 •
            (vG y.1.1.2 + y.1.1.1.1 • wG y.1.1.2))
          (wG y.1.1.2)
          (vG y.1.1.2 + y.1.1.1.1 • wG y.1.1.2))
      ((((I.prod I).prod τ).prod (T.map P)).prod volume) := by
  let E := EuclideanSpace ℝ (Fin d)
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let P := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  let UO := bentkusLeaveOneOut
    (fun i ↦ replacementOriginal (d := d) i) k
  let VG := bentkusLeaveOneOut
    (fun i ↦ replacementGaussian (d := d) i) k
  let U := bentkusLeaveOneOut X k
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let Z := fun ω ↦ (O ω, G ω)
  let τ := ρ.map Z
  let γ := stdGaussian E
  let ν := μ.map (fun ω ↦ e (U ω))
  let θ := (Real.sqrt 2)⁻¹
  let p := Real.cos α
  let s := Real.sin α
  let q := θ * s
  let T := ((γ.map (fun y ↦ q • y)).prod ν).map
    (fun z : E × E ↦ p • z.2 + z.1)
  let L := q • P
  let vO := fun z : E × E ↦ -((1 / θ) • B z.2)
  let wO := fun z : E × E ↦ -((p / (θ * s)) • B z.1)
  let vG := wO
  let wG := vO
  let base := T.map P
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
    exact Measure.isProbabilityMeasure_map
      (e.continuous.measurable.comp hUmeas).aemeasurable
  letI : IsProbabilityMeasure (γ.map (fun y ↦ q • y)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure T := by
    dsimp only [T]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure base := by
    dsimp only [base]
    exact Measure.isProbabilityMeasure_map P.continuous.measurable.aemeasurable
  have hZmeas : Measurable Z := by
    dsimp only [Z, O, G]
    exact ((measurable_pi_apply k).comp measurable_fst).prodMk
      ((measurable_pi_apply k).comp measurable_snd)
  letI : IsProbabilityMeasure τ := by
    dsimp only [τ]
    exact Measure.isProbabilityMeasure_map hZmeas.aemeasurable
  have hO3ρ : MemLp O 3 ρ := memLp_replacementOriginal hXm hX3 k
  have hG3ρ : MemLp G 3 ρ := memLp_three_replacementGaussian hXm k
  have hO3 : MemLp (fun z : E × E ↦ z.1) 3 τ := by
    apply (memLp_map_measure_iff measurable_fst.aestronglyMeasurable
      hZmeas.aemeasurable).2
    apply hO3ρ.ae_eq
    filter_upwards with ω
    rfl
  have hG3 : MemLp (fun z : E × E ↦ z.2) 3 τ := by
    apply (memLp_map_measure_iff measurable_snd.aestronglyMeasurable
      hZmeas.aemeasurable).2
    apply hG3ρ.ae_eq
    filter_upwards with ω
    rfl
  have hvO3 : MemLp vO 3 τ := by
    simpa only [vO, _root_.smul_apply, neg_smul] using
      hG3.continuousLinearMap_comp ((-(1 / θ)) • B)
  have hwO3 : MemLp wO 3 τ := by
    simpa only [wO, _root_.smul_apply, neg_smul] using
      hO3.continuousLinearMap_comp ((-(p / (θ * s))) • B)
  have hvOm : Measurable vO := by
    dsimp only [vO]
    fun_prop
  have hwOm : Measurable wO := by
    dsimp only [wO]
    fun_prop
  have hkernelO := integrable_smallAngle_twoShift_D2_kernel
    (τ := τ) (κ := base) hAconv hε L 1 (by norm_num)
      (fun z : E × E ↦ z.1) vO wO
      measurable_fst hvOm hwOm hO3 hvO3 hwO3
  have hkernelG := integrable_smallAngle_twoShift_D2_kernel
    (τ := τ) (κ := base) hAconv hε L 1 (by norm_num)
      (fun z : E × E ↦ z.2) wO vO
      measurable_snd hwOm hvOm hG3 hwO3 hvO3
  constructor
  · simpa only [base, one_mul] using hkernelO
  · simpa only [base, vG, wG, one_mul] using hkernelG

/-- The signed original and Gaussian small-angle remainders may both be put in the
`t,r,z,a,u` order used by the absolute majorant.  The original branch carries `-sin α`; the
Gaussian branch carries `cos α`, with the two shift orders reversed. -/
private theorem bentkus_smallAngle_signed_D2_remainder_integrals_swap
    {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (α : ℝ) (hsin : 0 < Real.sin α)
    (A : Set (EuclideanSpace ℝ (Fin d)))
    (hAconv : Convexity.IsConvexSet ℝ A) {ε : ℝ} (hε : 0 < ε) :
    let ρ := bentkusReplacementMeasure μ X
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
    let U := bentkusLeaveOneOut X k
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let Z := fun ω ↦ (O ω, G ω)
    let τ := ρ.map Z
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let ν := μ.map (fun ω ↦ e (U ω))
    let θ := (Real.sqrt 2)⁻¹
    let p := Real.cos α
    let s := Real.sin α
    let q := θ * s
    let T := ((γ.map (fun y ↦ q • y)).prod ν).map
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        p • z.2 + z.1)
    let L := q • P
    let vO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((1 / θ) • B z.2)
    let wO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((p / (θ * s)) • B z.1)
    let vG := wO
    let wG := vO
    let RO := fun (t r : ℝ)
        (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))
        (a u : EuclideanSpace ℝ (Fin d)) ↦
      (-s) * (convexSetCutoffDirectionalPullback A ε a z.1 L u *
        standardGaussianDensityD2
          (u + r • (vO z + t • wO z))
          (wO z) (vO z + t • wO z))
    let RG := fun (t r : ℝ)
        (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))
        (a u : EuclideanSpace ℝ (Fin d)) ↦
      p * (convexSetCutoffDirectionalPullback A ε a z.2 L u *
        standardGaussianDensityD2
          (u + r • (vG z + t • wG z))
          (wG z) (vG z + t • wG z))
    Integrable (fun q :
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
          (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ↦
      ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
        RO t r q.1 q.2.1 q.2.2)
      (τ.prod ((T.map P).prod volume)) ∧
    Integrable (fun q :
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
          (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ↦
      ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
        RG t r q.1 q.2.1 q.2.2)
      (τ.prod ((T.map P).prod volume)) ∧
    (((∫ a, (∫ u, (∫ z,
        (∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
          RO t r z a u) ∂τ) ∂volume) ∂(T.map P)) =
      ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
        (∫ z, (∫ a, (∫ u, RO t r z a u ∂volume)
          ∂(T.map P)) ∂τ))) ∧
    ((∫ a, (∫ u, (∫ z,
        (∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
          RG t r z a u) ∂τ) ∂volume) ∂(T.map P)) =
      ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
        (∫ z, (∫ a, (∫ u, RG t r z a u ∂volume)
          ∂(T.map P)) ∂τ)) ∧
    (((∫ a, (∫ u, (∫ z,
          (∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
            RO t r z a u) ∂τ) ∂volume) ∂(T.map P)) +
        ∫ a, (∫ u, (∫ z,
          (∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
            RG t r z a u) ∂τ) ∂volume) ∂(T.map P)) =
      ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, ∫ z,
        ((∫ a, ∫ u, RO t r z a u ∂volume ∂(T.map P)) +
          ∫ a, ∫ u, RG t r z a u ∂volume ∂(T.map P)) ∂τ) := by
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let P := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  let U := bentkusLeaveOneOut X k
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let Z := fun ω ↦ (O ω, G ω)
  let τ := ρ.map Z
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let ν := μ.map (fun ω ↦ e (U ω))
  let θ := (Real.sqrt 2)⁻¹
  let p := Real.cos α
  let s := Real.sin α
  let q := θ * s
  let T := ((γ.map (fun y ↦ q • y)).prod ν).map
    (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      p • z.2 + z.1)
  let L := q • P
  let vO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -((1 / θ) • B z.2)
  let wO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -((p / (θ * s)) • B z.1)
  let vG := wO
  let wG := vO
  let RO := fun (t r : ℝ)
      (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))
      (a u : EuclideanSpace ℝ (Fin d)) ↦
    (-s) * (convexSetCutoffDirectionalPullback A ε a z.1 L u *
      standardGaussianDensityD2
        (u + r • (vO z + t • wO z))
        (wO z) (vO z + t • wO z))
  let RG := fun (t r : ℝ)
      (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))
      (a u : EuclideanSpace ℝ (Fin d)) ↦
    p * (convexSetCutoffDirectionalPullback A ε a z.2 L u *
      standardGaussianDensityD2
        (u + r • (vG z + t • wG z))
        (wG z) (vG z + t • wG z))
  let I := volume.restrict (Set.uIoc (0 : ℝ) 1)
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
    exact Measure.isProbabilityMeasure_map
      (e.continuous.measurable.comp hUmeas).aemeasurable
  letI : IsProbabilityMeasure (γ.map (fun y ↦ q • y)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure T := by
    dsimp only [T]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (T.map P) :=
    Measure.isProbabilityMeasure_map P.continuous.measurable.aemeasurable
  have hZmeas : Measurable Z := by
    dsimp only [Z, O, G]
    exact ((measurable_pi_apply k).comp measurable_fst).prodMk
      ((measurable_pi_apply k).comp measurable_snd)
  letI : IsProbabilityMeasure τ := by
    dsimp only [τ]
    exact Measure.isProbabilityMeasure_map hZmeas.aemeasurable
  have hraw := bentkus_smallAngle_D2_remainderKernels_integrable
    hXm hX3 h_indep hX0 hidentity k hk α hsin A hAconv hε
  have hraw' :
      Integrable (fun y :
          ((((ℝ × ℝ) ×
            (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) ×
            EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d)) ↦
        convexSetCutoffDirectionalPullback A ε y.1.2 y.1.1.2.1 L y.2 *
          standardGaussianDensityD2
            (y.2 + y.1.1.1.2 •
              (vO y.1.1.2 + y.1.1.1.1 • wO y.1.1.2))
            (wO y.1.1.2)
            (vO y.1.1.2 + y.1.1.1.1 • wO y.1.1.2))
        ((((I.prod I).prod τ).prod (T.map P)).prod volume) ∧
      Integrable (fun y :
          ((((ℝ × ℝ) ×
            (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) ×
            EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d)) ↦
        convexSetCutoffDirectionalPullback A ε y.1.2 y.1.1.2.2 L y.2 *
          standardGaussianDensityD2
            (y.2 + y.1.1.1.2 •
              (vG y.1.1.2 + y.1.1.1.1 • wG y.1.1.2))
            (wG y.1.1.2)
            (vG y.1.1.2 + y.1.1.1.1 • wG y.1.1.2))
        ((((I.prod I).prod τ).prod (T.map P)).prod volume) := by
    simpa only [ρ, S, hS, e, P, B, U, O, G, Z, τ, γ, ν, θ, p, s, q,
      T, L, vO, wO, vG, wG, I] using hraw
  have hRO : Integrable (fun y :
      ((((ℝ × ℝ) ×
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) ×
        EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d)) ↦
      RO y.1.1.1.1 y.1.1.1.2 y.1.1.2 y.1.2 y.2)
      ((((I.prod I).prod τ).prod (T.map P)).prod volume) := by
    simpa only [RO] using hraw'.1.const_mul (-s)
  have hRG : Integrable (fun y :
      ((((ℝ × ℝ) ×
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) ×
        EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d)) ↦
      RG y.1.1.1.1 y.1.1.1.2 y.1.1.2 y.1.2 y.2)
      ((((I.prod I).prod τ).prod (T.map P)).prod volume) := by
    simpa only [RG] using hraw'.2.const_mul p
  have hROm : Measurable (fun q :
      (ℝ × ℝ) ×
        ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
          (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) ↦
      RO q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2) := by
    simpa only [RO] using
      measurable_smallAngle_twoShift_D2_kernel A hAconv hε L (-s)
        (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦ z.1)
        vO wO measurable_fst (by fun_prop) (by fun_prop)
  have hRGm : Measurable (fun q :
      (ℝ × ℝ) ×
        ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
          (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) ↦
      RG q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2) := by
    simpa only [RG] using
      measurable_smallAngle_twoShift_D2_kernel A hAconv hε L p
        (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦ z.2)
        vG wG measurable_snd (by fun_prop) (by fun_prop)
  have hRObar : Integrable (fun q :
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ↦
    ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
      RO t r q.1 q.2.1 q.2.2)
      (τ.prod ((T.map P).prod volume)) :=
    integrable_twoInterval_integral_of_integrable_left RO hROm
      (by simpa only [I] using hRO)
  have hRGbar : Integrable (fun q :
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ↦
    ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
      RG t r q.1 q.2.1 q.2.2)
      (τ.prod ((T.map P).prod volume)) :=
    integrable_twoInterval_integral_of_integrable_left RG hRGm
      (by simpa only [I] using hRG)
  have hswapO := integral_twoInterval_triple_swap_of_left RO hROm
    (by simpa only [I] using hRO)
  have hswapG := integral_twoInterval_triple_swap_of_left RG hRGm
    (by simpa only [I] using hRG)
  let FO : (ℝ × ℝ) ×
      ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) → ℝ := fun q ↦
    RO q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2
  let FG : (ℝ × ℝ) ×
      ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) → ℝ := fun q ↦
    RG q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2
  have hFOright : Integrable FO
      ((I.prod I).prod (τ.prod ((T.map P).prod volume))) := by
    apply integrable_fourfold_reassociate FO hROm
    simpa only [FO] using hRO
  have hFGright : Integrable FG
      ((I.prod I).prod (τ.prod ((T.map P).prod volume))) := by
    apply integrable_fourfold_reassociate FG hRGm
    simpa only [FG] using hRG
  let GO : ℝ × ℝ → ℝ := fun tr ↦
    ∫ z, ∫ a, ∫ u, RO tr.1 tr.2 z a u ∂volume ∂(T.map P) ∂τ
  let GG : ℝ × ℝ → ℝ := fun tr ↦
    ∫ z, ∫ a, ∫ u, RG tr.1 tr.2 z a u ∂volume ∂(T.map P) ∂τ
  have hFOGO : (fun tr ↦
      ∫ y, FO (tr, y) ∂(τ.prod ((T.map P).prod volume))) =ᵐ[I.prod I] GO := by
    have hsections := hFOright.prod_right_ae
    filter_upwards [hsections] with tr htr
    dsimp only [FO, GO]
    rw [integral_prod (fun y :
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ↦
      RO tr.1 tr.2 y.1 y.2.1 y.2.2) htr]
    apply integral_congr_ae
    filter_upwards [htr.prod_right_ae] with z hz
    rw [integral_prod (fun y :
      EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      RO tr.1 tr.2 z y.1 y.2) hz]
  have hFGGG : (fun tr ↦
      ∫ y, FG (tr, y) ∂(τ.prod ((T.map P).prod volume))) =ᵐ[I.prod I] GG := by
    have hsections := hFGright.prod_right_ae
    filter_upwards [hsections] with tr htr
    dsimp only [FG, GG]
    rw [integral_prod (fun y :
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ↦
      RG tr.1 tr.2 y.1 y.2.1 y.2.2) htr]
    apply integral_congr_ae
    filter_upwards [htr.prod_right_ae] with z hz
    rw [integral_prod (fun y :
      EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      RG tr.1 tr.2 z y.1 y.2) hz]
  have hGO : Integrable GO (I.prod I) :=
    hFOright.integral_prod_left.congr hFOGO
  have hGG : Integrable GG (I.prod I) :=
    hFGright.integral_prod_left.congr hFGGG
  have htargetAdd :
      (∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, GO (t, r)) +
        (∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, GG (t, r)) =
      ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, GO (t, r) + GG (t, r) := by
    simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp only [zero_le_one, if_true, one_smul]
    change
      (∫ t, ∫ r, GO (t, r) ∂I ∂I) +
          (∫ t, ∫ r, GG (t, r) ∂I ∂I) =
        ∫ t, ∫ r, GO (t, r) + GG (t, r) ∂I ∂I
    rw [← integral_prod GO hGO, ← integral_prod GG hGG,
      ← integral_prod (fun tr ↦ GO tr + GG tr) (hGO.add hGG)]
    exact (integral_add hGO hGG).symm
  let GOz : ℝ × ℝ →
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) → ℝ := fun tr z ↦
    ∫ a, ∫ u, RO tr.1 tr.2 z a u ∂volume ∂(T.map P)
  let GGz : ℝ × ℝ →
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) → ℝ := fun tr z ↦
    ∫ a, ∫ u, RG tr.1 tr.2 z a u ∂volume ∂(T.map P)
  have hGOz : ∀ᵐ tr ∂(I.prod I), Integrable (GOz tr) τ := by
    filter_upwards [hFOright.prod_right_ae] with tr htr
    apply htr.integral_prod_left.congr
    filter_upwards [htr.prod_right_ae] with z hz
    dsimp only [FO, GOz]
    exact integral_prod
      (fun au : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        RO tr.1 tr.2 z au.1 au.2) hz
  have hGGz : ∀ᵐ tr ∂(I.prod I), Integrable (GGz tr) τ := by
    filter_upwards [hFGright.prod_right_ae] with tr htr
    apply htr.integral_prod_left.congr
    filter_upwards [htr.prod_right_ae] with z hz
    dsimp only [FG, GGz]
    exact integral_prod
      (fun au : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        RG tr.1 tr.2 z au.1 au.2) hz
  have hGOeq : GO =ᵐ[I.prod I] fun tr ↦ ∫ z, GOz tr z ∂τ := by
    filter_upwards with tr
    rfl
  have hGGeq : GG =ᵐ[I.prod I] fun tr ↦ ∫ z, GGz tr z ∂τ := by
    filter_upwards with tr
    rfl
  have hcombinedAE :
      (fun tr ↦ GO tr + GG tr) =ᵐ[I.prod I]
        fun tr ↦ ∫ z, GOz tr z + GGz tr z ∂τ := by
    filter_upwards [hGOeq, hGGeq, hGOz, hGGz] with tr hOeq hGeq hOint hGint
    rw [hOeq, hGeq, integral_add hOint hGint]
  have hcombinedInt :
      Integrable (fun tr ↦ ∫ z, GOz tr z + GGz tr z ∂τ) (I.prod I) :=
    (hGO.add hGG).congr hcombinedAE
  have htargetCombined :
      (∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, GO (t, r) + GG (t, r)) =
        ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
          ∫ z, GOz (t, r) z + GGz (t, r) z ∂τ := by
    simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp only [zero_le_one, if_true, one_smul]
    change
      (∫ t, ∫ r, GO (t, r) + GG (t, r) ∂I ∂I) =
        ∫ t, ∫ r, (∫ z, GOz (t, r) z + GGz (t, r) z ∂τ) ∂I ∂I
    rw [← integral_prod (fun tr ↦ GO tr + GG tr) (hGO.add hGG),
      ← integral_prod
        (fun tr ↦ ∫ z, GOz tr z + GGz tr z ∂τ) hcombinedInt]
    exact integral_congr_ae hcombinedAE
  have hswapSum :
      (((∫ a, (∫ u, (∫ z,
          (∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
            RO t r z a u) ∂τ) ∂volume) ∂(T.map P)) +
        ∫ a, (∫ u, (∫ z,
          (∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
            RG t r z a u) ∂τ) ∂volume) ∂(T.map P)) =
      ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, ∫ z,
        ((∫ a, ∫ u, RO t r z a u ∂volume ∂(T.map P)) +
          ∫ a, ∫ u, RG t r z a u ∂volume ∂(T.map P)) ∂τ) := by
    calc
      _ = (∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, GO (t, r)) +
          ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, GG (t, r) := by
        rw [hswapO, hswapG]
      _ = ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
          GO (t, r) + GG (t, r) := htargetAdd
      _ = _ := by
        rw [htargetCombined]
  exact ⟨hRObar, hRGbar, hswapO, hswapG, hswapSum⟩

/-- The two normalized small-angle `D²` majorants at fixed Taylor parameters. -/
private theorem bentkus_smallAngle_fixedParameters_D2_le
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
    (α : ℝ) (hsin : 0 < Real.sin α) (hcos : 0 < Real.cos α)
    (A : Set (EuclideanSpace ℝ (Fin d))) (hAclosed : IsClosed A)
    (hAconv : Convexity.IsConvexSet ℝ A) {ε : ℝ} (hε : 0 < ε)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (r : ℝ) :
    let ρ := bentkusReplacementMeasure μ X
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
    let U := bentkusLeaveOneOut X k
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let Z := fun ω ↦ (O ω, G ω)
    let τ := ρ.map Z
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let ν := μ.map (fun ω ↦ e (U ω))
    let θ := (Real.sqrt 2)⁻¹
    let p := Real.cos α
    let s := Real.sin α
    let q := θ * s
    let T := ((γ.map (fun y ↦ q • y)).prod ν).map
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        p • z.2 + z.1)
    let L := q • P
    let vO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((1 / θ) • B z.2)
    let wO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((p / (θ * s)) • B z.1)
    let vG := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((p / (θ * s)) • B z.1)
    let wG := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((1 / θ) • B z.2)
    let β := ∑ i : Fin n, ∫ ω, ‖X (k.succAbove i) ω‖ ^ 3 ∂μ
    let βk := ∫ ω, ‖O ω‖ ^ 3 ∂ρ
    let J := 32 * (d : ℝ) ^ (1 / 4 : ℝ) * (C * β + ε)
    (∫ z, s * ∫ a,
      |∫ u, convexSetCutoffDirectionalPullback A ε a z.1 L u *
        standardGaussianDensityD2
          (u + r • (vO z + t • wO z)) (wO z) (vO z + t • wO z)
        ∂volume| ∂(T.map P) ∂τ) ≤
        (8 / ε ^ 2) * J * (16 * p * βk) ∧
      (∫ z, p * ∫ a,
        |∫ u, convexSetCutoffDirectionalPullback A ε a z.2 L u *
          standardGaussianDensityD2
            (u + r • (vG z + t • wG z)) (wG z) (vG z + t • wG z)
          ∂volume| ∂(T.map P) ∂τ) ≤
        (8 / ε ^ 2) * J * (224 * p * βk) := by
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let P := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  let U := bentkusLeaveOneOut X k
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let Z := fun ω ↦ (O ω, G ω)
  let τ := ρ.map Z
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let ν := μ.map (fun ω ↦ e (U ω))
  let θ := (Real.sqrt 2)⁻¹
  let p := Real.cos α
  let s := Real.sin α
  let q := θ * s
  let T := ((γ.map (fun y ↦ q • y)).prod ν).map
    (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      p • z.2 + z.1)
  let L := q • P
  let vO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -((1 / θ) • B z.2)
  let wO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -((p / (θ * s)) • B z.1)
  let vG := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -((p / (θ * s)) • B z.1)
  let wG := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -((1 / θ) • B z.2)
  let β := ∑ i : Fin n, ∫ ω, ‖X (k.succAbove i) ω‖ ^ 3 ∂μ
  let βk := ∫ ω, ‖O ω‖ ^ 3 ∂ρ
  let J := 32 * (d : ℝ) ^ (1 / 4 : ℝ) * (C * β + ε)
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
    exact Measure.isProbabilityMeasure_map
      (e.continuous.measurable.comp hUmeas).aemeasurable
  letI : IsProbabilityMeasure (γ.map (fun y ↦ q • y)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure T := by
    dsimp only [T]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (T.map P) :=
    Measure.isProbabilityMeasure_map P.continuous.measurable.aemeasurable
  have hbaseMeasure : T.map e.symm = T.map P := by
    congr 1
  have hZmeas : Measurable Z := by
    dsimp only [Z, O, G, replacementOriginal, replacementGaussian]
    fun_prop
  letI : IsProbabilityMeasure τ := by
    dsimp only [τ]
    exact Measure.isProbabilityMeasure_map hZmeas.aemeasurable
  have hs0 : 0 ≤ s := hsin.le
  have hp0 : 0 ≤ p := hcos.le
  have hβ : 0 ≤ β := by
    dsimp only [β]
    exact Finset.sum_nonneg fun i _ ↦
      integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg _) 3
  have hJ : 0 ≤ J := by
    dsimp only [J]
    positivity
  have hfactor := bentkus_smallAngle_pairFactors_integrable
    hXm hX3 h_indep hX0 hidentity k hk α hsin hp0 t ht ht1
  have hmom := bentkus_smallAngle_pairFactors_le
    hXm hX3 h_indep hX0 hidentity k hk α hsin hp0 t ht ht1
  have hboundO (z) :
      (∫ a, |∫ u, convexSetCutoffDirectionalPullback A ε a z.1 L u *
          standardGaussianDensityD2
            (u + r • (vO z + t • wO z)) (wO z) (vO z + t • wO z)
          ∂volume| ∂(T.map P)) ≤
        (((8 / ε ^ 2) * ‖L‖ * ‖z.1‖) * ‖vO z + t • wO z‖) *
          (J * ‖wO z‖) := by
    have hraw :=
      bentkus_splitGaussianBase_average_twoShift_D2_normalized_le_of_induction
        hC hIH hd hXm hX3 h_indep hX0 hidentity k hk α hcos
          A hAclosed hAconv hε z.1 L (vO z) (wO z) t r
    rw [← hbaseMeasure]
    simpa only [S, hS, e, P, B, U, O, G, Z, τ, γ, ν, θ, p, s, q, T, L,
      vO, wO, β, βk, J] using hraw
  have hboundG (z) :
      (∫ a, |∫ u, convexSetCutoffDirectionalPullback A ε a z.2 L u *
          standardGaussianDensityD2
            (u + r • (vG z + t • wG z)) (wG z) (vG z + t • wG z)
          ∂volume| ∂(T.map P)) ≤
        (((8 / ε ^ 2) * ‖L‖ * ‖z.2‖) * ‖vG z + t • wG z‖) *
          (J * ‖wG z‖) := by
    have hraw :=
      bentkus_splitGaussianBase_average_twoShift_D2_normalized_le_of_induction
        hC hIH hd hXm hX3 h_indep hX0 hidentity k hk α hcos
          A hAclosed hAconv hε z.2 L (vG z) (wG z) t r
    rw [← hbaseMeasure]
    simpa only [S, hS, e, P, B, U, O, G, Z, τ, γ, ν, θ, p, s, q, T, L,
      vG, wG, β, βk, J] using hraw
  have havgO := integral_pair_average_twoShift_D2_le
    (τ := τ) (ν := T.map P) hAconv hε hs0 hJ L
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦ z.1)
      vO wO (by fun_prop) (by fun_prop) (by fun_prop) hfactor.1 hboundO
  have havgG := integral_pair_average_twoShift_D2_le
    (τ := τ) (ν := T.map P) hAconv hε hp0 hJ L
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦ z.2)
      vG wG (by fun_prop) (by fun_prop) (by fun_prop) hfactor.2 hboundG
  have hK : 0 ≤ (8 / ε ^ 2) * J := by positivity
  constructor
  · calc
      (∫ z, s * ∫ a,
        |∫ u, convexSetCutoffDirectionalPullback A ε a z.1 L u *
          standardGaussianDensityD2
            (u + r • (vO z + t • wO z)) (wO z) (vO z + t • wO z)
          ∂volume| ∂(T.map P) ∂τ) ≤
          (8 / ε ^ 2) * J *
            ∫ z, s * ‖L‖ * ‖z.1‖ * ‖vO z + t • wO z‖ * ‖wO z‖ ∂τ :=
        havgO
      _ ≤ (8 / ε ^ 2) * J * (16 * p * βk) :=
        mul_le_mul_of_nonneg_left hmom.1 hK
  · calc
      (∫ z, p * ∫ a,
        |∫ u, convexSetCutoffDirectionalPullback A ε a z.2 L u *
          standardGaussianDensityD2
            (u + r • (vG z + t • wG z)) (wG z) (vG z + t • wG z)
          ∂volume| ∂(T.map P) ∂τ) ≤
          (8 / ε ^ 2) * J *
            ∫ z, p * ‖L‖ * ‖z.2‖ * ‖vG z + t • wG z‖ * ‖wG z‖ ∂τ :=
        havgG
      _ ≤ (8 / ε ^ 2) * J * (224 * p * βk) :=
        mul_le_mul_of_nonneg_left hmom.2 hK

/-- The integrated absolute `D²` majorant in the small-angle argument.  The constant is
`8 * (16 + 224) * 32 = 61440`. -/
private theorem bentkus_smallAngle_integrated_D2_majorant_le
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
    (α : ℝ) (hsin : 0 < Real.sin α) (hcos : 0 < Real.cos α)
    (A : Set (EuclideanSpace ℝ (Fin d))) (hAclosed : IsClosed A)
    (hAconv : Convexity.IsConvexSet ℝ A) {ε : ℝ} (hε : 0 < ε) :
    let ρ := bentkusReplacementMeasure μ X
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
    let U := bentkusLeaveOneOut X k
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let Z := fun ω ↦ (O ω, G ω)
    let τ := ρ.map Z
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let ν := μ.map (fun ω ↦ e (U ω))
    let θ := (Real.sqrt 2)⁻¹
    let p := Real.cos α
    let s := Real.sin α
    let q := θ * s
    let T := ((γ.map (fun y ↦ q • y)).prod ν).map
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        p • z.2 + z.1)
    let L := q • P
    let vO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((1 / θ) • B z.2)
    let wO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((p / (θ * s)) • B z.1)
    let vG := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((p / (θ * s)) • B z.1)
    let wG := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((1 / θ) • B z.2)
    let β := ∑ i : Fin n, ∫ ω, ‖X (k.succAbove i) ω‖ ^ 3 ∂μ
    let βk := ∫ ω, ‖O ω‖ ^ 3 ∂ρ
    let MO := fun (t r : ℝ) ↦ ∫ z, s * ∫ a,
      |∫ u, convexSetCutoffDirectionalPullback A ε a z.1 L u *
        standardGaussianDensityD2
          (u + r • (vO z + t • wO z)) (wO z) (vO z + t • wO z)
        ∂volume| ∂(T.map P) ∂τ
    let MG := fun (t r : ℝ) ↦ ∫ z, p * ∫ a,
      |∫ u, convexSetCutoffDirectionalPullback A ε a z.2 L u *
        standardGaussianDensityD2
          (u + r • (vG z + t • wG z)) (wG z) (vG z + t • wG z)
        ∂volume| ∂(T.map P) ∂τ
    (∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, MO t r + MG t r) ≤
      (61440 / ε ^ 2) * (d : ℝ) ^ (1 / 4 : ℝ) *
        (C * β + ε) * p * βk := by
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let P := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  let U := bentkusLeaveOneOut X k
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let Z := fun ω ↦ (O ω, G ω)
  let τ := ρ.map Z
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let ν := μ.map (fun ω ↦ e (U ω))
  let θ := (Real.sqrt 2)⁻¹
  let p := Real.cos α
  let s := Real.sin α
  let q := θ * s
  let T := ((γ.map (fun y ↦ q • y)).prod ν).map
    (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      p • z.2 + z.1)
  let L := q • P
  let vO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -((1 / θ) • B z.2)
  let wO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -((p / (θ * s)) • B z.1)
  let vG := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -((p / (θ * s)) • B z.1)
  let wG := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
    -((1 / θ) • B z.2)
  let β := ∑ i : Fin n, ∫ ω, ‖X (k.succAbove i) ω‖ ^ 3 ∂μ
  let βk := ∫ ω, ‖O ω‖ ^ 3 ∂ρ
  let MO := fun (t r : ℝ) ↦ ∫ z, s * ∫ a,
    |∫ u, convexSetCutoffDirectionalPullback A ε a z.1 L u *
      standardGaussianDensityD2
        (u + r • (vO z + t • wO z)) (wO z) (vO z + t • wO z)
      ∂volume| ∂(T.map P) ∂τ
  let MG := fun (t r : ℝ) ↦ ∫ z, p * ∫ a,
    |∫ u, convexSetCutoffDirectionalPullback A ε a z.2 L u *
      standardGaussianDensityD2
        (u + r • (vG z + t • wG z)) (wG z) (vG z + t • wG z)
      ∂volume| ∂(T.map P) ∂τ
  let J := 32 * (d : ℝ) ^ (1 / 4 : ℝ) * (C * β + ε)
  let K := (8 / ε ^ 2) * J * (240 * p * βk)
  have hs0 : 0 ≤ s := hsin.le
  have hp0 : 0 ≤ p := hcos.le
  have hβ : 0 ≤ β := by
    dsimp only [β]
    exact Finset.sum_nonneg fun i _ ↦
      integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg _) 3
  have hβk : 0 ≤ βk := by
    dsimp only [βk]
    exact integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg _) 3
  have hJ : 0 ≤ J := by
    dsimp only [J]
    positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hMO0 (t r : ℝ) : 0 ≤ MO t r := by
    dsimp only [MO]
    exact integral_nonneg fun z ↦
      mul_nonneg hs0 (integral_nonneg fun a ↦ abs_nonneg _)
  have hMG0 (t r : ℝ) : 0 ≤ MG t r := by
    dsimp only [MG]
    exact integral_nonneg fun z ↦
      mul_nonneg hp0 (integral_nonneg fun a ↦ abs_nonneg _)
  have hpoint (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (r : ℝ) :
      MO t r + MG t r ≤ K := by
    have hfixed := bentkus_smallAngle_fixedParameters_D2_le
      hC hIH hd hXm hX3 h_indep hX0 hidentity k hk α hsin hcos
        A hAclosed hAconv hε t ht ht1 r
    calc
      MO t r + MG t r ≤
          (8 / ε ^ 2) * J * (16 * p * βk) +
            (8 / ε ^ 2) * J * (224 * p * βk) := by
        exact add_le_add hfixed.1 hfixed.2
      _ = K := by
        dsimp only [K]
        ring
  have hr (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
      ‖∫ r in (0 : ℝ)..1, MO t r + MG t r‖ ≤ K := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1)
      (f := fun r ↦ MO t r + MG t r) (C := K) (by
        intro r _
        rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (hMO0 t r) (hMG0 t r))]
        exact hpoint t ht ht1 r)
    simpa using h
  have houter := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1)
    (f := fun t ↦ ∫ r in (0 : ℝ)..1, MO t r + MG t r) (C := K) (by
      intro t ht
      rw [Set.uIoc_of_le (by norm_num)] at ht
      exact hr t ht.1.le ht.2)
  have habs :
      |∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, MO t r + MG t r| ≤ K := by
    simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using houter
  calc
    (∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, MO t r + MG t r) ≤
        |∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, MO t r + MG t r| :=
      le_abs_self _
    _ ≤ K := habs
    _ = (61440 / ε ^ 2) * (d : ℝ) ^ (1 / 4 : ℝ) *
        (C * β + ε) * p * βk := by
      dsimp only [K, J]
      ring


/-- Two-shift Taylor identity for the Gaussian density in the form used in Bentkus (3.28). -/
private lemma standardGaussianDensity_twoShift_taylor
    {d : ℕ} (x v w : EuclideanSpace ℝ (Fin d)) :
    standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (x + v + w) -
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (x + v) -
        standardGaussianDensityD1 x w =
      ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
        standardGaussianDensityD2
          (x + r • (v + t • w)) w (v + t • w) := by
  have houter := standardGaussianDensity_add_taylor_one (x + v) w
  have hD1cont : Continuous (fun t : ℝ ↦
      standardGaussianDensityD1 (x + v + t • w) w) :=
    (continuous_standardGaussianDensityD1 w).comp (by fun_prop)
  have hconstCont : Continuous (fun _t : ℝ ↦ standardGaussianDensityD1 x w) :=
    continuous_const
  calc
    standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (x + v + w) -
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (x + v) -
        standardGaussianDensityD1 x w =
        (∫ t in (0 : ℝ)..1,
          standardGaussianDensityD1 (x + v + t • w) w) -
          ∫ _t in (0 : ℝ)..1, standardGaussianDensityD1 x w := by
      rw [houter]
      simp
    _ = ∫ t in (0 : ℝ)..1,
        (standardGaussianDensityD1 (x + v + t • w) w -
          standardGaussianDensityD1 x w) := by
      rw [intervalIntegral.integral_sub
        (hD1cont.intervalIntegrable 0 1)
        (hconstCont.intervalIntegrable 0 1)]
    _ = ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
        standardGaussianDensityD2
          (x + r • (v + t • w)) w (v + t • w) := by
      apply intervalIntegral.integral_congr
      intro t _
      have ht := standardGaussianDensityD1_add_taylor_one x (v + t • w) w
      change standardGaussianDensityD1 (x + v + t • w) w -
          standardGaussianDensityD1 x w =
        ∫ r in (0 : ℝ)..1,
          standardGaussianDensityD2 (x + r • (v + t • w)) w (v + t • w)
      rw [show x + v + t • w = x + (v + t • w) by abel, ht]
      ring

/-- Pointwise algebra behind Bentkus (3.27)--(3.35): after choosing the two shifts in opposite
orders for the original and Gaussian directions, the translated density splits into the two
zeroth-order terms, the covariance-cancelling first-order pair, and the signed remainders
`-s R_O + p R_G`. -/
private lemma bentkus_smallAngle_density_twoShift_decomposition
    {d : ℕ} (s p xO xG : ℝ)
    (u vO wO : EuclideanSpace ℝ (Fin d)) :
    (-s) * (xO *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + vO + wO)) +
      p * (xG *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + vO + wO)) =
      ((-s) * (xO *
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + vO)) +
        p * (xG *
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + wO))) +
      ((-s) * (xO * standardGaussianDensityD1 u wO) +
        p * (xG * standardGaussianDensityD1 u vO)) +
      ((-s) * (xO * ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
          standardGaussianDensityD2
            (u + r • (vO + t • wO)) wO (vO + t • wO)) +
        p * (xG * ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
          standardGaussianDensityD2
            (u + r • (wO + t • vO)) vO (wO + t • vO))) := by
  have hO := standardGaussianDensity_twoShift_taylor u vO wO
  have hG := standardGaussianDensity_twoShift_taylor u wO vO
  have hcomm : u + wO + vO = u + vO + wO := by abel
  rw [hcomm] at hG
  linear_combination (-s * xO) * hO + (p * xG) * hG

/-- Integral algebra for the small-angle density contraction.  Once the two low-order groups
have zero integral, the full translated contraction is exactly the signed sum of the two
two-shift remainders. -/
private theorem
    bentkus_smallAngle_densityContraction_eq_twoShiftRemainders_of_cancellation
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ] {ν : Measure Θ} [SFinite ν]
    {xO xG : Θ → ℝ}
    {vO wO : Θ → EuclideanSpace ℝ (Fin d)}
    (s p : ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    let full : Θ → ℝ := fun z ↦
      (-s) * (xO z *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + vO z + wO z)) +
      p * (xG z *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + vO z + wO z))
    let first : Θ → ℝ := fun z ↦
      xO z * (standardGaussianDensity (EuclideanSpace ℝ (Fin d))
          (u + vO z + wO z) -
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + vO z) -
        standardGaussianDensityD1 u (wO z))
    let second : Θ → ℝ := fun z ↦
      xG z * (standardGaussianDensity (EuclideanSpace ℝ (Fin d))
          (u + vO z + wO z) -
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + wO z) -
        standardGaussianDensityD1 u (vO z))
    let cancel : Θ → ℝ := fun z ↦
      ((-s) * (xO z *
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + vO z)) +
        p * (xG z *
          standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + wO z))) +
      ((-s) * (xO z * standardGaussianDensityD1 u (wO z)) +
        p * (xG z * standardGaussianDensityD1 u (vO z)))
    Integrable first ν →
    Integrable second ν →
    Integrable cancel ν →
    (∫ z, cancel z ∂ν) = 0 →
    (∫ z, full z ∂ν) =
      (-s) * (∫ z, first z ∂ν) + p * (∫ z, second z ∂ν) := by
  dsimp only
  intro hfirst hsecond hcancel hcancelZero
  let full : Θ → ℝ := fun z ↦
    (-s) * (xO z *
      standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + vO z + wO z)) +
    p * (xG z *
      standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + vO z + wO z))
  let first : Θ → ℝ := fun z ↦
    xO z * (standardGaussianDensity (EuclideanSpace ℝ (Fin d))
        (u + vO z + wO z) -
      standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + vO z) -
      standardGaussianDensityD1 u (wO z))
  let second : Θ → ℝ := fun z ↦
    xG z * (standardGaussianDensity (EuclideanSpace ℝ (Fin d))
        (u + vO z + wO z) -
      standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + wO z) -
      standardGaussianDensityD1 u (vO z))
  let cancel : Θ → ℝ := fun z ↦
    ((-s) * (xO z *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + vO z)) +
      p * (xG z *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d)) (u + wO z))) +
    ((-s) * (xO z * standardGaussianDensityD1 u (wO z)) +
      p * (xG z * standardGaussianDensityD1 u (vO z)))
  have hpoint (z : Θ) :
      full z = (-s) * first z + p * second z + cancel z := by
    dsimp only [full, first, second, cancel]
    ring
  have hfull : Integrable full ν := by
    apply (((hfirst.const_mul (-s)).add (hsecond.const_mul p)).add hcancel).congr
    filter_upwards with z
    exact (hpoint z).symm
  calc
    (∫ z, full z ∂ν) =
        ∫ z, ((-s) * first z + p * second z) + cancel z ∂ν := by
      apply integral_congr_ae
      filter_upwards with z
      rw [hpoint]
    _ = (∫ z, (-s) * first z + p * second z ∂ν) +
        ∫ z, cancel z ∂ν :=
      integral_add ((hfirst.const_mul (-s)).add (hsecond.const_mul p)) hcancel
    _ = (-s) * (∫ z, first z ∂ν) + p * (∫ z, second z ∂ν) := by
      rw [integral_add (hfirst.const_mul (-s)) (hsecond.const_mul p),
        integral_const_mul, integral_const_mul, hcancelZero, add_zero]

/-- The standard Gaussian density is integrable with respect to Euclidean volume. -/
private lemma integrable_standardGaussianDensity_volume {d : ℕ} :
    Integrable
      (standardGaussianDensity (EuclideanSpace ℝ (Fin d))) volume := by
  let E := EuclideanSpace ℝ (Fin d)
  have hconst : Integrable (fun _ : E ↦ (1 : ℝ)) (stdGaussian E) :=
    integrable_const 1
  rw [stdGaussian_eq_withDensity_standardGaussianDensityReal] at hconst
  have hweighted := (integrable_withDensity_iff_integrable_smul'
    measurable_standardGaussianDensityReal.ennreal_ofReal (by simp)).mp hconst
  simp_rw [ENNReal.toReal_ofReal (standardGaussianDensityReal_nonneg _)] at hweighted
  simpa only [standardGaussianDensityReal_eq_standardGaussianDensity,
    smul_eq_mul, mul_one] using hweighted

/-- A parameter-dependent translate of the standard Gaussian density remains integrable after
multiplication by a measurable envelope integrable in the parameter. -/
private lemma integrable_prod_parametric_mul_standardGaussianDensity_add
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ] {μ : Measure Θ} [SFinite μ]
    {φ : Θ × EuclideanSpace ℝ (Fin d) → ℝ} (hφm : Measurable φ)
    {b : Θ → EuclideanSpace ℝ (Fin d)} (hbm : Measurable b)
    {D : Θ → ℝ} (hD : ∀ z, 0 ≤ D z)
    (hφ : ∀ z u, |φ (z, u)| ≤ D z)
    (hDint : Integrable D μ) :
    Integrable (fun p : Θ × EuclideanSpace ℝ (Fin d) ↦
      φ p * standardGaussianDensity (EuclideanSpace ℝ (Fin d))
        (p.2 + b p.1)) (μ.prod volume) := by
  let E := EuclideanSpace ℝ (Fin d)
  let F : Θ × E → ℝ := fun p ↦
    φ p * standardGaussianDensity E (p.2 + b p.1)
  have hFm : Measurable F := by
    dsimp only [F]
    exact hφm.mul (continuous_standardGaussianDensity.measurable.comp
      (measurable_snd.add (hbm.comp measurable_fst)))
  apply (integrable_prod_iff hFm.aestronglyMeasurable).2
  constructor
  · filter_upwards with z
    have hdensity : Integrable (fun u : E ↦
        standardGaussianDensity E (u + b z)) volume := by
      have hbase :=
        (integrable_standardGaussianDensity_volume (d := d)).comp_sub_right (-b z)
      simpa only [sub_neg_eq_add] using hbase
    exact hdensity.bdd_mul
      (hφm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (by
        filter_upwards with u
        change |φ (z, u)| ≤ D z
        exact hφ z u)
  · have hinnerMeas : AEStronglyMeasurable
        (fun z ↦ ∫ u, ‖F (z, u)‖ ∂volume) μ :=
      hFm.aestronglyMeasurable.norm.integral_prod_right'
    let c : ℝ := ∫ u : E, |standardGaussianDensity E u| ∂volume
    have hc : 0 ≤ c := integral_nonneg fun _ ↦ abs_nonneg _
    have hmajor : Integrable (fun z ↦ c * D z) μ :=
      hDint.const_mul c
    apply hmajor.mono' hinnerMeas
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun u ↦ norm_nonneg _)]
    have hdensity : Integrable (fun u : E ↦
        standardGaussianDensity E (u + b z)) volume := by
      have hbase :=
        (integrable_standardGaussianDensity_volume (d := d)).comp_sub_right (-b z)
      simpa only [sub_neg_eq_add] using hbase
    calc
      (∫ u, ‖F (z, u)‖ ∂volume) ≤
          D z * ∫ u, |standardGaussianDensity E (u + b z)| ∂volume := by
        rw [← integral_const_mul]
        apply integral_mono
        · exact (hdensity.bdd_mul
            (hφm.comp (measurable_const.prodMk measurable_id)
              ).aestronglyMeasurable (by
                filter_upwards with u
                change |φ (z, u)| ≤ D z
                exact hφ z u)).norm
        · exact hdensity.abs.const_mul (D z)
        · intro u
          dsimp only [F]
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (hφ z u) (abs_nonneg _)
      _ = D z * c := by
        congr 1
        exact integral_add_right_eq_self
          (fun u : E ↦ |standardGaussianDensity E u|) (b z)
      _ = c * D z := mul_comm _ _

/-- Exact joint-law disintegration and Gaussian translation for one small-angle replacement
coordinate.  This is Bentkus (3.27) before the density is expanded by (3.28). -/
private theorem bentkus_smallAngle_rotationCoordinate_eq_translatedDensityContraction
    {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (α : ℝ) (hsin : 0 < Real.sin α)
    (A : Set (EuclideanSpace ℝ (Fin d)))
    (hAconv : Convexity.IsConvexSet ℝ A) {ε : ℝ} (hε : 0 < ε) :
    let ρ := bentkusReplacementMeasure μ X
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
    let UO := bentkusLeaveOneOut
      (fun i ↦ replacementOriginal (d := d) i) k
    let VG := bentkusLeaveOneOut
      (fun i ↦ replacementGaussian (d := d) i) k
    let U := bentkusLeaveOneOut X k
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let Z := fun ω ↦ (O ω, G ω)
    let τ := ρ.map Z
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let ν := μ.map (fun ω ↦ B (U ω))
    let θ := (Real.sqrt 2)⁻¹
    let p := Real.cos α
    let s := Real.sin α
    let q := θ * s
    let T := ((γ.map (fun y ↦ q • y)).prod ν).map
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        p • z.2 + z.1)
    let L := q • P
    let vO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((1 / θ) • B z.2)
    let wO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((p / (θ * s)) • B z.1)
    let full := fun
        (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))
        (a u : EuclideanSpace ℝ (Fin d)) ↦
      (-s) * (convexSetCutoffDirectionalPullback A ε a z.1 L u *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d))
          (u + vO z + wO z)) +
      p * (convexSetCutoffDirectionalPullback A ε a z.2 L u *
        standardGaussianDensity (EuclideanSpace ℝ (Fin d))
          (u + vO z + wO z))
    (∫ ω, (fderiv ℝ (convexSetCutoff A ε)
        ((p • UO ω + s • VG ω) + (p • O ω + s • G ω)))
        ((-s) • O ω + p • G ω) ∂ρ) =
      ∫ z, ∫ a, ∫ u, full z a u ∂volume ∂(T.map P) ∂τ := by
  let E := EuclideanSpace ℝ (Fin d)
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  let e := bentkusWhiteningEquiv S
    (bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk)
  let P := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  let UO := bentkusLeaveOneOut
    (fun i ↦ replacementOriginal (d := d) i) k
  let VG := bentkusLeaveOneOut
    (fun i ↦ replacementGaussian (d := d) i) k
  let U := bentkusLeaveOneOut X k
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let Z := fun ω ↦ (O ω, G ω)
  let τ := ρ.map Z
  let γ := stdGaussian E
  let ν := μ.map (fun ω ↦ B (U ω))
  let θ := (Real.sqrt 2)⁻¹
  let p := Real.cos α
  let s := Real.sin α
  let q := θ * s
  let T := ((γ.map (fun y ↦ q • y)).prod ν).map
    (fun z : E × E ↦ p • z.2 + z.1)
  let L := q • P
  let vO := fun z : E × E ↦ -((1 / θ) • B z.2)
  let wO := fun z : E × E ↦ -((p / (θ * s)) • B z.1)
  let N := fun ω ↦ p • UO ω + s • VG ω
  let r := fun z : E × E ↦ p • z.1 + s • z.2
  let r' := fun z : E × E ↦ (-s) • z.1 + p • z.2
  let M := fun z : E × E ↦ z.1 + L z.2
  let F : E × (E × E) → ℝ := fun z ↦
    (fderiv ℝ (convexSetCutoff A ε) (z.1 + r z.2)) (r' z.2)
  let full := fun (z : E × E) (a u : E) ↦
    (-s) * (convexSetCutoffDirectionalPullback A ε a z.1 L u *
      standardGaussianDensity E (u + vO z + wO z)) +
    p * (convexSetCutoffDirectionalPullback A ε a z.2 L u *
      standardGaussianDensity E (u + vO z + wO z))
  let base := T.map P
  let ξ := (base.prod γ).map M
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
    exact Measure.isProbabilityMeasure_map
      (B.continuous.measurable.comp hUmeas).aemeasurable
  letI : IsProbabilityMeasure (γ.map (fun y ↦ q • y)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure T := by
    dsimp only [T]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure base := by
    dsimp only [base]
    exact Measure.isProbabilityMeasure_map P.continuous.measurable.aemeasurable
  have hMmeas : Measurable M := by
    dsimp only [M]
    fun_prop
  letI : IsProbabilityMeasure ξ := by
    dsimp only [ξ]
    exact Measure.isProbabilityMeasure_map hMmeas.aemeasurable
  have hZmeas : Measurable Z := by
    dsimp only [Z, O, G]
    exact ((measurable_pi_apply k).comp measurable_fst).prodMk
      ((measurable_pi_apply k).comp measurable_snd)
  letI : IsProbabilityMeasure τ := by
    dsimp only [τ]
    exact Measure.isProbabilityMeasure_map hZmeas.aemeasurable
  have hNmeas : Measurable N := by
    dsimp only [N, UO, VG, bentkusLeaveOneOut, O, G,
      replacementOriginal, replacementGaussian]
    fun_prop
  have hrmeas : Measurable r := by
    dsimp only [r]
    fun_prop
  have hr'meas : Measurable r' := by
    dsimp only [r']
    fun_prop
  have hO3 : MemLp O 3 ρ := memLp_replacementOriginal hXm hX3 k
  have hG3 : MemLp G 3 ρ := memLp_three_replacementGaussian hXm k
  have hR'3 : MemLp (fun ω ↦ r' (Z ω)) 3 ρ := by
    change MemLp ((-s) • O + p • G) 3 ρ
    exact (hO3.const_smul (-s)).add (hG3.const_smul p)
  have hr'int : Integrable r' τ := by
    apply (integrable_map_measure hr'meas.aestronglyMeasurable
      hZmeas.aemeasurable).2
    exact hR'3.integrable (by norm_num)
  have hFmeas : Measurable F := by
    dsimp only [F]
    exact ((contDiff_convexSetCutoff hAconv hε).continuous_fderiv_apply
      (by norm_num)).measurable.comp
        (((measurable_fst.add (hrmeas.comp measurable_snd))).prodMk
          (hr'meas.comp measurable_snd))
  have hmajor : Integrable (fun z : E × (E × E) ↦
      (2 / ε) * ‖r' z.2‖) (ξ.prod τ) :=
    (hr'int.norm.const_mul (2 / ε)).comp_snd ξ
  have hFint : Integrable F (ξ.prod τ) := by
    apply hmajor.mono' hFmeas.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_eq_abs]
    have happly := ContinuousLinearMap.le_opNorm
      (fderiv ℝ (convexSetCutoff A ε) (z.1 + r z.2)) (r' z.2)
    calc
      |F z| =
          ‖(fderiv ℝ (convexSetCutoff A ε) (z.1 + r z.2)) (r' z.2)‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ ‖fderiv ℝ (convexSetCutoff A ε) (z.1 + r z.2)‖ * ‖r' z.2‖ :=
        happly
      _ ≤ (2 / ε) * ‖r' z.2‖ :=
        mul_le_mul_of_nonneg_right
          (norm_fderiv_convexSetCutoff_le hAconv hε _) (norm_nonneg _)
  have hjoint :
      ρ.map (fun ω ↦ (N ω, Z ω)) = ξ.prod τ := by
    simpa only [E, ρ, S, e, P, B, UO, VG, U, O, G, Z, τ, γ, ν,
      θ, p, s, q, T, L, N, M, base, ξ] using
      bentkus_smallAngle_splitBase_replacementPair_eq_prod
        hXm hX3 h_indep hX0 hidentity k hk α
  have htriple := integral_comp_pair_eq_triple_of_map_eq_mapped_prod
    hNmeas hZmeas M hMmeas hjoint hFint
  have htranslate (z : E × E) (a : E) :
      (∫ u, F (M (a, u), z) ∂γ) =
        ∫ u, full z a u ∂volume := by
    have hshift := bentkus_smallAngle_shift_relations e α hsin z.1 z.2
    have hOtrans := integral_fderiv_convexSetCutoff_affine_translate
      (s := A) ε a (r z) z.1 (-(vO z + wO z)) L hshift.2.2
    have hGtrans := integral_fderiv_convexSetCutoff_affine_translate
      (s := A) ε a (r z) z.2 (-(vO z + wO z)) L hshift.2.2
    have hOγ : Integrable (fun u : E ↦
        (fderiv ℝ (convexSetCutoff A ε) (a + L u + r z)) z.1) γ := by
      have hm : Measurable (fun u : E ↦
          (fderiv ℝ (convexSetCutoff A ε) (a + L u + r z)) z.1) :=
        ((contDiff_convexSetCutoff hAconv hε).continuous_fderiv_apply
          (by norm_num)).measurable.comp
            ((by fun_prop : Measurable (fun u : E ↦ a + L u + r z)).prodMk
              measurable_const)
      apply Integrable.of_bound hm.aestronglyMeasurable ((2 / ε) * ‖z.1‖)
      filter_upwards with u
      rw [Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm
        (fderiv ℝ (convexSetCutoff A ε) (a + L u + r z)) z.1).trans
          (mul_le_mul_of_nonneg_right
            (norm_fderiv_convexSetCutoff_le hAconv hε _)
            (norm_nonneg _))
    have hGγ : Integrable (fun u : E ↦
        (fderiv ℝ (convexSetCutoff A ε) (a + L u + r z)) z.2) γ := by
      have hm : Measurable (fun u : E ↦
          (fderiv ℝ (convexSetCutoff A ε) (a + L u + r z)) z.2) :=
        ((contDiff_convexSetCutoff hAconv hε).continuous_fderiv_apply
          (by norm_num)).measurable.comp
            ((by fun_prop : Measurable (fun u : E ↦ a + L u + r z)).prodMk
              measurable_const)
      apply Integrable.of_bound hm.aestronglyMeasurable ((2 / ε) * ‖z.2‖)
      filter_upwards with u
      rw [Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm
        (fderiv ℝ (convexSetCutoff A ε) (a + L u + r z)) z.2).trans
          (mul_le_mul_of_nonneg_right
            (norm_fderiv_convexSetCutoff_le hAconv hε _)
            (norm_nonneg _))
    let termO : E → ℝ := fun u ↦
      convexSetCutoffDirectionalPullback A ε a z.1 L u *
        standardGaussianDensity E (u + vO z + wO z)
    let termG : E → ℝ := fun u ↦
      convexSetCutoffDirectionalPullback A ε a z.2 L u *
        standardGaussianDensity E (u + vO z + wO z)
    have hdensity : Integrable (fun u : E ↦
        standardGaussianDensity E (u + vO z + wO z)) volume := by
      have hbase :=
        (integrable_standardGaussianDensity_volume (d := d)).comp_sub_right
          (-(vO z + wO z))
      simpa only [E, sub_neg_eq_add, add_assoc] using hbase
    have hcutOm : Measurable (fun u : E ↦
        convexSetCutoffDirectionalPullback A ε a z.1 L u) := by
      dsimp only [convexSetCutoffDirectionalPullback]
      exact ((contDiff_convexSetCutoff hAconv hε).continuous_fderiv_apply
        (by norm_num)).measurable.comp
          ((by fun_prop : Measurable (fun u : E ↦ a + L u)).prodMk
            measurable_const)
    have hcutGm : Measurable (fun u : E ↦
        convexSetCutoffDirectionalPullback A ε a z.2 L u) := by
      dsimp only [convexSetCutoffDirectionalPullback]
      exact ((contDiff_convexSetCutoff hAconv hε).continuous_fderiv_apply
        (by norm_num)).measurable.comp
          ((by fun_prop : Measurable (fun u : E ↦ a + L u)).prodMk
            measurable_const)
    have htermO : Integrable termO volume := by
      apply hdensity.bdd_mul hcutOm.aestronglyMeasurable
      filter_upwards with u
      dsimp only [convexSetCutoffDirectionalPullback]
      exact (ContinuousLinearMap.le_opNorm
          (fderiv ℝ (convexSetCutoff A ε) (a + L u)) z.1).trans
        (mul_le_mul_of_nonneg_right
          (norm_fderiv_convexSetCutoff_le hAconv hε _)
          (norm_nonneg _))
    have htermG : Integrable termG volume := by
      apply hdensity.bdd_mul hcutGm.aestronglyMeasurable
      filter_upwards with u
      dsimp only [convexSetCutoffDirectionalPullback]
      exact (ContinuousLinearMap.le_opNorm
          (fderiv ℝ (convexSetCutoff A ε) (a + L u)) z.2).trans
        (mul_le_mul_of_nonneg_right
          (norm_fderiv_convexSetCutoff_le hAconv hε _)
          (norm_nonneg _))
    have hOtrans' :
        (∫ u, (fderiv ℝ (convexSetCutoff A ε) (a + L u + r z)) z.1 ∂γ) =
          ∫ u, termO u ∂volume := by
      rw [hOtrans]
      apply integral_congr_ae
      filter_upwards with u
      dsimp only [termO]
      congr 2
      abel
    have hGtrans' :
        (∫ u, (fderiv ℝ (convexSetCutoff A ε) (a + L u + r z)) z.2 ∂γ) =
          ∫ u, termG u ∂volume := by
      rw [hGtrans]
      apply integral_congr_ae
      filter_upwards with u
      dsimp only [termG]
      congr 2
      abel
    calc
      (∫ u, F (M (a, u), z) ∂γ) =
          ∫ u, (-s) *
              (fderiv ℝ (convexSetCutoff A ε) (a + L u + r z)) z.1 +
            p * (fderiv ℝ (convexSetCutoff A ε) (a + L u + r z)) z.2 ∂γ := by
        apply integral_congr_ae
        filter_upwards with u
        dsimp only [F, M, r']
        rw [map_add, map_smul, map_smul]
        ring
      _ = (-s) * (∫ u,
            (fderiv ℝ (convexSetCutoff A ε) (a + L u + r z)) z.1 ∂γ) +
          p * (∫ u,
            (fderiv ℝ (convexSetCutoff A ε) (a + L u + r z)) z.2 ∂γ) := by
        rw [integral_add (hOγ.const_mul (-s)) (hGγ.const_mul p),
          integral_const_mul, integral_const_mul]
      _ = (-s) * (∫ u, termO u ∂volume) +
          p * (∫ u, termG u ∂volume) := by
        rw [hOtrans', hGtrans']
      _ = ∫ u, full z a u ∂volume := by
        rw [← integral_const_mul, ← integral_const_mul,
          ← integral_add (htermO.const_mul (-s)) (htermG.const_mul p)]
  change
    (∫ ω, (fderiv ℝ (convexSetCutoff A ε)
        ((p • UO ω + s • VG ω) + (p • O ω + s • G ω)))
        ((-s) • O ω + p • G ω) ∂ρ) =
      ∫ z, ∫ a, ∫ u, full z a u ∂volume ∂base ∂τ
  calc
    (∫ ω, (fderiv ℝ (convexSetCutoff A ε)
        ((p • UO ω + s • VG ω) + (p • O ω + s • G ω)))
        ((-s) • O ω + p • G ω) ∂ρ) =
        ∫ ω, F (N ω, Z ω) ∂ρ := by
      apply integral_congr_ae
      filter_upwards with ω
      rfl
    _ = ∫ z, ∫ a, ∫ u, F (M (a, u), z) ∂γ ∂base ∂τ := by
      simpa only [base, ξ] using htriple
    _ = ∫ z, ∫ a, ∫ u, full z a u ∂volume ∂base ∂τ := by
      apply integral_congr_ae
      filter_upwards with z
      apply integral_congr_ae
      filter_upwards with a
      exact htranslate z a

/-- Bentkus (3.27)--(3.35): after Gaussian translation, the low-order terms cancel and the
rotation-coordinate derivative is exactly the sum of the two signed second-density remainders. -/
private theorem bentkus_smallAngle_rotationCoordinate_eq_twoShiftRemainders
    {n d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin (n + 1) → Ω → EuclideanSpace ℝ (Fin d)}
    (hXm : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (h_indep : iIndepFun X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hidentity : ∀ x y,
      covarianceBilin (μ.map (fun ω ↦ ∑ i, X i ω)) x y = inner ℝ x y)
    (k : Fin (n + 1)) (hk : (∫ ω, ‖X k ω‖ ^ 2 ∂μ) < 1 / 4)
    (α : ℝ) (hsin : 0 < Real.sin α)
    (A : Set (EuclideanSpace ℝ (Fin d)))
    (hAconv : Convexity.IsConvexSet ℝ A) {ε : ℝ} (hε : 0 < ε) :
    let ρ := bentkusReplacementMeasure μ X
    let S := bentkusLeaveOneOutCovarianceMatrix μ X k
    let hS := bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
    let e := bentkusWhiteningEquiv S hS
    let P := e.symm.toContinuousLinearMap
    let B := e.toContinuousLinearMap
    let UO := bentkusLeaveOneOut
      (fun i ↦ replacementOriginal (d := d) i) k
    let VG := bentkusLeaveOneOut
      (fun i ↦ replacementGaussian (d := d) i) k
    let U := bentkusLeaveOneOut X k
    let O := replacementOriginal (d := d) k
    let G := replacementGaussian (d := d) k
    let Z := fun ω ↦ (O ω, G ω)
    let τ := ρ.map Z
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let ν := μ.map (fun ω ↦ e (U ω))
    let θ := (Real.sqrt 2)⁻¹
    let p := Real.cos α
    let s := Real.sin α
    let q := θ * s
    let T := ((γ.map (fun y ↦ q • y)).prod ν).map
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        p • z.2 + z.1)
    let L := q • P
    let vO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((1 / θ) • B z.2)
    let wO := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      -((p / (θ * s)) • B z.1)
    let vG := wO
    let wG := vO
    let RO := fun (t r : ℝ)
        (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))
        (a u : EuclideanSpace ℝ (Fin d)) ↦
      (-s) * (convexSetCutoffDirectionalPullback A ε a z.1 L u *
        standardGaussianDensityD2
          (u + r • (vO z + t • wO z))
          (wO z) (vO z + t • wO z))
    let RG := fun (t r : ℝ)
        (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))
        (a u : EuclideanSpace ℝ (Fin d)) ↦
      p * (convexSetCutoffDirectionalPullback A ε a z.2 L u *
        standardGaussianDensityD2
          (u + r • (vG z + t • wG z))
          (wG z) (vG z + t • wG z))
    (∫ ω, (fderiv ℝ (convexSetCutoff A ε)
        ((p • UO ω + s • VG ω) + (p • O ω + s • G ω)))
        ((-s) • O ω + p • G ω) ∂ρ) =
      ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, ∫ z,
        ((∫ a, ∫ u, RO t r z a u ∂volume ∂(T.map P)) +
          ∫ a, ∫ u, RG t r z a u ∂volume ∂(T.map P)) ∂τ := by
  let E := EuclideanSpace ℝ (Fin d)
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let P := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  let UO := bentkusLeaveOneOut
    (fun i ↦ replacementOriginal (d := d) i) k
  let VG := bentkusLeaveOneOut
    (fun i ↦ replacementGaussian (d := d) i) k
  let U := bentkusLeaveOneOut X k
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let Z := fun ω ↦ (O ω, G ω)
  let τ := ρ.map Z
  let γ := stdGaussian E
  let ν := μ.map (fun ω ↦ e (U ω))
  let θ := (Real.sqrt 2)⁻¹
  let p := Real.cos α
  let s := Real.sin α
  let q := θ * s
  let T := ((γ.map (fun y ↦ q • y)).prod ν).map
    (fun z : E × E ↦ p • z.2 + z.1)
  let L := q • P
  let vO := fun z : E × E ↦ -((1 / θ) • B z.2)
  let wO := fun z : E × E ↦ -((p / (θ * s)) • B z.1)
  let vG := wO
  let wG := vO
  let base := T.map P
  let full := fun (z : E × E) (a u : E) ↦
    (-s) * (convexSetCutoffDirectionalPullback A ε a z.1 L u *
      standardGaussianDensity E (u + vO z + wO z)) +
    p * (convexSetCutoffDirectionalPullback A ε a z.2 L u *
      standardGaussianDensity E (u + vO z + wO z))
  let cancel := fun (z : E × E) (a u : E) ↦
    (((-s) * (convexSetCutoffDirectionalPullback A ε a z.1 L u *
        standardGaussianDensity E (u + vO z)) +
      p * (convexSetCutoffDirectionalPullback A ε a z.2 L u *
        standardGaussianDensity E (u + wO z))) +
    ((-s) * (convexSetCutoffDirectionalPullback A ε a z.1 L u *
        standardGaussianDensityD1 u (wO z)) +
      p * (convexSetCutoffDirectionalPullback A ε a z.2 L u *
        standardGaussianDensityD1 u (vO z))))
  let RO := fun (t r : ℝ) (z : E × E) (a u : E) ↦
    (-s) * (convexSetCutoffDirectionalPullback A ε a z.1 L u *
      standardGaussianDensityD2
        (u + r • (vO z + t • wO z))
        (wO z) (vO z + t • wO z))
  let RG := fun (t r : ℝ) (z : E × E) (a u : E) ↦
    p * (convexSetCutoffDirectionalPullback A ε a z.2 L u *
      standardGaussianDensityD2
        (u + r • (vG z + t • wG z))
        (wG z) (vG z + t • wG z))
  let remO := fun (z : E × E) (a u : E) ↦
    ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, RO t r z a u
  let remG := fun (z : E × E) (a u : E) ↦
    ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, RG t r z a u
  let I := volume.restrict (Set.uIoc (0 : ℝ) 1)
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
    exact Measure.isProbabilityMeasure_map
      (e.continuous.measurable.comp hUmeas).aemeasurable
  letI : IsProbabilityMeasure (γ.map (fun y ↦ q • y)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure T := by
    dsimp only [T]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure base := by
    dsimp only [base]
    exact Measure.isProbabilityMeasure_map P.continuous.measurable.aemeasurable
  have hZmeas : Measurable Z := by
    dsimp only [Z, O, G]
    exact ((measurable_pi_apply k).comp measurable_fst).prodMk
      ((measurable_pi_apply k).comp measurable_snd)
  letI : IsProbabilityMeasure τ := by
    dsimp only [τ]
    exact Measure.isProbabilityMeasure_map hZmeas.aemeasurable
  have hremainders :=
    bentkus_smallAngle_signed_D2_remainder_integrals_swap
      hXm hX3 h_indep hX0 hidentity k hk α hsin A hAconv hε
  have hremainders' :
      Integrable (fun q : (E × E) × (E × E) ↦
        remO q.1 q.2.1 q.2.2) (τ.prod (base.prod volume)) ∧
      Integrable (fun q : (E × E) × (E × E) ↦
        remG q.1 q.2.1 q.2.2) (τ.prod (base.prod volume)) ∧
      ((∫ a, ∫ u, ∫ z, remO z a u ∂τ ∂volume ∂base) =
        ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
          ∫ z, ∫ a, ∫ u, RO t r z a u ∂volume ∂base ∂τ) ∧
      ((∫ a, ∫ u, ∫ z, remG z a u ∂τ ∂volume ∂base) =
        ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
          ∫ z, ∫ a, ∫ u, RG t r z a u ∂volume ∂base ∂τ) ∧
      (((∫ a, ∫ u, ∫ z, remO z a u ∂τ ∂volume ∂base) +
        ∫ a, ∫ u, ∫ z, remG z a u ∂τ ∂volume ∂base) =
        ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, ∫ z,
          ((∫ a, ∫ u, RO t r z a u ∂volume ∂base) +
            ∫ a, ∫ u, RG t r z a u ∂volume ∂base) ∂τ) := by
    simpa only [E, ρ, S, hS, e, P, B, U, O, G, Z, τ, γ, ν, θ, p, s, q,
      T, L, vO, wO, vG, wG, RO, RG, remO, remG, base] using hremainders
  have hremO : Integrable (fun q : (E × E) × (E × E) ↦
      remO q.1 q.2.1 q.2.2) (τ.prod (base.prod volume)) :=
    hremainders'.1
  have hremG : Integrable (fun q : (E × E) × (E × E) ↦
      remG q.1 q.2.1 q.2.2) (τ.prod (base.prod volume)) :=
    hremainders'.2.1
  let φ : (((E × E) × E) × E) → ℝ := fun q ↦
    (-s) * convexSetCutoffDirectionalPullback A ε q.1.2 q.1.1.1 L q.2 +
      p * convexSetCutoffDirectionalPullback A ε q.1.2 q.1.1.2 L q.2
  let b : (E × E) × E → E := fun q ↦ vO q.1 + wO q.1
  let D : (E × E) × E → ℝ := fun q ↦
    |s| * (2 / ε) * ‖q.1.1‖ + |p| * (2 / ε) * ‖q.1.2‖
  have hO3ρ : MemLp O 3 ρ := memLp_replacementOriginal hXm hX3 k
  have hG3ρ : MemLp G 3 ρ := memLp_three_replacementGaussian hXm k
  have hO3 : MemLp (fun z : E × E ↦ z.1) 3 τ := by
    apply (memLp_map_measure_iff measurable_fst.aestronglyMeasurable
      hZmeas.aemeasurable).2
    apply hO3ρ.ae_eq
    filter_upwards with ω
    rfl
  have hG3 : MemLp (fun z : E × E ↦ z.2) 3 τ := by
    apply (memLp_map_measure_iff measurable_snd.aestronglyMeasurable
      hZmeas.aemeasurable).2
    apply hG3ρ.ae_eq
    filter_upwards with ω
    rfl
  have hDintτ : Integrable (fun z : E × E ↦
      |s| * (2 / ε) * ‖z.1‖ + |p| * (2 / ε) * ‖z.2‖) τ :=
    ((hO3.integrable (by norm_num)).norm.const_mul (|s| * (2 / ε))).add
      ((hG3.integrable (by norm_num)).norm.const_mul (|p| * (2 / ε)))
  have hDint : Integrable D (τ.prod base) := by
    simpa only [D, mul_assoc] using hDintτ.comp_fst base
  have hφm : Measurable φ := by
    have hcutO : Measurable (fun q : (((E × E) × E) × E) ↦
        convexSetCutoffDirectionalPullback A ε q.1.2 q.1.1.1 L q.2) := by
      dsimp only [convexSetCutoffDirectionalPullback]
      exact ((contDiff_convexSetCutoff hAconv hε).continuous_fderiv_apply
        (by norm_num)).measurable.comp
          (((by fun_prop : Measurable (fun q : (((E × E) × E) × E) ↦
            q.1.2 + L q.2))).prodMk (by fun_prop))
    have hcutG : Measurable (fun q : (((E × E) × E) × E) ↦
        convexSetCutoffDirectionalPullback A ε q.1.2 q.1.1.2 L q.2) := by
      dsimp only [convexSetCutoffDirectionalPullback]
      exact ((contDiff_convexSetCutoff hAconv hε).continuous_fderiv_apply
        (by norm_num)).measurable.comp
          (((by fun_prop : Measurable (fun q : (((E × E) × E) × E) ↦
            q.1.2 + L q.2))).prodMk (by fun_prop))
    exact (hcutO.const_mul (-s)).add (hcutG.const_mul p)
  have hbm : Measurable b := by
    dsimp only [b, vO, wO]
    fun_prop
  have hD0 : ∀ z, 0 ≤ D z := by
    intro z
    dsimp only [D]
    positivity
  have hφD : ∀ z u, |φ (z, u)| ≤ D z := by
    intro z u
    have hcutO :
        |convexSetCutoffDirectionalPullback A ε z.2 z.1.1 L u| ≤
          (2 / ε) * ‖z.1.1‖ := by
      rw [← Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm
          (fderiv ℝ (convexSetCutoff A ε) (z.2 + L u)) z.1.1).trans
        (mul_le_mul_of_nonneg_right
          (norm_fderiv_convexSetCutoff_le hAconv hε _)
          (norm_nonneg _))
    have hcutG :
        |convexSetCutoffDirectionalPullback A ε z.2 z.1.2 L u| ≤
          (2 / ε) * ‖z.1.2‖ := by
      rw [← Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm
          (fderiv ℝ (convexSetCutoff A ε) (z.2 + L u)) z.1.2).trans
        (mul_le_mul_of_nonneg_right
          (norm_fderiv_convexSetCutoff_le hAconv hε _)
          (norm_nonneg _))
    dsimp only [φ, D]
    calc
      |(-s) * convexSetCutoffDirectionalPullback A ε z.2 z.1.1 L u +
          p * convexSetCutoffDirectionalPullback A ε z.2 z.1.2 L u| ≤
          |(-s) * convexSetCutoffDirectionalPullback A ε z.2 z.1.1 L u| +
            |p * convexSetCutoffDirectionalPullback A ε z.2 z.1.2 L u| :=
        abs_add_le _ _
      _ = |s| * |convexSetCutoffDirectionalPullback A ε z.2 z.1.1 L u| +
          |p| * |convexSetCutoffDirectionalPullback A ε z.2 z.1.2 L u| := by
        rw [abs_mul, abs_neg, abs_mul]
      _ ≤ |s| * ((2 / ε) * ‖z.1.1‖) +
          |p| * ((2 / ε) * ‖z.1.2‖) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hcutO (abs_nonneg s))
          (mul_le_mul_of_nonneg_left hcutG (abs_nonneg p))
      _ = |s| * (2 / ε) * ‖z.1.1‖ +
          |p| * (2 / ε) * ‖z.1.2‖ := by ring
  have hfullLeft : Integrable (fun q : (((E × E) × E) × E) ↦
      φ q * standardGaussianDensity E (q.2 + b q.1))
      ((τ.prod base).prod volume) :=
    integrable_prod_parametric_mul_standardGaussianDensity_add
      hφm hbm hD0 hφD hDint
  have hfullm : Measurable (fun q : (E × E) × (E × E) ↦
      full q.1 q.2.1 q.2.2) := by
    let assoc : (E × E) × (E × E) → (((E × E) × E) × E) :=
      fun q ↦ ((q.1, q.2.1), q.2.2)
    have hassoc : Measurable assoc := by
      dsimp only [assoc]
      exact (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)
    have hm : Measurable (fun q : (E × E) × (E × E) ↦
        φ (assoc q) * standardGaussianDensity E
          (q.2.2 + b (q.1, q.2.1))) :=
      (hφm.comp hassoc).mul
        (continuous_standardGaussianDensity.measurable.comp
          ((measurable_snd.comp measurable_snd).add
            (hbm.comp
              (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))))
    have heq : (fun q : (E × E) × (E × E) ↦
        full q.1 q.2.1 q.2.2) =
        fun q ↦ φ (assoc q) * standardGaussianDensity E
          (q.2.2 + b (q.1, q.2.1)) := by
      funext q
      dsimp only [full, φ, b, assoc]
      rw [add_assoc]
      ring
    rw [heq]
    exact hm
  have hfull : Integrable (fun q : (E × E) × (E × E) ↦
      full q.1 q.2.1 q.2.2) (τ.prod (base.prod volume)) := by
    have hfullLeft' : Integrable (fun q : (((E × E) × E) × E) ↦
        full q.1.1 q.1.2 q.2) ((τ.prod base).prod volume) := by
      apply hfullLeft.congr
      filter_upwards with q
      dsimp only [full, φ, b]
      rw [add_assoc]
      ring
    have hAssoc := measurePreserving_prodAssoc τ base (volume : Measure E)
    apply (hAssoc.integrable_comp hfullm.aestronglyMeasurable).mp
    simpa only [Function.comp_def, MeasurableEquiv.prodAssoc,
      MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply] using hfullLeft'
  have hremOpoint (z : E × E) (a u : E) :
      remO z a u =
        (-s) * (convexSetCutoffDirectionalPullback A ε a z.1 L u *
          ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
            standardGaussianDensityD2
              (u + r • (vO z + t • wO z))
              (wO z) (vO z + t • wO z)) := by
    dsimp only [remO, RO]
    simp_rw [intervalIntegral.integral_const_mul]
  have hremGpoint (z : E × E) (a u : E) :
      remG z a u =
        p * (convexSetCutoffDirectionalPullback A ε a z.2 L u *
          ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
            standardGaussianDensityD2
              (u + r • (vG z + t • wG z))
              (wG z) (vG z + t • wG z)) := by
    dsimp only [remG, RG]
    simp_rw [intervalIntegral.integral_const_mul]
  have hpoint (z : E × E) (a u : E) :
      full z a u = cancel z a u + (remO z a u + remG z a u) := by
    have hdecomp := bentkus_smallAngle_density_twoShift_decomposition
      s p
        (convexSetCutoffDirectionalPullback A ε a z.1 L u)
        (convexSetCutoffDirectionalPullback A ε a z.2 L u)
        u (vO z) (wO z)
    rw [hremOpoint, hremGpoint]
    simpa only [full, cancel, vG, wG, add_assoc] using hdecomp
  have hcancel : Integrable (fun q : (E × E) × (E × E) ↦
      cancel q.1 q.2.1 q.2.2) (τ.prod (base.prod volume)) := by
    have hdiff := hfull.sub (hremO.add hremG)
    apply hdiff.congr
    filter_upwards with q
    change full q.1 q.2.1 q.2.2 -
        (remO q.1 q.2.1 q.2.2 + remG q.1 q.2.1 q.2.2) =
      cancel q.1 q.2.1 q.2.2
    rw [hpoint]
    ring
  have hcancelFiberZero (a u : E) :
      (∫ z, cancel z a u ∂τ) = 0 := by
    have hlow := bentkus_smallAngle_lowOrder_pair_cancel
      hXm hX3 hX0 k B α hsin A ε a u L
    simpa only [E, ρ, O, G, Z, τ, θ, p, s, vO, wO, cancel] using hlow.2
  have hcancelTotalZero :
      (∫ q : (E × E) × (E × E),
        cancel q.1 q.2.1 q.2.2 ∂(τ.prod (base.prod volume))) = 0 := by
    calc
      (∫ q : (E × E) × (E × E),
          cancel q.1 q.2.1 q.2.2 ∂(τ.prod (base.prod volume))) =
          ∫ au : E × E, ∫ z, cancel z au.1 au.2 ∂τ
            ∂(base.prod volume) := by
        simpa only [Function.comp_apply, Prod.swap_prod_mk] using
          integral_prod_symm
            (fun q : (E × E) × (E × E) ↦ cancel q.1 q.2.1 q.2.2) hcancel
      _ = ∫ _au : E × E, 0 ∂(base.prod volume) := by
        apply integral_congr_ae
        filter_upwards with au
        exact hcancelFiberZero au.1 au.2
      _ = 0 :=
        MeasureTheory.integral_zero (E × E) ℝ
  have htotalDecomp :
      (∫ q : (E × E) × (E × E),
        full q.1 q.2.1 q.2.2 ∂(τ.prod (base.prod volume))) =
        (∫ q : (E × E) × (E × E),
          remO q.1 q.2.1 q.2.2 ∂(τ.prod (base.prod volume))) +
        ∫ q : (E × E) × (E × E),
          remG q.1 q.2.1 q.2.2 ∂(τ.prod (base.prod volume)) := by
    calc
      (∫ q : (E × E) × (E × E),
          full q.1 q.2.1 q.2.2 ∂(τ.prod (base.prod volume))) =
          ∫ q : (E × E) × (E × E),
            cancel q.1 q.2.1 q.2.2 +
              (remO q.1 q.2.1 q.2.2 + remG q.1 q.2.1 q.2.2)
            ∂(τ.prod (base.prod volume)) := by
        apply integral_congr_ae
        filter_upwards with q
        exact hpoint q.1 q.2.1 q.2.2
      _ = (∫ q : (E × E) × (E × E),
            cancel q.1 q.2.1 q.2.2 ∂(τ.prod (base.prod volume))) +
          ∫ q : (E × E) × (E × E),
            (remO q.1 q.2.1 q.2.2 + remG q.1 q.2.1 q.2.2)
            ∂(τ.prod (base.prod volume)) :=
        integral_add hcancel (hremO.add hremG)
      _ = (∫ q : (E × E) × (E × E),
            remO q.1 q.2.1 q.2.2 ∂(τ.prod (base.prod volume))) +
          ∫ q : (E × E) × (E × E),
            remG q.1 q.2.1 q.2.2 ∂(τ.prod (base.prod volume)) := by
        rw [hcancelTotalZero, zero_add, integral_add hremO hremG]
  let HO : E × E → ℝ := fun au ↦ ∫ z, remO z au.1 au.2 ∂τ
  let HG : E × E → ℝ := fun au ↦ ∫ z, remG z au.1 au.2 ∂τ
  have hHO : Integrable HO (base.prod volume) := by
    simpa only [HO, Function.comp_apply, Prod.swap_prod_mk] using
      hremO.swap.integral_prod_left
  have hHG : Integrable HG (base.prod volume) := by
    simpa only [HG, Function.comp_apply, Prod.swap_prod_mk] using
      hremG.swap.integral_prod_left
  have htotalO :
      (∫ q : (E × E) × (E × E),
        remO q.1 q.2.1 q.2.2 ∂(τ.prod (base.prod volume))) =
        ∫ a, ∫ u, ∫ z, remO z a u ∂τ ∂volume ∂base := by
    calc
      (∫ q : (E × E) × (E × E),
          remO q.1 q.2.1 q.2.2 ∂(τ.prod (base.prod volume))) =
          ∫ au : E × E, HO au ∂(base.prod volume) := by
        simpa only [HO, Function.comp_apply, Prod.swap_prod_mk] using
          integral_prod_symm
            (fun q : (E × E) × (E × E) ↦ remO q.1 q.2.1 q.2.2) hremO
      _ = ∫ a, ∫ u, HO (a, u) ∂volume ∂base :=
        integral_prod HO hHO
      _ = ∫ a, ∫ u, ∫ z, remO z a u ∂τ ∂volume ∂base := by
        rfl
  have htotalG :
      (∫ q : (E × E) × (E × E),
        remG q.1 q.2.1 q.2.2 ∂(τ.prod (base.prod volume))) =
        ∫ a, ∫ u, ∫ z, remG z a u ∂τ ∂volume ∂base := by
    calc
      (∫ q : (E × E) × (E × E),
          remG q.1 q.2.1 q.2.2 ∂(τ.prod (base.prod volume))) =
          ∫ au : E × E, HG au ∂(base.prod volume) := by
        simpa only [HG, Function.comp_apply, Prod.swap_prod_mk] using
          integral_prod_symm
            (fun q : (E × E) × (E × E) ↦ remG q.1 q.2.1 q.2.2) hremG
      _ = ∫ a, ∫ u, HG (a, u) ∂volume ∂base :=
        integral_prod HG hHG
      _ = ∫ a, ∫ u, ∫ z, remG z a u ∂τ ∂volume ∂base := by
        rfl
  have hfullIter :
      (∫ z, ∫ a, ∫ u, full z a u ∂volume ∂base ∂τ) =
        ∫ q : (E × E) × (E × E),
          full q.1 q.2.1 q.2.2 ∂(τ.prod (base.prod volume)) := by
    calc
      (∫ z, ∫ a, ∫ u, full z a u ∂volume ∂base ∂τ) =
          ∫ z, ∫ au : E × E, full z au.1 au.2
            ∂(base.prod volume) ∂τ := by
        apply integral_congr_ae
        filter_upwards [hfull.prod_right_ae] with z hz
        exact (integral_prod
          (fun au : E × E ↦ full z au.1 au.2) hz).symm
      _ = ∫ q : (E × E) × (E × E),
          full q.1 q.2.1 q.2.2 ∂(τ.prod (base.prod volume)) :=
        (integral_prod
          (fun q : (E × E) × (E × E) ↦ full q.1 q.2.1 q.2.2) hfull).symm
  have htranslated :=
    bentkus_smallAngle_rotationCoordinate_eq_translatedDensityContraction
      hXm hX3 h_indep hX0 hidentity k hk α hsin A hAconv hε
  have htranslated' :
      (∫ ω, (fderiv ℝ (convexSetCutoff A ε)
          ((p • UO ω + s • VG ω) + (p • O ω + s • G ω)))
          ((-s) • O ω + p • G ω) ∂ρ) =
        ∫ z, ∫ a, ∫ u, full z a u ∂volume ∂base ∂τ := by
    dsimp only [E, ρ, S, hS, e, P, B, UO, VG, U, O, G, Z, τ, γ, ν,
      θ, p, s, q, T, L, vO, wO, full, base] at htranslated ⊢
    exact htranslated
  change
    (∫ ω, (fderiv ℝ (convexSetCutoff A ε)
        ((p • UO ω + s • VG ω) + (p • O ω + s • G ω)))
        ((-s) • O ω + p • G ω) ∂ρ) =
      ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, ∫ z,
        ((∫ a, ∫ u, RO t r z a u ∂volume ∂base) +
          ∫ a, ∫ u, RG t r z a u ∂volume ∂base) ∂τ
  calc
    _ = ∫ z, ∫ a, ∫ u, full z a u ∂volume ∂base ∂τ :=
      htranslated'
    _ = ∫ q : (E × E) × (E × E),
        full q.1 q.2.1 q.2.2 ∂(τ.prod (base.prod volume)) :=
      hfullIter
    _ = (∫ q : (E × E) × (E × E),
          remO q.1 q.2.1 q.2.2 ∂(τ.prod (base.prod volume))) +
        ∫ q : (E × E) × (E × E),
          remG q.1 q.2.1 q.2.2 ∂(τ.prod (base.prod volume)) :=
      htotalDecomp
    _ = (∫ a, ∫ u, ∫ z, remO z a u ∂τ ∂volume ∂base) +
        ∫ a, ∫ u, ∫ z, remG z a u ∂τ ∂volume ∂base :=
      congrArg₂ (· + ·) htotalO htotalG
    _ = _ := hremainders'.2.2.2.2

/-- Conditional triangle inequality for the two signed small-angle remainder branches. -/
private theorem abs_twoInterval_triple_add_le_conditional_abs
    {Z A U : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace U]
    {τ : Measure Z} {κ : Measure A} {υ : Measure U}
    [SFinite τ] [SFinite κ] [SFinite υ]
    (F G : ℝ → ℝ → Z → A → U → ℝ)
    (hF : let I := volume.restrict (Set.uIoc (0 : ℝ) 1)
      Integrable (fun q : ((((ℝ × ℝ) × Z) × A) × U) ↦
        F q.1.1.1.1 q.1.1.1.2 q.1.1.2 q.1.2 q.2)
        ((((I.prod I).prod τ).prod κ).prod υ))
    (hG : let I := volume.restrict (Set.uIoc (0 : ℝ) 1)
      Integrable (fun q : ((((ℝ × ℝ) × Z) × A) × U) ↦
        G q.1.1.1.1 q.1.1.1.2 q.1.1.2 q.1.2 q.2)
        ((((I.prod I).prod τ).prod κ).prod υ)) :
    |∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, ∫ z,
        ((∫ a, ∫ u, F t r z a u ∂υ ∂κ) +
          ∫ a, ∫ u, G t r z a u ∂υ ∂κ) ∂τ| ≤
      ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
        ((∫ z, ∫ a, |∫ u, F t r z a u ∂υ| ∂κ ∂τ) +
          ∫ z, ∫ a, |∫ u, G t r z a u ∂υ| ∂κ ∂τ) := by
  let I := volume.restrict (Set.uIoc (0 : ℝ) 1)
  let Fu : (((ℝ × ℝ) × Z) × A) → ℝ := fun q ↦
    ∫ u, F q.1.1.1 q.1.1.2 q.1.2 q.2 u ∂υ
  let Gu : (((ℝ × ℝ) × Z) × A) → ℝ := fun q ↦
    ∫ u, G q.1.1.1 q.1.1.2 q.1.2 q.2 u ∂υ
  let Fs : (ℝ × ℝ) × Z → ℝ := fun q ↦ ∫ a, Fu (q, a) ∂κ
  let Gs : (ℝ × ℝ) × Z → ℝ := fun q ↦ ∫ a, Gu (q, a) ∂κ
  let Fm : (ℝ × ℝ) × Z → ℝ := fun q ↦ ∫ a, |Fu (q, a)| ∂κ
  let Gm : (ℝ × ℝ) × Z → ℝ := fun q ↦ ∫ a, |Gu (q, a)| ∂κ
  let S : ℝ × ℝ → ℝ := fun tr ↦ ∫ z, Fs (tr, z) + Gs (tr, z) ∂τ
  let MF : ℝ × ℝ → ℝ := fun tr ↦ ∫ z, Fm (tr, z) ∂τ
  let MG : ℝ × ℝ → ℝ := fun tr ↦ ∫ z, Gm (tr, z) ∂τ
  let M : ℝ × ℝ → ℝ := MF + MG
  have hFu : Integrable Fu (((I.prod I).prod τ).prod κ) := by
    simpa only [I, Fu] using hF.integral_prod_left
  have hGu : Integrable Gu (((I.prod I).prod τ).prod κ) := by
    simpa only [I, Gu] using hG.integral_prod_left
  have hFs : Integrable Fs ((I.prod I).prod τ) := by
    simpa only [Fs] using hFu.integral_prod_left
  have hGs : Integrable Gs ((I.prod I).prod τ) := by
    simpa only [Gs] using hGu.integral_prod_left
  have hFm : Integrable Fm ((I.prod I).prod τ) := by
    simpa only [Fm, Real.norm_eq_abs] using hFu.norm.integral_prod_left
  have hGm : Integrable Gm ((I.prod I).prod τ) := by
    simpa only [Gm, Real.norm_eq_abs] using hGu.norm.integral_prod_left
  have hS : Integrable S (I.prod I) := by
    simpa only [S, Pi.add_apply] using (hFs.add hGs).integral_prod_left
  have hMF : Integrable MF (I.prod I) := by
    simpa only [MF] using hFm.integral_prod_left
  have hMG : Integrable MG (I.prod I) := by
    simpa only [MG] using hGm.integral_prod_left
  have hM : Integrable M (I.prod I) := hMF.add hMG
  have hpoint : ∀ᵐ tr ∂(I.prod I), |S tr| ≤ M tr := by
    filter_upwards [hFm.prod_right_ae, hGm.prod_right_ae] with tr hFtr hGtr
    rw [← Real.norm_eq_abs]
    calc
      ‖∫ z, Fs (tr, z) + Gs (tr, z) ∂τ‖ ≤
          ∫ z, Fm (tr, z) + Gm (tr, z) ∂τ := by
        apply norm_integral_le_of_norm_le (hFtr.add hGtr)
        filter_upwards with z
        dsimp only [Fs, Gs, Fm, Gm]
        rw [Real.norm_eq_abs]
        exact (abs_add_le _ _).trans
          (add_le_add abs_integral_le_integral_abs abs_integral_le_integral_abs)
      _ = M tr := by
        rw [integral_add hFtr hGtr]
        rfl
  have hprod : |∫ tr, S tr ∂(I.prod I)| ≤ ∫ tr, M tr ∂(I.prod I) := by
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le hM hpoint
  change
    |∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, S (t, r)| ≤
      ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, M (t, r)
  simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp only [zero_le_one, if_true, one_smul]
  rw [← integral_prod S hS, ← integral_prod M hM]
  exact hprod

/-- Bentkus (3.13) at one small angle, in the public coordinate-integrand form. -/
theorem bentkus_smallAngle_rotationCoordinate_le
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
    (α : ℝ) (hsin : 0 < Real.sin α) (hcos : 0 < Real.cos α)
    (A : Set (EuclideanSpace ℝ (Fin d))) (hAclosed : IsClosed A)
    (hAconv : Convexity.IsConvexSet ℝ A) {ε : ℝ} (hε : 0 < ε) :
    let ρ := bentkusReplacementMeasure μ X
    let βrem := ∑ i : Fin n, ∫ ω, ‖X (k.succAbove i) ω‖ ^ 3 ∂μ
    let βk := ∫ ω, ‖replacementOriginal (d := d) k ω‖ ^ 3 ∂ρ
    |∫ ω, bentkusRotationCoordinateIntegrand A ε k α ω ∂ρ| ≤
      (61440 / ε ^ 2) * (d : ℝ) ^ (1 / 4 : ℝ) *
        (C * βrem + ε) * Real.cos α * βk := by
  let E := EuclideanSpace ℝ (Fin d)
  let ρ := bentkusReplacementMeasure μ X
  let S := bentkusLeaveOneOutCovarianceMatrix μ X k
  have hS : S.PosDef :=
    bentkusLeaveOneOutCovarianceMatrix_posDef_of_integral_norm_sq_lt_quarter
      hX3 h_indep hX0 hidentity k hk
  let e := bentkusWhiteningEquiv S hS
  let P := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  let UO := bentkusLeaveOneOut
    (fun i ↦ replacementOriginal (d := d) i) k
  let VG := bentkusLeaveOneOut
    (fun i ↦ replacementGaussian (d := d) i) k
  let U := bentkusLeaveOneOut X k
  let O := replacementOriginal (d := d) k
  let G := replacementGaussian (d := d) k
  let Z := fun ω ↦ (O ω, G ω)
  let τ := ρ.map Z
  let γ := stdGaussian E
  let ν := μ.map (fun ω ↦ e (U ω))
  let θ := (Real.sqrt 2)⁻¹
  let p := Real.cos α
  let s := Real.sin α
  let q := θ * s
  let T := ((γ.map (fun y ↦ q • y)).prod ν).map
    (fun z : E × E ↦ p • z.2 + z.1)
  let L := q • P
  let vO := fun z : E × E ↦ -((1 / θ) • B z.2)
  let wO := fun z : E × E ↦ -((p / (θ * s)) • B z.1)
  let vG := wO
  let wG := vO
  let RO := fun (t r : ℝ) (z : E × E) (a u : E) ↦
    (-s) * (convexSetCutoffDirectionalPullback A ε a z.1 L u *
      standardGaussianDensityD2
        (u + r • (vO z + t • wO z))
        (wO z) (vO z + t • wO z))
  let RG := fun (t r : ℝ) (z : E × E) (a u : E) ↦
    p * (convexSetCutoffDirectionalPullback A ε a z.2 L u *
      standardGaussianDensityD2
        (u + r • (vG z + t • wG z))
        (wG z) (vG z + t • wG z))
  let βrem := ∑ i : Fin n, ∫ ω, ‖X (k.succAbove i) ω‖ ^ 3 ∂μ
  let βk := ∫ ω, ‖O ω‖ ^ 3 ∂ρ
  let MO := fun (t r : ℝ) ↦ ∫ z, s * ∫ a,
    |∫ u, convexSetCutoffDirectionalPullback A ε a z.1 L u *
      standardGaussianDensityD2
        (u + r • (vO z + t • wO z)) (wO z) (vO z + t • wO z)
      ∂volume| ∂(T.map P) ∂τ
  let MG := fun (t r : ℝ) ↦ ∫ z, p * ∫ a,
    |∫ u, convexSetCutoffDirectionalPullback A ε a z.2 L u *
      standardGaussianDensityD2
        (u + r • (vG z + t • wG z)) (wG z) (vG z + t • wG z)
      ∂volume| ∂(T.map P) ∂τ
  let I := volume.restrict (Set.uIoc (0 : ℝ) 1)
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
    exact Measure.isProbabilityMeasure_map
      (e.continuous.measurable.comp hUmeas).aemeasurable
  letI : IsProbabilityMeasure (γ.map (fun y ↦ q • y)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure T := by
    dsimp only [T]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (T.map P) :=
    Measure.isProbabilityMeasure_map P.continuous.measurable.aemeasurable
  have hZmeas : Measurable Z := by
    dsimp only [Z, O, G]
    exact ((measurable_pi_apply k).comp measurable_fst).prodMk
      ((measurable_pi_apply k).comp measurable_snd)
  letI : IsProbabilityMeasure τ := by
    dsimp only [τ]
    exact Measure.isProbabilityMeasure_map hZmeas.aemeasurable
  have hs : 0 < s := by simpa only [s] using hsin
  have hp : 0 < p := by simpa only [p] using hcos
  have heq := bentkus_smallAngle_rotationCoordinate_eq_twoShiftRemainders
    hXm hX3 h_indep hX0 hidentity k hk α hsin A hAconv hε
  have heqRaw :
      (∫ ω, (fderiv ℝ (convexSetCutoff A ε)
          ((p • UO ω + s • VG ω) + (p • O ω + s • G ω)))
          ((-s) • O ω + p • G ω) ∂ρ) =
        ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, ∫ z,
          ((∫ a, ∫ u, RO t r z a u ∂volume ∂(T.map P)) +
            ∫ a, ∫ u, RG t r z a u ∂volume ∂(T.map P)) ∂τ := by
    dsimp only [E, ρ, S, hS, e, P, B, UO, VG, U, O, G, Z, τ, γ, ν,
      θ, p, s, q, T, L, vO, wO, vG, wG, RO, RG] at heq ⊢
    exact heq
  have heq' :
      (∫ ω, bentkusRotationCoordinateIntegrand A ε k α ω ∂ρ) =
        ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, ∫ z,
          ((∫ a, ∫ u, RO t r z a u ∂volume ∂(T.map P)) +
            ∫ a, ∫ u, RG t r z a u ∂volume ∂(T.map P)) ∂τ := by
    calc
      (∫ ω, bentkusRotationCoordinateIntegrand A ε k α ω ∂ρ) =
          ∫ ω, (fderiv ℝ (convexSetCutoff A ε)
            ((p • UO ω + s • VG ω) + (p • O ω + s • G ω)))
            ((-s) • O ω + p • G ω) ∂ρ := by
        apply integral_congr_ae
        filter_upwards with ω
        dsimp only [bentkusRotationCoordinateIntegrand, UO, VG, O, G,
          bentkusRotated, bentkusRotatedDeriv, p, s]
        rw [bentkusRotatedSum_eq_leaveOneOut_add α
          (fun i ↦ replacementOriginal (d := d) i)
          (fun i ↦ replacementGaussian (d := d) i) k ω]
        rfl
      _ = _ := heqRaw
  have hraw := bentkus_smallAngle_D2_remainderKernels_integrable
    hXm hX3 h_indep hX0 hidentity k hk α hsin A hAconv hε
  have hraw' :
      Integrable (fun y : ((((ℝ × ℝ) × (E × E)) × E) × E) ↦
        convexSetCutoffDirectionalPullback A ε y.1.2 y.1.1.2.1 L y.2 *
          standardGaussianDensityD2
            (y.2 + y.1.1.1.2 •
              (vO y.1.1.2 + y.1.1.1.1 • wO y.1.1.2))
            (wO y.1.1.2)
            (vO y.1.1.2 + y.1.1.1.1 • wO y.1.1.2))
        ((((I.prod I).prod τ).prod (T.map P)).prod volume) ∧
      Integrable (fun y : ((((ℝ × ℝ) × (E × E)) × E) × E) ↦
        convexSetCutoffDirectionalPullback A ε y.1.2 y.1.1.2.2 L y.2 *
          standardGaussianDensityD2
            (y.2 + y.1.1.1.2 •
              (vG y.1.1.2 + y.1.1.1.1 • wG y.1.1.2))
            (wG y.1.1.2)
            (vG y.1.1.2 + y.1.1.1.1 • wG y.1.1.2))
        ((((I.prod I).prod τ).prod (T.map P)).prod volume) := by
    simpa only [E, ρ, S, hS, e, P, B, U, O, G, Z, τ, γ, ν, θ, p, s, q,
      T, L, vO, wO, vG, wG, I] using hraw
  have hRO : Integrable (fun y : ((((ℝ × ℝ) × (E × E)) × E) × E) ↦
      RO y.1.1.1.1 y.1.1.1.2 y.1.1.2 y.1.2 y.2)
      ((((I.prod I).prod τ).prod (T.map P)).prod volume) := by
    simpa only [RO] using hraw'.1.const_mul (-s)
  have hRG : Integrable (fun y : ((((ℝ × ℝ) × (E × E)) × E) × E) ↦
      RG y.1.1.1.1 y.1.1.1.2 y.1.1.2 y.1.2 y.2)
      ((((I.prod I).prod τ).prod (T.map P)).prod volume) := by
    simpa only [RG] using hraw'.2.const_mul p
  have hconditional := abs_twoInterval_triple_add_le_conditional_abs
    (τ := τ) (κ := T.map P) (υ := volume) RO RG
    (by simpa only [I] using hRO) (by simpa only [I] using hRG)
  have hconditional' :
      |∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, ∫ z,
          ((∫ a, ∫ u, RO t r z a u ∂volume ∂(T.map P)) +
            ∫ a, ∫ u, RG t r z a u ∂volume ∂(T.map P)) ∂τ| ≤
        ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, MO t r + MG t r := by
    simpa only [RO, RG, MO, MG, integral_const_mul, abs_mul, abs_neg,
      abs_of_pos hs, abs_of_pos hp] using hconditional
  have hmajor := bentkus_smallAngle_integrated_D2_majorant_le
    hC hIH hd hXm hX3 h_indep hX0 hidentity k hk α hsin hcos
      A hAclosed hAconv hε
  change
    |∫ ω, bentkusRotationCoordinateIntegrand A ε k α ω ∂ρ| ≤
      (61440 / ε ^ 2) * (d : ℝ) ^ (1 / 4 : ℝ) *
        (C * βrem + ε) * p * βk
  rw [heq']
  exact hconditional'.trans (by
    simpa only [E, ρ, S, hS, e, P, B, U, O, G, Z, τ, γ, ν, θ, p, s, q,
      T, L, vO, wO, vG, wG, βrem, βk, MO, MG] using hmajor)

end BentkusInduction

end ProbabilityTheory
