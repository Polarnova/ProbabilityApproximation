/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.ConvexGeometry.SquaredDistance
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Bentkus smooth cutoffs for convex sets

This file implements the distance cutoff used in Bentkus's smoothing argument. The scalar profile
is the piecewise quadratic profile from Bentkus (2003), Lemma 2.3; composing it with distance to a
closed nonempty convex set gives the cutoff recorded in Bentkus (2004), Lemma 2.2.
-/

open Set Topology

noncomputable section

namespace ProbabilityTheory

local instance {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

local instance {d : ℕ} :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.ofModule

private def positivePartSq (t : ℝ) : ℝ :=
  max t 0 ^ 2

/-- Bentkus's continuously differentiable scalar cutoff profile. -/
def bentkusProfile (t : ℝ) : ℝ :=
  1 - 2 * positivePartSq t + 4 * positivePartSq (t - 1 / 2) -
    2 * positivePartSq (t - 1)

/-- The derivative of `bentkusProfile`. -/
def bentkusProfileDeriv (t : ℝ) : ℝ :=
  -4 * max t 0 + 8 * max (t - 1 / 2) 0 - 4 * max (t - 1) 0

private lemma hasDerivAt_positivePartSq (t : ℝ) :
    HasDerivAt positivePartSq (2 * max t 0) t := by
  by_cases ht : t = 0
  · subst t
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    have hbig :
        (fun h : ℝ ↦ positivePartSq (0 + h) - positivePartSq 0 -
          h • (2 * max (0 : ℝ) 0)) =O[𝓝 0] (fun h : ℝ ↦ ‖h‖ ^ 2) := by
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards with h
      by_cases hh : h ≤ 0
      · simp [positivePartSq, max_eq_right hh, sq_nonneg]
      · have hh0 : 0 ≤ h := le_of_not_ge hh
        simp [positivePartSq, max_eq_left hh0, Real.norm_eq_abs, abs_of_nonneg hh0]
    exact hbig.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  · rcases lt_or_gt_of_ne ht with htneg | htpos
    · have heq : positivePartSq =ᶠ[𝓝 t] fun _ : ℝ ↦ 0 := by
        filter_upwards [Iio_mem_nhds htneg] with u hu
        change u < 0 at hu
        simp [positivePartSq, max_eq_right hu.le]
      rw [heq.hasDerivAt_iff]
      simpa [max_eq_right htneg.le] using hasDerivAt_const t (0 : ℝ)
    · have heq : positivePartSq =ᶠ[𝓝 t] fun u : ℝ ↦ u ^ 2 := by
        filter_upwards [Ioi_mem_nhds htpos] with u hu
        change 0 < u at hu
        simp [positivePartSq, max_eq_left hu.le]
      rw [heq.hasDerivAt_iff]
      simpa [max_eq_left htpos.le] using hasDerivAt_pow 2 t

/-- The derivative formula for Bentkus's scalar profile. -/
lemma hasDerivAt_bentkusProfile (t : ℝ) :
    HasDerivAt bentkusProfile (bentkusProfileDeriv t) t := by
  have h0 := (hasDerivAt_positivePartSq t).const_mul 2
  have h1 := (hasDerivAt_positivePartSq (t - 1 / 2)).comp t
    ((hasDerivAt_id t).sub_const (1 / 2))
  have h2 := (hasDerivAt_positivePartSq (t - 1)).comp t
    ((hasDerivAt_id t).sub_const 1)
  have h := (((hasDerivAt_const t (1 : ℝ)).sub h0).add (h1.const_mul 4)).sub
    (h2.const_mul 2)
  have hd : 0 - 2 * (2 * max t 0) + 4 * (2 * max (t - 1 / 2) 0 * 1) -
      2 * (2 * max (t - 1) 0 * 1) = bentkusProfileDeriv t := by
    simp [bentkusProfileDeriv]
    ring
  have hfun : bentkusProfile =ᶠ[𝓝 t]
      (((fun _ : ℝ ↦ 1) - fun y ↦ 2 * positivePartSq y) +
        fun y ↦ 4 * (positivePartSq ∘ fun x ↦ id x - 1 / 2) y) -
        fun y ↦ 2 * (positivePartSq ∘ fun x ↦ id x - 1) y := by
    filter_upwards with u
    simp [bentkusProfile, Function.comp_apply]
  exact (HasDerivAt.congr_deriv h hd).congr_of_eventuallyEq hfun

/-- The Bentkus profile is continuously differentiable. -/
lemma differentiable_bentkusProfile : Differentiable ℝ bentkusProfile :=
  fun t ↦ (hasDerivAt_bentkusProfile t).differentiableAt

private lemma bentkusProfile_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    bentkusProfile t = 1 := by
  have h1 : t - 1 / 2 ≤ 0 := by linarith
  have h2 : t - 1 ≤ 0 := by linarith
  simp only [bentkusProfile, positivePartSq]
  rw [max_eq_right ht, max_eq_right h1, max_eq_right h2]
  ring

private lemma bentkusProfile_of_mem_firstHalf {t : ℝ} (h0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    bentkusProfile t = 1 - 2 * t ^ 2 := by
  have h1 : t - 1 / 2 ≤ 0 := sub_nonpos.mpr ht
  have h2 : t - 1 ≤ 0 := by linarith
  simp only [bentkusProfile, positivePartSq]
  rw [max_eq_left h0, max_eq_right h1, max_eq_right h2]
  ring

private lemma bentkusProfile_of_mem_secondHalf {t : ℝ} (h0 : 1 / 2 ≤ t) (ht : t ≤ 1) :
    bentkusProfile t = 2 * (1 - t) ^ 2 := by
  have ht0 : 0 ≤ t := by linarith
  have h10 : 0 ≤ t - 1 / 2 := sub_nonneg.mpr h0
  have h2 : t - 1 ≤ 0 := sub_nonpos.mpr ht
  simp only [bentkusProfile, positivePartSq]
  rw [max_eq_left ht0, max_eq_left h10, max_eq_right h2]
  ring

/-- The Bentkus profile vanishes on `[1, ∞)`, including the endpoint. -/
lemma bentkusProfile_of_one_le {t : ℝ} (ht : 1 ≤ t) : bentkusProfile t = 0 := by
  have ht0 : 0 ≤ t := by linarith
  have h10 : 0 ≤ t - 1 / 2 := by linarith
  have h20 : 0 ≤ t - 1 := sub_nonneg.mpr ht
  simp only [bentkusProfile, positivePartSq]
  rw [max_eq_left ht0, max_eq_left h10, max_eq_left h20]
  ring

/-- The Bentkus scalar profile takes values in the unit interval. -/
lemma bentkusProfile_mem_unitInterval (t : ℝ) :
    0 ≤ bentkusProfile t ∧ bentkusProfile t ≤ 1 := by
  by_cases h0 : t ≤ 0
  · rw [bentkusProfile_of_nonpos h0]
    norm_num
  · have ht0 : 0 ≤ t := by linarith
    by_cases hh : t ≤ 1 / 2
    · rw [bentkusProfile_of_mem_firstHalf ht0 hh]
      constructor
      · nlinarith [sq_nonneg (t - 1 / 2)]
      · nlinarith [sq_nonneg t]
    · have hh0 : 1 / 2 ≤ t := by linarith
      by_cases h1 : t ≤ 1
      · rw [bentkusProfile_of_mem_secondHalf hh0 h1]
        constructor
        · positivity
        · nlinarith [sq_nonneg (t - 1 / 2), sq_nonneg (1 - t)]
      · rw [bentkusProfile_of_one_le (by linarith)]
        norm_num

private def bentkusTent (t : ℝ) : ℝ :=
  max 0 (min t (1 - t))

private lemma bentkusProfileDeriv_eq_tent (t : ℝ) :
    bentkusProfileDeriv t = -4 * bentkusTent t := by
  by_cases h0 : t ≤ 0
  · have h1 : t - 1 / 2 ≤ 0 := by linarith
    have h2 : t - 1 ≤ 0 := by linarith
    have hmin : min t (1 - t) = t := min_eq_left (by linarith)
    rw [bentkusProfileDeriv, max_eq_right h0, max_eq_right h1, max_eq_right h2,
      bentkusTent, hmin, max_eq_left h0]
    ring
  · have ht0 : 0 ≤ t := by linarith
    by_cases hh : t ≤ 1 / 2
    · have h1 : t - 1 / 2 ≤ 0 := sub_nonpos.mpr hh
      have h2 : t - 1 ≤ 0 := by linarith
      have hmin : min t (1 - t) = t := min_eq_left (by linarith)
      rw [bentkusProfileDeriv, max_eq_left ht0, max_eq_right h1, max_eq_right h2,
        bentkusTent, hmin, max_eq_right ht0]
      ring
    · have hh0 : 1 / 2 ≤ t := by linarith
      by_cases h1 : t ≤ 1
      · have hhalf : 0 ≤ t - 1 / 2 := sub_nonneg.mpr hh0
        have hone : t - 1 ≤ 0 := sub_nonpos.mpr h1
        have hmin : min t (1 - t) = 1 - t := min_eq_right (by linarith)
        have hnonneg : 0 ≤ 1 - t := sub_nonneg.mpr h1
        rw [bentkusProfileDeriv, max_eq_left ht0, max_eq_left hhalf, max_eq_right hone,
          bentkusTent, hmin, max_eq_right hnonneg]
        ring
      · have ht1 : 1 ≤ t := by linarith
        have hhalf : 0 ≤ t - 1 / 2 := by linarith
        have hone : 0 ≤ t - 1 := sub_nonneg.mpr ht1
        have hmin : min t (1 - t) = 1 - t := min_eq_right (by linarith)
        have hneg : 1 - t ≤ 0 := sub_nonpos.mpr ht1
        rw [bentkusProfileDeriv, max_eq_left ht0, max_eq_left hhalf, max_eq_left hone,
          bentkusTent, hmin, max_eq_left hneg]
        ring

private lemma lipschitzWith_one_sub : LipschitzWith 1 (fun t : ℝ ↦ 1 - t) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  have h : (1 - x) - (1 - y) = -(x - y) := by ring
  rw [h, abs_neg]

private lemma lipschitzWith_bentkusTent : LipschitzWith 1 bentkusTent := by
  have hmin : LipschitzWith 1 (fun t : ℝ ↦ min t (1 - t)) := by
    simpa using LipschitzWith.id.min lipschitzWith_one_sub
  exact hmin.const_max 0

private lemma bentkusTent_nonneg (t : ℝ) : 0 ≤ bentkusTent t :=
  le_max_left _ _

private lemma bentkusTent_le_half (t : ℝ) : bentkusTent t ≤ 1 / 2 := by
  by_cases hmin : min t (1 - t) ≤ 0
  · rw [bentkusTent, max_eq_left hmin]
    norm_num
  · rw [bentkusTent, max_eq_right (le_of_not_ge hmin)]
    have hleft := min_le_left t (1 - t)
    have hright := min_le_right t (1 - t)
    linarith

private lemma bentkusTent_le_abs (t : ℝ) : bentkusTent t ≤ |t| := by
  by_cases ht : t ≤ 0
  · have hmin : min t (1 - t) ≤ 0 := (min_le_left _ _).trans ht
    rw [bentkusTent, max_eq_left hmin]
    exact abs_nonneg _
  · rw [abs_of_nonneg (by linarith)]
    rw [bentkusTent]
    exact max_le (by linarith) (min_le_left _ _)

/-- The scalar profile derivative is bounded by `2`. -/
lemma abs_bentkusProfileDeriv_le_two (t : ℝ) : |bentkusProfileDeriv t| ≤ 2 := by
  rw [bentkusProfileDeriv_eq_tent, abs_mul, abs_of_nonneg (bentkusTent_nonneg t)]
  norm_num
  nlinarith [bentkusTent_le_half t]

/-- The scalar profile derivative vanishes linearly at the left endpoint. -/
lemma abs_bentkusProfileDeriv_le_four_mul_abs (t : ℝ) :
    |bentkusProfileDeriv t| ≤ 4 * |t| := by
  rw [bentkusProfileDeriv_eq_tent, abs_mul, abs_of_nonneg (bentkusTent_nonneg t)]
  norm_num
  exact bentkusTent_le_abs t

/-- The derivative of the scalar profile is `4`-Lipschitz. -/
lemma bentkusProfileDeriv_lipschitz (t u : ℝ) :
    |bentkusProfileDeriv t - bentkusProfileDeriv u| ≤ 4 * |t - u| := by
  have h := lipschitzWith_bentkusTent.norm_sub_le t u
  rw [bentkusProfileDeriv_eq_tent, bentkusProfileDeriv_eq_tent]
  have heq : -4 * bentkusTent t - -4 * bentkusTent u =
      -4 * (bentkusTent t - bentkusTent u) := by ring
  rw [heq, abs_mul]
  norm_num
  simpa only [NNReal.coe_one, one_mul, Real.norm_eq_abs] using h

/-- Bentkus's distance cutoff for a set at smoothing radius `ε`. -/
def bentkusCutoff {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  bentkusProfile (Metric.infDist x s / ε)

/-- The Fréchet derivative field of the Bentkus distance cutoff. On the set it is zero; outside
the set it is the scalar-profile derivative times the normalized metric-projection residual. -/
noncomputable def bentkusCutoffFDeriv {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (hclosed : IsClosed s) (hne : s.Nonempty) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := by
  classical
  exact if x ∈ s then 0 else
    (ε⁻¹ * bentkusProfileDeriv (Metric.infDist x s / ε)) •
      ((Metric.infDist x s)⁻¹ •
        ((innerSL ℝ) (x - metricProjection s hclosed hne x)))

@[simp]
lemma bentkusCutoffFDeriv_of_mem {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))} {ε : ℝ}
    (hclosed : IsClosed s) (hne : s.Nonempty) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ s) :
    bentkusCutoffFDeriv s ε hclosed hne x = 0 := by
  classical
  simp [bentkusCutoffFDeriv, hx]

lemma bentkusCutoffFDeriv_of_notMem {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))} {ε : ℝ}
    (hclosed : IsClosed s) (hne : s.Nonempty) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∉ s) :
    bentkusCutoffFDeriv s ε hclosed hne x =
      (ε⁻¹ * bentkusProfileDeriv (Metric.infDist x s / ε)) •
        ((Metric.infDist x s)⁻¹ •
          ((innerSL ℝ) (x - metricProjection s hclosed hne x))) := by
  classical
  simp [bentkusCutoffFDeriv, hx]

/-- The Bentkus cutoff is Fréchet differentiable everywhere. -/
lemma hasFDerivAt_bentkusCutoff {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))} {ε : ℝ}
    (hclosed : IsClosed s) (hne : s.Nonempty) (hconv : Convexity.IsConvexSet ℝ s)
    (hε : 0 < ε) (x : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (bentkusCutoff s ε) (bentkusCutoffFDeriv s ε hclosed hne x) x := by
  by_cases hx : x ∈ s
  · have hs := hasFDerivAt_squaredInfDist hclosed hne hconv x
    have hraw := ((hs.mul_const (ε⁻¹ ^ 2)).const_mul 2).const_sub 1
    have hfun : (fun y ↦ 1 - 2 * (Metric.infDist y s / ε) ^ 2) =
        fun y ↦ 1 - 2 * (Metric.infDist y s ^ 2 * (ε⁻¹ ^ 2)) := by
      funext y
      simp only [div_eq_mul_inv]
      ring
    have hpoly : HasFDerivAt (fun y ↦ 1 - 2 * (Metric.infDist y s / ε) ^ 2)
        (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) x := by
      rw [hfun]
      apply hraw.congr_fderiv
      rw [metricProjection_eq_self hclosed hne hconv hx]
      simp
    have hratio : Continuous (fun y ↦ Metric.infDist y s / ε) :=
      (Metric.continuous_infDist_pt s).div_const ε
    have hxratio : Metric.infDist x s / ε < 1 / 2 := by
      rw [Metric.infDist_zero_of_mem hx]
      norm_num
    have hevent : ∀ᶠ y in 𝓝 x, Metric.infDist y s / ε < 1 / 2 :=
      hratio.continuousAt.eventually_lt continuous_const.continuousAt hxratio
    have heq : bentkusCutoff s ε =ᶠ[𝓝 x]
        fun y ↦ 1 - 2 * (Metric.infDist y s / ε) ^ 2 := by
      filter_upwards [hevent] with y hy
      have hy0 : 0 ≤ Metric.infDist y s / ε :=
        div_nonneg Metric.infDist_nonneg hε.le
      rw [bentkusCutoff, bentkusProfile_of_mem_firstHalf hy0 hy.le]
    rw [bentkusCutoffFDeriv_of_mem hclosed hne hx]
    exact hpoly.congr_of_eventuallyEq heq
  · have hd := (hasFDerivAt_infDist_of_notMem hclosed hne hconv hx).mul_const ε⁻¹
    have hp := hasDerivAt_bentkusProfile (Metric.infDist x s / ε)
    have hcomp := hp.comp_hasFDerivAt x hd
    have hfun : bentkusCutoff s ε =
        bentkusProfile ∘ fun y ↦ Metric.infDist y s * ε⁻¹ := by
      funext y
      simp [bentkusCutoff, div_eq_mul_inv]
    rw [hfun]
    apply hcomp.congr_fderiv
    rw [bentkusCutoffFDeriv_of_notMem hclosed hne hx]
    simp [div_eq_mul_inv, smul_smul]
    ring_nf

/-- The Bentkus cutoff is differentiable everywhere. -/
lemma differentiable_bentkusCutoff {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))} {ε : ℝ}
    (hclosed : IsClosed s) (hne : s.Nonempty) (hconv : Convexity.IsConvexSet ℝ s)
    (hε : 0 < ε) : Differentiable ℝ (bentkusCutoff s ε) :=
  fun x ↦ (hasFDerivAt_bentkusCutoff hclosed hne hconv hε x).differentiableAt

/-- The Bentkus cutoff is continuous. -/
lemma continuous_bentkusCutoff {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) :
    Continuous (bentkusCutoff s ε) :=
  differentiable_bentkusProfile.continuous.comp
    ((Metric.continuous_infDist_pt s).div_const ε)

/-- The Bentkus cutoff is measurable. -/
lemma measurable_bentkusCutoff {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) :
    Measurable (bentkusCutoff s ε) :=
  (continuous_bentkusCutoff s ε).measurable

/-- The Bentkus cutoff is nonnegative. -/
lemma bentkusCutoff_nonneg {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ bentkusCutoff s ε x :=
  (bentkusProfile_mem_unitInterval _).1

/-- The Bentkus cutoff is at most one. -/
lemma bentkusCutoff_le_one {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : bentkusCutoff s ε x ≤ 1 :=
  (bentkusProfile_mem_unitInterval _).2

/-- The Bentkus cutoff equals one on the set. -/
lemma bentkusCutoff_eq_one_of_mem {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))} {ε : ℝ}
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ s) : bentkusCutoff s ε x = 1 := by
  rw [bentkusCutoff, Metric.infDist_zero_of_mem hx, zero_div,
    bentkusProfile_of_nonpos le_rfl]

/-- The Bentkus cutoff vanishes when distance is at least `ε`; equality at the boundary is
included. -/
lemma bentkusCutoff_eq_zero_of_le_infDist {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {ε : ℝ} (hε : 0 < ε)
    {x : EuclideanSpace ℝ (Fin d)} (hx : ε ≤ Metric.infDist x s) :
    bentkusCutoff s ε x = 0 := by
  apply bentkusProfile_of_one_le
  exact (le_div_iff₀ hε).2 (by simpa using hx)

private lemma abs_cutoffScalar_le {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) :
    |ε⁻¹ * bentkusProfileDeriv (r / ε)| ≤ 4 * r / ε ^ 2 := by
  calc
    |ε⁻¹ * bentkusProfileDeriv (r / ε)| =
        ε⁻¹ * |bentkusProfileDeriv (r / ε)| := by
      rw [abs_mul, abs_inv, abs_of_pos hε]
    _ ≤ ε⁻¹ * (4 * |r / ε|) :=
      mul_le_mul_of_nonneg_left (abs_bentkusProfileDeriv_le_four_mul_abs (r / ε))
        (inv_nonneg.mpr hε.le)
    _ = 4 * r / ε ^ 2 := by
      rw [abs_div, abs_of_nonneg hr, abs_of_pos hε]
      field_simp

private lemma abs_cutoffScalar_sub_le {ε r q : ℝ} (hε : 0 < ε) :
    |ε⁻¹ * bentkusProfileDeriv (r / ε) - ε⁻¹ * bentkusProfileDeriv (q / ε)| ≤
      4 * |r - q| / ε ^ 2 := by
  have hp := bentkusProfileDeriv_lipschitz (r / ε) (q / ε)
  have heq : ε⁻¹ * bentkusProfileDeriv (r / ε) -
      ε⁻¹ * bentkusProfileDeriv (q / ε) =
      ε⁻¹ * (bentkusProfileDeriv (r / ε) - bentkusProfileDeriv (q / ε)) := by
    ring
  rw [heq, abs_mul, abs_inv, abs_of_pos hε]
  calc
    ε⁻¹ * |bentkusProfileDeriv (r / ε) - bentkusProfileDeriv (q / ε)| ≤
        ε⁻¹ * (4 * |r / ε - q / ε|) :=
      mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hε.le)
    _ = 4 * |r - q| / ε ^ 2 := by
      have hdiv : r / ε - q / ε = (r - q) / ε := by ring
      rw [hdiv, abs_div, abs_of_pos hε]
      field_simp

/-- The Fréchet derivative of the Bentkus cutoff has norm at most `2 / ε`. -/
lemma norm_fderiv_bentkusCutoff_le {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    {ε : ℝ} (hclosed : IsClosed s) (hne : s.Nonempty)
    (hconv : Convexity.IsConvexSet ℝ s) (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ (bentkusCutoff s ε) x‖ ≤ 2 / ε := by
  rw [(hasFDerivAt_bentkusCutoff hclosed hne hconv hε x).fderiv]
  by_cases hx : x ∈ s
  · rw [bentkusCutoffFDeriv_of_mem hclosed hne hx, norm_zero]
    exact div_nonneg (by norm_num) hε.le
  · rw [bentkusCutoffFDeriv_of_notMem hclosed hne hx, norm_smul, norm_smul,
      innerSL_apply_norm]
    have hrpos : 0 < Metric.infDist x s := (hclosed.notMem_iff_infDist_pos hne).1 hx
    have hres : ‖x - metricProjection s hclosed hne x‖ = Metric.infDist x s := by
      rw [infDist_eq_dist_metricProjection s hclosed hne x, dist_eq_norm]
    rw [hres, norm_mul, norm_inv, norm_inv, Real.norm_of_nonneg hε.le,
      Real.norm_of_nonneg Metric.infDist_nonneg, inv_mul_cancel₀ (ne_of_gt hrpos),
      mul_one, Real.norm_eq_abs]
    have hp := abs_bentkusProfileDeriv_le_two (Metric.infDist x s / ε)
    calc
      ε⁻¹ * |bentkusProfileDeriv (Metric.infDist x s / ε)| ≤ ε⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hε.le)
      _ = 2 / ε := by field_simp

private lemma norm_normalize_sub_le_of_norm_le {d : ℕ}
    {a b : EuclideanSpace ℝ (Fin d)} (ha : 0 < ‖a‖) (hb : 0 < ‖b‖)
    (hab : ‖a‖ ≤ ‖b‖) :
    ‖NormedSpace.normalize a - NormedSpace.normalize b‖ ≤ ‖a - b‖ / ‖a‖ := by
  have hc : inner ℝ a b ≤ ‖a‖ * ‖b‖ := real_inner_le_norm _ _
  let k : ℝ := ‖a‖ / ‖b‖
  have hk0 : 0 ≤ k := div_nonneg ha.le hb.le
  have hk : k * ‖b‖ = ‖a‖ := div_mul_cancel₀ _ (ne_of_gt hb)
  have hbracket : 0 ≤ ‖b‖ * (‖b‖ + ‖a‖) - 2 * inner ℝ a b := by
    nlinarith
  have hprod : 0 ≤ (‖b‖ - ‖a‖) *
      (‖b‖ * (‖b‖ + ‖a‖) - 2 * inner ℝ a b) :=
    mul_nonneg (sub_nonneg.mpr hab) hbracket
  have hsquare : ‖a - k • b‖ ^ 2 ≤ ‖a - b‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real, inner_smul_right, norm_smul,
      Real.norm_of_nonneg hk0, hk]
    have hmul : 0 ≤ ‖b‖ * (‖a - b‖ ^ 2 - ‖a - k • b‖ ^ 2) := by
      rw [norm_sub_sq_real, norm_sub_sq_real, inner_smul_right, norm_smul,
        Real.norm_of_nonneg hk0, hk]
      nlinarith
    nlinarith
  have hnorm : ‖a - k • b‖ ≤ ‖a - b‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare
  have hscale : ‖a‖ • (NormedSpace.normalize a - NormedSpace.normalize b) =
      a - k • b := by
    rw [smul_sub, NormedSpace.norm_smul_normalize]
    congr 1
    rw [NormedSpace.normalize, smul_smul]
    congr 1
  have hnormscale : ‖a‖ * ‖NormedSpace.normalize a - NormedSpace.normalize b‖ ≤
      ‖a - b‖ := by
    rw [← Real.norm_of_nonneg ha.le, ← norm_smul, hscale]
    exact hnorm
  exact (le_div_iff₀ ha).2 (by simpa [mul_comm] using hnormscale)

private lemma norm_normalize_sub_le {d : ℕ} {a b : EuclideanSpace ℝ (Fin d)}
    (ha : 0 < ‖a‖) (hb : 0 < ‖b‖) :
    ‖NormedSpace.normalize a - NormedSpace.normalize b‖ ≤
      ‖a - b‖ / min ‖a‖ ‖b‖ := by
  rcases le_total ‖a‖ ‖b‖ with hab | hba
  · rw [min_eq_left hab]
    exact norm_normalize_sub_le_of_norm_le ha hb hab
  · rw [min_eq_right hba]
    simpa only [norm_sub_rev] using norm_normalize_sub_le_of_norm_le hb ha hba

private def distanceFDeriv {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d)))
    (hclosed : IsClosed s) (hne : s.Nonempty) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  (Metric.infDist x s)⁻¹ • ((innerSL ℝ) (x - metricProjection s hclosed hne x))

private lemma norm_distanceFDeriv {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hclosed : IsClosed s) (hne : s.Nonempty) (hconv : Convexity.IsConvexSet ℝ s)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∉ s) :
    ‖distanceFDeriv s hclosed hne x‖ = 1 := by
  have h := norm_fderiv_infDist_of_notMem hclosed hne hconv hx
  rw [(hasFDerivAt_infDist_of_notMem hclosed hne hconv hx).fderiv] at h
  exact h

private lemma norm_distanceFDeriv_sub_le {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hclosed : IsClosed s) (hne : s.Nonempty)
    (hconv : Convexity.IsConvexSet ℝ s) {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∉ s) (hy : y ∉ s) :
    ‖distanceFDeriv s hclosed hne x - distanceFDeriv s hclosed hne y‖ ≤
      ‖x - y‖ / min (Metric.infDist x s) (Metric.infDist y s) := by
  let a := x - metricProjection s hclosed hne x
  let b := y - metricProjection s hclosed hne y
  have hrx : Metric.infDist x s = ‖a‖ := by
    rw [infDist_eq_dist_metricProjection s hclosed hne x, dist_eq_norm]
  have hry : Metric.infDist y s = ‖b‖ := by
    rw [infDist_eq_dist_metricProjection s hclosed hne y, dist_eq_norm]
  have hax : 0 < ‖a‖ := by
    rw [← hrx]
    exact (hclosed.notMem_iff_infDist_pos hne).1 hx
  have hby : 0 < ‖b‖ := by
    rw [← hry]
    exact (hclosed.notMem_iff_infDist_pos hne).1 hy
  have hmapa : distanceFDeriv s hclosed hne x =
      (innerSL ℝ) (NormedSpace.normalize a) := by
    ext z
    simp [distanceFDeriv, NormedSpace.normalize, a, innerSL_apply_apply, smul_eq_mul, hrx]
  have hmapb : distanceFDeriv s hclosed hne y =
      (innerSL ℝ) (NormedSpace.normalize b) := by
    ext z
    simp [distanceFDeriv, NormedSpace.normalize, b, innerSL_apply_apply, smul_eq_mul, hry]
  rw [hmapa, hmapb]
  have hmapSub : (innerSL ℝ) (NormedSpace.normalize a) -
      (innerSL ℝ) (NormedSpace.normalize b) =
      (innerSL ℝ) (NormedSpace.normalize a - NormedSpace.normalize b) := by
    ext z
    simp [innerSL_apply_apply]
  rw [hmapSub, innerSL_apply_norm]
  calc
    ‖NormedSpace.normalize a - NormedSpace.normalize b‖ ≤
        ‖a - b‖ / min ‖a‖ ‖b‖ := norm_normalize_sub_le hax hby
    _ ≤ ‖x - y‖ / min ‖a‖ ‖b‖ := by
      apply div_le_div_of_nonneg_right
      · simpa only [a, b, NNReal.coe_one, one_mul] using
          (metricProjection_residual_lipschitzWith hclosed hne hconv).norm_sub_le x y
      · exact (lt_min hax hby).le
    _ = ‖x - y‖ / min (Metric.infDist x s) (Metric.infDist y s) := by
      rw [hrx, hry]

private lemma norm_bentkusCutoffFDeriv_sub_le_of_notMem_of_infDist_le {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {ε : ℝ} (hclosed : IsClosed s) (hne : s.Nonempty)
    (hconv : Convexity.IsConvexSet ℝ s) (hε : 0 < ε)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∉ s) (hy : y ∉ s)
    (hxy : Metric.infDist x s ≤ Metric.infDist y s) :
    ‖bentkusCutoffFDeriv s ε hclosed hne x - bentkusCutoffFDeriv s ε hclosed hne y‖ ≤
      8 * ‖x - y‖ / ε ^ 2 := by
  rw [bentkusCutoffFDeriv_of_notMem hclosed hne hx,
    bentkusCutoffFDeriv_of_notMem hclosed hne hy]
  change ‖(ε⁻¹ * bentkusProfileDeriv (Metric.infDist x s / ε)) •
      distanceFDeriv s hclosed hne x -
      (ε⁻¹ * bentkusProfileDeriv (Metric.infDist y s / ε)) •
        distanceFDeriv s hclosed hne y‖ ≤ _
  let ax := ε⁻¹ * bentkusProfileDeriv (Metric.infDist x s / ε)
  let ay := ε⁻¹ * bentkusProfileDeriv (Metric.infDist y s / ε)
  let Dx := distanceFDeriv s hclosed hne x
  let Dy := distanceFDeriv s hclosed hne y
  have hrx : 0 < Metric.infDist x s := (hclosed.notMem_iff_infDist_pos hne).1 hx
  have hdecomp : ax • Dx - ay • Dy = ax • (Dx - Dy) + (ax - ay) • Dy := by
    module
  rw [hdecomp]
  calc
    ‖ax • (Dx - Dy) + (ax - ay) • Dy‖ ≤
        ‖ax • (Dx - Dy)‖ + ‖(ax - ay) • Dy‖ := norm_add_le _ _
    _ = |ax| * ‖Dx - Dy‖ + |ax - ay| * ‖Dy‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (4 * Metric.infDist x s / ε ^ 2) * (‖x - y‖ / Metric.infDist x s) +
        (4 * |Metric.infDist x s - Metric.infDist y s| / ε ^ 2) * 1 := by
      apply add_le_add
      · apply mul_le_mul
        · exact abs_cutoffScalar_le hε Metric.infDist_nonneg
        · simpa only [Dx, Dy, min_eq_left hxy] using
            norm_distanceFDeriv_sub_le hclosed hne hconv hx hy
        · exact norm_nonneg _
        · positivity
      · apply mul_le_mul
        · exact abs_cutoffScalar_sub_le hε
        · exact le_of_eq (norm_distanceFDeriv hclosed hne hconv hy)
        · exact norm_nonneg _
        · positivity
    _ ≤ 4 * ‖x - y‖ / ε ^ 2 + 4 * ‖x - y‖ / ε ^ 2 := by
      apply add_le_add
      · rw [show (4 * Metric.infDist x s / ε ^ 2) *
            (‖x - y‖ / Metric.infDist x s) = 4 * ‖x - y‖ / ε ^ 2 by
          field_simp]
      · have hdist := (Metric.lipschitz_infDist_pt (s := s)).norm_sub_le x y
        have habs : |Metric.infDist x s - Metric.infDist y s| ≤ ‖x - y‖ := by
          simpa only [Real.norm_eq_abs, NNReal.coe_one, one_mul] using hdist
        calc
          (4 * |Metric.infDist x s - Metric.infDist y s| / ε ^ 2) * 1 =
              (4 / ε ^ 2) * |Metric.infDist x s - Metric.infDist y s| := by ring
          _ ≤ (4 / ε ^ 2) * ‖x - y‖ :=
            mul_le_mul_of_nonneg_left habs (div_nonneg (by norm_num) (sq_nonneg ε))
          _ = 4 * ‖x - y‖ / ε ^ 2 := by ring
    _ = 8 * ‖x - y‖ / ε ^ 2 := by ring

private lemma norm_bentkusCutoffFDeriv_sub_le_of_mem_of_notMem {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {ε : ℝ} (hclosed : IsClosed s) (hne : s.Nonempty)
    (hconv : Convexity.IsConvexSet ℝ s) (hε : 0 < ε)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ s) (hy : y ∉ s) :
    ‖bentkusCutoffFDeriv s ε hclosed hne x - bentkusCutoffFDeriv s ε hclosed hne y‖ ≤
      8 * ‖x - y‖ / ε ^ 2 := by
  rw [bentkusCutoffFDeriv_of_mem hclosed hne hx,
    bentkusCutoffFDeriv_of_notMem hclosed hne hy, zero_sub, norm_neg]
  change ‖(ε⁻¹ * bentkusProfileDeriv (Metric.infDist y s / ε)) •
      distanceFDeriv s hclosed hne y‖ ≤ _
  rw [norm_smul, norm_distanceFDeriv hclosed hne hconv hy, mul_one, Real.norm_eq_abs]
  have hdist : Metric.infDist y s ≤ ‖x - y‖ := by
    have h := Metric.infDist_le_dist_of_mem (x := y) hx
    simpa only [dist_eq_norm, norm_sub_rev] using h
  calc
    |ε⁻¹ * bentkusProfileDeriv (Metric.infDist y s / ε)| ≤
        4 * Metric.infDist y s / ε ^ 2 :=
      abs_cutoffScalar_le hε Metric.infDist_nonneg
    _ ≤ 4 * ‖x - y‖ / ε ^ 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdist (by norm_num)) (sq_nonneg ε)
    _ ≤ 8 * ‖x - y‖ / ε ^ 2 := by
      have hnonneg : 0 ≤ ‖x - y‖ / ε ^ 2 :=
        div_nonneg (norm_nonneg _) (sq_nonneg ε)
      have h := mul_le_mul_of_nonneg_right (show (4 : ℝ) ≤ 8 by norm_num) hnonneg
      simpa [div_eq_mul_inv, mul_assoc] using h

private lemma norm_bentkusCutoffFDeriv_sub_le {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {ε : ℝ} (hclosed : IsClosed s) (hne : s.Nonempty)
    (hconv : Convexity.IsConvexSet ℝ s) (hε : 0 < ε)
    (x y : EuclideanSpace ℝ (Fin d)) :
    ‖bentkusCutoffFDeriv s ε hclosed hne x - bentkusCutoffFDeriv s ε hclosed hne y‖ ≤
      8 * ‖x - y‖ / ε ^ 2 := by
  by_cases hx : x ∈ s
  · by_cases hy : y ∈ s
    · rw [bentkusCutoffFDeriv_of_mem hclosed hne hx,
        bentkusCutoffFDeriv_of_mem hclosed hne hy, sub_self, norm_zero]
      exact div_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (sq_nonneg ε)
    · exact norm_bentkusCutoffFDeriv_sub_le_of_mem_of_notMem
        hclosed hne hconv hε hx hy
  · by_cases hy : y ∈ s
    · have h := norm_bentkusCutoffFDeriv_sub_le_of_mem_of_notMem
        hclosed hne hconv hε hy hx
      simpa only [norm_sub_rev] using h
    · rcases le_total (Metric.infDist x s) (Metric.infDist y s) with hxy | hyx
      · exact norm_bentkusCutoffFDeriv_sub_le_of_notMem_of_infDist_le
          hclosed hne hconv hε hx hy hxy
      · have h := norm_bentkusCutoffFDeriv_sub_le_of_notMem_of_infDist_le
          hclosed hne hconv hε hy hx hyx
        simpa only [norm_sub_rev] using h

/-- The derivative field of the Bentkus cutoff is `8 / ε²`-Lipschitz. -/
lemma norm_fderiv_bentkusCutoff_sub_le {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {ε : ℝ} (hclosed : IsClosed s) (hne : s.Nonempty)
    (hconv : Convexity.IsConvexSet ℝ s) (hε : 0 < ε)
    (x y : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ (bentkusCutoff s ε) x - fderiv ℝ (bentkusCutoff s ε) y‖ ≤
      8 * ‖x - y‖ / ε ^ 2 := by
  rw [(hasFDerivAt_bentkusCutoff hclosed hne hconv hε x).fderiv,
    (hasFDerivAt_bentkusCutoff hclosed hne hconv hε y).fderiv]
  exact norm_bentkusCutoffFDeriv_sub_le hclosed hne hconv hε x y

/-- The Bentkus distance cutoff is continuously differentiable. -/
lemma contDiff_bentkusCutoff {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))} {ε : ℝ}
    (hclosed : IsClosed s) (hne : s.Nonempty) (hconv : Convexity.IsConvexSet ℝ s)
    (hε : 0 < ε) : ContDiff ℝ 1 (bentkusCutoff s ε) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨differentiable_bentkusCutoff hclosed hne hconv hε, ?_⟩
  have hK : 0 ≤ (8 : ℝ) / ε ^ 2 := div_nonneg (by norm_num) (sq_nonneg ε)
  let K : NNReal := ⟨8 / ε ^ 2, hK⟩
  have hL : LipschitzWith K (fderiv ℝ (bentkusCutoff s ε)) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simp only [dist_eq_norm]
    change ‖fderiv ℝ (bentkusCutoff s ε) x - fderiv ℝ (bentkusCutoff s ε) y‖ ≤
      (8 / ε ^ 2) * ‖x - y‖
    calc
      ‖fderiv ℝ (bentkusCutoff s ε) x - fderiv ℝ (bentkusCutoff s ε) y‖ ≤
          8 * ‖x - y‖ / ε ^ 2 :=
        norm_fderiv_bentkusCutoff_sub_le hclosed hne hconv hε x y
      _ = 8 / ε ^ 2 * ‖x - y‖ := by ring
  exact hL.continuous

end ProbabilityTheory
