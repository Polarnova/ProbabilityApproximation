/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Differential calculus for the standard Gaussian density

This file formalizes the Gaussian-density calculus used in V. Bentkus, *A Lyapunov type bound in
`ℝ^d`*, Theory of Probability and its Applications 49 (2004), 311--323 (Russian original pages
400--410).  Bentkus's Lemma 2.3 is the directional integration-by-parts estimate on original page
402, equations (2.3)--(2.4).  Its later Gaussian application uses the exact third directional
derivative identity on original page 405, equation (3.21).

The normalization below is `(2π)⁻^(dim E / 2)`.  The named first, second, and third contractions are
the successive Fréchet derivatives of this density.  The twice-equal-direction specialization of
the third contraction is exactly the polynomial displayed in Bentkus's equation (3.21).
-/

open MeasureTheory Real
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The normalizing constant `(2π)⁻^(dim E / 2)` for the standard Gaussian density. -/
def standardGaussianDensityNormalization (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : ℝ :=
  exp (-((Module.finrank ℝ E : ℝ) / 2) * log (2 * π))

/-- The standard Gaussian Lebesgue density on a finite-dimensional real inner-product space. -/
def standardGaussianDensity (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (x : E) : ℝ :=
  standardGaussianDensityNormalization E * exp (-‖x‖ ^ 2 / 2)

/-- The first derivative of the standard Gaussian density, contracted with one direction. -/
def standardGaussianDensityD1 (x h : E) : ℝ :=
  -(inner ℝ x h) * standardGaussianDensity E x

/-- The second derivative of the standard Gaussian density, contracted with two directions. -/
def standardGaussianDensityD2 (x h k : E) : ℝ :=
  (inner ℝ x h * inner ℝ x k - inner ℝ h k) * standardGaussianDensity E x

/-- The third derivative of the standard Gaussian density, contracted with three directions. -/
def standardGaussianDensityD3 (x h k l : E) : ℝ :=
  (-(inner ℝ x h) * inner ℝ x k * inner ℝ x l +
      inner ℝ h k * inner ℝ x l + inner ℝ h l * inner ℝ x k +
      inner ℝ k l * inner ℝ x h) *
    standardGaussianDensity E x

private lemma hasFDerivAt_gaussianExponent (x : E) :
    HasFDerivAt (fun y : E ↦ -‖y‖ ^ 2 / 2) (-(innerSL ℝ x)) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (-1 / 2 : ℝ)
  have hfun : (fun y : E ↦ (-1 / 2 : ℝ) * ‖y‖ ^ 2) =
      fun y ↦ -‖y‖ ^ 2 / 2 := by
    funext y
    ring
  have hder : (-1 / 2 : ℝ) • (2 • innerSL ℝ x) = -(innerSL ℝ x) := by
    ext v
    simp only [smul_apply, innerSL_apply_apply, neg_apply]
    ring
  rwa [hfun, hder] at h

/-- The exact Fréchet derivative of the standard Gaussian density. -/
lemma hasFDerivAt_standardGaussianDensity (x : E) :
    HasFDerivAt (standardGaussianDensity E)
      ((-standardGaussianDensity E x) • innerSL ℝ x) x := by
  have h := (hasFDerivAt_gaussianExponent x).exp.const_mul
    (standardGaussianDensityNormalization E)
  change HasFDerivAt
    (fun y : E ↦ standardGaussianDensityNormalization E * exp (-‖y‖ ^ 2 / 2))
    ((-(standardGaussianDensityNormalization E * exp (-‖x‖ ^ 2 / 2))) • innerSL ℝ x) x
  have hder :
      standardGaussianDensityNormalization E • exp (-‖x‖ ^ 2 / 2) • -(innerSL ℝ x) =
        (-(standardGaussianDensityNormalization E * exp (-‖x‖ ^ 2 / 2))) • innerSL ℝ x := by
    ext v
    simp only [smul_apply, neg_apply, innerSL_apply_apply, smul_eq_mul]
    ring
  rwa [hder] at h

/-- Contracting the Fréchet derivative gives the first directional formula. -/
lemma fderiv_standardGaussianDensity_apply (x h : E) :
    fderiv ℝ (standardGaussianDensity E) x h = standardGaussianDensityD1 x h := by
  rw [(hasFDerivAt_standardGaussianDensity x).fderiv]
  simp only [standardGaussianDensityD1, smul_apply, innerSL_apply_apply,
    smul_eq_mul]
  ring

private lemma hasFDerivAt_inner_right (x h : E) :
    HasFDerivAt (fun y : E ↦ inner ℝ y h) (innerSL ℝ h) x := by
  have heq : (fun y : E ↦ inner ℝ y h) = fun y ↦ inner ℝ h y := by
    funext y
    exact (real_inner_comm y h).symm
  rw [heq]
  exact (innerSL ℝ h).hasFDerivAt

/-- The derivative of the first contraction is the second contraction. -/
lemma fderiv_standardGaussianDensityD1_apply (x h k : E) :
    fderiv ℝ (fun y : E ↦ standardGaussianDensityD1 y h) x k =
      standardGaussianDensityD2 x h k := by
  have hi := (hasFDerivAt_inner_right x h).neg
  have hρ := hasFDerivAt_standardGaussianDensity x
  have hprod := hi.fun_mul hρ
  have heq : (fun i : E ↦ (- fun y : E ↦ inner ℝ y h) i *
      standardGaussianDensity E i) =
      fun y ↦ -(inner ℝ y h) * standardGaussianDensity E y := by
    funext y
    rfl
  rw [heq] at hprod
  change fderiv ℝ (fun y : E ↦ -(inner ℝ y h) * standardGaussianDensity E y) x k =
    standardGaussianDensityD2 x h k
  rw [hprod.fderiv]
  simp only [standardGaussianDensityD2, Pi.neg_apply, add_apply, smul_apply, neg_apply,
    innerSL_apply_apply, smul_eq_mul]
  ring

/-- The derivative of the second contraction is the third contraction. -/
lemma fderiv_standardGaussianDensityD2_apply (x h k l : E) :
    fderiv ℝ (fun y : E ↦ standardGaussianDensityD2 y h k) x l =
      standardGaussianDensityD3 x h k l := by
  have hh := hasFDerivAt_inner_right x h
  have hk := hasFDerivAt_inner_right x k
  have hpoly := (hh.fun_mul hk).sub_const (inner ℝ h k)
  have hρ := hasFDerivAt_standardGaussianDensity x
  have hprod := hpoly.fun_mul hρ
  change fderiv ℝ
    (fun y : E ↦ (inner ℝ y h * inner ℝ y k - inner ℝ h k) *
      standardGaussianDensity E y) x l = standardGaussianDensityD3 x h k l
  rw [hprod.fderiv]
  simp only [standardGaussianDensityD3, add_apply, smul_apply,
    innerSL_apply_apply, smul_eq_mul]
  ring

/-- The cubic Hermite contraction in Bentkus (2004), equation (3.21). -/
def gaussianThirdHermiteContraction (x w g : E) : ℝ :=
  2 * inner ℝ w g * inner ℝ x w + ‖w‖ ^ 2 * inner ℝ x g -
    inner ℝ x g * (inner ℝ x w) ^ 2

/-- The twice-equal-direction third derivative is exactly Bentkus's formula (3.21). -/
lemma standardGaussianDensityD3_sameDirection (x w g : E) :
    standardGaussianDensityD3 x w w g =
      standardGaussianDensity E x * gaussianThirdHermiteContraction x w g := by
  simp only [standardGaussianDensityD3, gaussianThirdHermiteContraction,
    real_inner_self_eq_norm_sq]
  ring

/-- Equation (3.21) as a third directional Fréchet-derivative identity. -/
lemma fderiv_standardGaussianDensityD2_sameDirection (x w g : E) :
    fderiv ℝ (fun y : E ↦ standardGaussianDensityD2 y w w) x g =
      standardGaussianDensity E x * gaussianThirdHermiteContraction x w g := by
  rw [fderiv_standardGaussianDensityD2_apply,
    standardGaussianDensityD3_sameDirection]

/-- The standard Gaussian density is continuous. -/
lemma continuous_standardGaussianDensity : Continuous (standardGaussianDensity E) := by
  change Continuous (fun x : E ↦ standardGaussianDensityNormalization E *
    exp (-‖x‖ ^ 2 / 2))
  fun_prop

/-- Every first directional contraction is continuous. -/
lemma continuous_standardGaussianDensityD1 (h : E) :
    Continuous (fun x : E ↦ standardGaussianDensityD1 x h) := by
  simp only [standardGaussianDensityD1]
  apply Continuous.mul
  · fun_prop
  · exact continuous_standardGaussianDensity

/-- Every second directional contraction is continuous. -/
lemma continuous_standardGaussianDensityD2 (h k : E) :
    Continuous (fun x : E ↦ standardGaussianDensityD2 x h k) := by
  simp only [standardGaussianDensityD2]
  apply Continuous.mul
  · fun_prop
  · exact continuous_standardGaussianDensity

/-- Every third directional contraction is continuous. -/
lemma continuous_standardGaussianDensityD3 (h k l : E) :
    Continuous (fun x : E ↦ standardGaussianDensityD3 x h k l) := by
  simp only [standardGaussianDensityD3]
  apply Continuous.mul
  · fun_prop
  · exact continuous_standardGaussianDensity

/-- The cubic Hermite contraction in (3.21) is continuous. -/
lemma continuous_gaussianThirdHermiteContraction (w g : E) :
    Continuous (fun x : E ↦ gaussianThirdHermiteContraction x w g) := by
  simp only [gaussianThirdHermiteContraction]
  fun_prop

section MeasurabilityAndIntegrability

variable [MeasurableSpace E] [BorelSpace E]

/-- The third density contraction is Borel measurable. -/
lemma measurable_standardGaussianDensityD3 (h k l : E) :
    Measurable (fun x : E ↦ standardGaussianDensityD3 x h k l) :=
  (continuous_standardGaussianDensityD3 h k l).measurable

/-- The cubic Hermite contraction is Borel measurable. -/
lemma measurable_gaussianThirdHermiteContraction (w g : E) :
    Measurable (fun x : E ↦ gaussianThirdHermiteContraction x w g) :=
  (continuous_gaussianThirdHermiteContraction w g).measurable

private lemma memLp_three_inner_stdGaussian (v : E) :
    MemLp (fun x : E ↦ inner ℝ x v) 3 (stdGaussian E) := by
  have h := IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ v) 3 (by norm_num)
  have heq : (fun x : E ↦ inner ℝ x v) = innerSL ℝ v := by
    funext x
    exact (real_inner_comm x v).symm
  rw [heq]
  exact h

private lemma ennreal_holderTriple_three_three_threeHalves :
    ENNReal.HolderTriple 3 3 (3 / 2) := by
  constructor
  have hdiv : (3 / 2 : ℝ≥0∞) ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩
  have hinvdiv : (3 / 2 : ℝ≥0∞)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hdiv
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) hinvdiv,
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_ofNat]
  norm_num

private lemma ennreal_holderTriple_threeHalves_three_one :
    ENNReal.HolderTriple (3 / 2) 3 1 := by
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

private lemma integrable_inner_mul_inner_mul_inner_stdGaussian (u v w : E) :
    Integrable (fun x : E ↦ inner ℝ x u * inner ℝ x v * inner ℝ x w)
      (stdGaussian E) := by
  letI : ENNReal.HolderTriple 3 3 (3 / 2) :=
    ennreal_holderTriple_three_three_threeHalves
  have huv : MemLp ((fun x : E ↦ inner ℝ x u) * fun x ↦ inner ℝ x v)
      (3 / 2) (stdGaussian E) :=
    (memLp_three_inner_stdGaussian v).mul (memLp_three_inner_stdGaussian u)
  letI : ENNReal.HolderTriple (3 / 2) 3 1 :=
    ennreal_holderTriple_threeHalves_three_one
  have huvw : MemLp
      (((fun x : E ↦ inner ℝ x u) * fun x ↦ inner ℝ x v) *
        fun x ↦ inner ℝ x w) 1 (stdGaussian E) :=
    (memLp_three_inner_stdGaussian w).mul huv
  exact huvw.integrable (by norm_num)

/-- The cubic Hermite contraction in Bentkus's equation (3.21) is integrable under standard
Gaussian measure. -/
lemma integrable_gaussianThirdHermiteContraction_stdGaussian (w g : E) :
    Integrable (fun x : E ↦ gaussianThirdHermiteContraction x w g) (stdGaussian E) := by
  have hw : Integrable (fun x : E ↦ inner ℝ x w) (stdGaussian E) :=
    (memLp_three_inner_stdGaussian w).integrable (by norm_num)
  have hg : Integrable (fun x : E ↦ inner ℝ x g) (stdGaussian E) :=
    (memLp_three_inner_stdGaussian g).integrable (by norm_num)
  have hcubic : Integrable
      (fun x : E ↦ inner ℝ x g * inner ℝ x w * inner ℝ x w) (stdGaussian E) :=
    integrable_inner_mul_inner_mul_inner_stdGaussian g w w
  have hlinear := (hw.const_mul (2 * inner ℝ w g)).add
    (hg.const_mul (‖w‖ ^ 2))
  have htarget := hlinear.sub hcubic
  convert htarget using 1
  funext x
  simp only [gaussianThirdHermiteContraction, Pi.add_apply, Pi.sub_apply]
  ring

/-- The universal fourth moment used in the dimension-free bound for the cubic contraction. -/
def standardGaussianFourthMoment : ℝ :=
  ∫ t : ℝ, t ^ 4 ∂gaussianReal 0 1

/-- The universal fourth moment is nonnegative. -/
lemma standardGaussianFourthMoment_nonneg : 0 ≤ standardGaussianFourthMoment := by
  exact integral_nonneg fun t ↦ by positivity

private lemma map_innerSL_stdGaussian (v : E) :
    (stdGaussian E).map (innerSL ℝ v) = gaussianReal 0 (‖v‖ ^ 2).toNNReal := by
  rw [IsGaussian.map_eq_gaussianReal]
  congr 2
  · exact integral_strongDual_stdGaussian (innerSL ℝ v)
  · rw [variance_dual_stdGaussian, innerSL_apply_norm]

private lemma gaussianReal_zero_sq_eq_map_standard (c : ℝ) :
    gaussianReal 0 (c ^ 2).toNNReal =
      (gaussianReal 0 1).map (fun t : ℝ ↦ c * t) := by
  rw [gaussianReal_map_const_mul]
  congr 2
  simp only [mul_zero]
  rw [Real.toNNReal_of_nonneg (sq_nonneg c)]
  simp

/-- A linear functional of a standard Gaussian has the expected fourth-moment scaling. -/
lemma integral_inner_pow_four_stdGaussian (v : E) :
    ∫ x : E, (inner ℝ v x) ^ 4 ∂stdGaussian E =
      ‖v‖ ^ 4 * standardGaussianFourthMoment := by
  calc
    ∫ x : E, (inner ℝ v x) ^ 4 ∂stdGaussian E =
        ∫ t : ℝ, t ^ 4 ∂(stdGaussian E).map (innerSL ℝ v) := by
          rw [integral_map (by fun_prop) (by fun_prop)]
          simp only [innerSL_apply_apply]
    _ = ∫ t : ℝ, t ^ 4 ∂gaussianReal 0 (‖v‖ ^ 2).toNNReal := by
      rw [map_innerSL_stdGaussian]
    _ = ∫ t : ℝ, t ^ 4 ∂(gaussianReal 0 1).map (fun s : ℝ ↦ ‖v‖ * s) := by
      rw [gaussianReal_zero_sq_eq_map_standard]
    _ = ∫ s : ℝ, (‖v‖ * s) ^ 4 ∂gaussianReal 0 1 := by
      rw [integral_map (by fun_prop) (by fun_prop)]
    _ = ‖v‖ ^ 4 * standardGaussianFourthMoment := by
      simp_rw [mul_pow]
      rw [integral_const_mul]
      rfl

/-- A linear functional of a standard Gaussian has second moment equal to its squared norm. -/
lemma integral_inner_sq_stdGaussian (v : E) :
    ∫ x : E, (inner ℝ v x) ^ 2 ∂stdGaussian E = ‖v‖ ^ 2 := by
  calc
    ∫ x : E, (inner ℝ v x) ^ 2 ∂stdGaussian E =
        ∫ t : ℝ, t ^ 2 ∂(stdGaussian E).map (innerSL ℝ v) := by
          rw [integral_map (by fun_prop) (by fun_prop)]
          simp only [innerSL_apply_apply]
    _ = ∫ t : ℝ, t ^ 2 ∂gaussianReal 0 (‖v‖ ^ 2).toNNReal := by
      rw [map_innerSL_stdGaussian]
    _ = ‖v‖ ^ 2 := by
      have h := variance_id_gaussianReal (μ := 0) (v := (‖v‖ ^ 2).toNNReal)
      rw [variance_eq_integral measurable_id.aemeasurable] at h
      have h' : ∫ t : ℝ, t ^ 2 ∂gaussianReal 0 (‖v‖ ^ 2).toNNReal =
          ((‖v‖ ^ 2).toNNReal : ℝ) := by
        simpa using h
      rw [h', Real.coe_toNNReal _ (sq_nonneg ‖v‖)]

/-- The first absolute moment of a standard-Gaussian linear functional is at most its norm. -/
lemma integral_abs_inner_stdGaussian_le_norm (v : E) :
    ∫ x : E, |inner ℝ v x| ∂stdGaussian E ≤ ‖v‖ := by
  have hv : MemLp (fun x : E ↦ inner ℝ v x) (ENNReal.ofReal 2) (stdGaussian E) := by
    have h := IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ v)
      (ENNReal.ofReal 2) (by norm_num)
    have heq : (fun x : E ↦ inner ℝ v x) = innerSL ℝ v := by
      funext x
      rfl
    rw [heq]
    exact h
  have h1 : MemLp (fun _ : E ↦ (1 : ℝ)) (ENNReal.ofReal 2) (stdGaussian E) :=
    memLp_const 1
  have hc := integral_mul_norm_le_Lp_mul_Lq
    (p := (2 : ℝ)) (q := (2 : ℝ))
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) hv h1
  simp only [norm_eq_abs, abs_one, mul_one, one_rpow, mul_one] at hc
  rw [← Real.sqrt_eq_rpow] at hc
  rw [show (∫ a : E, |inner ℝ v a| ^ (2 : ℝ) ∂stdGaussian E) = ‖v‖ ^ 2 by
    calc
      _ = ∫ x : E, (inner ℝ v x) ^ 2 ∂stdGaussian E := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Real.rpow_two]
        exact sq_abs (inner ℝ v x)
      _ = ‖v‖ ^ 2 := integral_inner_sq_stdGaussian v] at hc
  simpa using hc

private lemma integral_abs_inner_mul_abs_inner_sq_stdGaussian_le
    (w g : E) :
    ∫ x : E, |inner ℝ g x| * |inner ℝ w x| ^ 2 ∂stdGaussian E ≤
      ‖g‖ * ‖w‖ ^ 2 * √standardGaussianFourthMoment := by
  have hg2 : MemLp (fun x : E ↦ inner ℝ g x) (ENNReal.ofReal 2) (stdGaussian E) := by
    have h := IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ g)
      (ENNReal.ofReal 2) (by norm_num)
    have heq : (fun x : E ↦ inner ℝ g x) = innerSL ℝ g := by
      funext x
      rfl
    rw [heq]
    exact h
  have hw4 : MemLp (fun x : E ↦ inner ℝ w x) (ENNReal.ofReal 4) (stdGaussian E) := by
    have h := IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ w)
      (ENNReal.ofReal 4) (by norm_num)
    have heq : (fun x : E ↦ inner ℝ w x) = innerSL ℝ w := by
      funext x
      rfl
    rw [heq]
    exact h
  letI : ENNReal.HolderTriple (ENNReal.ofReal 4) (ENNReal.ofReal 4)
      (ENNReal.ofReal 2) :=
    Real.HolderTriple.ennrealOfReal (show Real.HolderTriple 4 4 2 by
      rw [Real.holderTriple_iff]
      norm_num)
  have hw2 : MemLp ((fun x : E ↦ inner ℝ w x) * fun x ↦ inner ℝ w x)
      (ENNReal.ofReal 2) (stdGaussian E) := hw4.mul hw4
  have hwSq2 : MemLp (fun x : E ↦ (inner ℝ w x) ^ 2)
      (ENNReal.ofReal 2) (stdGaussian E) := by
    convert hw2 using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have hc := integral_mul_norm_le_Lp_mul_Lq
    (p := (2 : ℝ)) (q := (2 : ℝ))
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) hg2 hwSq2
  simp only [norm_eq_abs] at hc
  have h2 : (∫ a : E, |inner ℝ g a| ^ (2 : ℝ) ∂stdGaussian E) = ‖g‖ ^ 2 := by
    calc
      _ = ∫ x : E, (inner ℝ g x) ^ 2 ∂stdGaussian E := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Real.rpow_two]
        exact sq_abs (inner ℝ g x)
      _ = ‖g‖ ^ 2 := integral_inner_sq_stdGaussian g
  have h4 : (∫ a : E, |(inner ℝ w a) ^ 2| ^ (2 : ℝ) ∂stdGaussian E) =
      ‖w‖ ^ 4 * standardGaussianFourthMoment := by
    calc
      _ = ∫ x : E, (inner ℝ w x) ^ 4 ∂stdGaussian E := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Real.rpow_two, abs_of_nonneg (sq_nonneg (inner ℝ w x))]
        ring
      _ = ‖w‖ ^ 4 * standardGaussianFourthMoment :=
        integral_inner_pow_four_stdGaussian w
  rw [h2, h4] at hc
  have hc' : ∫ x : E, |inner ℝ g x| * |inner ℝ w x| ^ 2 ∂stdGaussian E ≤
      √(‖g‖ ^ 2) * √(‖w‖ ^ 4 * standardGaussianFourthMoment) := by
    simpa only [abs_pow, ← Real.sqrt_eq_rpow] using hc
  have hsqrtg : √(‖g‖ ^ 2) = ‖g‖ := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg g)]
  have hsqrtw : √(‖w‖ ^ 4 * standardGaussianFourthMoment) =
      ‖w‖ ^ 2 * √standardGaussianFourthMoment := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ ‖w‖ ^ 4)]
    congr 1
    rw [show ‖w‖ ^ 4 = (‖w‖ ^ 2) ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (sq_nonneg ‖w‖)]
  rw [hsqrtg, hsqrtw] at hc'
  simpa [mul_assoc] using hc'

/-- Dimension-free integral bound for Bentkus's third-derivative contraction.

The coefficient is an absolute constant: it depends only on the fourth moment of a one-dimensional
standard Gaussian.  This is the precise formal counterpart of the estimate following equations
(3.21)--(3.23) on original pages 405--406 of Bentkus (2004). -/
theorem integral_abs_gaussianThirdHermiteContraction_le (w g : E) :
    ∫ x : E, |gaussianThirdHermiteContraction x w g| ∂stdGaussian E ≤
      (3 + √standardGaussianFourthMoment) * ‖w‖ ^ 2 * ‖g‖ := by
  have hw : Integrable (fun x : E ↦ inner ℝ x w) (stdGaussian E) :=
    (memLp_three_inner_stdGaussian w).integrable (by norm_num)
  have hg : Integrable (fun x : E ↦ inner ℝ x g) (stdGaussian E) :=
    (memLp_three_inner_stdGaussian g).integrable (by norm_num)
  have hcubic : Integrable
      (fun x : E ↦ inner ℝ x g * inner ℝ x w * inner ℝ x w) (stdGaussian E) :=
    integrable_inner_mul_inner_mul_inner_stdGaussian g w w
  have hcross : Integrable
      (fun x : E ↦ |inner ℝ x g| * |inner ℝ x w| ^ 2) (stdGaussian E) := by
    convert hcubic.abs using 1
    funext x
    simp only [abs_mul]
    ring
  have hmajor : Integrable
      (fun x : E ↦ 2 * |inner ℝ w g| * |inner ℝ x w| +
        ‖w‖ ^ 2 * |inner ℝ x g| + |inner ℝ x g| * |inner ℝ x w| ^ 2)
      (stdGaussian E) :=
    (((hw.abs.const_mul (2 * |inner ℝ w g|)).add
      (hg.abs.const_mul (‖w‖ ^ 2))).add hcross)
  have habs := (integrable_gaussianThirdHermiteContraction_stdGaussian w g).abs
  calc
    _ ≤ ∫ x : E, (2 * |inner ℝ w g| * |inner ℝ x w| +
        ‖w‖ ^ 2 * |inner ℝ x g| + |inner ℝ x g| * |inner ℝ x w| ^ 2)
        ∂stdGaussian E := by
      apply integral_mono habs hmajor
      intro x
      simp only [gaussianThirdHermiteContraction]
      calc
        _ ≤ |2 * inner ℝ w g * inner ℝ x w + ‖w‖ ^ 2 * inner ℝ x g| +
            |inner ℝ x g * (inner ℝ x w) ^ 2| := abs_sub _ _
        _ ≤ (|2 * inner ℝ w g * inner ℝ x w| + |‖w‖ ^ 2 * inner ℝ x g|) +
            |inner ℝ x g * (inner ℝ x w) ^ 2| := by
          gcongr
          exact abs_add_le _ _
        _ = _ := by
          simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_pow,
            abs_of_nonneg (sq_nonneg ‖w‖)]
    _ = 2 * |inner ℝ w g| * (∫ x : E, |inner ℝ x w| ∂stdGaussian E) +
        ‖w‖ ^ 2 * (∫ x : E, |inner ℝ x g| ∂stdGaussian E) +
        ∫ x : E, |inner ℝ x g| * |inner ℝ x w| ^ 2 ∂stdGaussian E := by
      have hA := hw.abs.const_mul (2 * |inner ℝ w g|)
      have hB := hg.abs.const_mul (‖w‖ ^ 2)
      calc
        _ = (∫ x : E, 2 * |inner ℝ w g| * |inner ℝ x w| +
            ‖w‖ ^ 2 * |inner ℝ x g| ∂stdGaussian E) +
            ∫ x : E, |inner ℝ x g| * |inner ℝ x w| ^ 2 ∂stdGaussian E :=
          integral_add (hA.add hB) hcross
        _ = ((∫ x : E, 2 * |inner ℝ w g| * |inner ℝ x w| ∂stdGaussian E) +
            ∫ x : E, ‖w‖ ^ 2 * |inner ℝ x g| ∂stdGaussian E) +
            ∫ x : E, |inner ℝ x g| * |inner ℝ x w| ^ 2 ∂stdGaussian E := by
          rw [integral_add hA hB]
        _ = _ := by
          rw [integral_const_mul, integral_const_mul]
    _ ≤ 2 * (‖w‖ * ‖g‖) * ‖w‖ + ‖w‖ ^ 2 * ‖g‖ +
        ‖g‖ * ‖w‖ ^ 2 * √standardGaussianFourthMoment := by
      gcongr
      · exact abs_real_inner_le_norm w g
      · have heq : (fun x : E ↦ |inner ℝ x w|) = fun x ↦ |inner ℝ w x| := by
          funext x
          rw [real_inner_comm]
        rw [heq]
        exact integral_abs_inner_stdGaussian_le_norm w
      · have heq : (fun x : E ↦ |inner ℝ x g|) = fun x ↦ |inner ℝ g x| := by
          funext x
          rw [real_inner_comm]
        rw [heq]
        exact integral_abs_inner_stdGaussian_le_norm g
      · have heq : (fun x : E ↦ |inner ℝ x g| * |inner ℝ x w| ^ 2) =
            fun x ↦ |inner ℝ g x| * |inner ℝ w x| ^ 2 := by
          funext x
          rw [real_inner_comm x g, real_inner_comm x w]
        rw [heq]
        exact integral_abs_inner_mul_abs_inner_sq_stdGaussian_le w g
    _ = (3 + √standardGaussianFourthMoment) * ‖w‖ ^ 2 * ‖g‖ := by
      ring

end MeasurabilityAndIntegrability

end ProbabilityTheory
