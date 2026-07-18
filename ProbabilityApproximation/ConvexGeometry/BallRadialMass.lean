/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.ConvexGeometry.BallRadialMajorant
import ProbabilityApproximation.ConvexGeometry.BallSphereMeasure
import ProbabilityApproximation.ConvexGeometry.GaussianShell
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The mass of Ball's radial majorant

This module formalizes the last one-dimensional estimate in Keith Ball,
*The reverse isoperimetric problem for Gaussian measure* (1993), printed pp. 418--419.
It keeps the Abel primitive, its zero, and the two interval estimates separate from the spherical
projection identity in `BallRadialMajorant`.
-/

open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

/-- The explicit coefficient converting Ball's one-dimensional radial integral into
`(n - 1)`-dimensional Euclidean mass. -/
def ballRadialMassCoefficient (n : ℕ) : ℝ :=
  (2 ^ ((n : ℝ) / 2 - 1) * Real.Gamma (((n : ℝ) - 1) / 2) *
    Real.sqrt Real.pi)⁻¹

private def ballRadialAbelIntegrand (n : ℕ) (t θ : ℝ) : ℝ :=
  Real.sin θ ^ (n - 2) * Real.exp (-(t ^ 2 * Real.sin θ ^ 2) / 2)

private def ballRadialAbelParameterDerivative (n : ℕ) (t θ : ℝ) : ℝ :=
  -(t * Real.sin θ ^ n * Real.exp (-(t ^ 2 * Real.sin θ ^ 2) / 2))

private def ballRadialAbelPrimitive (n : ℕ) (t : ℝ) : ℝ :=
  ballGaussianNormalization n * t ^ (n - 1) *
    ∫ θ in (0 : ℝ)..Real.pi / 2, ballRadialAbelIntegrand n t θ

private lemma continuous_ballRadialAbelIntegrand (n : ℕ) :
    Continuous fun p : ℝ × ℝ ↦ ballRadialAbelIntegrand n p.1 p.2 := by
  unfold ballRadialAbelIntegrand
  fun_prop

private lemma continuous_ballRadialAbelParameterDerivative (n : ℕ) :
    Continuous fun p : ℝ × ℝ ↦ ballRadialAbelParameterDerivative n p.1 p.2 := by
  unfold ballRadialAbelParameterDerivative
  fun_prop

private lemma hasDerivAt_ballRadialAbelIntegrand {n : ℕ} (hn : 2 ≤ n)
    (t θ : ℝ) :
    HasDerivAt (fun u ↦ ballRadialAbelIntegrand n u θ)
      (ballRadialAbelParameterDerivative n t θ) t := by
  unfold ballRadialAbelIntegrand ballRadialAbelParameterDerivative
  have hq := (((hasDerivAt_id t).pow 2).mul_const (Real.sin θ ^ 2)).neg.div_const 2
  have hexp := (Real.hasDerivAt_exp (-(t ^ 2 * Real.sin θ ^ 2) / 2)).comp t hq
  have h := hexp.const_mul (Real.sin θ ^ (n - 2))
  apply h.congr_deriv
  rw [show Real.sin θ ^ n = Real.sin θ ^ (n - 2) * Real.sin θ ^ 2 by
    rw [← pow_add]; congr 1; omega]
  simp only [id_eq]
  ring

private lemma hasDerivAt_integral_ballRadialAbelIntegrand {n : ℕ} (hn : 2 ≤ n)
    (t : ℝ) :
    HasDerivAt
      (fun u ↦ ∫ θ in (0 : ℝ)..Real.pi / 2, ballRadialAbelIntegrand n u θ)
      (∫ θ in (0 : ℝ)..Real.pi / 2,
        ballRadialAbelParameterDerivative n t θ) t := by
  let K : Set (ℝ × ℝ) :=
    Metric.closedBall t 1 ×ˢ Set.uIcc (0 : ℝ) (Real.pi / 2)
  let G : ℝ × ℝ → ℝ := fun p ↦ ‖ballRadialAbelParameterDerivative n p.1 p.2‖
  have hK : IsCompact K :=
    (isCompact_closedBall t 1).prod isCompact_uIcc
  have hG : Continuous G := by
    dsimp only [G]
    exact (continuous_ballRadialAbelParameterDerivative n).norm
  obtain ⟨B, hB⟩ := bddAbove_def.mp (hK.bddAbove_image hG.continuousOn)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume)
    (F := fun u θ ↦ ballRadialAbelIntegrand n u θ)
    (F' := fun u θ ↦ ballRadialAbelParameterDerivative n u θ)
    (x₀ := t) (s := Metric.closedBall t 1) (bound := fun _ ↦ B)
    (a := (0 : ℝ)) (b := Real.pi / 2)
    (Metric.closedBall_mem_nhds t zero_lt_one)
    (by
      filter_upwards with u
      exact ((continuous_ballRadialAbelIntegrand n).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (((continuous_ballRadialAbelIntegrand n).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
    (((continuous_ballRadialAbelParameterDerivative n).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (by
      filter_upwards with θ
      intro hθ u hu
      exact hB (G (u, θ)) (mem_image_of_mem G (show (u, θ) ∈ K by
        exact ⟨hu, uIoc_subset_uIcc hθ⟩)))
    (continuous_const.intervalIntegrable _ _)
    (by
      filter_upwards with θ
      intro _hθ u _hu
      exact hasDerivAt_ballRadialAbelIntegrand hn u θ)).2

private lemma hasDerivAt_ballRadialAbelPrimitive {n : ℕ} (hn : 2 ≤ n)
    (t : ℝ) :
    HasDerivAt (ballRadialAbelPrimitive n)
      (t ^ (n - 2) * ballRadialAux n t) t := by
  let J : ℝ → ℝ := fun u ↦
    ∫ θ in (0 : ℝ)..Real.pi / 2, ballRadialAbelIntegrand n u θ
  let J' : ℝ := ∫ θ in (0 : ℝ)..Real.pi / 2,
    ballRadialAbelParameterDerivative n t θ
  have hpow := (hasDerivAt_id t).pow (n - 1)
  have hJ : HasDerivAt J J' t := hasDerivAt_integral_ballRadialAbelIntegrand hn t
  have h := (hpow.mul hJ).const_mul (ballGaussianNormalization n)
  unfold ballRadialAbelPrimitive
  apply (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u ↦ by
    dsimp only [J]
    simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
    ring)).congr_deriv
  have hpred : n - 1 - 1 = n - 2 := by omega
  rw [hpred]
  unfold ballRadialAux
  dsimp only [J, J']
  rw [show
      (∫ θ in (0 : ℝ)..Real.pi / 2,
        ballRadialAbelParameterDerivative n t θ) =
        ∫ θ in (0 : ℝ)..Real.pi / 2,
          (-(t * Real.sin θ ^ 2)) * ballRadialAbelIntegrand n t θ by
    apply intervalIntegral.integral_congr
    intro θ _hθ
    unfold ballRadialAbelParameterDerivative ballRadialAbelIntegrand
    rw [show Real.sin θ ^ n = Real.sin θ ^ (n - 2) * Real.sin θ ^ 2 by
      rw [← pow_add]; congr 1; omega]
    ring]
  simp only [id_eq, Pi.pow_apply, mul_one]
  rw [show
      (((n - 1 : ℕ) : ℝ) * t ^ (n - 2) *
          (∫ θ in (0 : ℝ)..Real.pi / 2, ballRadialAbelIntegrand n t θ) +
        t ^ (n - 1) *
          (∫ θ in (0 : ℝ)..Real.pi / 2,
            (-(t * Real.sin θ ^ 2)) * ballRadialAbelIntegrand n t θ)) =
        t ^ (n - 2) *
          ∫ θ in (0 : ℝ)..Real.pi / 2,
            (((n - 1 : ℕ) : ℝ) - t ^ 2 * Real.sin θ ^ 2) *
              ballRadialAbelIntegrand n t θ by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add,
      ← intervalIntegral.integral_const_mul]
    · apply intervalIntegral.integral_congr
      intro θ _hθ
      rw [show t ^ (n - 1) = t ^ (n - 2) * t by
        rw [← pow_succ]; congr 1; omega]
      ring
    · exact ((continuous_ballRadialAbelIntegrand n).comp
        (continuous_const.prodMk continuous_id) |>.const_mul
          (((n - 1 : ℕ) : ℝ) * t ^ (n - 2))).intervalIntegrable _ _
    · exact ((by
          unfold ballRadialAbelIntegrand
          fun_prop : Continuous fun θ : ℝ ↦
            (-(t * Real.sin θ ^ 2)) * ballRadialAbelIntegrand n t θ) |>.const_mul
              (t ^ (n - 1))).intervalIntegrable _ _]
  unfold ballRadialAuxIntegrand ballRadialAbelIntegrand
  ring_nf

private theorem integral_ballRadialAux_mul_pow_eq_abelPrimitive
    {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (_hs : 0 ≤ s) :
    (∫ t in (0 : ℝ)..s, ballRadialAux n t * t ^ (n - 2)) =
      ballRadialAbelPrimitive n s := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := s) (f := ballRadialAbelPrimitive n)
    (f' := fun t ↦ t ^ (n - 2) * ballRadialAux n t)
    (fun t _ht ↦ hasDerivAt_ballRadialAbelPrimitive hn t)
    (((continuous_id.pow (n - 2)).mul (continuous_ballRadialAux n))
      |>.intervalIntegrable _ _)
  have hn1 : n - 1 ≠ 0 := by omega
  simp only [ballRadialAbelPrimitive, zero_pow hn1, mul_zero, zero_mul, sub_zero] at hftc
  rw [show (fun t : ℝ ↦ ballRadialAux n t * t ^ (n - 2)) =
      fun t ↦ t ^ (n - 2) * ballRadialAux n t by funext t; ring]
  exact hftc

private lemma ballRadialAux_one_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < ballRadialAux n 1 := by
  have htop : (1 : ℝ) ≤ √((n - 1 : ℕ) : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    norm_num
    exact_mod_cast (show 1 ≤ n - 1 by omega)
  unfold ballRadialAux
  apply mul_pos (ballGaussianNormalization_pos n)
  apply intervalIntegral.integral_pos (by positivity)
  · exact ((continuous_ballRadialAuxIntegrand n).comp
      (continuous_const.prodMk continuous_id)).continuousOn
  · intro θ hθ
    exact ballRadialAuxIntegrand_nonneg (show 2 ≤ n by omega) (by positivity) htop
      (by
        rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
        exact ⟨hθ.1.le, hθ.2⟩)
  · refine ⟨Real.pi / 4, ⟨by positivity, by linarith [Real.pi_pos]⟩, ?_⟩
    unfold ballRadialAuxIntegrand
    rw [Real.sin_pi_div_four]
    simp only [one_pow, one_mul]
    have hsqrt : (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : ℝ) := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hfactor : 0 < ((n - 1 : ℕ) : ℝ) - (Real.sqrt 2 / 2) ^ 2 := by
      rw [hsqrt]
      have hcast : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ n - 1 by omega)
      linarith
    exact mul_pos (mul_pos hfactor (pow_pos (by positivity) _)) (Real.exp_pos _)

private theorem exists_ballRadialAux_zero {n : ℕ} (hn : 2 ≤ n) :
    ∃ s ∈ Set.Icc (1 : ℝ) (√(2 * n)), ballRadialAux n s = 0 := by
  have hupper := ballRadialAux_nonpos_of_sqrt_two_mul_le
    (show 2 ≤ n by omega) (le_rfl : √(2 * (n : ℝ)) ≤ √(2 * n))
  have hlower := ballRadialAux_one_pos hn
  have hbounds : (0 : ℝ) ∈ Set.Icc
      (ballRadialAux n (√(2 * n))) (ballRadialAux n 1) :=
    ⟨hupper, hlower.le⟩
  have hinterval : (1 : ℝ) ≤ √(2 * n) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    norm_num
    exact_mod_cast (show 1 ≤ 2 * n by omega)
  obtain ⟨s, hs, hszero⟩ :=
    (intermediate_value_Icc' hinterval
      (continuous_ballRadialAux n).continuousOn) hbounds
  exact ⟨s, hs, hszero⟩

private noncomputable def ballRadialCutoff (n : ℕ) (hn : 2 ≤ n) : ℝ :=
  Classical.choose (exists_ballRadialAux_zero hn)

private lemma ballRadialCutoff_mem {n : ℕ} (hn : 2 ≤ n) :
    ballRadialCutoff n hn ∈ Set.Icc (1 : ℝ) (√(2 * n)) :=
  (Classical.choose_spec (exists_ballRadialAux_zero hn)).1

private lemma ballRadialAux_cutoff_eq_zero {n : ℕ} (hn : 2 ≤ n) :
    ballRadialAux n (ballRadialCutoff n hn) = 0 :=
  (Classical.choose_spec (exists_ballRadialAux_zero hn)).2

private lemma ballRadialCutoff_gt_one {n : ℕ} (hn : 2 ≤ n) :
    1 < ballRadialCutoff n hn := by
  have hle := (ballRadialCutoff_mem hn).1
  exact hle.lt_of_ne fun heq ↦ by
    have hz := ballRadialAux_cutoff_eq_zero hn
    rw [← heq] at hz
    linarith [ballRadialAux_one_pos hn]

private lemma ballRadialAux_nonneg_of_le_cutoff {n : ℕ} (hn : 2 ≤ n)
    {t : ℝ} (ht : 0 ≤ t) (hts : t ≤ ballRadialCutoff n hn) :
    0 ≤ ballRadialAux n t := by
  have hs : 0 ≤ ballRadialCutoff n hn :=
    zero_le_one.trans (ballRadialCutoff_mem hn).1
  have hscaled :
      ballRadialScaledAux n (ballRadialCutoff n hn) ≤ ballRadialScaledAux n t :=
    antitoneOn_ballRadialScaledAux hn ht hs hts
  have hscaledZero : ballRadialScaledAux n (ballRadialCutoff n hn) = 0 := by
    unfold ballRadialScaledAux
    rw [ballRadialAux_cutoff_eq_zero hn, mul_zero]
  rw [hscaledZero] at hscaled
  rw [ballRadialAux_eq_exp_neg_mul_scaledAux]
  exact mul_nonneg (Real.exp_nonneg _) hscaled

private lemma ballRadialAux_nonpos_of_cutoff_le {n : ℕ} (hn : 2 ≤ n)
    {t : ℝ} (hts : ballRadialCutoff n hn ≤ t) :
    ballRadialAux n t ≤ 0 := by
  have hs : 0 ≤ ballRadialCutoff n hn :=
    zero_le_one.trans (ballRadialCutoff_mem hn).1
  have ht : 0 ≤ t := hs.trans hts
  have hscaled :
      ballRadialScaledAux n t ≤ ballRadialScaledAux n (ballRadialCutoff n hn) :=
    antitoneOn_ballRadialScaledAux hn hs ht hts
  have hscaledZero : ballRadialScaledAux n (ballRadialCutoff n hn) = 0 := by
    unfold ballRadialScaledAux
    rw [ballRadialAux_cutoff_eq_zero hn, mul_zero]
  rw [hscaledZero] at hscaled
  rw [ballRadialAux_eq_exp_neg_mul_scaledAux]
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) hscaled

private lemma ballRadialMajorant_eq_aux_of_mem_cutoff {n : ℕ} (hn : 2 ≤ n)
    {t : ℝ} (ht : 0 ≤ t) (hts : t ≤ ballRadialCutoff n hn) :
    ballRadialMajorant n t = ballRadialAux n t :=
  ballRadialMajorant_eq_ballRadialAux_of_nonneg
    (ballRadialAux_nonneg_of_le_cutoff hn ht hts)

private lemma ballRadialMajorant_eq_zero_of_cutoff_le {n : ℕ} (hn : 2 ≤ n)
    {t : ℝ} (hts : ballRadialCutoff n hn ≤ t) :
    ballRadialMajorant n t = 0 :=
  ballRadialMajorant_eq_zero_of_nonpos (ballRadialAux_nonpos_of_cutoff_le hn hts)

private theorem integral_ballRadialMajorant_mul_pow_eq_abelPrimitive
    {n : ℕ} (hn : 2 ≤ n) :
    (∫ t in Set.Ioi (0 : ℝ), ballRadialMajorant n t * t ^ (n - 2)) =
      ballRadialAbelPrimitive n (ballRadialCutoff n hn) := by
  let s := ballRadialCutoff n hn
  have hs : 0 ≤ s := zero_le_one.trans (ballRadialCutoff_mem hn).1
  have hrestrict :
      (∫ t in Set.Ioi (0 : ℝ), ballRadialMajorant n t * t ^ (n - 2)) =
        ∫ t in Set.Ioc (0 : ℝ) s, ballRadialMajorant n t * t ^ (n - 2) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    · intro t ht
      exact ht.1
    · intro t ht
      have hst : s ≤ t := by
        by_contra hnot
        exact ht.2 ⟨ht.1, le_of_not_ge hnot⟩
      rw [ballRadialMajorant_eq_zero_of_cutoff_le hn hst, zero_mul]
  rw [hrestrict, ← intervalIntegral.integral_of_le hs]
  calc
    (∫ t in (0 : ℝ)..s, ballRadialMajorant n t * t ^ (n - 2)) =
        ∫ t in (0 : ℝ)..s, ballRadialAux n t * t ^ (n - 2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      have ht' : t ∈ Set.Icc (0 : ℝ) s := by
        simpa [Set.uIcc_of_le hs] using ht
      rw [ballRadialMajorant_eq_aux_of_mem_cutoff hn
        ht'.1 ht'.2]
    _ = ballRadialAbelPrimitive n s :=
      integral_ballRadialAux_mul_pow_eq_abelPrimitive hn hs

private theorem integral_exp_neg_half_mul_pow {n : ℕ} (hn : 2 ≤ n) :
    (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-(t ^ 2) / 2) * t ^ (n - 2)) =
      2 ^ (((n : ℝ) - 3) / 2) * Real.Gamma (((n : ℝ) - 1) / 2) := by
  have hq : (-1 : ℝ) < (n : ℝ) - 2 := by
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (n : ℝ) - 2) (b := (1 / 2 : ℝ))
    (by norm_num) hq (by norm_num)
  calc
    (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-(t ^ 2) / 2) * t ^ (n - 2)) =
        ∫ t in Set.Ioi (0 : ℝ),
          t ^ ((n : ℝ) - 2) * Real.exp (-(1 / 2 : ℝ) * t ^ (2 : ℝ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : 0 ≤ t := ht.le
      have hcast : (((n - 2 : ℕ) : ℝ)) = (n : ℝ) - 2 := by
        rw [Nat.cast_sub (show 2 ≤ n by omega)]
        norm_num
      have hnatpow : t ^ (n - 2) = t ^ ((n : ℝ) - 2) := by
        rw [← Real.rpow_natCast t (n - 2), hcast]
      dsimp only
      rw [hnatpow, Real.rpow_two]
      ring_nf
    _ = (1 / 2 : ℝ) ^ (-(((n : ℝ) - 2) + 1) / 2) * (1 / 2) *
        Real.Gamma ((((n : ℝ) - 2) + 1) / 2) := h
    _ = 2 ^ (((n : ℝ) - 3) / 2) * Real.Gamma (((n : ℝ) - 1) / 2) := by
      have hpow : (1 / 2 : ℝ) ^ (-(((n : ℝ) - 2) + 1) / 2) =
          (2 : ℝ) ^ (((n : ℝ) - 1) / 2) := by
        calc
          (1 / 2 : ℝ) ^ (-(((n : ℝ) - 2) + 1) / 2) =
              (1 : ℝ) ^ (-(((n : ℝ) - 2) + 1) / 2) /
                (2 : ℝ) ^ (-(((n : ℝ) - 2) + 1) / 2) := by
            rw [Real.div_rpow (by positivity) (by positivity)]
          _ = ((2 : ℝ) ^ (-(((n : ℝ) - 2) + 1) / 2))⁻¹ := by
            rw [Real.one_rpow, one_div]
          _ = (2 : ℝ) ^ (-(-(((n : ℝ) - 2) + 1) / 2)) := by
            rw [Real.rpow_neg (by positivity)]
          _ = (2 : ℝ) ^ (((n : ℝ) - 1) / 2) := by
            congr 1
            ring
      rw [hpow]
      have hhalf : (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by
        rw [Real.rpow_neg (by positivity)]
        norm_num
      rw [hhalf, ← Real.rpow_add (by positivity)]
      congr 2 <;> ring

private lemma ballRadialMassCoefficient_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < ballRadialMassCoefficient n := by
  unfold ballRadialMassCoefficient
  have harg : 0 < ((n : ℝ) - 1) / 2 := by
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  exact inv_pos.mpr (mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.Gamma_pos_of_pos harg)) (Real.sqrt_pos.2 Real.pi_pos))

private theorem ballRadialMassCoefficient_mul_full_integral {n : ℕ} (hn : 2 ≤ n) :
    ballRadialMassCoefficient n *
      (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-(t ^ 2) / 2) * t ^ (n - 2)) =
      1 / Real.sqrt (2 * Real.pi) := by
  rw [integral_exp_neg_half_mul_pow hn]
  unfold ballRadialMassCoefficient
  have harg : 0 < ((n : ℝ) - 1) / 2 := by
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hgamma : Real.Gamma (((n : ℝ) - 1) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos harg).ne'
  have hsqrtpi : Real.sqrt Real.pi ≠ 0 := by positivity
  have hsqrtTwo : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hsqrtMul : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by positivity)]
  have hpowMul :
      (2 : ℝ) ^ (((n : ℝ) - 3) / 2) * Real.sqrt 2 =
        (2 : ℝ) ^ ((n : ℝ) / 2 - 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity)]
    congr 1
    ring
  rw [hsqrtMul]
  change
    ((2 : ℝ) ^ ((n : ℝ) / 2 - 1) * Real.Gamma (((n : ℝ) - 1) / 2) *
        Real.sqrt Real.pi)⁻¹ *
      ((2 : ℝ) ^ (((n : ℝ) - 3) / 2) *
        Real.Gamma (((n : ℝ) - 1) / 2)) =
      1 / (Real.sqrt 2 * Real.sqrt Real.pi)
  field_simp
  convert hpowMul using 1
  all_goals ring_nf

private def ballRadialAngularMassIntegrand (n : ℕ) (s θ : ℝ) : ℝ :=
  ballRadialMassCoefficient n * s ^ (n - 1) *
    Real.exp (-(s ^ 2 * Real.sin θ ^ 2) / 2) * Real.sin θ ^ (n - 2)

private lemma continuous_ballRadialAngularMassIntegrand (n : ℕ) (s : ℝ) :
    Continuous (ballRadialAngularMassIntegrand n s) := by
  unfold ballRadialAngularMassIntegrand
  fun_prop

private theorem ballRadialMass_scaledIntegral_eq_angularIntegral
    {n : ℕ} (hn : 2 ≤ n) :
    (ballRadialMassCoefficient n / ballGaussianNormalization n) *
        (∫ t in Set.Ioi (0 : ℝ), ballRadialMajorant n t * t ^ (n - 2)) =
      ∫ θ in (0 : ℝ)..Real.pi / 2,
        ballRadialAngularMassIntegrand n (ballRadialCutoff n hn) θ := by
  rw [integral_ballRadialMajorant_mul_pow_eq_abelPrimitive hn]
  unfold ballRadialAbelPrimitive ballRadialAbelIntegrand
    ballRadialAngularMassIntegrand
  have hnorm : ballGaussianNormalization n ≠ 0 :=
    (ballGaussianNormalization_pos n).ne'
  have hintegral :
      (∫ θ in (0 : ℝ)..Real.pi / 2,
        Real.sin θ ^ (n - 2) *
          Real.exp (-(ballRadialCutoff n hn ^ 2 * Real.sin θ ^ 2) / 2)) =
        ∫ θ in (0 : ℝ)..Real.pi / 2,
          Real.exp (-(ballRadialCutoff n hn ^ 2 * Real.sin θ ^ 2) / 2) *
            Real.sin θ ^ (n - 2) := by
    apply intervalIntegral.integral_congr
    intro θ _hθ
    ring
  rw [hintegral]
  calc
    (ballRadialMassCoefficient n / ballGaussianNormalization n) *
        (ballGaussianNormalization n * ballRadialCutoff n hn ^ (n - 1) *
          (∫ θ in (0 : ℝ)..Real.pi / 2,
            Real.exp (-(ballRadialCutoff n hn ^ 2 * Real.sin θ ^ 2) / 2) *
              Real.sin θ ^ (n - 2))) =
        (ballRadialMassCoefficient n * ballRadialCutoff n hn ^ (n - 1)) *
          (∫ θ in (0 : ℝ)..Real.pi / 2,
            Real.exp (-(ballRadialCutoff n hn ^ 2 * Real.sin θ ^ 2) / 2) *
              Real.sin θ ^ (n - 2)) := by
      field_simp
    _ = ∫ θ in (0 : ℝ)..Real.pi / 2,
        (ballRadialMassCoefficient n * ballRadialCutoff n hn ^ (n - 1)) *
          (Real.exp (-(ballRadialCutoff n hn ^ 2 * Real.sin θ ^ 2) / 2) *
            Real.sin θ ^ (n - 2)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ θ in (0 : ℝ)..Real.pi / 2,
        ballRadialMassCoefficient n * ballRadialCutoff n hn ^ (n - 1) *
          Real.exp (-(ballRadialCutoff n hn ^ 2 * Real.sin θ ^ 2) / 2) *
            Real.sin θ ^ (n - 2) := by
      apply intervalIntegral.integral_congr
      intro θ _hθ
      ring

private def ballRadialAngularSplit (s : ℝ) : ℝ :=
  Real.pi / 2 - (Real.sqrt s)⁻¹

private lemma ballRadialAngularSplit_mem {s : ℝ} (hs : 1 < s) :
    ballRadialAngularSplit s ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
  have hsqrt : 1 ≤ Real.sqrt s := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    simpa using hs.le
  have hinv : (Real.sqrt s)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).2 hsqrt
  have hone : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.two_le_pi]
  unfold ballRadialAngularSplit
  constructor
  · linarith
  · exact sub_le_self _ (inv_nonneg.mpr (Real.sqrt_nonneg _))

private lemma one_le_pi_div_two_mul_sqrt_mul_cos_of_le_split
    {s θ : ℝ} (hs : 1 < s) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ ballRadialAngularSplit s) :
    1 ≤ (Real.pi / 2) * Real.sqrt s * Real.cos θ := by
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.2 (by linarith)
  have hx0 : 0 ≤ Real.pi / 2 - θ := by
    have := hθ.trans (ballRadialAngularSplit_mem hs).2
    linarith
  have hxpi : Real.pi / 2 - θ ≤ Real.pi / 2 := by linarith
  have hsin := Real.mul_le_sin hx0 hxpi
  rw [Real.sin_pi_div_two_sub] at hsin
  have hxlower : (Real.sqrt s)⁻¹ ≤ Real.pi / 2 - θ := by
    unfold ballRadialAngularSplit at hθ
    linarith
  have hcos : 2 / Real.pi * (Real.sqrt s)⁻¹ ≤ Real.cos θ :=
    (mul_le_mul_of_nonneg_left hxlower (by positivity)).trans hsin
  have hmul := mul_le_mul_of_nonneg_left hcos
    (mul_nonneg (by positivity : 0 ≤ Real.pi / 2) hsqrtpos.le)
  calc
    (1 : ℝ) = (Real.pi / 2 * Real.sqrt s) *
        (2 / Real.pi * (Real.sqrt s)⁻¹) := by
      field_simp [Real.pi_ne_zero, hsqrtpos.ne']
    _ ≤ (Real.pi / 2 * Real.sqrt s) * Real.cos θ := hmul
    _ = (Real.pi / 2) * Real.sqrt s * Real.cos θ := by ring

private def ballRadialGaussianPowerIntegrand (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2) / 2) * t ^ (n - 2)

private lemma ballRadialGaussianPowerIntegrand_nonneg
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ballRadialGaussianPowerIntegrand n t := by
  unfold ballRadialGaussianPowerIntegrand
  positivity

private lemma continuous_ballRadialGaussianPowerIntegrand (n : ℕ) :
    Continuous (ballRadialGaussianPowerIntegrand n) := by
  unfold ballRadialGaussianPowerIntegrand
  fun_prop

private lemma intervalIntegral_comp_sin_ballRadialGaussianPowerIntegrand
    (n : ℕ) {s a : ℝ} :
    (∫ θ in (0 : ℝ)..a,
      ballRadialGaussianPowerIntegrand n (s * Real.sin θ) *
        (s * Real.cos θ)) =
      ∫ t in (0 : ℝ)..s * Real.sin a, ballRadialGaussianPowerIntegrand n t := by
  simpa using intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := a)
    (f := fun θ ↦ s * Real.sin θ) (f' := fun θ ↦ s * Real.cos θ)
    (g := ballRadialGaussianPowerIntegrand n)
    (fun θ _hθ ↦ (Real.hasDerivAt_sin θ).const_mul s)
    ((continuous_const.mul Real.continuous_cos).continuousOn)
    (continuous_ballRadialGaussianPowerIntegrand n)

private lemma integrableOn_ballRadialGaussianPowerIntegrand
    {n : ℕ} (hn : 2 ≤ n) :
    IntegrableOn (ballRadialGaussianPowerIntegrand n) (Set.Ioi (0 : ℝ)) := by
  have hq : (-1 : ℝ) < (n : ℝ) - 2 := by
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (s := (n : ℝ) - 2) (b := (1 / 2 : ℝ))
    hq (by norm_num) (by norm_num)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t ht
  unfold ballRadialGaussianPowerIntegrand
  have hcast : (((n - 2 : ℕ) : ℝ)) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub hn]
    norm_num
  have hnatpow : t ^ (n - 2) = t ^ ((n : ℝ) - 2) := by
    rw [← Real.rpow_natCast t (n - 2), hcast]
  dsimp only
  rw [hnatpow]
  rw [mul_comm]
  congr 1
  rw [Real.rpow_two]
  ring_nf

private lemma ballRadialAngularMassIntegrand_le_comp
    {n : ℕ} (hn : 2 ≤ n) {s θ : ℝ} (hs : 1 < s)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ ballRadialAngularSplit s) :
    ballRadialAngularMassIntegrand n s θ ≤
      ((Real.pi / 2) * Real.sqrt s * ballRadialMassCoefficient n) *
        (ballRadialGaussianPowerIntegrand n (s * Real.sin θ) *
          (s * Real.cos θ)) := by
  have hsin : 0 ≤ Real.sin θ := by
    have hθpi : θ ≤ Real.pi :=
      hθ.trans (ballRadialAngularSplit_mem hs).2 |>.trans (by linarith [Real.pi_pos])
    exact Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθpi
  have hmassNonneg : 0 ≤ ballRadialAngularMassIntegrand n s θ := by
    unfold ballRadialAngularMassIntegrand
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (ballRadialMassCoefficient_pos hn).le
          (pow_nonneg (zero_le_one.trans hs.le) _))
        (Real.exp_nonneg _)) (pow_nonneg hsin _)
  have hone := one_le_pi_div_two_mul_sqrt_mul_cos_of_le_split hs hθ0 hθ
  calc
    ballRadialAngularMassIntegrand n s θ =
        ballRadialAngularMassIntegrand n s θ * 1 := (mul_one _).symm
    _ ≤ ballRadialAngularMassIntegrand n s θ *
        ((Real.pi / 2) * Real.sqrt s * Real.cos θ) :=
      mul_le_mul_of_nonneg_left hone hmassNonneg
    _ = ((Real.pi / 2) * Real.sqrt s * ballRadialMassCoefficient n) *
        (ballRadialGaussianPowerIntegrand n (s * Real.sin θ) *
          (s * Real.cos θ)) := by
      unfold ballRadialAngularMassIntegrand ballRadialGaussianPowerIntegrand
      rw [show s ^ (n - 1) = s ^ (n - 2) * s by
        rw [← pow_succ]; congr 1; omega, mul_pow]
      ring

private theorem integral_ballRadialAngularMassIntegrand_first_le
    {n : ℕ} (hn : 2 ≤ n) :
    let s := ballRadialCutoff n hn
    (∫ θ in (0 : ℝ)..ballRadialAngularSplit s,
      ballRadialAngularMassIntegrand n s θ) ≤
      (Real.pi / 2) * Real.sqrt s * (1 / Real.sqrt (2 * Real.pi)) := by
  let s := ballRadialCutoff n hn
  let a := ballRadialAngularSplit s
  have hs : 1 < s := ballRadialCutoff_gt_one hn
  have ha := ballRadialAngularSplit_mem hs
  let K : ℝ := (Real.pi / 2) * Real.sqrt s * ballRadialMassCoefficient n
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (ballRadialMassCoefficient_pos hn).le
  have hmono :
      (∫ θ in (0 : ℝ)..a, ballRadialAngularMassIntegrand n s θ) ≤
        ∫ θ in (0 : ℝ)..a,
          K * (ballRadialGaussianPowerIntegrand n (s * Real.sin θ) *
            (s * Real.cos θ)) := by
    apply intervalIntegral.integral_mono_on ha.1
    · exact (continuous_ballRadialAngularMassIntegrand n s).intervalIntegrable _ _
    · exact ((continuous_ballRadialGaussianPowerIntegrand n).comp
        (continuous_const.mul Real.continuous_sin) |>.mul
          (continuous_const.mul Real.continuous_cos) |>.const_mul K)
        |>.intervalIntegrable _ _
    · intro θ hθ
      exact ballRadialAngularMassIntegrand_le_comp hn hs hθ.1 hθ.2
  have hsubst := intervalIntegral_comp_sin_ballRadialGaussianPowerIntegrand
    n (s := s) (a := a)
  have hsa : 0 ≤ s * Real.sin a := by
    have hasin : 0 ≤ Real.sin a :=
      Real.sin_nonneg_of_nonneg_of_le_pi ha.1 (ha.2.trans (by linarith [Real.pi_pos]))
    exact mul_nonneg (zero_le_one.trans hs.le) hasin
  have htoFull :
      (∫ t in (0 : ℝ)..s * Real.sin a, ballRadialGaussianPowerIntegrand n t) ≤
        ∫ t in Set.Ioi (0 : ℝ), ballRadialGaussianPowerIntegrand n t := by
    rw [intervalIntegral.integral_of_le hsa]
    apply setIntegral_mono_set (integrableOn_ballRadialGaussianPowerIntegrand hn)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      simpa only [Pi.zero_apply] using
        ballRadialGaussianPowerIntegrand_nonneg n ht.le
    · filter_upwards with t
      intro ht
      exact ht.1
  calc
    (∫ θ in (0 : ℝ)..a, ballRadialAngularMassIntegrand n s θ) ≤
        ∫ θ in (0 : ℝ)..a,
          K * (ballRadialGaussianPowerIntegrand n (s * Real.sin θ) *
            (s * Real.cos θ)) := hmono
    _ = K * (∫ θ in (0 : ℝ)..a,
        ballRadialGaussianPowerIntegrand n (s * Real.sin θ) *
          (s * Real.cos θ)) := intervalIntegral.integral_const_mul _ _
    _ = K * (∫ t in (0 : ℝ)..s * Real.sin a,
        ballRadialGaussianPowerIntegrand n t) := by rw [hsubst]
    _ ≤ K * (∫ t in Set.Ioi (0 : ℝ),
        ballRadialGaussianPowerIntegrand n t) :=
      mul_le_mul_of_nonneg_left htoFull hK
    _ = (Real.pi / 2) * Real.sqrt s *
        (1 / Real.sqrt (2 * Real.pi)) := by
      dsimp only [K]
      rw [show (∫ t in Set.Ioi (0 : ℝ),
          ballRadialGaussianPowerIntegrand n t) =
          ∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-(t ^ 2) / 2) * t ^ (n - 2) from rfl]
      rw [← ballRadialMassCoefficient_mul_full_integral hn]
      ring

private lemma ballRadialMassCoefficient_mul_peak_le_one_div_pi
    {n : ℕ} (hn : 3 ≤ n) :
    ballRadialMassCoefficient n *
      (Real.exp (-(((n : ℝ) - 2) / 2)) *
        ((n : ℝ) - 2) ^ (((n : ℝ) - 2) / 2)) ≤ 1 / Real.pi := by
  have h := ball_radial_gamma_peak_le (n := n) hn
  unfold ballRadialMassCoefficient
  calc
    (2 ^ ((n : ℝ) / 2 - 1) * Real.Gamma (((n : ℝ) - 1) / 2) *
          Real.sqrt Real.pi)⁻¹ *
        (Real.exp (-(((n : ℝ) - 2) / 2)) *
          ((n : ℝ) - 2) ^ (((n : ℝ) - 2) / 2)) =
        (Real.exp (-(((n : ℝ) - 2) / 2)) *
          ((n : ℝ) - 2) ^ (((n : ℝ) - 2) / 2)) /
          (2 ^ ((n : ℝ) / 2 - 1) * Real.Gamma (((n : ℝ) - 1) / 2) *
            Real.sqrt Real.pi) := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ 1 / Real.pi := h

private lemma ballRadialMassCoefficient_mul_gaussianPower_le_one_div_pi
    {n : ℕ} (hn : 3 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    ballRadialMassCoefficient n * ballRadialGaussianPowerIntegrand n t ≤
      1 / Real.pi := by
  have hcast : (((n - 2 : ℕ) : ℝ)) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (show 2 ≤ n by omega)]
    norm_num
  have hnatpow : t ^ (n - 2) = t ^ ((n : ℝ) - 2) := by
    rw [← Real.rpow_natCast t (n - 2), hcast]
  have hpeak := exp_neg_half_mul_rpow_le_peak hn ht
  have hc := ballRadialMassCoefficient_pos (show 2 ≤ n by omega)
  calc
    ballRadialMassCoefficient n * ballRadialGaussianPowerIntegrand n t =
        ballRadialMassCoefficient n *
          (Real.exp (-(t ^ 2) / 2) * t ^ ((n : ℝ) - 2)) := by
      unfold ballRadialGaussianPowerIntegrand
      rw [hnatpow]
    _ ≤ ballRadialMassCoefficient n *
        (Real.exp (-(((n : ℝ) - 2) / 2)) *
          ((n : ℝ) - 2) ^ (((n : ℝ) - 2) / 2)) :=
      mul_le_mul_of_nonneg_left hpeak hc.le
    _ ≤ 1 / Real.pi := ballRadialMassCoefficient_mul_peak_le_one_div_pi hn

private lemma ballRadialMassCoefficient_two :
    ballRadialMassCoefficient 2 = 1 / Real.pi := by
  unfold ballRadialMassCoefficient
  norm_num only [Nat.cast_ofNat]
  rw [Real.Gamma_one_half_eq, one_mul]
  have hsqrt : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_nonneg
  rw [hsqrt, inv_eq_one_div]

private lemma ballRadialMassCoefficient_mul_gaussianPower_le_one_div_pi_two
    {t : ℝ} (_ht : 0 ≤ t) :
    ballRadialMassCoefficient 2 * ballRadialGaussianPowerIntegrand 2 t ≤
      1 / Real.pi := by
  rw [ballRadialMassCoefficient_two]
  unfold ballRadialGaussianPowerIntegrand
  simp only [Nat.reduceSubDiff, pow_zero, mul_one]
  have hexp : Real.exp (-(t ^ 2) / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp
    (div_nonneg zero_le_one Real.pi_pos.le)

private lemma ballRadialAngularMassIntegrand_le_s_div_pi
    {n : ℕ} (hn : 2 ≤ n) {s θ : ℝ} (hs : 0 ≤ s) (hθ : 0 ≤ θ)
    (hθpi : θ ≤ Real.pi / 2) :
    ballRadialAngularMassIntegrand n s θ ≤ s / Real.pi := by
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ (hθpi.trans (by linarith [Real.pi_pos]))
  have ht : 0 ≤ s * Real.sin θ := mul_nonneg hs hsin
  have hcoeff : ballRadialMassCoefficient n *
      ballRadialGaussianPowerIntegrand n (s * Real.sin θ) ≤ 1 / Real.pi := by
    by_cases hn2 : n = 2
    · subst n
      exact ballRadialMassCoefficient_mul_gaussianPower_le_one_div_pi_two ht
    · exact ballRadialMassCoefficient_mul_gaussianPower_le_one_div_pi
        (show 3 ≤ n by omega) ht
  calc
    ballRadialAngularMassIntegrand n s θ =
        s * (ballRadialMassCoefficient n *
          ballRadialGaussianPowerIntegrand n (s * Real.sin θ)) := by
      unfold ballRadialAngularMassIntegrand ballRadialGaussianPowerIntegrand
      rw [show s ^ (n - 1) = s ^ (n - 2) * s by
        rw [← pow_succ]; congr 1; omega, mul_pow]
      ring
    _ ≤ s * (1 / Real.pi) := mul_le_mul_of_nonneg_left hcoeff hs
    _ = s / Real.pi := by ring

private theorem integral_ballRadialAngularMassIntegrand_tail_le
    {n : ℕ} (hn : 2 ≤ n) :
    let s := ballRadialCutoff n hn
    (∫ θ in ballRadialAngularSplit s..Real.pi / 2,
      ballRadialAngularMassIntegrand n s θ) ≤ Real.sqrt s / Real.pi := by
  let s := ballRadialCutoff n hn
  let a := ballRadialAngularSplit s
  have hs : 1 < s := ballRadialCutoff_gt_one hn
  have ha := ballRadialAngularSplit_mem hs
  calc
    (∫ θ in a..Real.pi / 2, ballRadialAngularMassIntegrand n s θ) ≤
        ∫ _θ in a..Real.pi / 2, s / Real.pi := by
      apply intervalIntegral.integral_mono_on ha.2
      · exact (continuous_ballRadialAngularMassIntegrand n s).intervalIntegrable _ _
      · exact continuous_const.intervalIntegrable _ _
      · intro θ hθ
        exact ballRadialAngularMassIntegrand_le_s_div_pi hn
          (zero_le_one.trans hs.le) (ha.1.trans hθ.1) hθ.2
    _ = Real.sqrt s / Real.pi := by
      rw [intervalIntegral.integral_const]
      simp only [sub_eq_add_neg, smul_eq_mul]
      have hsqrt : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
      unfold a ballRadialAngularSplit
      field_simp
      rw [Real.sq_sqrt (by linarith)]
      ring

private lemma sqrt_ballRadialCutoff_le_three_halves_mul_rpow
    {n : ℕ} (hn : 2 ≤ n) :
    Real.sqrt (ballRadialCutoff n hn) ≤
      (3 / 2 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) := by
  let s := ballRadialCutoff n hn
  have hspos : 0 < s := lt_trans zero_lt_one (ballRadialCutoff_gt_one hn)
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hsUpper : s ≤ Real.sqrt (2 * (n : ℝ)) := (ballRadialCutoff_mem hn).2
  have hsqrtTwo : Real.sqrt (2 : ℝ) ≤ 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  have hsle : s ≤ 2 * Real.sqrt (n : ℝ) := by
    calc
      s ≤ Real.sqrt (2 * (n : ℝ)) := hsUpper
      _ = Real.sqrt 2 * Real.sqrt (n : ℝ) := by
        rw [Real.sqrt_mul (by positivity)]
      _ ≤ 2 * Real.sqrt (n : ℝ) :=
        mul_le_mul_of_nonneg_right hsqrtTwo (Real.sqrt_nonneg _)
  have hquarter : Real.sqrt (Real.sqrt (n : ℝ)) =
      (n : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hn0]
    norm_num
  have hsq :
      (Real.sqrt s) ^ 2 ≤
        ((3 / 2 : ℝ) * Real.sqrt (Real.sqrt (n : ℝ))) ^ 2 := by
    rw [Real.sq_sqrt hspos.le, mul_pow,
      Real.sq_sqrt (Real.sqrt_nonneg _)]
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  rw [← hquarter]
  exact (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp hsq

private lemma first_ballRadialAngularMassIntegral_le_three_halves_mul_rpow
    {n : ℕ} (hn : 2 ≤ n) :
    let s := ballRadialCutoff n hn
    (∫ θ in (0 : ℝ)..ballRadialAngularSplit s,
      ballRadialAngularMassIntegrand n s θ) ≤
      (3 / 2 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) := by
  let s := ballRadialCutoff n hn
  have hfirst := integral_ballRadialAngularMassIntegrand_first_le hn
  have hsqrtBound := sqrt_ballRadialCutoff_le_three_halves_mul_rpow hn
  have hpiSqrt : Real.pi / 2 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have hpile : Real.pi ≤ 4 := Real.pi_le_four
    nlinarith [Real.pi_pos]
  have hden : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hcoef : (Real.pi / 2) * (1 / Real.sqrt (2 * Real.pi)) ≤ 1 := by
    rw [mul_one_div, div_le_one hden]
    exact hpiSqrt
  calc
    (∫ θ in (0 : ℝ)..ballRadialAngularSplit s,
        ballRadialAngularMassIntegrand n s θ) ≤
        (Real.pi / 2) * Real.sqrt s * (1 / Real.sqrt (2 * Real.pi)) := hfirst
    _ = ((Real.pi / 2) * (1 / Real.sqrt (2 * Real.pi))) * Real.sqrt s := by ring
    _ ≤ 1 * Real.sqrt s :=
      mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)
    _ = Real.sqrt s := one_mul _
    _ ≤ (3 / 2 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) := hsqrtBound

private lemma tail_ballRadialAngularMassIntegral_le_one_half_mul_rpow
    {n : ℕ} (hn : 2 ≤ n) :
    let s := ballRadialCutoff n hn
    (∫ θ in ballRadialAngularSplit s..Real.pi / 2,
      ballRadialAngularMassIntegrand n s θ) ≤
      (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) := by
  let s := ballRadialCutoff n hn
  let q : ℝ := (n : ℝ) ^ (1 / 4 : ℝ)
  have htail := integral_ballRadialAngularMassIntegrand_tail_le hn
  have hsqrtBound : Real.sqrt s ≤ (3 / 2 : ℝ) * q :=
    sqrt_ballRadialCutoff_le_three_halves_mul_rpow hn
  have hq : 0 ≤ q := Real.rpow_nonneg (by positivity) _
  calc
    (∫ θ in ballRadialAngularSplit s..Real.pi / 2,
        ballRadialAngularMassIntegrand n s θ) ≤ Real.sqrt s / Real.pi := htail
    _ ≤ ((3 / 2 : ℝ) * q) / Real.pi :=
      div_le_div_of_nonneg_right hsqrtBound Real.pi_pos.le
    _ ≤ ((3 / 2 : ℝ) * q) / 3 := by
      exact (div_le_div_iff_of_pos_left
        (a := (3 / 2 : ℝ) * q) (b := Real.pi) (c := 3)
        (by positivity : 0 < (3 / 2 : ℝ) * q)
        Real.pi_pos (by norm_num : (0 : ℝ) < 3)).2 Real.pi_gt_three.le
    _ = (1 / 2 : ℝ) * q := by ring

/-- Ball's radial majorant has mass at most `2 n^(1/4)` after the exact polar-coordinate
normalization.  This is the one-dimensional estimate on printed pp. 418--419. -/
theorem integral_ballRadialMajorant_rpow_le {n : ℕ} (hn : 2 ≤ n) :
    (ballRadialMassCoefficient n / ballGaussianNormalization n) *
        (∫ t in Set.Ioi (0 : ℝ), ballRadialMajorant n t * t ^ (n - 2)) ≤
      2 * (n : ℝ) ^ (1 / 4 : ℝ) := by
  let s := ballRadialCutoff n hn
  let a := ballRadialAngularSplit s
  rw [ballRadialMass_scaledIntegral_eq_angularIntegral hn]
  have hfirst := first_ballRadialAngularMassIntegral_le_three_halves_mul_rpow hn
  have htail := tail_ballRadialAngularMassIntegral_le_one_half_mul_rpow hn
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((continuous_ballRadialAngularMassIntegrand n s).intervalIntegrable (0 : ℝ) a)
    ((continuous_ballRadialAngularMassIntegrand n s).intervalIntegrable a (Real.pi / 2))
  rw [← hadd]
  linarith

/-- The polar-coordinate surface factor in dimension `n - 1`. -/
def ballRadialPolarFactor (n : ℕ) : ℝ :=
  ((n - 1 : ℕ) : ℝ) *
    volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin (n - 1))) 1)

private lemma integral_standardGaussianDensityReal_eq_one {d : ℕ} :
    (∫ x : EuclideanSpace ℝ (Fin d), standardGaussianDensityReal x) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall standardGaussianDensityReal_nonneg)
    measurable_standardGaussianDensityReal.aestronglyMeasurable,
    lintegral_standardGaussianDensityReal_eq_one, ENNReal.toReal_one]

private lemma integral_ballGaussianNormalization_exp_norm_eq
    {n : ℕ} (hn : 2 ≤ n) :
    (∫ x : EuclideanSpace ℝ (Fin (n - 1)),
      ballGaussianNormalization n * Real.exp (-‖x‖ ^ 2 / 2)) =
      1 / Real.sqrt (2 * Real.pi) := by
  have hnEq : n = (n - 1) + 1 := by omega
  have hpoint (x : EuclideanSpace ℝ (Fin (n - 1))) :
      ballGaussianNormalization n * Real.exp (-‖x‖ ^ 2 / 2) =
        (1 / Real.sqrt (2 * Real.pi)) * standardGaussianDensityReal x := by
    unfold ballGaussianNormalization standardGaussianDensityReal
    have hpow : (√(2 * Real.pi))⁻¹ ^ n =
        (√(2 * Real.pi))⁻¹ ^ (n - 1) * (√(2 * Real.pi))⁻¹ := by
      calc
        (√(2 * Real.pi))⁻¹ ^ n =
            (√(2 * Real.pi))⁻¹ ^ ((n - 1) + 1) := by congr 1
        _ = (√(2 * Real.pi))⁻¹ ^ (n - 1) * (√(2 * Real.pi))⁻¹ :=
          pow_succ _ _
    rw [hpow]
    have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
    field_simp
  calc
    (∫ x : EuclideanSpace ℝ (Fin (n - 1)),
        ballGaussianNormalization n * Real.exp (-‖x‖ ^ 2 / 2)) =
        ∫ x : EuclideanSpace ℝ (Fin (n - 1)),
          (1 / Real.sqrt (2 * Real.pi)) * standardGaussianDensityReal x := by
      apply integral_congr_ae
      filter_upwards with x
      exact hpoint x
    _ = (1 / Real.sqrt (2 * Real.pi)) *
        ∫ x : EuclideanSpace ℝ (Fin (n - 1)), standardGaussianDensityReal x := by
      rw [integral_const_mul]
    _ = 1 / Real.sqrt (2 * Real.pi) := by
      rw [integral_standardGaussianDensityReal_eq_one, mul_one]

/-- The explicit Gamma coefficient is exactly the Haar polar-coordinate factor times the
`n`-dimensional Gaussian normalization. -/
theorem ballRadialPolarFactor_mul_normalization {n : ℕ} (hn : 2 ≤ n) :
    ballRadialPolarFactor n * ballGaussianNormalization n =
      ballRadialMassCoefficient n := by
  letI : Nonempty (Fin (n - 1)) := ⟨⟨0, by omega⟩⟩
  let f : ℝ → ℝ := fun t ↦
    ballGaussianNormalization n * Real.exp (-(t ^ 2) / 2)
  have hhaar := MeasureTheory.integral_fun_norm_addHaar
    (E := EuclideanSpace ℝ (Fin (n - 1))) (μ := volume) f
  have hleft : (∫ x : EuclideanSpace ℝ (Fin (n - 1)), f ‖x‖) =
      1 / Real.sqrt (2 * Real.pi) := by
    simpa only [f, neg_div] using integral_ballGaussianNormalization_exp_norm_eq hn
  have hright :
      (∫ t in Set.Ioi (0 : ℝ), t ^ (n - 2) * f t) =
        ballGaussianNormalization n *
          (∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-(t ^ 2) / 2) * t ^ (n - 2)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _ht
    dsimp only [f]
    ring
  have hpolar :
      1 / Real.sqrt (2 * Real.pi) =
        ballRadialPolarFactor n * ballGaussianNormalization n *
          (∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-(t ^ 2) / 2) * t ^ (n - 2)) := by
    rw [← hleft, hhaar]
    simp only [finrank_euclideanSpace, Fintype.card_fin,
      show n - 1 - 1 = n - 2 by omega, smul_eq_mul, nsmul_eq_mul]
    rw [hright]
    unfold ballRadialPolarFactor
    ring
  have hcoeff := ballRadialMassCoefficient_mul_full_integral hn
  have hIpos : 0 < (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-(t ^ 2) / 2) * t ^ (n - 2)) := by
    rw [integral_exp_neg_half_mul_pow hn]
    have harg : 0 < ((n : ℝ) - 1) / 2 := by
      have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.Gamma_pos_of_pos harg)
  apply mul_right_cancel₀ hIpos.ne'
  exact hpolar.symm.trans hcoeff.symm

private lemma integrableOn_ballRadialMajorant_mul_pow {n : ℕ} (hn : 2 ≤ n) :
    IntegrableOn (fun t : ℝ ↦ t ^ (n - 2) * ballRadialMajorant n t)
      (Set.Ioi (0 : ℝ)) := by
  let S : ℝ := Real.sqrt (2 * n)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hcompact : IntegrableOn
      (fun t : ℝ ↦ t ^ (n - 2) * ballRadialMajorant n t) (Set.Icc 0 S) :=
    ((continuous_id.pow (n - 2)).mul (continuous_ballRadialMajorant n)).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hsmall : IntegrableOn
      (fun t : ℝ ↦ t ^ (n - 2) * ballRadialMajorant n t) (Set.Ioc 0 S) :=
    hcompact.mono_set Set.Ioc_subset_Icc_self
  have htail : IntegrableOn
      (fun t : ℝ ↦ t ^ (n - 2) * ballRadialMajorant n t) (Set.Ioi S) := by
    apply integrableOn_zero.congr_fun _ measurableSet_Ioi
    intro t ht
    dsimp only
    rw [ballRadialMajorant_eq_zero_of_sqrt_two_mul_le hn ht.le, mul_zero]
  rw [show Set.Ioi (0 : ℝ) = Set.Ioc 0 S ∪ Set.Ioi S by
    ext t
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro ht
      by_cases h : t ≤ S
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr (lt_of_not_ge h)
    · rintro (ht | ht) <;> linarith]
  exact hsmall.union htail

/-- The Euclidean integral of Ball's radial majorant on `R^(n-1)` is at most `2 n^(1/4)`. -/
theorem integral_ballRadialMajorant_norm_le {n : ℕ} (hn : 2 ≤ n) :
    (∫ x : EuclideanSpace ℝ (Fin (n - 1)),
      ballRadialMajorant n ‖x‖) ≤ 2 * (n : ℝ) ^ (1 / 4 : ℝ) := by
  letI : Nonempty (Fin (n - 1)) := ⟨⟨0, by omega⟩⟩
  have hhaar := MeasureTheory.integral_fun_norm_addHaar
    (E := EuclideanSpace ℝ (Fin (n - 1))) (μ := volume)
    (ballRadialMajorant n)
  have hfactor : ballRadialPolarFactor n =
      ballRadialMassCoefficient n / ballGaussianNormalization n := by
    apply (eq_div_iff (ballGaussianNormalization_pos n).ne').2
    exact ballRadialPolarFactor_mul_normalization hn
  rw [hhaar]
  simp only [finrank_euclideanSpace, Fintype.card_fin,
    show n - 1 - 1 = n - 2 by omega, smul_eq_mul, nsmul_eq_mul]
  rw [show
      ((n - 1 : ℕ) : ℝ) *
          (volume.real (Metric.ball
            (0 : EuclideanSpace ℝ (Fin (n - 1))) 1) *
            (∫ t in Set.Ioi (0 : ℝ),
              t ^ (n - 2) * ballRadialMajorant n t)) =
        ballRadialPolarFactor n *
          (∫ t in Set.Ioi (0 : ℝ),
            t ^ (n - 2) * ballRadialMajorant n t) by
      unfold ballRadialPolarFactor
      ring]
  rw [hfactor]
  simpa only [mul_comm] using integral_ballRadialMajorant_rpow_le hn

/-- ENNReal form of the Euclidean mass bound, used by the projection-area argument. -/
theorem lintegral_ballRadialMajorant_norm_le {n : ℕ} (hn : 2 ≤ n) :
    (∫⁻ x : EuclideanSpace ℝ (Fin (n - 1)),
      ENNReal.ofReal (ballRadialMajorant n ‖x‖)) ≤
      ENNReal.ofReal (2 * (n : ℝ) ^ (1 / 4 : ℝ)) := by
  letI : Nonempty (Fin (n - 1)) := ⟨⟨0, by omega⟩⟩
  have hradial : Integrable (fun x : EuclideanSpace ℝ (Fin (n - 1)) ↦
      ballRadialMajorant n ‖x‖) :=
    (MeasureTheory.integrable_fun_norm_addHaar (μ := volume)
      (E := EuclideanSpace ℝ (Fin (n - 1)))).2 (by
        simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
        rw [show n - 1 - 1 = n - 2 by omega]
        exact integrableOn_ballRadialMajorant_mul_pow hn)
  rw [← ofReal_integral_eq_lintegral_ofReal hradial
    (Filter.Eventually.of_forall fun x ↦ ballRadialMajorant_nonneg n ‖x‖)]
  exact ENNReal.ofReal_le_ofReal (integral_ballRadialMajorant_norm_le hn)

/-- Coordinate-free form of the radial mass bound for any finite-dimensional real inner-product
space of dimension `n - 1`. -/
theorem lintegral_ballRadialMajorant_norm_le_of_finrank
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {n : ℕ} (hn : 2 ≤ n) (hrank : Module.finrank ℝ E = n - 1) :
    (∫⁻ x : E, ENNReal.ofReal (ballRadialMajorant n ‖x‖)) ≤
      ENNReal.ofReal (2 * (n : ℝ) ^ (1 / 4 : ℝ)) := by
  let b := stdOrthonormalBasis ℝ E
  have hcomp :
      (fun x : E ↦ ENNReal.ofReal (ballRadialMajorant n ‖x‖)) =
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ↦
          ENNReal.ofReal (ballRadialMajorant n ‖y‖)) ∘ b.repr := by
    funext x
    rw [Function.comp_apply, b.repr.norm_map]
  rw [hcomp]
  calc
    (∫⁻ x : E, ENNReal.ofReal (ballRadialMajorant n ‖b.repr x‖)) =
        ∫⁻ y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
          ENNReal.ofReal (ballRadialMajorant n ‖y‖) :=
      b.repr.measurePreserving.lintegral_comp
        (((continuous_ballRadialMajorant n).comp continuous_norm).measurable.ennreal_ofReal)
    _ ≤ ENNReal.ofReal (2 * (n : ℝ) ^ (1 / 4 : ℝ)) := by
      rw [hrank]
      exact lintegral_ballRadialMajorant_norm_le hn

end ProbabilityTheory
