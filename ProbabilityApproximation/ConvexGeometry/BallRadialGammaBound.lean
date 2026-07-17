/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Ball's radial Gamma peak estimate

This module proves the one-dimensional maximum and the normalized Gamma-function estimate used in
Keith Ball's proof of the Gaussian perimeter bound for convex sets.  They are the analytic steps
on printed p. 419 of Ball, *The reverse isoperimetric problem for Gaussian measure*, Discrete &
Computational Geometry **10** (1993), 411--420.

The maximum follows from `log x ≤ x - 1`.  For the normalized peak, the proof separates integer
and half-integer Gamma values.  The integer branch uses Mathlib's effective lower Stirling bound;
the half-integer branch combines the Gamma duplication formula with both the lower bound and the
monotonic upper bound for the Stirling sequence.  Thus the bound below retains Ball's exact
`1 / π` constant rather than appealing to an asymptotic statement.
-/

open scoped Real

noncomputable section

namespace ProbabilityTheory

private lemma one_add_div_two_mul_pow_le_exp_half (k : ℕ) (hk : 1 ≤ k) :
    (1 + 1 / (2 * (k : ℝ))) ^ k ≤ Real.exp (1 / 2) := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hbase : 0 < 1 + 1 / (2 * (k : ℝ)) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hbase
  have hscaled := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k)
  rw [← Real.exp_log (pow_pos hbase k), ← Real.exp_log (Real.exp_pos (1 / 2))]
  apply Real.exp_le_exp.mpr
  rw [Real.log_pow, Real.log_exp]
  calc
    (k : ℝ) * Real.log (1 + 1 / (2 * (k : ℝ))) ≤
        (k : ℝ) * ((1 + 1 / (2 * (k : ℝ))) - 1) := hscaled
    _ = 1 / 2 := by field_simp; ring

private lemma odd_half_gamma_lower (k : ℕ) (hk : 1 ≤ k) :
    Real.sqrt Real.pi * Real.exp (-((k : ℝ) + 1 / 2)) *
        ((k : ℝ) + 1 / 2) ^ ((k : ℝ) + 1 / 2) ≤
      (Nat.factorial k : ℝ) := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  let q : ℝ := 1 + 1 / (2 * (k : ℝ))
  let a : ℝ := (k : ℝ) + 1 / 2
  have hq : 0 < q := by dsimp [q]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hpow : q ^ k ≤ Real.exp (1 / 2) := by
    simpa only [q] using one_add_div_two_mul_pow_le_exp_half k hk
  have hfactor : Real.exp (-(1 / 2)) * q ^ k ≤ 1 := by
    calc
      Real.exp (-(1 / 2)) * q ^ k ≤
          Real.exp (-(1 / 2)) * Real.exp (1 / 2) :=
        mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add]; norm_num
  have hsqrt : Real.sqrt Real.pi * Real.sqrt a ≤
      Real.sqrt (2 * Real.pi * (k : ℝ)) := by
    rw [← Real.sqrt_mul Real.pi_nonneg]
    apply Real.sqrt_le_sqrt
    have ha_le : a ≤ 2 * (k : ℝ) := by
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
      dsimp [a]
      linarith
    calc
      Real.pi * a ≤ Real.pi * (2 * (k : ℝ)) :=
        mul_le_mul_of_nonneg_left ha_le Real.pi_nonneg
      _ = 2 * Real.pi * (k : ℝ) := by ring
  have hbracket :
      (Real.sqrt Real.pi * Real.sqrt a) *
          (Real.exp (-(1 / 2)) * q ^ k) ≤
        Real.sqrt (2 * Real.pi * (k : ℝ)) := by
    calc
      (Real.sqrt Real.pi * Real.sqrt a) *
          (Real.exp (-(1 / 2)) * q ^ k) ≤
          (Real.sqrt Real.pi * Real.sqrt a) * 1 :=
        mul_le_mul_of_nonneg_left hfactor (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = Real.sqrt Real.pi * Real.sqrt a := by ring
      _ ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) := hsqrt
  have hfactorTarget :
      Real.sqrt Real.pi * Real.exp (-a) * a ^ a =
        (Real.exp (-(k : ℝ)) * (k : ℝ) ^ k) *
          ((Real.sqrt Real.pi * Real.sqrt a) *
            (Real.exp (-(1 / 2)) * q ^ k)) := by
    have haq : a = (k : ℝ) * q := by
      dsimp [a, q]
      field_simp
    have hak : a ^ k = (k : ℝ) ^ k * q ^ k := by rw [haq, mul_pow]
    have hexp : Real.exp (-a) =
        Real.exp (-(k : ℝ)) * Real.exp (-(1 / 2)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [a]
      ring
    rw [Real.rpow_add ha (k : ℝ) (1 / 2), Real.rpow_natCast,
      ← Real.sqrt_eq_rpow, hak, hexp]
    ring
  have hfactorStirling :
      Real.sqrt (2 * Real.pi * (k : ℝ)) *
          ((k : ℝ) / Real.exp 1) ^ k =
        (Real.exp (-(k : ℝ)) * (k : ℝ) ^ k) *
          Real.sqrt (2 * Real.pi * (k : ℝ)) := by
    rw [div_pow, ← Real.exp_nat_mul, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  rw [show (k : ℝ) + 1 / 2 = a by rfl, hfactorTarget]
  calc
    (Real.exp (-(k : ℝ)) * (k : ℝ) ^ k) *
        ((Real.sqrt Real.pi * Real.sqrt a) *
          (Real.exp (-(1 / 2)) * q ^ k)) ≤
        (Real.exp (-(k : ℝ)) * (k : ℝ) ^ k) *
          Real.sqrt (2 * Real.pi * (k : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hbracket
        (mul_nonneg (Real.exp_nonneg _) (pow_nonneg hkpos.le _))
    _ = Real.sqrt (2 * Real.pi * (k : ℝ)) *
        ((k : ℝ) / Real.exp 1) ^ k := hfactorStirling.symm
    _ ≤ (Nat.factorial k : ℝ) := Stirling.le_factorial_stirling k

private lemma factorial_le_exp_div_sqrt_two_mul_stirling (k : ℕ) (hk : 1 ≤ k) :
    (Nat.factorial k : ℝ) ≤
      (Real.exp 1 / Real.sqrt 2) *
        (Real.sqrt (2 * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    exact ⟨k - 1, by omega⟩
  have hseq : Stirling.stirlingSeq (j + 1) ≤ Real.exp 1 / Real.sqrt 2 := by
    calc
      Stirling.stirlingSeq (j + 1) ≤ Stirling.stirlingSeq 1 := by
        simpa only [Function.comp_apply, Nat.succ_eq_add_one] using
          Stirling.stirlingSeq'_antitone (Nat.zero_le j)
      _ = Real.exp 1 / Real.sqrt 2 := Stirling.stirlingSeq_one
  rw [Stirling.stirlingSeq] at hseq
  exact (div_le_iff₀ (by positivity)).mp hseq

private lemma exp_one_le_two_sqrt_pi : Real.exp 1 ≤ 2 * Real.sqrt Real.pi := by
  have hsqrt : 3 / 2 < Real.sqrt Real.pi := by
    have hsq := Real.sq_sqrt Real.pi_nonneg
    have hsnonneg := Real.sqrt_nonneg Real.pi
    nlinarith [Real.pi_gt_three]
  exact Real.exp_one_lt_three.le.trans (by linarith)

private lemma even_half_gamma_lower (k : ℕ) (hk : 1 ≤ k) :
    Real.sqrt Real.pi * Real.exp (-(k : ℝ)) * (k : ℝ) ^ k ≤
      Real.Gamma ((k : ℝ) + 1 / 2) := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have ha : 0 < (k : ℝ) + 1 / 2 := by positivity
  have hdup := Real.Gamma_mul_Gamma_add_half_of_pos ha
  have hgammaK : Real.Gamma ((k : ℝ) + 1 / 2 + 1 / 2) =
      (Nat.factorial k : ℝ) := by
    rw [show (k : ℝ) + 1 / 2 + 1 / 2 = (k : ℝ) + 1 by ring]
    exact Real.Gamma_nat_eq_factorial k
  have hgammaTwoK : Real.Gamma (2 * ((k : ℝ) + 1 / 2)) =
      (Nat.factorial (2 * k) : ℝ) := by
    rw [show 2 * ((k : ℝ) + 1 / 2) = ((2 * k : ℕ) : ℝ) + 1 by push_cast; ring]
    exact Real.Gamma_nat_eq_factorial (2 * k)
  have hformula :
      Real.Gamma ((k : ℝ) + 1 / 2) * (Nat.factorial k : ℝ) =
        (Nat.factorial (2 * k) : ℝ) *
          (2 : ℝ) ^ (-(2 * (k : ℝ))) * Real.sqrt Real.pi := by
    calc
      Real.Gamma ((k : ℝ) + 1 / 2) * (Nat.factorial k : ℝ) =
          Real.Gamma ((k : ℝ) + 1 / 2) *
            Real.Gamma ((k : ℝ) + 1 / 2 + 1 / 2) := by rw [hgammaK]
      _ = Real.Gamma (2 * ((k : ℝ) + 1 / 2)) *
          (2 : ℝ) ^ (1 - 2 * ((k : ℝ) + 1 / 2)) * Real.sqrt Real.pi := hdup
      _ = (Nat.factorial (2 * k) : ℝ) *
          (2 : ℝ) ^ (-(2 * (k : ℝ))) * Real.sqrt Real.pi := by
        rw [hgammaTwoK]
        rw [show 1 - 2 * ((k : ℝ) + 1 / 2) = -(2 * (k : ℝ)) by ring]
  apply (mul_le_mul_iff_of_pos_right
    (show 0 < (Nat.factorial k : ℝ) by positivity)).mp
  rw [hformula]
  let A : ℝ := Real.sqrt Real.pi * Real.exp (-(k : ℝ)) * (k : ℝ) ^ k
  let D : ℝ := (Real.exp 1 / Real.sqrt 2) *
    (Real.sqrt (2 * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k)
  let B : ℝ := Real.sqrt (2 * Real.pi * (2 * (k : ℝ))) *
    ((2 * (k : ℝ)) / Real.exp 1) ^ (2 * k)
  have hD : (Nat.factorial k : ℝ) ≤ D := by
    exact factorial_le_exp_div_sqrt_two_mul_stirling k hk
  have hB : B ≤ (Nat.factorial (2 * k) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      Stirling.le_factorial_stirling (2 * k)
  have hAD : A * (Nat.factorial k : ℝ) ≤ A * D :=
    mul_le_mul_of_nonneg_left hD (by dsimp [A]; positivity)
  have hsqrt2k : Real.sqrt (2 * (k : ℝ)) / Real.sqrt 2 = Real.sqrt (k : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  have hsqrt4pik : Real.sqrt (2 * Real.pi * (2 * (k : ℝ))) =
      2 * Real.sqrt Real.pi * Real.sqrt (k : ℝ) := by
    have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
      exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
    calc
      Real.sqrt (2 * Real.pi * (2 * (k : ℝ))) =
          Real.sqrt (4 * (Real.pi * (k : ℝ))) := by congr 1; ring
      _ = Real.sqrt 4 * Real.sqrt (Real.pi * (k : ℝ)) :=
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) _
      _ = 2 * Real.sqrt (Real.pi * (k : ℝ)) := by rw [hsqrt4]
      _ = 2 * (Real.sqrt Real.pi * Real.sqrt (k : ℝ)) := by
        rw [Real.sqrt_mul Real.pi_nonneg]
      _ = 2 * Real.sqrt Real.pi * Real.sqrt (k : ℝ) := by ring
  let C : ℝ := Real.sqrt Real.pi * Real.exp (-(2 * (k : ℝ))) * (k : ℝ) ^ (2 * k)
  have hpowK : ((k : ℝ) / Real.exp 1) ^ k =
      (k : ℝ) ^ k * Real.exp (-(k : ℝ)) := by
    rw [div_pow, ← Real.exp_nat_mul, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  have hDform : D =
      Real.exp 1 * Real.sqrt (k : ℝ) *
        ((k : ℝ) ^ k * Real.exp (-(k : ℝ))) := by
    dsimp [D]
    rw [hpowK]
    calc
      Real.exp 1 / Real.sqrt 2 *
          (Real.sqrt (2 * (k : ℝ)) *
            ((k : ℝ) ^ k * Real.exp (-(k : ℝ)))) =
          Real.exp 1 * (Real.sqrt (2 * (k : ℝ)) / Real.sqrt 2) *
            ((k : ℝ) ^ k * Real.exp (-(k : ℝ))) := by ring
      _ = Real.exp 1 * Real.sqrt (k : ℝ) *
          ((k : ℝ) ^ k * Real.exp (-(k : ℝ))) := by rw [hsqrt2k]
  have hleft : A * D = C * (Real.exp 1 * Real.sqrt (k : ℝ)) := by
    rw [hDform]
    dsimp [A, C]
    rw [show Real.exp (-(2 * (k : ℝ))) =
      Real.exp (-(k : ℝ)) * Real.exp (-(k : ℝ)) by rw [← Real.exp_add]; congr 1; ring]
    rw [show (k : ℝ) ^ (2 * k) = (k : ℝ) ^ k * (k : ℝ) ^ k by
      rw [show 2 * k = k + k by omega, pow_add]]
    ring
  have hcast2k : (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) := by norm_num
  have hrpowTwo : (2 : ℝ) ^ (-(2 * (k : ℝ))) = ((2 : ℝ) ^ (2 * k))⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), hcast2k, Real.rpow_natCast]
  have hpowCancel :
      ((2 * (k : ℝ)) / Real.exp 1) ^ (2 * k) *
          (2 : ℝ) ^ (-(2 * (k : ℝ))) =
        (k : ℝ) ^ (2 * k) * Real.exp (-(2 * (k : ℝ))) := by
    rw [div_pow, ← Real.exp_nat_mul, Real.exp_neg, hrpowTwo]
    rw [mul_pow]
    field_simp [Real.exp_ne_zero]
    norm_num [Nat.cast_mul]
  have hright : B * (2 : ℝ) ^ (-(2 * (k : ℝ))) * Real.sqrt Real.pi =
      C * ((2 * Real.sqrt Real.pi) * Real.sqrt (k : ℝ)) := by
    dsimp [B, C]
    rw [hsqrt4pik]
    rw [show (2 * Real.sqrt Real.pi * Real.sqrt (k : ℝ)) *
        ((2 * (k : ℝ)) / Real.exp 1) ^ (2 * k) *
          (2 : ℝ) ^ (-(2 * (k : ℝ))) * Real.sqrt Real.pi =
        (2 * Real.sqrt Real.pi * Real.sqrt (k : ℝ)) *
          (((2 * (k : ℝ)) / Real.exp 1) ^ (2 * k) *
            (2 : ℝ) ^ (-(2 * (k : ℝ)))) * Real.sqrt Real.pi by ring]
    rw [hpowCancel]
    ring
  calc
    A * (Nat.factorial k : ℝ) ≤ A * D := hAD
    _ = C * (Real.exp 1 * Real.sqrt (k : ℝ)) := hleft
    _ ≤ C * ((2 * Real.sqrt Real.pi) * Real.sqrt (k : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [C]; positivity)
      exact mul_le_mul_of_nonneg_right exp_one_le_two_sqrt_pi (Real.sqrt_nonneg _)
    _ = B * (2 : ℝ) ^ (-(2 * (k : ℝ))) * Real.sqrt Real.pi := hright.symm
    _ ≤ (Nat.factorial (2 * k) : ℝ) *
        (2 : ℝ) ^ (-(2 * (k : ℝ))) * Real.sqrt Real.pi := by
      gcongr

private lemma half_gamma_lower_base :
    Real.sqrt Real.pi * Real.exp (-(1 / 2)) * (1 / 2 : ℝ) ^ (1 / 2 : ℝ) ≤
      Real.Gamma 1 := by
  rw [Real.Gamma_one, ← Real.sqrt_eq_rpow]
  let y := Real.sqrt Real.pi * Real.exp (-(1 / 2)) * Real.sqrt (1 / 2 : ℝ)
  change y ≤ 1
  apply (sq_le_sq₀ (by dsimp [y]; positivity) zero_le_one).mp
  have hpi : Real.pi ≤ 2 * Real.exp 1 := by
    calc
      Real.pi ≤ 4 := Real.pi_le_four
      _ ≤ 2 * Real.exp 1 := by linarith [Real.exp_one_gt_two]
  have hy2 : y ^ 2 = Real.pi / (2 * Real.exp 1) := by
    dsimp [y]
    rw [mul_pow, mul_pow, Real.sq_sqrt Real.pi_nonneg,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [show Real.exp (-(1 / 2)) ^ 2 = Real.exp (-1) by
      rw [pow_two, ← Real.exp_add]; congr 1; ring, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  rw [hy2, one_pow]
  exact (div_le_one (by positivity : 0 < 2 * Real.exp 1)).2 hpi

private lemma gamma_half_nat_lower (m : ℕ) (hm : 1 ≤ m) :
    Real.sqrt Real.pi * Real.exp (-((m : ℝ) / 2)) *
        ((m : ℝ) / 2) ^ ((m : ℝ) / 2) ≤
      Real.Gamma (((m : ℝ) + 1) / 2) := by
  rcases Nat.even_or_odd m with he | ho
  · rcases he with ⟨k, hk⟩
    have hmk : m = 2 * k := by omega
    have hk1 : 1 ≤ k := by omega
    rw [hmk]
    have hcast : ((2 * k : ℕ) : ℝ) / 2 = (k : ℝ) := by push_cast; ring
    rw [hcast, Real.rpow_natCast]
    have hgammaarg : ((((2 * k : ℕ) : ℝ) + 1) / 2) =
        (k : ℝ) + 1 / 2 := by push_cast; ring
    rw [hgammaarg]
    exact even_half_gamma_lower k hk1
  · rcases ho with ⟨k, hk⟩
    have hmk : m = 2 * k + 1 := by omega
    rw [hmk]
    by_cases hk0 : k = 0
    · subst k
      norm_num
      simpa [Real.Gamma_one] using half_gamma_lower_base
    · have hk1 : 1 ≤ k := by omega
      have hcast : (((2 * k + 1 : ℕ) : ℝ) / 2) = (k : ℝ) + 1 / 2 := by
        push_cast
        ring
      rw [hcast]
      have hgamma : Real.Gamma ((((2 * k + 1 : ℕ) : ℝ) + 1) / 2) =
          (Nat.factorial k : ℝ) := by
        rw [show ((((2 * k + 1 : ℕ) : ℝ) + 1) / 2) = (k : ℝ) + 1 by
          push_cast; ring]
        exact Real.Gamma_nat_eq_factorial k
      rw [hgamma]
      exact odd_half_gamma_lower k hk1

/-- Ball's normalized radial peak is at most `1 / π` in every dimension `n ≥ 3`.

This is the Stirling/Gamma estimate displayed in the last paragraph of Ball (1993), printed
p. 419. -/
theorem ball_radial_gamma_peak_le {n : ℕ} (hn : 3 ≤ n) :
    (Real.exp (-(((n : ℝ) - 2) / 2)) *
        ((n : ℝ) - 2) ^ (((n : ℝ) - 2) / 2)) /
      (2 ^ ((n : ℝ) / 2 - 1) *
        Real.Gamma (((n : ℝ) - 1) / 2) * Real.sqrt Real.pi) ≤
      1 / Real.pi := by
  let m : ℕ := n - 2
  have hm : 1 ≤ m := by omega
  have hn_eq : n = m + 2 := by dsimp [m]; omega
  rw [hn_eq]
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  let P : ℝ := Real.exp (-((m : ℝ) / 2)) * (m : ℝ) ^ ((m : ℝ) / 2)
  let q : ℝ := (2 : ℝ) ^ ((m : ℝ) / 2)
  have hq : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hgamma := gamma_half_nat_lower m hm
  have hdivpow : ((m : ℝ) / 2) ^ ((m : ℝ) / 2) =
      (m : ℝ) ^ ((m : ℝ) / 2) / q := by
    dsimp [q]
    rw [Real.div_rpow (le_of_lt hmR) (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrtpi : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_nonneg
  have hden : Real.pi * P ≤
      q * Real.Gamma (((m : ℝ) + 1) / 2) * Real.sqrt Real.pi := by
    have hmul := mul_le_mul_of_nonneg_left hgamma
      (mul_nonneg hq.le (Real.sqrt_nonneg Real.pi))
    calc
      Real.pi * P =
          (q * Real.sqrt Real.pi) *
            (Real.sqrt Real.pi * Real.exp (-((m : ℝ) / 2)) *
              ((m : ℝ) / 2) ^ ((m : ℝ) / 2)) := by
        dsimp [P]
        rw [hdivpow]
        field_simp [hq.ne']
        nlinarith [hsqrtpi]
      _ ≤ (q * Real.sqrt Real.pi) *
          Real.Gamma (((m : ℝ) + 1) / 2) := hmul
      _ = q * Real.Gamma (((m : ℝ) + 1) / 2) * Real.sqrt Real.pi := by ring
  have hD : 0 < q * Real.Gamma (((m : ℝ) + 1) / 2) * Real.sqrt Real.pi := by
    positivity
  have hadd : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  rw [hadd]
  have hsub : (m : ℝ) + 2 - 2 = (m : ℝ) := by ring
  rw [hsub]
  change P /
      (2 ^ (((m : ℝ) + 2) / 2 - 1) *
        Real.Gamma ((((m : ℝ) + 2) - 1) / 2) * Real.sqrt Real.pi) ≤
    1 / Real.pi
  have hpowexp : ((m : ℝ) + 2) / 2 - 1 = (m : ℝ) / 2 := by ring
  have hgammaarg : (((m : ℝ) + 2) - 1) / 2 = ((m : ℝ) + 1) / 2 := by ring
  rw [hpowexp, hgammaarg]
  change P / (q * Real.Gamma (((m : ℝ) + 1) / 2) * Real.sqrt Real.pi) ≤
    1 / Real.pi
  apply (div_le_iff₀ hD).2
  calc
    P ≤ (q * Real.Gamma (((m : ℝ) + 1) / 2) * Real.sqrt Real.pi) /
        Real.pi := (le_div_iff₀ Real.pi_pos).2 (by simpa [mul_comm] using hden)
    _ = (1 / Real.pi) *
        (q * Real.Gamma (((m : ℝ) + 1) / 2) * Real.sqrt Real.pi) := by ring

/-- The radial factor `exp (-t²/2) t^(n-2)` attains its maximum at `t = √(n-2)`.

The right-hand side is the value at the maximizer.  This is the estimate immediately preceding
the normalized Gamma bound on Ball (1993), printed p. 419. -/
theorem exp_neg_half_mul_rpow_le_peak {n : ℕ} (hn : 3 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(t^2)/2) * t ^ ((n:ℝ)-2) ≤
    Real.exp (-(((n:ℝ)-2)/2)) * ((n:ℝ)-2)^(((n:ℝ)-2)/2) := by
  let m : ℝ := (n : ℝ) - 2
  have hm : 0 < m := by
    have hn' : (2 : ℝ) < n := by
      exact_mod_cast (show 2 < n by omega)
    dsimp [m]
    linarith
  change Real.exp (-(t ^ 2) / 2) * t ^ m ≤
    Real.exp (-(m / 2)) * m ^ (m / 2)
  by_cases ht0 : t = 0
  · subst t
    simp [hm.ne']
    positivity
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hqpos : 0 < t ^ 2 / m := div_pos (sq_pos_of_pos htpos) hm
  have hlog := Real.log_le_sub_one_of_pos hqpos
  rw [Real.log_div (pow_ne_zero 2 ht0) hm.ne', Real.log_pow] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ m / 2)
  have halgebra :
      m / 2 * (2 * Real.log t - Real.log m) ≤
        t ^ 2 / 2 - m / 2 := by
    calc
      m / 2 * (2 * Real.log t - Real.log m) ≤
          m / 2 * (t ^ 2 / m - 1) := hscaled
      _ = t ^ 2 / 2 - m / 2 := by field_simp
  have hleft : 0 < Real.exp (-(t ^ 2) / 2) * t ^ m :=
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos htpos _)
  have hright : 0 < Real.exp (-(m / 2)) * m ^ (m / 2) :=
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hm _)
  rw [← Real.log_le_log_iff hleft hright]
  rw [Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos htpos _).ne',
    Real.log_exp, Real.log_rpow htpos,
    Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hm _).ne',
    Real.log_exp, Real.log_rpow hm]
  linarith

end ProbabilityTheory
