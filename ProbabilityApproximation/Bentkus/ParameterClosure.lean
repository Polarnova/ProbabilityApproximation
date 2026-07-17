/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import Mathlib.Analysis.MeanInequalities

/-!
# Parameter closure for Bentkus's induction

This module isolates the final scalar calculation on Bentkus (2004), printed page 404,
equations (3.9)--(3.10).  The smoothing scale is `β * sqrt C`.  The two branches below say that
this scale is either below one, where the Taylor estimate applies, or at least one, where the
trivial probability bound is already sufficient.
-/

noncomputable section

namespace ProbabilityTheory

/-- A positive finite dimension contributes at least one to the factor `d^(1/4)`. -/
lemma one_le_dimension_rpow_quarter {d : ℕ} (hd : 0 < d) :
    1 ≤ (d : ℝ) ^ (1 / 4 : ℝ) := by
  apply Real.one_le_rpow
  · exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd))
  · norm_num

/-- The parameter choice `ε = β * sqrt C` closes Bentkus's induction once the absolute constant
dominates the coefficient in the Taylor estimate. -/
lemma bentkus_parameter_closure {K C d β Δ : ℝ}
    (hC : 1 ≤ C) (hKC : K * (2 * Real.sqrt C + 1) ≤ C)
    (hd : 1 ≤ d) (hβ : 0 < β) (hΔ1 : Δ ≤ 1)
    (hmain : β * Real.sqrt C < 1 →
      Δ ≤ K * d ^ (1 / 4 : ℝ) *
        (β * Real.sqrt C + β + C * β ^ 2 / (β * Real.sqrt C))) :
    Δ ≤ C * d ^ (1 / 4 : ℝ) * β := by
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hsqrtpos : 0 < Real.sqrt C := Real.sqrt_pos.2 (lt_of_lt_of_le (by norm_num) hC)
  have hdq : 1 ≤ d ^ (1 / 4 : ℝ) := Real.one_le_rpow hd (by norm_num)
  have hquot : C * β ^ 2 / (β * Real.sqrt C) = β * Real.sqrt C := by
    field_simp [ne_of_gt hβ, ne_of_gt hsqrtpos]
    nlinarith [Real.sq_sqrt hC0]
  by_cases hsmall : β * Real.sqrt C < 1
  · have h := hmain hsmall
    rw [hquot] at h
    have hscale := mul_le_mul_of_nonneg_right hKC
      (mul_nonneg (le_trans (by norm_num) hdq) hβ.le)
    calc
      Δ ≤ K * d ^ (1 / 4 : ℝ) *
          (β * Real.sqrt C + β + β * Real.sqrt C) := h
      _ = (K * (2 * Real.sqrt C + 1)) * (d ^ (1 / 4 : ℝ) * β) := by ring
      _ ≤ C * (d ^ (1 / 4 : ℝ) * β) := hscale
      _ = C * d ^ (1 / 4 : ℝ) * β := by ring
  · have hlarge : 1 ≤ β * Real.sqrt C := le_of_not_gt hsmall
    have hsqrtC : Real.sqrt C ≤ C := by
      nlinarith [Real.sq_sqrt hC0]
    have hfirst : β * Real.sqrt C ≤ β * C :=
      mul_le_mul_of_nonneg_left hsqrtC hβ.le
    have hsecond : β * C ≤ (β * C) * d ^ (1 / 4 : ℝ) := by
      have := mul_le_mul_of_nonneg_left hdq (mul_nonneg hβ.le hC0)
      simpa using this
    calc
      Δ ≤ 1 := hΔ1
      _ ≤ β * Real.sqrt C := hlarge
      _ ≤ β * C := hfirst
      _ ≤ (β * C) * d ^ (1 / 4 : ℝ) := hsecond
      _ = C * d ^ (1 / 4 : ℝ) * β := by ring

/-- Summing the coordinatewise replacement estimates converts the factor
`1 + C * β / ε` into Bentkus's smooth-error expression
`β + C * β² / ε`. -/
lemma bentkus_coordinate_bounds_sum
    {n : ℕ} {T βk : Fin n → ℝ} {K d14 C β ε : ℝ}
    (hβ : β = ∑ k, βk k) (hε : 0 < ε)
    (hcoord : ∀ k,
      |T k| ≤ K * d14 * (1 + C * β / ε) * βk k) :
    |∑ k, T k| ≤ K * d14 * (β + C * β ^ 2 / ε) := by
  calc
    |∑ k, T k| ≤ ∑ k, |T k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, K * d14 * (1 + C * β / ε) * βk k :=
      Finset.sum_le_sum fun k _ ↦ hcoord k
    _ = K * d14 * (1 + C * β / ε) * β := by
      rw [← Finset.mul_sum, ← hβ]
    _ = K * d14 * (β + C * β ^ 2 / ε) := by
      field_simp [ne_of_gt hε]

/-- Removing one nonnegative coordinate from a finite sum can only decrease the sum. -/
lemma fin_sum_succAbove_le_sum_univ {n : ℕ} (k : Fin (n + 1))
    (f : Fin (n + 1) → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ i : Fin n, f (k.succAbove i)) ≤ ∑ i, f i := by
  rw [Fin.sum_univ_succAbove f k]
  exact le_add_of_nonneg_left (hf k)

/-- The small-angle term, the large-angle comparison, and the Gaussian reference term share one
coordinate envelope after enlarging each nonnegative coefficient by `1 + q`. -/
lemma bentkus_three_coordinate_pieces
    {S L R T : ℝ} {Ks Kl Kr d14 q βk : ℝ}
    (hKl : 0 ≤ Kl) (hKr : 0 ≤ Kr)
    (hd : 0 ≤ d14) (hq : 0 ≤ q) (hβk : 0 ≤ βk)
    (hT : T = S + L + R)
    (hS : |S| ≤ Ks * d14 * (1 + q) * βk)
    (hL : |L| ≤ Kl * d14 * q * βk)
    (hR : |R| ≤ Kr * d14 * βk) :
    |T| ≤ (Ks + Kl + Kr) * d14 * (1 + q) * βk := by
  rw [hT]
  calc
    |S + L + R| ≤ |S| + |L| + |R| := by
      exact (abs_add_le (S + L) R).trans
        (add_le_add (abs_add_le S L) le_rfl)
    _ ≤ Ks * d14 * (1 + q) * βk +
        Kl * d14 * q * βk + Kr * d14 * βk := by
      linarith
    _ ≤ (Ks + Kl + Kr) * d14 * (1 + q) * βk := by
      nlinarith [mul_nonneg hd hβk,
        mul_nonneg (mul_nonneg hKl hd) hβk,
        mul_nonneg (mul_nonneg hKr hd) hβk]

/-- A concrete square closes all scalar hypotheses of Bentkus's induction once the analytic
constant `K` is at least four. -/
lemma bentkus_constant_closure {K : ℝ} (hK : 4 ≤ K) :
    let C := (4 * K + 3) ^ 2
    0 < C ∧ 1 ≤ C ∧ 8 ≤ C ∧
      K * (2 * Real.sqrt C + 1) ≤ C := by
  let C := (4 * K + 3) ^ 2
  have hbase : 0 < 4 * K + 3 := by
    nlinarith
  have hsqrt : Real.sqrt C = 4 * K + 3 := by
    dsimp only [C]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hbase]
  have hCpos : 0 < C := by
    dsimp only [C]
    positivity
  have hC1 : 1 ≤ C := by
    dsimp only [C]
    nlinarith [sq_nonneg (4 * K + 2)]
  have hC8 : 8 ≤ C := by
    dsimp only [C]
    nlinarith [sq_nonneg (4 * K + 3)]
  refine ⟨hCpos, hC1, hC8, ?_⟩
  rw [hsqrt]
  nlinarith [sq_nonneg K]

end ProbabilityTheory
