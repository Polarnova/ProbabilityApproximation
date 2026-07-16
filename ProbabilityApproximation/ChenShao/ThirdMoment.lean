/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProbabilityApproximation.ChenShao.Leaves
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

/-!
# Third moment of an independent centered sum

This file proves the `p = 3` instance of the moment estimate used in Chen--Shao 2005,
Lemma 6.3.  Under the unit-variance normalization it gives

`E |∑ i, X i|³ ≤ 3 + ∑ i, E |X i|³`.

The numerical constant is deliberately not optimized; the nonuniform Berry--Esseen theorem only
uses an absolute bound.
-/

open MeasureTheory ProbabilityTheory Real

noncomputable section

namespace ProbabilityTheory

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ι → Ω → ℝ}

/-- A third-order Taylor majorant for the absolute-value cube. -/
lemma abs_add_pow_three_le (x y : ℝ) :
    |x + y| ^ 3 ≤
      |x| ^ 3 + 3 * (x * |x|) * y + 3 * |x| * y ^ 2 + |y| ^ 3 := by
  rcases le_total 0 x with hx | hx <;>
    rcases le_total 0 y with hy | hy <;>
      rcases le_total 0 (x + y) with hxy | hxy
  all_goals
    simp only [abs_of_nonneg, abs_of_nonpos, hx, hy, hxy]
  all_goals nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x + y)]

omit [IsProbabilityMeasure μ] in
private lemma integrable_abs_pow_three_of_memLp
    {Y : Ω → ℝ} (hY : MemLp Y 3 μ) : Integrable (fun ω => |Y ω| ^ 3) μ := by
  simpa [Real.norm_eq_abs] using hY.integrable_norm_pow (by decide : (3 : ℕ) ≠ 0)

private lemma memLp_two_of_memLp_three {Y : Ω → ℝ} (hY : MemLp Y 3 μ) : MemLp Y 2 μ :=
  hY.mono_exponent (by norm_num)

/-- Third-moment Markov bound in the real-valued measure API. -/
lemma measureReal_abs_ge_le_integral_abs_pow_three
    {Y : Ω → ℝ} (hYmeas : Measurable Y) (hY3 : MemLp Y 3 μ)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |Y ω|} ≤ (∫ ω, |Y ω| ^ 3 ∂μ) / t ^ 3 := by
  have hInt : Integrable (fun ω ↦ |Y ω| ^ 3) μ :=
    integrable_abs_pow_three_of_memLp hY3
  have hset : MeasurableSet {ω | t ≤ |Y ω|} :=
    measurableSet_le measurable_const hYmeas.abs
  have hpt : ∀ ω ∈ {ω | t ≤ |Y ω|}, t ^ 3 ≤ |Y ω| ^ 3 := by
    intro ω hω
    exact pow_le_pow_left₀ ht.le hω 3
  have hmono :
      t ^ 3 * μ.real {ω | t ≤ |Y ω|} ≤ ∫ ω, |Y ω| ^ 3 ∂μ := by
    calc
      t ^ 3 * μ.real {ω | t ≤ |Y ω|} =
          ∫ ω in {ω | t ≤ |Y ω|}, (t ^ 3 : ℝ) ∂μ := by
        rw [integral_const]
        simp [Measure.real, smul_eq_mul, mul_comm]
      _ ≤ ∫ ω in {ω | t ≤ |Y ω|}, |Y ω| ^ 3 ∂μ :=
        setIntegral_mono_on (integrable_const _).integrableOn hInt.integrableOn hset hpt
      _ ≤ ∫ ω, |Y ω| ^ 3 ∂μ :=
        setIntegral_le_integral hInt
          (Filter.Eventually.of_forall fun ω ↦ pow_nonneg (abs_nonneg _) 3)
  exact (le_div_iff₀ (pow_pos ht 3)).2 (by simpa [mul_comm] using hmono)

/-- Adding an independent centered summand increases the third absolute moment by at most its own
third moment plus three times its variance, provided the existing partial sum has second moment at
most one. -/
lemma integral_abs_add_pow_three_le
    {S Y : Ω → ℝ}
    (hSmeas : Measurable S) (hYmeas : Measurable Y)
    (hS3 : MemLp S 3 μ) (hY3 : MemLp Y 3 μ)
    (hSY : IndepFun S Y μ) (hY0 : ∫ ω, Y ω ∂μ = 0)
    (hS2le : ∫ ω, (S ω) ^ 2 ∂μ ≤ 1) :
    ∫ ω, |S ω + Y ω| ^ 3 ∂μ ≤
      (∫ ω, |S ω| ^ 3 ∂μ) + 3 * (∫ ω, (Y ω) ^ 2 ∂μ) +
        ∫ ω, |Y ω| ^ 3 ∂μ := by
  have hS2 := memLp_two_of_memLp_three hS3
  have hY2 := memLp_two_of_memLp_three hY3
  have hS1 : Integrable (fun ω => |S ω|) μ := by
    simpa [Real.norm_eq_abs] using (hS2.integrable one_le_two).norm
  have hY1 : Integrable Y μ := hY2.integrable one_le_two
  have hYsq : Integrable (fun ω => (Y ω) ^ 2) μ := hY2.integrable_sq
  have hSabs3 := integrable_abs_pow_three_of_memLp hS3
  have hYabs3 := integrable_abs_pow_three_of_memLp hY3
  have hSum3 : MemLp (fun ω => S ω + Y ω) 3 μ := hS3.add hY3
  have hLhs := integrable_abs_pow_three_of_memLp hSum3
  have hSsignedSq : Integrable (fun ω => S ω * |S ω|) μ := by
    refine hS2.integrable_sq.mono' (hSmeas.mul hSmeas.abs).aestronglyMeasurable ?_
    filter_upwards with ω
    simp [Real.norm_eq_abs, pow_two]
  have hIndepLinear : IndepFun (fun ω => S ω * |S ω|) Y μ := by
    simpa [Function.comp_def] using
      hSY.comp (φ := fun s : ℝ => s * |s|) (ψ := id)
        (continuous_id.mul continuous_abs).measurable measurable_id
  have hLinearInt : Integrable (fun ω => (S ω * |S ω|) * Y ω) μ := by
    change Integrable ((fun ω => S ω * |S ω|) * Y) μ
    exact hIndepLinear.integrable_mul hSsignedSq hY1
  have hLinearZero : ∫ ω, (S ω * |S ω|) * Y ω ∂μ = 0 := by
    have hfac := hIndepLinear.integral_fun_mul_eq_mul_integral
      (hSmeas.mul hSmeas.abs).aestronglyMeasurable hYmeas.aestronglyMeasurable
    rw [hfac, hY0, mul_zero]
  have hIndepCross : IndepFun (fun ω => |S ω|) (fun ω => (Y ω) ^ 2) μ := by
    simpa [Function.comp_def] using
      hSY.comp (φ := fun s : ℝ => |s|) (ψ := fun y : ℝ => y ^ 2)
        continuous_abs.measurable (continuous_pow 2).measurable
  have hCrossInt : Integrable (fun ω => |S ω| * (Y ω) ^ 2) μ := by
    change Integrable ((fun ω => |S ω|) * fun ω => (Y ω) ^ 2) μ
    exact hIndepCross.integrable_mul hS1 hYsq
  have hCrossFactor :
      ∫ ω, |S ω| * (Y ω) ^ 2 ∂μ =
        (∫ ω, |S ω| ∂μ) * ∫ ω, (Y ω) ^ 2 ∂μ := by
    exact hIndepCross.integral_fun_mul_eq_mul_integral
      hSmeas.abs.aestronglyMeasurable (hYmeas.pow_const 2).aestronglyMeasurable
  have hSabsNonneg : 0 ≤ ∫ ω, |S ω| ∂μ := integral_nonneg fun _ => abs_nonneg _
  have hSsqNonneg : 0 ≤ ∫ ω, (S ω) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hSabsLeOne : ∫ ω, |S ω| ∂μ ≤ 1 := by
    have hpt : ∀ ω, |S ω| ≤ ((S ω) ^ 2 + 1) / 2 := fun ω => by
      nlinarith [sq_nonneg (|S ω| - 1), sq_abs (S ω)]
    have hconst : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
    have hrhs : Integrable (fun ω => ((S ω) ^ 2 + 1) / 2) μ :=
      (hS2.integrable_sq.add hconst).div_const 2
    have hmono := integral_mono hS1 hrhs hpt
    have hone : ∫ _ : Ω, (1 : ℝ) ∂μ = 1 := by simp
    rw [integral_div, integral_add hS2.integrable_sq hconst, hone] at hmono
    linarith
  have hYsqNonneg : 0 ≤ ∫ ω, (Y ω) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hCrossBound :
      3 * ∫ ω, |S ω| * (Y ω) ^ 2 ∂μ ≤ 3 * ∫ ω, (Y ω) ^ 2 ∂μ := by
    rw [hCrossFactor]
    nlinarith
  let R : Ω → ℝ := fun ω =>
    |S ω| ^ 3 + 3 * (S ω * |S ω|) * Y ω +
      3 * |S ω| * (Y ω) ^ 2 + |Y ω| ^ 3
  have hLinear3 : Integrable (fun ω => 3 * (S ω * |S ω|) * Y ω) μ := by
    refine (hLinearInt.const_mul 3).congr (Filter.Eventually.of_forall fun ω => ?_)
    ring
  have hCross3 : Integrable (fun ω => 3 * |S ω| * (Y ω) ^ 2) μ := by
    refine (hCrossInt.const_mul 3).congr (Filter.Eventually.of_forall fun ω => ?_)
    ring
  have hFirstTwo : Integrable
      (fun ω => |S ω| ^ 3 + 3 * (S ω * |S ω|) * Y ω) μ := hSabs3.add hLinear3
  have hFirstThree : Integrable
      (fun ω => |S ω| ^ 3 + 3 * (S ω * |S ω|) * Y ω +
        3 * |S ω| * (Y ω) ^ 2) μ := hFirstTwo.add hCross3
  have hR : Integrable R μ := by
    dsimp [R]
    exact hFirstThree.add hYabs3
  have hpoint : ∀ ω, |S ω + Y ω| ^ 3 ≤ R ω := fun ω => by
    simpa [R, mul_assoc] using abs_add_pow_three_le (S ω) (Y ω)
  have hmono := integral_mono hLhs hR hpoint
  have hRint : ∫ ω, R ω ∂μ =
      (∫ ω, |S ω| ^ 3 ∂μ) +
        3 * (∫ ω, |S ω| * (Y ω) ^ 2 ∂μ) +
          ∫ ω, |Y ω| ^ 3 ∂μ := by
    have hlin : ∫ ω, 3 * (S ω * |S ω|) * Y ω ∂μ = 0 := by
      have heq : (fun ω => 3 * (S ω * |S ω|) * Y ω) =
          fun ω => 3 * ((S ω * |S ω|) * Y ω) := by
        funext ω
        ring
      rw [heq, integral_const_mul, hLinearZero, mul_zero]
    have hcross : ∫ ω, 3 * |S ω| * (Y ω) ^ 2 ∂μ =
        3 * ∫ ω, |S ω| * (Y ω) ^ 2 ∂μ := by
      have heq : (fun ω => 3 * |S ω| * (Y ω) ^ 2) =
          fun ω => 3 * (|S ω| * (Y ω) ^ 2) := by
        funext ω
        ring
      rw [heq, integral_const_mul]
    dsimp [R]
    rw [integral_add hFirstThree hYabs3, integral_add hFirstTwo hCross3,
      integral_add hSabs3 hLinear3, hlin, hcross]
    ring
  rw [hRint] at hmono
  linarith

/-- Third absolute moment bound for any partial sum of an independent centered family whose total
second moment is at most one. -/
lemma integral_abs_finsetSum_pow_three_le
    (hXmeas : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ)
    (h_indep : iIndepFun X μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hsecond : ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ ≤ 1)
    (s : Finset ι) :
    ∫ ω, |∑ i ∈ s, X i ω| ^ 3 ∂μ ≤
      3 * (∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ) +
        ∑ i ∈ s, ∫ ω, |X i ω| ^ 3 ∂μ := by
  classical
  have hX2 : ∀ i, MemLp (X i) 2 μ := fun i => memLp_two_of_memLp_three (hX3 i)
  have hfinset : ∀ s : Finset ι,
      ∫ ω, |∑ i ∈ s, X i ω| ^ 3 ∂μ ≤
        3 * (∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ) +
          ∑ i ∈ s, ∫ ω, |X i ω| ^ 3 ∂μ := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | @insert j s hjs ih =>
        let S : Ω → ℝ := fun ω => ∑ i ∈ s, X i ω
        let Y : Ω → ℝ := X j
        have hSmeas : Measurable S :=
          Finset.measurable_fun_sum s fun i _ => hXmeas i
        have hYmeas : Measurable Y := hXmeas j
        have hS3 : MemLp S 3 μ := by
          dsimp [S]
          exact memLp_finsetSum s fun i _ => hX3 i
        have hY3 : MemLp Y 3 μ := hX3 j
        have hSY : IndepFun S Y μ := by
          have h := h_indep.indepFun_finsetSum_of_notMem hXmeas hjs
          convert h using 1
          ext ω
          simp [S, Finset.sum_apply]
        have hpartial : ∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ ≤ 1 := by
          exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
            fun i _ _ => integral_nonneg fun ω => sq_nonneg (X i ω)).trans hsecond
        have hS2eq : ∫ ω, (S ω) ^ 2 ∂μ =
            ∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ := by
          simpa [S] using integral_sq_finsetSum_eq (X := X) s hX2 h_indep h_mean
        have hS2le : ∫ ω, (S ω) ^ 2 ∂μ ≤ 1 := hS2eq.trans_le hpartial
        have hadd := integral_abs_add_pow_three_le hSmeas hYmeas hS3 hY3 hSY
          (h_mean j) hS2le
        have hrepr : (fun ω => ∑ i ∈ insert j s, X i ω) = fun ω => S ω + Y ω := by
          funext ω
          simp [S, Y, hjs, add_comm]
        change ∫ ω, |(fun ω => ∑ i ∈ insert j s, X i ω) ω| ^ 3 ∂μ ≤ _
        rw [hrepr]
        calc
          ∫ ω, |S ω + Y ω| ^ 3 ∂μ ≤
              (∫ ω, |S ω| ^ 3 ∂μ) + 3 * (∫ ω, (Y ω) ^ 2 ∂μ) +
                ∫ ω, |Y ω| ^ 3 ∂μ := hadd
          _ ≤ (3 * (∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ) +
                ∑ i ∈ s, ∫ ω, |X i ω| ^ 3 ∂μ) +
              3 * (∫ ω, (X j ω) ^ 2 ∂μ) +
                ∫ ω, |X j ω| ^ 3 ∂μ := by
              dsimp [S, Y]
              linarith
          _ = 3 * (∑ i ∈ insert j s, ∫ ω, (X i ω) ^ 2 ∂μ) +
                ∑ i ∈ insert j s, ∫ ω, |X i ω| ^ 3 ∂μ := by
              simp [hjs]
              ring
  exact hfinset s

/-- Chen--Shao's `p = 3` moment bound in the unit-variance normalization, with a harmless absolute
constant `3` in place of the sharper `2`. -/
lemma integral_abs_sumX_pow_three_le
    (hXmeas : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ)
    (h_indep : iIndepFun X μ)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1) :
    ∫ ω, |sumX X ω| ^ 3 ∂μ ≤
      3 + ∑ i, ∫ ω, |X i ω| ^ 3 ∂μ := by
  have hX2 : ∀ i, MemLp (X i) 2 μ := fun i => memLp_two_of_memLp_three (hX3 i)
  have hsumSq : ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ = 1 := by
    calc
      ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ = ∑ i, variance (X i) μ := by
        apply Finset.sum_congr rfl
        intro i _
        exact (variance_eq_integral_sq (hX2 i) (h_mean i)).symm
      _ = 1 := hvar
  have h := integral_abs_finsetSum_pow_three_le hXmeas hX3 h_indep h_mean hsumSq.le
    Finset.univ
  simpa [sumX, hsumSq] using h

end ProbabilityTheory
