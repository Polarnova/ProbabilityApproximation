/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProbabilityApproximation.ChenShao.Leaves
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

/-!
# Fourth-moment identity and Rosenthal-type bound for independent centered sums

For independent mean-zero summands with finite fourth moments,
`E(∑ X_i)⁴ ≤ 3 (∑ EX_i²)² + ∑ EX_i⁴`.
-/

open MeasureTheory ProbabilityTheory Real

noncomputable section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma integral_pow_mul_y_of_indep_mean_zero
    {S Y : Ω → ℝ} {k : ℕ}
    (hS : Measurable S) (hY : Measurable Y)
    (hY0 : ∫ ω, Y ω ∂μ = 0) (hindep : IndepFun S Y μ) :
    ∫ ω, (S ω) ^ k * Y ω ∂μ = 0 := by
  have hindep' : IndepFun (fun ω => (S ω) ^ k) Y μ := by
    simpa [Function.comp_def] using
      hindep.comp (φ := fun x : ℝ => x ^ k) (ψ := (id : ℝ → ℝ))
        (continuous_pow k).measurable measurable_id
  have h := hindep'.integral_mul_eq_mul_integral
    (hS.pow_const k).aestronglyMeasurable hY.aestronglyMeasurable
  change ∫ ω, ((fun ω => (S ω) ^ k) * Y) ω ∂μ = 0
  rw [h, hY0, mul_zero]

omit [IsProbabilityMeasure μ] in
lemma integral_s_mul_pow_of_indep_mean_zero
    {S Y : Ω → ℝ} {k : ℕ}
    (hS : Measurable S) (hY : Measurable Y)
    (hS0 : ∫ ω, S ω ∂μ = 0) (hindep : IndepFun S Y μ) :
    ∫ ω, S ω * (Y ω) ^ k ∂μ = 0 := by
  have hindep' : IndepFun S (fun ω => (Y ω) ^ k) μ := by
    simpa [Function.comp_def] using
      hindep.comp (φ := (id : ℝ → ℝ)) (ψ := fun x : ℝ => x ^ k)
        measurable_id (continuous_pow k).measurable
  have h := hindep'.integral_mul_eq_mul_integral
    hS.aestronglyMeasurable (hY.pow_const k).aestronglyMeasurable
  change ∫ ω, (S * fun ω => (Y ω) ^ k) ω ∂μ = 0
  rw [h, hS0, zero_mul]

omit [IsProbabilityMeasure μ] in
lemma integral_sq_mul_sq_of_indep
    {S Y : Ω → ℝ}
    (hS : Measurable S) (hY : Measurable Y)
    (hindep : IndepFun S Y μ) :
    ∫ ω, (S ω) ^ 2 * (Y ω) ^ 2 ∂μ =
      (∫ ω, (S ω) ^ 2 ∂μ) * (∫ ω, (Y ω) ^ 2 ∂μ) := by
  have hindep' : IndepFun (fun ω => (S ω) ^ 2) (fun ω => (Y ω) ^ 2) μ := by
    simpa [Function.comp_def] using
      hindep.comp (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2)
        (continuous_pow 2).measurable (continuous_pow 2).measurable
  have h := hindep'.integral_mul_eq_mul_integral
    (hS.pow_const 2).aestronglyMeasurable (hY.pow_const 2).aestronglyMeasurable
  change ∫ ω, ((fun ω => (S ω) ^ 2) * fun ω => (Y ω) ^ 2) ω ∂μ = _
  rw [h]

/-- `E(S+Y)⁴ = ES⁴ + EY⁴ + 6 ES² EY²` for independent mean-zero pairs. -/
lemma integral_add_pow_four_indepMeanZero
    {S Y : Ω → ℝ}
    (hS : Measurable S) (hY : Measurable Y)
    (hS4 : Integrable (fun ω => (S ω) ^ 4) μ)
    (hY4 : Integrable (fun ω => (Y ω) ^ 4) μ)
    (hS3Y : Integrable (fun ω => (S ω) ^ 3 * Y ω) μ)
    (hSY3 : Integrable (fun ω => S ω * (Y ω) ^ 3) μ)
    (hS2Y2 : Integrable (fun ω => (S ω) ^ 2 * (Y ω) ^ 2) μ)
    (hS0 : ∫ ω, S ω ∂μ = 0) (hY0 : ∫ ω, Y ω ∂μ = 0)
    (hindep : IndepFun S Y μ) :
    ∫ ω, (S ω + Y ω) ^ 4 ∂μ =
      (∫ ω, (S ω) ^ 4 ∂μ) + (∫ ω, (Y ω) ^ 4 ∂μ) +
        6 * (∫ ω, (S ω) ^ 2 ∂μ) * (∫ ω, (Y ω) ^ 2 ∂μ) := by
  let g : Fin 5 → Ω → ℝ := ![
    fun ω => (S ω) ^ 4,
    fun ω => (Y ω) ^ 4,
    fun ω => 4 * ((S ω) ^ 3 * Y ω),
    fun ω => 4 * (S ω * (Y ω) ^ 3),
    fun ω => 6 * ((S ω) ^ 2 * (Y ω) ^ 2)]
  have hg : ∀ i, Integrable (g i) μ := by
    intro i
    fin_cases i <;> simp only [g]
    · exact hS4
    · exact hY4
    · exact hS3Y.const_mul 4
    · exact hSY3.const_mul 4
    · exact hS2Y2.const_mul 6
  have hpt : (fun ω => (S ω + Y ω) ^ 4) = fun ω => ∑ i : Fin 5, g i ω := by
    ext ω
    simp [g, Fin.sum_univ_five]
    ring
  rw [hpt, integral_finsetSum Finset.univ fun i _ => hg i]
  simp [Fin.sum_univ_five, g, integral_const_mul]
  rw [integral_pow_mul_y_of_indep_mean_zero (k := 3) hS hY hY0 hindep,
    integral_s_mul_pow_of_indep_mean_zero (k := 3) hS hY hS0 hindep,
    integral_sq_mul_sq_of_indep hS hY hindep]
  ring

/-! ### Bounded independent family: fourth-moment Rosenthal bound -/

variable {ι : Type*} [DecidableEq ι]

open Filter

/-- Pointwise bound implies `L⁴` integrability on a probability space. -/
lemma integrable_pow_four_of_bound {Y : Ω → ℝ} (hY : Measurable Y) {M : ℝ} (hM : 0 ≤ M)
    (hbd : ∀ ω, |Y ω| ≤ M) :
    Integrable (fun ω => (Y ω) ^ 4) μ := by
  refine Integrable.of_bound (hY.pow_const 4).aestronglyMeasurable (M ^ 4) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hbd ω) 4

lemma integrable_cross_pow_of_bound {S Y : Ω → ℝ}
    (hS : Measurable S) (hY : Measurable Y) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hSbd : ∀ ω, |S ω| ≤ M) (hYbd : ∀ ω, |Y ω| ≤ N) :
    Integrable (fun ω => (S ω) ^ 3 * Y ω) μ ∧
      Integrable (fun ω => S ω * (Y ω) ^ 3) μ ∧
      Integrable (fun ω => (S ω) ^ 2 * (Y ω) ^ 2) μ := by
  have hS3Y : Integrable (fun ω => (S ω) ^ 3 * Y ω) μ := by
    refine Integrable.of_bound
      ((hS.pow_const 3).mul hY).aestronglyMeasurable (M ^ 3 * N) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    -- |S|³ * |Y| ≤ M³ * N
    refine mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hSbd ω) 3)
      (hYbd ω) (abs_nonneg _) (pow_nonneg hM 3)
  have hSY3 : Integrable (fun ω => S ω * (Y ω) ^ 3) μ := by
    refine Integrable.of_bound
      (hS.mul (hY.pow_const 3)).aestronglyMeasurable (M * N ^ 3) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    -- |S| * |Y|³ ≤ M * N³; mul_le_mul needs 0 ≤ |Y|³ and 0 ≤ M
    exact mul_le_mul (hSbd ω) (pow_le_pow_left₀ (abs_nonneg _) (hYbd ω) 3)
      (pow_nonneg (abs_nonneg _) 3) hM
  have hS2Y2 : Integrable (fun ω => (S ω) ^ 2 * (Y ω) ^ 2) μ := by
    refine Integrable.of_bound
      ((hS.pow_const 2).mul (hY.pow_const 2)).aestronglyMeasurable (M ^ 2 * N ^ 2) ?_
    filter_upwards with ω
    have hnn : 0 ≤ (S ω) ^ 2 * (Y ω) ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have heqS : (S ω) ^ 2 = |S ω| ^ 2 := (sq_abs _).symm
    have heqY : (Y ω) ^ 2 = |Y ω| ^ 2 := (sq_abs _).symm
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, heqS, heqY]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hSbd ω) 2)
      (pow_le_pow_left₀ (abs_nonneg _) (hYbd ω) 2) (sq_nonneg _) (sq_nonneg M)
  exact ⟨hS3Y, hSY3, hS2Y2⟩

/-- Fourth-moment bound for a finset sum of independent centered bounded r.v.s:

`E(∑_{i∈s} X_i)⁴ ≤ 3 (∑_{i∈s} EX_i²)² + ∑_{i∈s} EX_i⁴`. -/
lemma integral_finsetSum_pow_four_le
    {X : ι → Ω → ℝ}
    (hX : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    (h0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hbd : ∀ i ω, |X i ω| ≤ M)
    (s : Finset ι) :
    ∫ ω, (∑ i ∈ s, X i ω) ^ 4 ∂μ ≤
      3 * (∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ) ^ 2 +
        ∑ i ∈ s, ∫ ω, (X i ω) ^ 4 ∂μ := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp
  | insert j s hjs ih =>
    set S : Ω → ℝ := fun ω => ∑ i ∈ s, X i ω
    set Y : Ω → ℝ := X j
    have hSmeas : Measurable S := Finset.measurable_fun_sum _ fun i _ => hX i
    have hYmeas : Measurable Y := hX j
    have hSbd : ∀ ω, |S ω| ≤ (s.card : ℝ) * M := fun ω => by
      calc
        |S ω| ≤ ∑ i ∈ s, |X i ω| := by
          simpa [S] using Finset.abs_sum_le_sum_abs (fun i => X i ω) s
        _ ≤ ∑ i ∈ s, M := Finset.sum_le_sum fun i _ => hbd i ω
        _ = (s.card : ℝ) * M := by simp [Finset.sum_const, nsmul_eq_mul]
    have hYbd : ∀ ω, |Y ω| ≤ M := fun ω => hbd j ω
    have hcardM : 0 ≤ (s.card : ℝ) * M := mul_nonneg (Nat.cast_nonneg _) hM
    have hInt : ∀ i, Integrable (X i) μ := fun i =>
      Integrable.of_bound (hX i).aestronglyMeasurable M
        (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hbd i ω)
    have hS0 : ∫ ω, S ω ∂μ = 0 := by
      simpa [S] using integral_finsetSum_eq_zero (X := X) s hInt h0
    have hY0 : ∫ ω, Y ω ∂μ = 0 := h0 j
    have hindepSY : IndepFun S Y μ := by
      have h := h_indep.indepFun_finsetSum_of_notMem hX hjs
      have hS_eq : S = ∑ i ∈ s, X i := by
        funext ω; simp [S, Finset.sum_apply]
      simpa [hS_eq, Y] using h
    have hS4 : Integrable (fun ω => (S ω) ^ 4) μ :=
      integrable_pow_four_of_bound (μ := μ) hSmeas hcardM hSbd
    have hY4 : Integrable (fun ω => (Y ω) ^ 4) μ :=
      integrable_pow_four_of_bound (μ := μ) hYmeas hM hYbd
    obtain ⟨hS3Y, hSY3, hS2Y2⟩ :=
      integrable_cross_pow_of_bound (μ := μ) hSmeas hYmeas hcardM hM hSbd hYbd
    have hadd :
        ∫ ω, (S ω + Y ω) ^ 4 ∂μ =
          (∫ ω, (S ω) ^ 4 ∂μ) + (∫ ω, (Y ω) ^ 4 ∂μ) +
            6 * (∫ ω, (S ω) ^ 2 ∂μ) * (∫ ω, (Y ω) ^ 2 ∂μ) :=
      integral_add_pow_four_indepMeanZero (μ := μ) hSmeas hYmeas hS4 hY4 hS3Y hSY3 hS2Y2
        hS0 hY0 hindepSY
    have hX2 : ∀ i, MemLp (X i) 2 μ := fun i =>
      MemLp.of_bound (hX i).aestronglyMeasurable M
        (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hbd i ω)
    have hS2 : ∫ ω, (S ω) ^ 2 ∂μ = ∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ := by
      simpa [S] using integral_sq_finsetSum_eq (X := X) s hX2 h_indep h0
    have ih' :
        ∫ ω, (S ω) ^ 4 ∂μ ≤
          3 * (∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ) ^ 2 +
            ∑ i ∈ s, ∫ ω, (X i ω) ^ 4 ∂μ := by
      simpa [S] using ih
    set a := ∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ
    set b := ∫ ω, (Y ω) ^ 2 ∂μ
    set c := ∑ i ∈ s, ∫ ω, (X i ω) ^ 4 ∂μ
    set d := ∫ ω, (Y ω) ^ 4 ∂μ
    have ha : ∫ ω, (S ω) ^ 2 ∂μ = a := hS2
    have hab : ∑ i ∈ insert j s, ∫ ω, (X i ω) ^ 2 ∂μ = a + b := by
      rw [Finset.sum_insert hjs, add_comm]
    have hcd : ∑ i ∈ insert j s, ∫ ω, (X i ω) ^ 4 ∂μ = c + d := by
      rw [Finset.sum_insert hjs, add_comm]
    have ha_nn : 0 ≤ a := by rw [← ha]; exact integral_nonneg fun _ => sq_nonneg _
    have hb_nn : 0 ≤ b := integral_nonneg fun _ => sq_nonneg _
    have hstep :
        (∫ ω, (S ω) ^ 4 ∂μ) + d + 6 * a * b ≤ 3 * (a + b) ^ 2 + c + d := by
      nlinarith [ih', ha_nn, hb_nn, sq_nonneg b]
    have hadd' :
        ∫ ω, (S ω + Y ω) ^ 4 ∂μ = (∫ ω, (S ω) ^ 4 ∂μ) + d + 6 * a * b := by
      rw [hadd, ha]
    have hpt (ω : Ω) : (∑ i ∈ insert j s, X i ω) ^ 4 = (S ω + Y ω) ^ 4 := by
      simp [S, Y, Finset.sum_insert hjs, add_comm]
    calc
      ∫ ω, (∑ i ∈ insert j s, X i ω) ^ 4 ∂μ =
          ∫ ω, (S ω + Y ω) ^ 4 ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => hpt ω)
      _ = (∫ ω, (S ω) ^ 4 ∂μ) + d + 6 * a * b := hadd'
      _ ≤ 3 * (a + b) ^ 2 + c + d := hstep
      _ = 3 * (∑ i ∈ insert j s, ∫ ω, (X i ω) ^ 2 ∂μ) ^ 2 +
            ∑ i ∈ insert j s, ∫ ω, (X i ω) ^ 4 ∂μ := by
          rw [hab, hcd]; ring

end ProbabilityTheory
