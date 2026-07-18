/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic
import ProbabilityApproximation.ChenShao.Concentration
import ProbabilityApproximation.ChenShao.Leaves

/-!
# Bennett--Hoeffding exponential concentration

The moment-generating-function part of Chen--Shao (2005), Lemma 6.2.  The declarations in this
module isolate the exponential concentration input used by the nonuniform Berry--Esseen argument.
-/

open MeasureTheory ProbabilityTheory Real Set

noncomputable section

namespace ProbabilityTheory

/-! ### The pointwise Bennett bound -/

private lemma exp_le_quadratic_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 := by
  let q : ℝ → ℝ := (fun _ ↦ 1) + id + (fun z ↦ z ^ 2 / 2) - Real.exp
  have hq_cont : ContinuousOn q (Iic 0) := by
    dsimp [q]
    fun_prop
  have hq_deriv : ∀ z ∈ Iic (0 : ℝ), HasDerivAt q (1 + z - Real.exp z) z := by
    intro z hz
    simpa [q] using
      (((hasDerivAt_const z (1 : ℝ)).add (hasDerivAt_id z)).add
        ((hasDerivAt_pow 2 z).div_const 2)).sub (Real.hasDerivAt_exp z)
  have hq_anti : AntitoneOn q (Iic 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Iic (0 : ℝ)) hq_cont ?_ ?_
    · intro z hz
      exact (hq_deriv z (interior_subset hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [(hq_deriv z (interior_subset hz)).deriv]
      linarith [Real.add_one_le_exp z]
  have h := hq_anti hx (Set.mem_Iic.mpr le_rfl) hx
  simpa [q] using h

private lemma exp_mul_le_quadratic_of_mem_Icc {t y : ℝ} (ht : 0 ≤ t)
    (hy : y ∈ Icc (0 : ℝ) 1) :
    Real.exp (t * y) ≤ 1 + t * y + (Real.exp t - 1 - t) * y ^ 2 := by
  have hsum_t : Summable (fun n : ℕ ↦ t ^ n / n.factorial) := by
    exact NormedSpace.expSeries_div_summable t
  have hsum_ty : Summable (fun n : ℕ ↦ (t * y) ^ n / n.factorial) := by
    exact NormedSpace.expSeries_div_summable (t * y)
  have hsum_t_tail : Summable (fun n : ℕ ↦ t ^ (n + 2) / (n + 2).factorial) := by
    exact hsum_t.comp_injective (add_left_injective 2)
  have hsum_ty_tail : Summable (fun n : ℕ ↦ (t * y) ^ (n + 2) / (n + 2).factorial) := by
    exact hsum_ty.comp_injective (add_left_injective 2)
  have htail :
      (∑' n : ℕ, (t * y) ^ (n + 2) / (n + 2).factorial) ≤
        y ^ 2 * ∑' n : ℕ, t ^ (n + 2) / (n + 2).factorial := by
    rw [← tsum_mul_left]
    refine hsum_ty_tail.tsum_le_tsum (fun n ↦ ?_) (hsum_t_tail.mul_left (y ^ 2))
    have hyn : y ^ n ≤ 1 := pow_le_one₀ hy.1 hy.2
    have ht_nonneg : 0 ≤ t ^ (n + 2) / (n + 2).factorial := by positivity
    calc
      (t * y) ^ (n + 2) / (n + 2).factorial
          = y ^ 2 * (t ^ (n + 2) / (n + 2).factorial) * y ^ n := by
              rw [mul_pow]
              field_simp
              ring
      _ ≤ y ^ 2 * (t ^ (n + 2) / (n + 2).factorial) * 1 := by
            gcongr
      _ = y ^ 2 * (t ^ (n + 2) / (n + 2).factorial) := by ring
  have hsplit_t := hsum_t.sum_add_tsum_nat_add 2
  have hsplit_ty := hsum_ty.sum_add_tsum_nat_add 2
  rw [show (∑' n : ℕ, t ^ n / n.factorial) = Real.exp t by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]] at hsplit_t
  rw [show (∑' n : ℕ, (t * y) ^ n / n.factorial) = Real.exp (t * y) by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]] at hsplit_ty
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, pow_one, Nat.factorial_one] at hsplit_t hsplit_ty
  nlinarith

/-- Chen--Shao (2005), (6.5), normalized to the upper endpoint `1`. -/
lemma exp_mul_le_quadratic_of_le_one {t y : ℝ} (ht : 0 ≤ t) (hy : y ≤ 1) :
    Real.exp (t * y) ≤ 1 + t * y + (Real.exp t - 1 - t) * y ^ 2 := by
  rcases le_total y 0 with hy0 | hy0
  · have hty : t * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hy0
    have hbase := exp_le_quadratic_of_nonpos hty
    have hcoeff : t ^ 2 / 2 ≤ Real.exp t - 1 - t := by
      linarith [Real.quadratic_le_exp_of_nonneg ht]
    calc
      Real.exp (t * y) ≤ 1 + t * y + (t * y) ^ 2 / 2 := hbase
      _ ≤ 1 + t * y + (Real.exp t - 1 - t) * y ^ 2 := by
        have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
        nlinarith [mul_le_mul_of_nonneg_right hcoeff hy2]
  · exact exp_mul_le_quadratic_of_mem_Icc ht ⟨hy0, hy⟩

/-- Scaled form of Chen--Shao (2005), (6.5). -/
lemma exp_mul_le_bennett_quadratic {t α y : ℝ} (ht : 0 ≤ t) (hα : 0 < α) (hy : y ≤ α) :
    Real.exp (t * y) ≤
      1 + t * y + ((Real.exp (t * α) - 1 - t * α) / α ^ 2) * y ^ 2 := by
  have hy' : y / α ≤ 1 := (div_le_one hα).mpr hy
  have h := exp_mul_le_quadratic_of_le_one (t := t * α) (y := y / α)
    (mul_nonneg ht hα.le) hy'
  convert h using 1 <;> field_simp [hα.ne']

/-! ### Moment-generating functions -/

variable {I Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

private lemma integrable_exp_mul_of_ae_le {Y : Ω → ℝ} {t α : ℝ}
    (hY : AEMeasurable Y μ) (ht : 0 ≤ t) (hY_le : ∀ᵐ ω ∂μ, Y ω ≤ α) :
    Integrable (fun ω ↦ Real.exp (t * Y ω)) μ := by
  refine (integrable_const (Real.exp (t * α))).mono' ?_ ?_
  · exact (hY.const_mul t).exp.aestronglyMeasurable
  · filter_upwards [hY_le] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω ht)

/-- The one-variable MGF estimate in Chen--Shao (2005), Lemma 6.2. -/
lemma mgf_le_exp_bennett {Y : Ω → ℝ} {t α : ℝ}
    (hY_meas : Measurable Y) (hY_mem : MemLp Y 2 μ)
    (hY_mean : ∫ ω, Y ω ∂μ ≤ 0) (hY_le : ∀ᵐ ω ∂μ, Y ω ≤ α)
    (ht : 0 ≤ t) (hα : 0 < α) :
    mgf Y μ t ≤ Real.exp
      (((Real.exp (t * α) - 1 - t * α) / α ^ 2) * ∫ ω, (Y ω) ^ 2 ∂μ) := by
  let c := (Real.exp (t * α) - 1 - t * α) / α ^ 2
  have hc : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (by linarith [Real.add_one_le_exp (t * α)]) (sq_nonneg α)
  have hY_int : Integrable Y μ := hY_mem.integrable (by norm_num)
  have hY_sq_int : Integrable (fun ω ↦ (Y ω) ^ 2) μ := hY_mem.integrable_sq
  have hexp_int : Integrable (fun ω ↦ Real.exp (t * Y ω)) μ :=
    integrable_exp_mul_of_ae_le hY_meas.aemeasurable ht hY_le
  have hquad_int : Integrable (fun ω ↦ 1 + t * Y ω + c * (Y ω) ^ 2) μ :=
    ((integrable_const (1 : ℝ)).add (hY_int.const_mul t)).add (hY_sq_int.const_mul c)
  have hmono :
      ∫ ω, Real.exp (t * Y ω) ∂μ ≤
        ∫ ω, (1 + t * Y ω + c * (Y ω) ^ 2) ∂μ := by
    refine integral_mono_ae hexp_int hquad_int ?_
    filter_upwards [hY_le] with ω hω
    simpa [c] using exp_mul_le_bennett_quadratic ht hα hω
  have hsecond_nonneg : 0 ≤ ∫ ω, (Y ω) ^ 2 ∂μ :=
    integral_nonneg fun ω ↦ sq_nonneg (Y ω)
  calc
    mgf Y μ t ≤ 1 + t * (∫ ω, Y ω ∂μ) + c * ∫ ω, (Y ω) ^ 2 ∂μ := by
      rw [mgf]
      refine hmono.trans_eq ?_
      calc
        ∫ ω, 1 + t * Y ω + c * (Y ω) ^ 2 ∂μ =
            (∫ ω, 1 + t * Y ω ∂μ) + ∫ ω, c * (Y ω) ^ 2 ∂μ :=
          integral_add ((integrable_const (1 : ℝ)).add (hY_int.const_mul t))
            (hY_sq_int.const_mul c)
        _ = ((∫ _ : Ω, (1 : ℝ) ∂μ) + t * ∫ ω, Y ω ∂μ) +
            c * ∫ ω, (Y ω) ^ 2 ∂μ := by
          rw [integral_add (integrable_const (1 : ℝ)) (hY_int.const_mul t),
            integral_const_mul t Y, integral_const_mul c (fun ω ↦ (Y ω) ^ 2)]
        _ = 1 + t * (∫ ω, Y ω ∂μ) + c * ∫ ω, (Y ω) ^ 2 ∂μ := by simp
    _ ≤ 1 + c * ∫ ω, (Y ω) ^ 2 ∂μ := by
      have : t * (∫ ω, Y ω ∂μ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hY_mean
      linarith
    _ ≤ Real.exp (c * ∫ ω, (Y ω) ^ 2 ∂μ) := by
      simpa [add_comm] using Real.add_one_le_exp (c * ∫ ω, (Y ω) ^ 2 ∂μ)

/-- Chen--Shao (2005), (6.2), for a finite independent family. -/
lemma mgf_finsetSum_le_exp_bennett [Fintype I] {Y : I → Ω → ℝ} {t α B2 : ℝ}
    (s : Finset I) (hY_meas : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ)
    (hY_mem : ∀ i, MemLp (Y i) 2 μ) (hY_mean : ∀ i, ∫ ω, Y i ω ∂μ ≤ 0)
    (hY_le : ∀ i, ∀ᵐ ω ∂μ, Y i ω ≤ α)
    (hsecond : ∑ i ∈ s, ∫ ω, (Y i ω) ^ 2 ∂μ ≤ B2)
    (ht : 0 ≤ t) (hα : 0 < α) :
    mgf (∑ i ∈ s, Y i) μ t ≤
      Real.exp (((Real.exp (t * α) - 1 - t * α) / α ^ 2) * B2) := by
  let c := (Real.exp (t * α) - 1 - t * α) / α ^ 2
  have hc : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (by linarith [Real.add_one_le_exp (t * α)]) (sq_nonneg α)
  rw [h_indep.mgf_sum hY_meas s]
  calc
    ∏ i ∈ s, mgf (Y i) μ t
        ≤ ∏ i ∈ s, Real.exp (c * ∫ ω, (Y i ω) ^ 2 ∂μ) := by
          refine Finset.prod_le_prod (fun i hi ↦ mgf_nonneg) ?_
          intro i hi
          simpa [c] using mgf_le_exp_bennett (hY_meas i) (hY_mem i) (hY_mean i)
            (hY_le i) ht hα
    _ = Real.exp (∑ i ∈ s, c * ∫ ω, (Y i ω) ^ 2 ∂μ) := by
      rw [Real.exp_sum]
    _ ≤ Real.exp (c * B2) := by
      rw [Real.exp_le_exp]
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hsecond hc

/-- Chernoff consequence of the Bennett--Hoeffding MGF estimate. -/
lemma measure_finsetSum_ge_le_exp_bennett [Fintype I] {Y : I → Ω → ℝ}
    {t α B2 x : ℝ} (s : Finset I) (hY_meas : ∀ i, Measurable (Y i))
    (h_indep : iIndepFun Y μ) (hY_mem : ∀ i, MemLp (Y i) 2 μ)
    (hY_mean : ∀ i, ∫ ω, Y i ω ∂μ ≤ 0) (hY_le : ∀ i, ∀ᵐ ω ∂μ, Y i ω ≤ α)
    (hsecond : ∑ i ∈ s, ∫ ω, (Y i ω) ^ 2 ∂μ ≤ B2)
    (ht : 0 ≤ t) (hα : 0 < α) :
    μ.real {ω | x ≤ ∑ i ∈ s, Y i ω} ≤
      Real.exp (-t * x + ((Real.exp (t * α) - 1 - t * α) / α ^ 2) * B2) := by
  have h_exp_i : ∀ i ∈ s, Integrable (fun ω ↦ Real.exp (t * Y i ω)) μ := by
    intro i hi
    exact integrable_exp_mul_of_ae_le (hY_meas i).aemeasurable ht (hY_le i)
  have h_exp_sum : Integrable (fun ω ↦ Real.exp (t * (∑ i ∈ s, Y i) ω)) μ :=
    h_indep.integrable_exp_mul_sum hY_meas h_exp_i
  calc
    μ.real {ω | x ≤ ∑ i ∈ s, Y i ω}
        ≤ Real.exp (-t * x) * mgf (∑ i ∈ s, Y i) μ t :=
          by simpa only [Finset.sum_apply] using measure_ge_le_exp_mul_mgf x ht h_exp_sum
    _ ≤ Real.exp (-t * x) *
        Real.exp (((Real.exp (t * α) - 1 - t * α) / α ^ 2) * B2) := by
          gcongr
          exact mgf_finsetSum_le_exp_bennett s hY_meas h_indep hY_mem hY_mean hY_le
            hsecond ht hα
    _ = Real.exp (-t * x + ((Real.exp (t * α) - 1 - t * α) / α ^ 2) * B2) := by
      rw [Real.exp_add]

/-! ### One-sided truncation -/

/-- One-sided truncation at `1`, written `\bar ξ = ξ 1_{ξ ≤ 1}` by Chen--Shao. -/
def upperTruncateOne (x : ℝ) : ℝ := if x ≤ 1 then x else 0

lemma measurable_upperTruncateOne : Measurable upperTruncateOne :=
  Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_id measurable_const

lemma upperTruncateOne_le_one (x : ℝ) : upperTruncateOne x ≤ 1 := by
  by_cases hx : x ≤ 1 <;> simp [upperTruncateOne, hx]

lemma upperTruncateOne_le_self (x : ℝ) : upperTruncateOne x ≤ x := by
  by_cases hx : x ≤ 1
  · simp [upperTruncateOne, hx]
  · simp only [upperTruncateOne, if_neg hx]
    linarith

/-- The nonnegative drift removed by one-sided truncation. -/
def upperTruncateOneRemainder (x : ℝ) : ℝ := x - upperTruncateOne x

lemma measurable_upperTruncateOneRemainder : Measurable upperTruncateOneRemainder :=
  measurable_id.sub measurable_upperTruncateOne

lemma upperTruncateOneRemainder_nonneg (x : ℝ) : 0 ≤ upperTruncateOneRemainder x :=
  sub_nonneg.mpr (upperTruncateOne_le_self x)

lemma upperTruncateOneRemainder_le_abs_cube (x : ℝ) :
    upperTruncateOneRemainder x ≤ |x| ^ 3 := by
  by_cases hx : x ≤ 1
  · simp [upperTruncateOneRemainder, upperTruncateOne, hx, pow_nonneg (abs_nonneg x)]
  · have hx1 : 1 < x := lt_of_not_ge hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx1
    rw [upperTruncateOneRemainder, upperTruncateOne, if_neg hx, sub_zero, abs_of_pos hx0]
    nlinarith [mul_self_le_mul_self (by linarith : 0 ≤ (1 : ℝ)) hx1.le]

lemma abs_upperTruncateOne_le_abs (x : ℝ) : |upperTruncateOne x| ≤ |x| := by
  by_cases hx : x ≤ 1 <;> simp [upperTruncateOne, hx]

lemma sq_upperTruncateOne_le_sq (x : ℝ) : upperTruncateOne x ^ 2 ≤ x ^ 2 := by
  by_cases hx : x ≤ 1
  · simp [upperTruncateOne, hx]
  · simp only [upperTruncateOne, if_neg hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact sq_nonneg x

lemma measurable_upperTruncateOne_comp {Y : Ω → ℝ} (hY : Measurable Y) :
    Measurable (upperTruncateOne ∘ Y) :=
  measurable_upperTruncateOne.comp hY

omit [IsProbabilityMeasure μ] in
lemma memLp_upperTruncateOne_comp {Y : Ω → ℝ} (hY_meas : Measurable Y)
    (hY : MemLp Y 2 μ) : MemLp (upperTruncateOne ∘ Y) 2 μ := by
  refine hY.mono (measurable_upperTruncateOne_comp hY_meas).aestronglyMeasurable ?_
  filter_upwards with ω
  simpa only [Function.comp_apply, Real.norm_eq_abs] using abs_upperTruncateOne_le_abs (Y ω)

lemma integral_upperTruncateOne_comp_nonpos {Y : Ω → ℝ} (hY_meas : Measurable Y)
    (hY : MemLp Y 2 μ) (hY_mean : ∫ ω, Y ω ∂μ = 0) :
    ∫ ω, upperTruncateOne (Y ω) ∂μ ≤ 0 := by
  have hY_int : Integrable Y μ := hY.integrable (by norm_num)
  have hbar_int : Integrable (upperTruncateOne ∘ Y) μ :=
    (memLp_upperTruncateOne_comp hY_meas hY).integrable (by norm_num)
  have hmono : ∫ ω, upperTruncateOne (Y ω) ∂μ ≤ ∫ ω, Y ω ∂μ := by
    exact integral_mono hbar_int hY_int fun ω ↦ upperTruncateOne_le_self (Y ω)
  simpa [hY_mean] using hmono

lemma neg_integral_upperTruncateOne_comp_le_cube {Y : Ω → ℝ}
    (hY_meas : Measurable Y) (hY : MemLp Y 2 μ)
    (hY_mean : ∫ ω, Y ω ∂μ = 0) (h3 : Integrable (fun ω ↦ |Y ω| ^ 3) μ) :
    -(∫ ω, upperTruncateOne (Y ω) ∂μ) ≤ ∫ ω, |Y ω| ^ 3 ∂μ := by
  have hY_int : Integrable Y μ := hY.integrable (by norm_num)
  have hbar_int : Integrable (fun ω ↦ upperTruncateOne (Y ω)) μ :=
    (memLp_upperTruncateOne_comp hY_meas hY).integrable (by norm_num)
  have hrem_int : Integrable (fun ω ↦ upperTruncateOneRemainder (Y ω)) μ := by
    convert hY_int.sub hbar_int using 1
    ext ω
    simp only [Pi.sub_apply, upperTruncateOneRemainder]
  have hrem_le : ∫ ω, upperTruncateOneRemainder (Y ω) ∂μ ≤
      ∫ ω, |Y ω| ^ 3 ∂μ :=
    integral_mono hrem_int h3 fun ω ↦ upperTruncateOneRemainder_le_abs_cube (Y ω)
  have hrem_eq : ∫ ω, upperTruncateOneRemainder (Y ω) ∂μ =
      -(∫ ω, upperTruncateOne (Y ω) ∂μ) := by
    rw [show (fun ω ↦ upperTruncateOneRemainder (Y ω)) =
        fun ω ↦ Y ω - upperTruncateOne (Y ω) by
      ext ω; rfl]
    rw [integral_sub hY_int hbar_int, hY_mean, zero_sub]
  rwa [hrem_eq] at hrem_le

omit [IsProbabilityMeasure μ] in
lemma integral_sq_upperTruncateOne_comp_le {Y : Ω → ℝ} (hY_meas : Measurable Y)
    (hY : MemLp Y 2 μ) :
    ∫ ω, upperTruncateOne (Y ω) ^ 2 ∂μ ≤ ∫ ω, Y ω ^ 2 ∂μ := by
  have hbar_sq := (memLp_upperTruncateOne_comp hY_meas hY).integrable_sq
  exact integral_mono hbar_sq hY.integrable_sq fun ω ↦ sq_upperTruncateOne_le_sq (Y ω)

omit [IsProbabilityMeasure μ] in
lemma iIndepFun_upperTruncateOne_comp [Fintype I] {Y : I → Ω → ℝ}
    (h_indep : iIndepFun Y μ) : iIndepFun (fun i ↦ upperTruncateOne ∘ Y i) μ :=
  h_indep.comp (fun _ ↦ upperTruncateOne) fun _ ↦ measurable_upperTruncateOne

/-! ### The exponentially weighted ramp -/

/-- The nonnegative ramp of height `b - a + 2 * δ` used in Chen--Shao (2005), (6.6). -/
def positiveConcRamp (a b δ w : ℝ) : ℝ :=
  concRamp a b δ w + ((b - a) / 2 + δ)

/-- Chen--Shao's exponentially weighted ramp (6.6). -/
def exponentialConcRamp (a b δ w : ℝ) : ℝ :=
  Real.exp (w / 2) * positiveConcRamp a b δ w

lemma continuous_positiveConcRamp (a b δ : ℝ) : Continuous (positiveConcRamp a b δ) :=
  (continuous_concRamp a b δ).add continuous_const

lemma continuous_exponentialConcRamp (a b δ : ℝ) : Continuous (exponentialConcRamp a b δ) := by
  exact (Real.continuous_exp.comp (continuous_id.div_const 2)).mul
    (continuous_positiveConcRamp a b δ)

lemma positiveConcRamp_nonneg {a b δ w : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    0 ≤ positiveConcRamp a b δ w := by
  have habs := abs_concRamp_le (w := w) hδ hab
  rw [abs_le] at habs
  simp only [positiveConcRamp]
  linarith [habs.1]

lemma positiveConcRamp_le {a b δ w : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    positiveConcRamp a b δ w ≤ b - a + 2 * δ := by
  have habs := abs_concRamp_le (w := w) hδ hab
  rw [abs_le] at habs
  simp only [positiveConcRamp]
  linarith [habs.2]

lemma positiveConcRamp_mono {a b δ u v : ℝ} (huv : u ≤ v) :
    positiveConcRamp a b δ u ≤ positiveConcRamp a b δ v := by
  simp only [positiveConcRamp, concRamp]
  gcongr

lemma exponentialConcRamp_nonneg {a b δ w : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    0 ≤ exponentialConcRamp a b δ w :=
  mul_nonneg (Real.exp_pos _).le (positiveConcRamp_nonneg hδ hab)

lemma exponentialConcRamp_le {a b δ w : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    exponentialConcRamp a b δ w ≤ Real.exp (w / 2) * (b - a + 2 * δ) := by
  exact mul_le_mul_of_nonneg_left (positiveConcRamp_le hδ hab) (Real.exp_pos _).le

lemma exponentialConcRamp_mono {a b δ u v : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b)
    (huv : u ≤ v) :
    exponentialConcRamp a b δ u ≤ exponentialConcRamp a b δ v := by
  have hexp : Real.exp (u / 2) ≤ Real.exp (v / 2) := Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul hexp (positiveConcRamp_mono huv)
    (positiveConcRamp_nonneg hδ hab) (Real.exp_pos _).le

lemma exponentialConcRamp_exchange_nonneg {a b δ w ξ : ℝ} (hδ : 0 ≤ δ)
    (hab : a ≤ b) :
    0 ≤ ξ * (exponentialConcRamp a b δ w - exponentialConcRamp a b δ (w - ξ)) := by
  rcases le_total 0 ξ with hξ | hξ
  · exact mul_nonneg hξ (sub_nonneg.mpr (exponentialConcRamp_mono hδ hab (by linarith)))
  · exact mul_nonneg_of_nonpos_of_nonpos hξ
      (sub_nonpos.mpr (exponentialConcRamp_mono hδ hab (by linarith)))

/-- On the target interval, weighted exchange dominates an exponentially weighted kernel mass.

The loss `exp (-1/2)` replaces the sharper `exp (-δ/2)` in Chen--Shao (6.7); it is enough
because the one-sided truncated increment is always at most `1`. -/
lemma exponentialConcRamp_exchange_ge {a b δ w ξ : ℝ}
    (hδ : 0 ≤ δ) (hab : a ≤ b) (hw : w ∈ Icc a b) (hξ : ξ ≤ 1) :
    Real.exp ((w - 1) / 2) * kernelMass δ ξ ≤
      ξ * (exponentialConcRamp a b δ w - exponentialConcRamp a b δ (w - ξ)) := by
  have hkernel : kernelMass δ ξ ≤
      ξ * (positiveConcRamp a b δ w - positiveConcRamp a b δ (w - ξ)) := by
    have h := integral_kernel_mul_concInd_ge (a := a) (b := b) hδ hw ( ξ := ξ)
    rw [← mul_concRamp_sub_eq_integral_kernel hδ hab] at h
    simpa [positiveConcRamp, kernelMass] using h
  rcases le_total 0 ξ with hξ0 | hξ0
  · have hwu : w - ξ ≤ w := by linarith
    have hgmono := positiveConcRamp_mono (a := a) (b := b) (δ := δ) hwu
    have hgw0 := positiveConcRamp_nonneg (a := a) (b := b) (w := w) hδ hab
    have hexp_mono : Real.exp ((w - ξ) / 2) ≤ Real.exp (w / 2) := by
      rw [Real.exp_le_exp]
      linarith
    have hexp_lower : Real.exp ((w - 1) / 2) ≤ Real.exp ((w - ξ) / 2) := by
      rw [Real.exp_le_exp]
      linarith
    have hfdiff :
        Real.exp ((w - ξ) / 2) *
            (positiveConcRamp a b δ w - positiveConcRamp a b δ (w - ξ)) ≤
          exponentialConcRamp a b δ w - exponentialConcRamp a b δ (w - ξ) := by
      simp only [exponentialConcRamp]
      have hnonneg : 0 ≤
          (Real.exp (w / 2) - Real.exp ((w - ξ) / 2)) * positiveConcRamp a b δ w :=
        mul_nonneg (sub_nonneg.mpr hexp_mono) hgw0
      nlinarith
    have hq0 : 0 ≤
        ξ * (positiveConcRamp a b δ w - positiveConcRamp a b δ (w - ξ)) :=
      mul_nonneg hξ0 (sub_nonneg.mpr hgmono)
    calc
      Real.exp ((w - 1) / 2) * kernelMass δ ξ ≤
          Real.exp ((w - 1) / 2) *
            (ξ * (positiveConcRamp a b δ w - positiveConcRamp a b δ (w - ξ))) := by
              gcongr
      _ ≤ Real.exp ((w - ξ) / 2) *
            (ξ * (positiveConcRamp a b δ w - positiveConcRamp a b δ (w - ξ))) := by
              exact mul_le_mul_of_nonneg_right hexp_lower hq0
      _ = ξ * (Real.exp ((w - ξ) / 2) *
            (positiveConcRamp a b δ w - positiveConcRamp a b δ (w - ξ))) := by ring
      _ ≤ ξ * (exponentialConcRamp a b δ w -
            exponentialConcRamp a b δ (w - ξ)) :=
        mul_le_mul_of_nonneg_left hfdiff hξ0
  · have hξ_nonpos : ξ ≤ 0 := hξ0
    have hwu : w ≤ w - ξ := by linarith
    have hgmono := positiveConcRamp_mono (a := a) (b := b) (δ := δ) hwu
    have hgnext0 := positiveConcRamp_nonneg (a := a) (b := b) (w := w - ξ) hδ hab
    have hexp_mono : Real.exp (w / 2) ≤ Real.exp ((w - ξ) / 2) := by
      rw [Real.exp_le_exp]
      linarith
    have hexp_lower : Real.exp ((w - 1) / 2) ≤ Real.exp (w / 2) := by
      rw [Real.exp_le_exp]
      linarith
    have hfdiff :
        Real.exp (w / 2) *
            (positiveConcRamp a b δ (w - ξ) - positiveConcRamp a b δ w) ≤
          exponentialConcRamp a b δ (w - ξ) - exponentialConcRamp a b δ w := by
      simp only [exponentialConcRamp]
      have hnonneg : 0 ≤
          (Real.exp ((w - ξ) / 2) - Real.exp (w / 2)) * positiveConcRamp a b δ (w - ξ) :=
        mul_nonneg (sub_nonneg.mpr hexp_mono) hgnext0
      nlinarith
    have hq0 : 0 ≤
        ξ * (positiveConcRamp a b δ w - positiveConcRamp a b δ (w - ξ)) := by
      exact mul_nonneg_of_nonpos_of_nonpos hξ_nonpos (sub_nonpos.mpr hgmono)
    calc
      Real.exp ((w - 1) / 2) * kernelMass δ ξ ≤
          Real.exp ((w - 1) / 2) *
            (ξ * (positiveConcRamp a b δ w - positiveConcRamp a b δ (w - ξ))) := by
              gcongr
      _ ≤ Real.exp (w / 2) *
            (ξ * (positiveConcRamp a b δ w - positiveConcRamp a b δ (w - ξ))) := by
              exact mul_le_mul_of_nonneg_right hexp_lower hq0
      _ = (-ξ) * (Real.exp (w / 2) *
            (positiveConcRamp a b δ (w - ξ) - positiveConcRamp a b δ w)) := by ring
      _ ≤ (-ξ) * (exponentialConcRamp a b δ (w - ξ) -
            exponentialConcRamp a b δ w) :=
        mul_le_mul_of_nonneg_left hfdiff (neg_nonneg.mpr hξ_nonpos)
      _ = ξ * (exponentialConcRamp a b δ w -
            exponentialConcRamp a b δ (w - ξ)) := by ring

/-! ### Fixed parameters used by Chen--Shao Proposition 6.1 -/

/-- The `t = 1/2`, `α = B² = 1` specialization used in Proposition 6.1. -/
lemma mgf_finsetSum_le_half [Fintype I] {Y : I → Ω → ℝ} (s : Finset I)
    (hY_meas : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ)
    (hY_mem : ∀ i, MemLp (Y i) 2 μ) (hY_mean : ∀ i, ∫ ω, Y i ω ∂μ ≤ 0)
    (hY_le : ∀ i, ∀ᵐ ω ∂μ, Y i ω ≤ 1)
    (hsecond : ∑ i ∈ s, ∫ ω, (Y i ω) ^ 2 ∂μ ≤ 1) :
    mgf (∑ i ∈ s, Y i) μ (1 / 2) ≤ Real.exp (Real.exp (1 / 2) - 3 / 2) := by
  convert mgf_finsetSum_le_exp_bennett s hY_meas h_indep hY_mem hY_mean hY_le hsecond
      (t := (1 / 2 : ℝ)) (by norm_num) (by norm_num) using 1
  ring_nf

/-- The `t = 1`, `α = B² = 1` specialization used in the covariance estimate. -/
lemma mgf_finsetSum_le_one [Fintype I] {Y : I → Ω → ℝ} (s : Finset I)
    (hY_meas : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ)
    (hY_mem : ∀ i, MemLp (Y i) 2 μ) (hY_mean : ∀ i, ∫ ω, Y i ω ∂μ ≤ 0)
    (hY_le : ∀ i, ∀ᵐ ω ∂μ, Y i ω ≤ 1)
    (hsecond : ∑ i ∈ s, ∫ ω, (Y i ω) ^ 2 ∂μ ≤ 1) :
    mgf (∑ i ∈ s, Y i) μ 1 ≤ Real.exp (Real.exp 1 - 2) := by
  convert mgf_finsetSum_le_exp_bennett s hY_meas h_indep hY_mem hY_mean hY_le hsecond
      (t := (1 : ℝ)) (by norm_num) (by norm_num) using 1
  ring_nf

private lemma exp_one_le_three : Real.exp 1 ≤ 3 := by
  exact (Real.exp_le_two_add_div_two_sub (x := (1 : ℝ)) (by norm_num) (by norm_num)).trans_eq
    (by norm_num)

private lemma exp_half_le_two : Real.exp (1 / 2) ≤ 2 := by
  exact (Real.exp_le_two_add_div_two_sub (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).trans
    (by norm_num)

lemma mgf_finsetSum_one_le_three [Fintype I] {Y : I → Ω → ℝ} (s : Finset I)
    (hY_meas : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ)
    (hY_mem : ∀ i, MemLp (Y i) 2 μ) (hY_mean : ∀ i, ∫ ω, Y i ω ∂μ ≤ 0)
    (hY_le : ∀ i, ∀ᵐ ω ∂μ, Y i ω ≤ 1)
    (hsecond : ∑ i ∈ s, ∫ ω, (Y i ω) ^ 2 ∂μ ≤ 1) :
    mgf (∑ i ∈ s, Y i) μ 1 ≤ 3 := by
  calc
    mgf (∑ i ∈ s, Y i) μ 1 ≤ Real.exp (Real.exp 1 - 2) :=
      mgf_finsetSum_le_one s hY_meas h_indep hY_mem hY_mean hY_le hsecond
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith [exp_one_le_three])
    _ ≤ 3 := exp_one_le_three

lemma mgf_finsetSum_half_le_two [Fintype I] {Y : I → Ω → ℝ} (s : Finset I)
    (hY_meas : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ)
    (hY_mem : ∀ i, MemLp (Y i) 2 μ) (hY_mean : ∀ i, ∫ ω, Y i ω ∂μ ≤ 0)
    (hY_le : ∀ i, ∀ᵐ ω ∂μ, Y i ω ≤ 1)
    (hsecond : ∑ i ∈ s, ∫ ω, (Y i ω) ^ 2 ∂μ ≤ 1) :
    mgf (∑ i ∈ s, Y i) μ (1 / 2) ≤ 2 := by
  calc
    mgf (∑ i ∈ s, Y i) μ (1 / 2) ≤
        Real.exp (Real.exp (1 / 2) - 3 / 2) :=
      mgf_finsetSum_le_half s hY_meas h_indep hY_mem hY_mean hY_le hsecond
    _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith [exp_half_le_two])
    _ ≤ 2 := exp_half_le_two

lemma memLp_exp_half_finsetSum [Fintype I] {Y : I → Ω → ℝ} (s : Finset I)
    (hY_meas : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ)
    (hY_le : ∀ i, ∀ᵐ ω ∂μ, Y i ω ≤ 1) :
    MemLp (fun ω ↦ Real.exp ((∑ i ∈ s, Y i ω) / 2)) 2 μ := by
  let W : Ω → ℝ := fun ω ↦ ∑ i ∈ s, Y i ω
  have hW_meas : Measurable W := Finset.measurable_fun_sum s fun i _ ↦ hY_meas i
  have h_exp_i : ∀ i ∈ s, Integrable (fun ω ↦ Real.exp (1 * Y i ω)) μ := by
    intro i hi
    exact integrable_exp_mul_of_ae_le (hY_meas i).aemeasurable (by norm_num) (hY_le i)
  have h_exp_W : Integrable (fun ω ↦ Real.exp (1 * W ω)) μ :=
    by simpa only [W, Finset.sum_apply] using
      h_indep.integrable_exp_mul_sum hY_meas h_exp_i
  have hG_meas : Measurable (fun ω ↦ Real.exp (W ω / 2)) := (hW_meas.div_const 2).exp
  have hG : MemLp (fun ω ↦ Real.exp (W ω / 2)) 2 μ := by
    refine (memLp_two_iff_integrable_sq hG_meas.aestronglyMeasurable).2 ?_
    convert h_exp_W using 1
    ext ω
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [W, Finset.sum_apply] using hG

lemma memLp_exponentialConcRamp_finsetSum [Fintype I] {Y : I → Ω → ℝ} (s : Finset I)
    (hY_meas : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ)
    (hY_le : ∀ i, ∀ᵐ ω ∂μ, Y i ω ≤ 1)
    {a b δ : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    MemLp (fun ω ↦ exponentialConcRamp a b δ (∑ i ∈ s, Y i ω)) 2 μ := by
  let W : Ω → ℝ := fun ω ↦ ∑ i ∈ s, Y i ω
  let L : ℝ := b - a + 2 * δ
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hW_meas : Measurable W := Finset.measurable_fun_sum _ fun i _ ↦ hY_meas i
  have hG : MemLp (fun ω ↦ Real.exp (W ω / 2)) 2 μ := by
    simpa only [W] using memLp_exp_half_finsetSum s hY_meas h_indep hY_le
  have hF_meas : Measurable (fun ω ↦ exponentialConcRamp a b δ (W ω)) :=
    (continuous_exponentialConcRamp a b δ).measurable.comp hW_meas
  have hF : MemLp (fun ω ↦ exponentialConcRamp a b δ (W ω)) 2 μ := by
    refine (hG.const_mul L).mono hF_meas.aestronglyMeasurable ?_
    filter_upwards with ω
    calc
      ‖exponentialConcRamp a b δ (W ω)‖ = exponentialConcRamp a b δ (W ω) :=
        Real.norm_of_nonneg (exponentialConcRamp_nonneg hδ hab)
      _ ≤ Real.exp (W ω / 2) * L := by
        simpa only [L] using
          exponentialConcRamp_le (a := a) (b := b) (δ := δ) (w := W ω) hδ hab
      _ = L * Real.exp (W ω / 2) := mul_comm _ _
      _ = ‖L * Real.exp (W ω / 2)‖ :=
        (Real.norm_of_nonneg (mul_nonneg hL (Real.exp_pos _).le)).symm
  simpa only [W] using hF

/-- The preliminary exponential interval bound in the proof of Proposition 6.1. -/
lemma measure_finsetSum_mem_Icc_le_half [Fintype I] {Y : I → Ω → ℝ}
    (s : Finset I) (hY_meas : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ)
    (hY_mem : ∀ i, MemLp (Y i) 2 μ) (hY_mean : ∀ i, ∫ ω, Y i ω ∂μ ≤ 0)
    (hY_le : ∀ i, ∀ᵐ ω ∂μ, Y i ω ≤ 1)
    (hsecond : ∑ i ∈ s, ∫ ω, (Y i ω) ^ 2 ∂μ ≤ 1) {a b : ℝ} :
    μ.real {ω | ∑ i ∈ s, Y i ω ∈ Icc a b} ≤
      Real.exp (-a / 2 + Real.exp (1 / 2) - 3 / 2) := by
  calc
    μ.real {ω | ∑ i ∈ s, Y i ω ∈ Icc a b}
        ≤ μ.real {ω | a ≤ ∑ i ∈ s, Y i ω} :=
      measureReal_mono fun ω hω ↦ hω.1
    _ ≤ Real.exp (-(1 / 2) * a + (Real.exp ((1 / 2) * 1) - 1 - (1 / 2) * 1) /
          1 ^ 2 * 1) :=
      measure_finsetSum_ge_le_exp_bennett s hY_meas h_indep hY_mem hY_mean hY_le
        hsecond (t := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    _ = Real.exp (-a / 2 + Real.exp (1 / 2) - 3 / 2) := by
      congr 1
      ring_nf

/-! ### The preliminary leave-one-out bound -/

variable [Fintype I] [DecidableEq I]

lemma sum_neg_integral_upperTruncateOne_erase_le_thirdMomentSum {X : I → Ω → ℝ}
    (hX_meas : ∀ j, Measurable (X j)) (hX_mem : ∀ j, MemLp (X j) 2 μ)
    (hX_mean : ∀ j, ∫ ω, X j ω ∂μ = 0)
    (h3 : ∀ j, Integrable (fun ω ↦ |X j ω| ^ 3) μ) (i : I) :
    ∑ j ∈ Finset.univ.erase i, -(∫ ω, upperTruncateOne (X j ω) ∂μ) ≤
      thirdMomentSum X μ := by
  calc
    ∑ j ∈ Finset.univ.erase i, -(∫ ω, upperTruncateOne (X j ω) ∂μ) ≤
        ∑ j ∈ Finset.univ.erase i, ∫ ω, |X j ω| ^ 3 ∂μ :=
      Finset.sum_le_sum fun j hj ↦
        neg_integral_upperTruncateOne_comp_le_cube (hX_meas j) (hX_mem j)
          (hX_mean j) (h3 j)
    _ ≤ ∑ j : I, ∫ ω, |X j ω| ^ 3 ∂μ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun j hj hnot ↦ integral_nonneg fun ω ↦ pow_nonneg (abs_nonneg _) _
    _ = thirdMomentSum X μ := rfl

omit [DecidableEq I] in
lemma thirdMomentSum_pos_of_variance_sum_eq_one {X : I → Ω → ℝ}
    (hX_mem : ∀ j, MemLp (X j) 2 μ) (hX_mean : ∀ j, ∫ ω, X j ω ∂μ = 0)
    (hvar : ∑ j, variance (X j) μ = 1)
    (h3 : ∀ j, Integrable (fun ω ↦ |X j ω| ^ 3) μ) :
    0 < thirdMomentSum X μ := by
  have hγ0 : 0 ≤ thirdMomentSum X μ := thirdMomentSum_nonneg h3
  refine hγ0.lt_of_ne ?_
  intro hγeq
  have hterm : ∀ j : I, ∫ ω, |X j ω| ^ 3 ∂μ = 0 := by
    have hsum : ∑ j : I, ∫ ω, |X j ω| ^ 3 ∂μ = 0 := by
      simpa only [thirdMomentSum] using hγeq.symm
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j hj ↦ integral_nonneg fun ω ↦ pow_nonneg (abs_nonneg _) _)).mp hsum
    exact fun j ↦ hall j (Finset.mem_univ j)
  have hsq0 : ∀ j : I, ∫ ω, (X j ω) ^ 2 ∂μ = 0 := by
    intro j
    have hcube_ae : (fun ω ↦ |X j ω| ^ 3) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun ω ↦ pow_nonneg (abs_nonneg _) _) (h3 j)).mp (hterm j)
    have hX0 : X j =ᵐ[μ] 0 := by
      filter_upwards [hcube_ae] with ω hω
      change |X j ω| ^ 3 = 0 at hω
      have habs : |X j ω| = 0 :=
        (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hω
      exact abs_eq_zero.mp habs
    have hpow0 : (fun ω ↦ (X j ω) ^ 2) =ᵐ[μ] (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [hX0] with ω hω
      simp [hω]
    calc
      ∫ ω, (X j ω) ^ 2 ∂μ = ∫ _ : Ω, (0 : ℝ) ∂μ :=
        integral_congr_ae hpow0
      _ = 0 := by simp
  have hsecond := sum_integral_sq_eq_one hX_mem hX_mean hvar
  have : ∑ j : I, ∫ ω, (X j ω) ^ 2 ∂μ = 0 := Finset.sum_eq_zero fun j hj ↦ hsq0 j
  linarith

lemma sum_integral_sq_upperTruncateOne_erase_le_one {X : I → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i)) (hX_mem : ∀ i, MemLp (X i) 2 μ)
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1) (i : I) :
    ∑ j ∈ Finset.univ.erase i, ∫ ω, upperTruncateOne (X j ω) ^ 2 ∂μ ≤ 1 := by
  have htotal : ∑ j : I, ∫ ω, (X j ω) ^ 2 ∂μ = 1 := by
    calc
      ∑ j : I, ∫ ω, (X j ω) ^ 2 ∂μ = ∑ j : I, variance (X j) μ := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        exact (variance_eq_integral_sq (hX_mem j) (hX_mean j)).symm
      _ = 1 := hvar
  calc
    ∑ j ∈ Finset.univ.erase i, ∫ ω, upperTruncateOne (X j ω) ^ 2 ∂μ
        ≤ ∑ j ∈ Finset.univ.erase i, ∫ ω, (X j ω) ^ 2 ∂μ := by
          exact Finset.sum_le_sum fun j hj ↦
            integral_sq_upperTruncateOne_comp_le (hX_meas j) (hX_mem j)
    _ ≤ ∑ j : I, ∫ ω, (X j ω) ^ 2 ∂μ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (Finset.univ.erase i))
        fun j hj hnot ↦ integral_nonneg fun ω ↦ sq_nonneg (X j ω)
    _ = 1 := htotal

lemma integral_sq_upperTruncated_leaveOneOut_le_two {X : I → Ω → ℝ}
    (hX_meas : ∀ j, Measurable (X j)) (h_indep : iIndepFun X μ)
    (hX_mem : ∀ j, MemLp (X j) 2 μ) (hX_mean : ∀ j, ∫ ω, X j ω ∂μ = 0)
    (hvar : ∑ j, variance (X j) μ = 1)
    (h3 : ∀ j, Integrable (fun ω ↦ |X j ω| ^ 3) μ)
    (hγ : thirdMomentSum X μ ≤ 1) (i : I) :
    ∫ ω, (∑ j ∈ Finset.univ.erase i, upperTruncateOne (X j ω)) ^ 2 ∂μ ≤ 2 := by
  let Y : I → Ω → ℝ := fun j ↦ upperTruncateOne ∘ X j
  let W : Ω → ℝ := fun ω ↦ ∑ j ∈ Finset.univ.erase i, Y j ω
  have hY_meas : ∀ j, Measurable (Y j) := fun j ↦
    measurable_upperTruncateOne_comp (hX_meas j)
  have hY_mem : ∀ j, MemLp (Y j) 2 μ := fun j ↦
    memLp_upperTruncateOne_comp (hX_meas j) (hX_mem j)
  have hY_indep : iIndepFun Y μ := iIndepFun_upperTruncateOne_comp h_indep
  have hY_mean : ∀ j, ∫ ω, Y j ω ∂μ ≤ 0 := fun j ↦
    integral_upperTruncateOne_comp_nonpos (hX_meas j) (hX_mem j) (hX_mean j)
  have hW_mem : MemLp W 2 μ := by
    exact memLp_finsetSum (s := Finset.univ.erase i) fun j hj ↦ hY_mem j
  have hW_mean : ∫ ω, W ω ∂μ =
      ∑ j ∈ Finset.univ.erase i, ∫ ω, Y j ω ∂μ := by
    simpa only [W, Finset.sum_apply] using
      (integral_finsetSum (μ := μ) (s := Finset.univ.erase i) (f := Y)
        fun j hj ↦ (hY_mem j).integrable (by norm_num))
  have hmean_nonpos : ∫ ω, W ω ∂μ ≤ 0 := by
    rw [hW_mean]
    exact Finset.sum_nonpos fun j hj ↦ hY_mean j
  have hmean_lower : -(thirdMomentSum X μ) ≤ ∫ ω, W ω ∂μ := by
    rw [hW_mean]
    have hsum := sum_neg_integral_upperTruncateOne_erase_le_thirdMomentSum
      hX_meas hX_mem hX_mean h3 i
    have hneg : -(∑ j ∈ Finset.univ.erase i, ∫ ω, Y j ω ∂μ) ≤
        thirdMomentSum X μ := by
      simpa only [Y, Function.comp_apply, Finset.sum_neg_distrib] using hsum
    linarith
  have hvarW : variance W μ ≤ 1 := by
    have hvarsum : variance W μ =
        ∑ j ∈ Finset.univ.erase i, variance (Y j) μ := by
      have h := IndepFun.variance_sum (s := Finset.univ.erase i)
        (fun j hj ↦ hY_mem j) (fun j hj k hk hjk ↦ hY_indep.indepFun hjk)
      have hW_eq : W = ∑ j ∈ Finset.univ.erase i, Y j := by
        ext ω
        simp only [W, Finset.sum_apply]
      rw [hW_eq]
      exact h
    rw [hvarsum]
    calc
      ∑ j ∈ Finset.univ.erase i, variance (Y j) μ ≤
          ∑ j ∈ Finset.univ.erase i, ∫ ω, (Y j ω) ^ 2 ∂μ :=
        Finset.sum_le_sum fun j hj ↦
          variance_le_expectation_sq (μ := μ) (X := Y j) (hY_meas j).aestronglyMeasurable
      _ ≤ 1 := by
        simpa [Y, Function.comp_apply] using
          sum_integral_sq_upperTruncateOne_erase_le_one hX_meas hX_mem hX_mean hvar i
  have hγ0 : 0 ≤ thirdMomentSum X μ := thirdMomentSum_nonneg h3
  have hmean_sq : (∫ ω, W ω ∂μ) ^ 2 ≤ 1 := by
    have habs : |∫ ω, W ω ∂μ| ≤ thirdMomentSum X μ := by
      rw [abs_of_nonpos hmean_nonpos]
      linarith
    have hsquare : (∫ ω, W ω ∂μ) ^ 2 ≤ (thirdMomentSum X μ) ^ 2 :=
      (sq_le_sq).2 (by simpa only [abs_abs, abs_of_nonneg hγ0] using habs)
    nlinarith
  have hsq : ∫ ω, (W ω) ^ 2 ∂μ ≤ 2 := by
    rw [variance_eq_sub hW_mem] at hvarW
    change (∫ ω, (W ω) ^ 2 ∂μ) - (∫ ω, W ω ∂μ) ^ 2 ≤ 1 at hvarW
    linarith
  simpa only [W, Y, Function.comp_apply] using hsq

/-- Kernel-mass sum over a one-sided truncated leave-one-out family. -/
def upperTruncatedKernelMassSum (δ : ℝ) (X : I → Ω → ℝ) (i : I) : Ω → ℝ :=
  fun ω ↦ ∑ j ∈ Finset.univ.erase i, kernelMass δ (upperTruncateOne (X j ω))

lemma measurable_upperTruncatedKernelMassSum {X : I → Ω → ℝ}
    (hX_meas : ∀ j, Measurable (X j)) (δ : ℝ) (i : I) :
    Measurable (upperTruncatedKernelMassSum δ X i) :=
  Finset.measurable_fun_sum _ fun j _ ↦
    (measurable_kernelMass δ).comp (measurable_upperTruncateOne.comp (hX_meas j))

omit [IsProbabilityMeasure μ] in
lemma memLp_upperTruncatedKernelMassSum {X : I → Ω → ℝ}
    (hX_meas : ∀ j, Measurable (X j)) (hX_mem : ∀ j, MemLp (X j) 2 μ)
    {δ : ℝ} (hδ : 0 ≤ δ) (i : I) : MemLp (upperTruncatedKernelMassSum δ X i) 2 μ := by
  refine memLp_finsetSum (s := Finset.univ.erase i) fun j hj ↦ ?_
  exact memLp_kernelMass (memLp_upperTruncateOne_comp (hX_meas j) (hX_mem j)) hδ
    (measurable_upperTruncateOne_comp (hX_meas j)).aestronglyMeasurable

lemma variance_upperTruncatedKernelMassSum_le {X : I → Ω → ℝ}
    (hX_meas : ∀ j, Measurable (X j)) (h_indep : iIndepFun X μ)
    (hX_mem : ∀ j, MemLp (X j) 2 μ) {δ : ℝ} (hδ : 0 ≤ δ) (i : I)
    (hsecond : ∑ j ∈ Finset.univ.erase i,
      ∫ ω, upperTruncateOne (X j ω) ^ 2 ∂μ ≤ 1) :
    variance (upperTruncatedKernelMassSum δ X i) μ ≤ δ ^ 2 := by
  let Y : I → Ω → ℝ := fun j ↦ upperTruncateOne ∘ X j
  let Z : I → Ω → ℝ := fun j ↦ kernelMass δ ∘ Y j
  have hY_meas : ∀ j, Measurable (Y j) := fun j ↦
    measurable_upperTruncateOne_comp (hX_meas j)
  have hY_mem : ∀ j, MemLp (Y j) 2 μ := fun j ↦
    memLp_upperTruncateOne_comp (hX_meas j) (hX_mem j)
  have hY_indep : iIndepFun Y μ := iIndepFun_upperTruncateOne_comp h_indep
  have hZ_meas : ∀ j, Measurable (Z j) := fun j ↦ (measurable_kernelMass δ).comp (hY_meas j)
  have hZ_mem : ∀ j, MemLp (Z j) 2 μ := fun j ↦
    memLp_kernelMass (hY_mem j) hδ (hY_meas j).aestronglyMeasurable
  have hZ_indep : iIndepFun Z μ :=
    hY_indep.comp (fun _ ↦ kernelMass δ) fun _ ↦ measurable_kernelMass δ
  have hsumvar : variance (∑ j ∈ Finset.univ.erase i, Z j) μ =
      ∑ j ∈ Finset.univ.erase i, variance (Z j) μ :=
    IndepFun.variance_sum (fun j hj ↦ hZ_mem j)
      (fun j hj k hk hjk ↦ hZ_indep.indepFun hjk)
  have hvar_each (j : I) :
      variance (Z j) μ ≤ δ ^ 2 * ∫ ω, (Y j ω) ^ 2 ∂μ := by
    have hvar0 : variance (Z j) μ ≤ ∫ ω, (Z j ω) ^ 2 ∂μ :=
      variance_le_expectation_sq (μ := μ) (X := Z j) (hZ_meas j).aestronglyMeasurable
    have hint : ∫ ω, (Z j ω) ^ 2 ∂μ ≤
        δ ^ 2 * ∫ ω, (Y j ω) ^ 2 ∂μ := by
      calc
        ∫ ω, (Z j ω) ^ 2 ∂μ ≤ ∫ ω, (δ * |Y j ω|) ^ 2 ∂μ := by
          refine integral_mono (hZ_mem j).integrable_sq ((hY_mem j).abs.const_mul δ).integrable_sq
            fun ω ↦ ?_
          exact (sq_le_sq₀ (kernelMass_nonneg hδ _)
            (mul_nonneg hδ (abs_nonneg _))).2 (kernelMass_le_mul_abs hδ)
        _ = ∫ ω, δ ^ 2 * (Y j ω) ^ 2 ∂μ := by
          refine integral_congr_ae (ae_of_all μ fun ω ↦ ?_)
          simp only [mul_pow, sq_abs]
        _ = δ ^ 2 * ∫ ω, (Y j ω) ^ 2 ∂μ := integral_const_mul _ _
    exact hvar0.trans hint
  have hdef : upperTruncatedKernelMassSum δ X i =
      ∑ j ∈ Finset.univ.erase i, Z j := by
    ext ω
    simp only [upperTruncatedKernelMassSum, Z, Y, Finset.sum_apply, Function.comp_apply]
  rw [hdef, hsumvar]
  calc
    ∑ j ∈ Finset.univ.erase i, variance (Z j) μ ≤
        ∑ j ∈ Finset.univ.erase i, δ ^ 2 * ∫ ω, (Y j ω) ^ 2 ∂μ :=
      Finset.sum_le_sum fun j hj ↦ hvar_each j
    _ = δ ^ 2 * ∑ j ∈ Finset.univ.erase i, ∫ ω, (Y j ω) ^ 2 ∂μ := by
      rw [Finset.mul_sum]
    _ ≤ δ ^ 2 * 1 := by
      gcongr
      simpa [Y, Function.comp_apply] using hsecond
    _ = δ ^ 2 := mul_one _

private lemma kernelMass_le_upperTruncateOne_add_cube {δ x : ℝ} (hδ : 0 ≤ δ) :
    kernelMass δ x ≤ kernelMass δ (upperTruncateOne x) + δ * |x| ^ 3 := by
  by_cases hx : x ≤ 1
  · simp [upperTruncateOne, hx, mul_nonneg hδ (pow_nonneg (abs_nonneg _) _)]
  · have hx1 : 1 < |x| := by rw [abs_of_pos (by linarith)]; linarith
    have hpow : |x| ≤ |x| ^ 3 := by
      calc
        |x| = 1 * |x| := by ring
        _ ≤ |x| ^ 2 * |x| := by
          gcongr
          nlinarith [sq_nonneg (|x| - 1)]
        _ = |x| ^ 3 := by ring
    simp only [upperTruncateOne, if_neg hx]
    rw [show kernelMass δ 0 = 0 by simp [kernelMass]]
    simpa only [zero_add] using
      (kernelMass_le_mul_abs (δ := δ) (ξ := x) hδ).trans
        (mul_le_mul_of_nonneg_left hpow hδ)

private lemma integral_kernelMass_le_upperTruncateOne_add_cube {Y : Ω → ℝ}
    (hY_meas : Measurable Y) (hY_mem : MemLp Y 2 μ)
    (h3 : Integrable (fun ω ↦ |Y ω| ^ 3) μ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∫ ω, kernelMass δ (Y ω) ∂μ ≤
      ∫ ω, kernelMass δ (upperTruncateOne (Y ω)) ∂μ +
        δ * ∫ ω, |Y ω| ^ 3 ∂μ := by
  have hK := (memLp_kernelMass hY_mem hδ hY_meas.aestronglyMeasurable).integrable (by norm_num)
  have hbar := memLp_upperTruncateOne_comp hY_meas hY_mem
  have hKbar := (memLp_kernelMass hbar hδ
    (measurable_upperTruncateOne_comp hY_meas).aestronglyMeasurable).integrable (by norm_num)
  have hKbar' : Integrable
      (fun ω ↦ kernelMass δ (upperTruncateOne (Y ω))) μ := by
    simpa only [Function.comp_apply] using hKbar
  have hrhs : Integrable (fun ω ↦
      kernelMass δ (upperTruncateOne (Y ω)) + δ * |Y ω| ^ 3) μ :=
    hKbar'.add (h3.const_mul δ)
  calc
    ∫ ω, kernelMass δ (Y ω) ∂μ ≤
        ∫ ω, (kernelMass δ (upperTruncateOne (Y ω)) + δ * |Y ω| ^ 3) ∂μ :=
      integral_mono hK hrhs fun ω ↦ kernelMass_le_upperTruncateOne_add_cube hδ
    _ = ∫ ω, kernelMass δ (upperTruncateOne (Y ω)) ∂μ +
        δ * ∫ ω, |Y ω| ^ 3 ∂μ := by
      rw [integral_add hKbar' (h3.const_mul δ), integral_const_mul]

private lemma integral_abs_coordinate_le_one {X : I → Ω → ℝ}
    (hX_mem : ∀ j, MemLp (X j) 2 μ) (hX_mean : ∀ j, ∫ ω, X j ω ∂μ = 0)
    (hvar : ∑ j, variance (X j) μ = 1) (i : I) : ∫ ω, |X i ω| ∂μ ≤ 1 := by
  have hdecomp : ∑ j, variance (X j) μ =
      (∑ j ∈ Finset.univ.erase i, variance (X j) μ) + variance (X i) μ := by
    exact (Finset.sum_erase_add
      (s := Finset.univ) (f := fun j ↦ variance (X j) μ) (Finset.mem_univ i)).symm
  have hvi : variance (X i) μ ≤ 1 := by
    have hnonneg : 0 ≤ ∑ j ∈ Finset.univ.erase i, variance (X j) μ :=
      Finset.sum_nonneg fun j hj ↦ variance_nonneg _ _
    linarith [hdecomp, hvar]
  have hsq : ∫ ω, (X i ω) ^ 2 ∂μ ≤ 1 := by
    rw [← variance_eq_integral_sq (hX_mem i) (hX_mean i)]
    exact hvi
  calc
    ∫ ω, |X i ω| ∂μ ≤ √(∫ ω, (X i ω) ^ 2 ∂μ) :=
      integral_abs_le_sqrt_integral_sq (hX_mem i)
    _ ≤ √1 := sqrt_le_sqrt hsq
    _ = 1 := sqrt_one

lemma integral_upperTruncatedKernelMassSum_ge_half {X : I → Ω → ℝ}
    (hX_meas : ∀ j, Measurable (X j)) (hX_mem : ∀ j, MemLp (X j) 2 μ)
    (hX_mean : ∀ j, ∫ ω, X j ω ∂μ = 0) (hvar : ∑ j, variance (X j) μ = 1)
    (h3 : ∀ j, Integrable (fun ω ↦ |X j ω| ^ 3) μ)
    (hγpos : 0 < thirdMomentSum X μ) (hγsmall : thirdMomentSum X μ ≤ 1 / 8) (i : I) :
    (1 : ℝ) / 2 ≤ ∫ ω, upperTruncatedKernelMassSum (thirdMomentSum X μ) X i ω ∂μ := by
  let γ := thirdMomentSum X μ
  have hγ : 0 ≤ γ := hγpos.le
  have hfull := integral_kernelMassSum_ge hX_mem hX_meas hX_mean hvar h3 hγpos
  have hfull34 : (3 : ℝ) / 4 ≤ ∫ ω, kernelMassSum γ X ω ∂μ := by
    convert hfull using 1
    all_goals
      field_simp [hγpos.ne']
      ring
  have hKi : ∫ ω, kernelMass γ (X i ω) ∂μ ≤ γ := by
    have hK := (memLp_kernelMass (hX_mem i) hγ (hX_meas i).aestronglyMeasurable).integrable
      (by norm_num)
    have habs := ((hX_mem i).integrable (by norm_num)).abs
    calc
      ∫ ω, kernelMass γ (X i ω) ∂μ ≤ ∫ ω, γ * |X i ω| ∂μ :=
        integral_mono hK (habs.const_mul γ) fun ω ↦ kernelMass_le_mul_abs hγ
      _ = γ * ∫ ω, |X i ω| ∂μ := integral_const_mul _ _
      _ ≤ γ * 1 := by gcongr; exact integral_abs_coordinate_le_one hX_mem hX_mean hvar i
      _ = γ := mul_one _
  have hsum_cmp :
      ∑ j ∈ Finset.univ.erase i, ∫ ω, kernelMass γ (X j ω) ∂μ ≤
        ∑ j ∈ Finset.univ.erase i,
            ∫ ω, kernelMass γ (upperTruncateOne (X j ω)) ∂μ + γ * γ := by
    calc
      ∑ j ∈ Finset.univ.erase i, ∫ ω, kernelMass γ (X j ω) ∂μ ≤
          ∑ j ∈ Finset.univ.erase i,
            (∫ ω, kernelMass γ (upperTruncateOne (X j ω)) ∂μ +
              γ * ∫ ω, |X j ω| ^ 3 ∂μ) :=
        Finset.sum_le_sum fun j hj ↦
          integral_kernelMass_le_upperTruncateOne_add_cube (hX_meas j) (hX_mem j) (h3 j) hγ
      _ = (∑ j ∈ Finset.univ.erase i,
            ∫ ω, kernelMass γ (upperTruncateOne (X j ω)) ∂μ) +
          γ * ∑ j ∈ Finset.univ.erase i, ∫ ω, |X j ω| ^ 3 ∂μ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (∑ j ∈ Finset.univ.erase i,
            ∫ ω, kernelMass γ (upperTruncateOne (X j ω)) ∂μ) + γ * γ := by
        gcongr
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun j hj hnot ↦ integral_nonneg fun ω ↦ pow_nonneg (abs_nonneg _) _
  have hfull_split : ∫ ω, kernelMassSum γ X ω ∂μ =
      (∑ j ∈ Finset.univ.erase i, ∫ ω, kernelMass γ (X j ω) ∂μ) +
        ∫ ω, kernelMass γ (X i ω) ∂μ := by
    rw [show ∫ ω, kernelMassSum γ X ω ∂μ =
        ∑ j : I, ∫ ω, kernelMass γ (X j ω) ∂μ by
      rw [show kernelMassSum γ X = ∑ j : I, fun ω ↦ kernelMass γ (X j ω) by
        ext ω; simp [kernelMassSum, Finset.sum_apply]]
      simpa only [Finset.sum_apply] using
        (integral_finsetSum (μ := μ) (s := Finset.univ)
          (f := fun j ω ↦ kernelMass γ (X j ω)) fun j hj ↦
            (memLp_kernelMass (hX_mem j) hγ
              (hX_meas j).aestronglyMeasurable).integrable (by norm_num))]
    exact (Finset.sum_erase_add
      (s := Finset.univ) (f := fun j ↦ ∫ ω, kernelMass γ (X j ω) ∂μ)
      (Finset.mem_univ i)).symm
  have hS_int : ∫ ω, upperTruncatedKernelMassSum γ X i ω ∂μ =
      ∑ j ∈ Finset.univ.erase i,
        ∫ ω, kernelMass γ (upperTruncateOne (X j ω)) ∂μ := by
    rw [show upperTruncatedKernelMassSum γ X i =
        ∑ j ∈ Finset.univ.erase i,
          fun ω ↦ kernelMass γ (upperTruncateOne (X j ω)) by
      ext ω; simp [upperTruncatedKernelMassSum, Finset.sum_apply]]
    simpa only [Finset.sum_apply] using
      (integral_finsetSum (μ := μ) (s := Finset.univ.erase i)
        (f := fun j ω ↦ kernelMass γ (upperTruncateOne (X j ω))) fun j hj ↦
          (memLp_kernelMass (memLp_upperTruncateOne_comp (hX_meas j) (hX_mem j)) hγ
            (measurable_upperTruncateOne_comp
              (hX_meas j)).aestronglyMeasurable).integrable (by norm_num))
  have hcompare : ∫ ω, kernelMassSum γ X ω ∂μ ≤
      ∫ ω, upperTruncatedKernelMassSum γ X i ω ∂μ + γ * γ + γ := by
    rw [hfull_split, hS_int]
    linarith [hsum_cmp, hKi]
  have hγsq : γ * γ ≤ 1 / 64 := by nlinarith [hγsmall]
  have hγle : γ ≤ 1 / 8 := hγsmall
  linarith [hfull34, hcompare]

/-- Fixed-parameter Bennett bound for the one-sided truncated leave-one-out sum. -/
lemma mgf_upperTruncated_leaveOneOut_le_half {X : I → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i)) (h_indep : iIndepFun X μ)
    (hX_mem : ∀ i, MemLp (X i) 2 μ) (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1) (i : I) :
    mgf (∑ j ∈ Finset.univ.erase i, upperTruncateOne ∘ X j) μ (1 / 2) ≤
      Real.exp (Real.exp (1 / 2) - 3 / 2) := by
  let Y : I → Ω → ℝ := fun j ↦ upperTruncateOne ∘ X j
  have hY_meas : ∀ j, Measurable (Y j) := fun j ↦
    measurable_upperTruncateOne_comp (hX_meas j)
  have hY_indep : iIndepFun Y μ := iIndepFun_upperTruncateOne_comp h_indep
  have hY_mem : ∀ j, MemLp (Y j) 2 μ := fun j ↦
    memLp_upperTruncateOne_comp (hX_meas j) (hX_mem j)
  have hY_mean : ∀ j, ∫ ω, Y j ω ∂μ ≤ 0 := fun j ↦
    integral_upperTruncateOne_comp_nonpos (hX_meas j) (hX_mem j) (hX_mean j)
  have hY_le : ∀ j, ∀ᵐ ω ∂μ, Y j ω ≤ 1 := fun j ↦
    ae_of_all μ fun ω ↦ upperTruncateOne_le_one (X j ω)
  have hsecond : ∑ j ∈ Finset.univ.erase i, ∫ ω, (Y j ω) ^ 2 ∂μ ≤ 1 := by
    simpa [Y, Function.comp_apply] using
      sum_integral_sq_upperTruncateOne_erase_le_one hX_meas hX_mem hX_mean hvar i
  simpa only [Y] using mgf_finsetSum_le_half (Finset.univ.erase i) hY_meas hY_indep
    hY_mem hY_mean hY_le hsecond

/-- Preliminary exponential interval bound for the one-sided truncated leave-one-out sum. -/
lemma measure_upperTruncated_leaveOneOut_mem_Icc_le_half {X : I → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i)) (h_indep : iIndepFun X μ)
    (hX_mem : ∀ i, MemLp (X i) 2 μ) (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∑ i, variance (X i) μ = 1) (i : I) {a b : ℝ} :
    μ.real {ω | ∑ j ∈ Finset.univ.erase i, upperTruncateOne (X j ω) ∈ Icc a b} ≤
      Real.exp (-a / 2 + Real.exp (1 / 2) - 3 / 2) := by
  let Y : I → Ω → ℝ := fun j ↦ upperTruncateOne ∘ X j
  have hY_meas : ∀ j, Measurable (Y j) := fun j ↦
    measurable_upperTruncateOne_comp (hX_meas j)
  have hY_indep : iIndepFun Y μ := iIndepFun_upperTruncateOne_comp h_indep
  have hY_mem : ∀ j, MemLp (Y j) 2 μ := fun j ↦
    memLp_upperTruncateOne_comp (hX_meas j) (hX_mem j)
  have hY_mean : ∀ j, ∫ ω, Y j ω ∂μ ≤ 0 := fun j ↦
    integral_upperTruncateOne_comp_nonpos (hX_meas j) (hX_mem j) (hX_mean j)
  have hY_le : ∀ j, ∀ᵐ ω ∂μ, Y j ω ≤ 1 := fun j ↦
    ae_of_all μ fun ω ↦ upperTruncateOne_le_one (X j ω)
  have hsecond : ∑ j ∈ Finset.univ.erase i, ∫ ω, (Y j ω) ^ 2 ∂μ ≤ 1 := by
    simpa [Y, Function.comp_apply] using
      sum_integral_sq_upperTruncateOne_erase_le_one hX_meas hX_mem hX_mean hvar i
  simpa [Y, Function.comp_apply] using
    measure_finsetSum_mem_Icc_le_half (Finset.univ.erase i) hY_meas hY_indep hY_mem
      hY_mean hY_le hsecond (a := a) (b := b)

/-! ### Weighted interval and corrected exchange estimates -/

/-- The exponentially weighted indicator of `W ∈ [a,b]`. -/
def exponentialIntervalWeight (a b : ℝ) (W : Ω → ℝ) : Ω → ℝ :=
  fun ω ↦ if W ω ∈ Icc a b then Real.exp (W ω / 2) else 0

lemma measurable_exponentialIntervalWeight {W : Ω → ℝ} (hW : Measurable W) (a b : ℝ) :
    Measurable (exponentialIntervalWeight a b W) := by
  exact Measurable.ite
    ((measurableSet_Icc.preimage hW)) ((hW.div_const 2).exp) measurable_const

omit [MeasurableSpace Ω] in
lemma exponentialIntervalWeight_nonneg (a b : ℝ) (W : Ω → ℝ) (ω : Ω) :
    0 ≤ exponentialIntervalWeight a b W ω := by
  simp only [exponentialIntervalWeight]
  split_ifs <;> positivity

omit [MeasurableSpace Ω] in
lemma exponentialIntervalWeight_le_exp (a b : ℝ) (W : Ω → ℝ) (ω : Ω) :
    exponentialIntervalWeight a b W ω ≤ Real.exp (W ω / 2) := by
  simp only [exponentialIntervalWeight]
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos (W ω / 2)).le

omit [MeasurableSpace Ω] in
lemma sq_exponentialIntervalWeight_le_exp (a b : ℝ) (W : Ω → ℝ) (ω : Ω) :
    exponentialIntervalWeight a b W ω ^ 2 ≤ Real.exp (W ω) := by
  simp only [exponentialIntervalWeight]
  split_ifs with h
  · rw [pow_two, ← Real.exp_add]
    apply le_of_eq
    congr 1
    ring
  · simpa using (Real.exp_pos (W ω)).le

omit [IsProbabilityMeasure μ] in
lemma memLp_exponentialIntervalWeight {W : Ω → ℝ} (hW : Measurable W)
    (hG : MemLp (fun ω ↦ Real.exp (W ω / 2)) 2 μ) (a b : ℝ) :
    MemLp (exponentialIntervalWeight a b W) 2 μ := by
  refine hG.mono (measurable_exponentialIntervalWeight hW a b).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (exponentialIntervalWeight_nonneg a b W ω),
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exponentialIntervalWeight_le_exp a b W ω

lemma exp_mul_measureReal_mem_Icc_le_integral_exponentialIntervalWeight
    {W : Ω → ℝ} (hW : Measurable W) (hG : MemLp (fun ω ↦ Real.exp (W ω / 2)) 2 μ)
    {a b : ℝ} :
    Real.exp (a / 2) * μ.real {ω | W ω ∈ Icc a b} ≤
      ∫ ω, exponentialIntervalWeight a b W ω ∂μ := by
  let A : Set Ω := {ω | W ω ∈ Icc a b}
  have hA : MeasurableSet A := measurableSet_Icc.preimage hW
  have hH_int := (memLp_exponentialIntervalWeight hW hG a b).integrable (by norm_num)
  have hconst_int : Integrable (A.indicator fun _ ↦ Real.exp (a / 2)) μ :=
    (integrable_const (Real.exp (a / 2))).indicator hA
  have hmono : ∫ ω, A.indicator (fun _ ↦ Real.exp (a / 2)) ω ∂μ ≤
      ∫ ω, exponentialIntervalWeight a b W ω ∂μ := by
    refine integral_mono hconst_int hH_int fun ω ↦ ?_
    by_cases hω : ω ∈ A
    · rw [indicator_of_mem hω]
      have hω' : W ω ∈ Icc a b := hω
      have haw : a ≤ W ω := hω'.1
      rw [exponentialIntervalWeight, if_pos hω']
      exact Real.exp_le_exp.mpr (by linarith)
    · rw [indicator_of_notMem hω]
      exact exponentialIntervalWeight_nonneg a b W ω
  calc
    Real.exp (a / 2) * μ.real {ω | W ω ∈ Icc a b} =
        ∫ ω, A.indicator (fun _ ↦ Real.exp (a / 2)) ω ∂μ := by
      rw [integral_indicator hA, integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
      exact mul_comm _ _
    _ ≤ ∫ ω, exponentialIntervalWeight a b W ω ∂μ := hmono

/-- Corrected exchange identity for one-sided, generally non-centered truncations.

The second term is the drift correction missing from the displayed equality in the proof of
Chen--Shao (2005), Proposition 6.1. -/
lemma integral_exponentialExchange_eq {Y : I → Ω → ℝ} (s : Finset I)
    (hY_meas : ∀ j, Measurable (Y j)) (h_indep : iIndepFun Y μ)
    (hY_mem : ∀ j, MemLp (Y j) 2 μ) (hY_le : ∀ j, ∀ᵐ ω ∂μ, Y j ω ≤ 1)
    {a b δ : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    ∫ ω, ∑ j ∈ s, Y j ω *
        (exponentialConcRamp a b δ (∑ k ∈ s, Y k ω) -
          exponentialConcRamp a b δ ((∑ k ∈ s, Y k ω) - Y j ω)) ∂μ =
      ∫ ω, (∑ j ∈ s, Y j ω) *
          exponentialConcRamp a b δ (∑ j ∈ s, Y j ω) ∂μ -
        ∑ j ∈ s, (∫ ω, Y j ω ∂μ) *
          ∫ ω, exponentialConcRamp a b δ (∑ k ∈ s.erase j, Y k ω) ∂μ := by
  let W : Ω → ℝ := fun ω ↦ ∑ j ∈ s, Y j ω
  let V : I → Ω → ℝ := fun j ω ↦ ∑ k ∈ s.erase j, Y k ω
  let f : ℝ → ℝ := exponentialConcRamp a b δ
  have hFW : MemLp (fun ω ↦ f (W ω)) 2 μ := by
    simpa only [f, W] using
      memLp_exponentialConcRamp_finsetSum s hY_meas h_indep hY_le hδ hab
  have hFV : ∀ j, MemLp (fun ω ↦ f (V j ω)) 2 μ := fun j ↦ by
    simpa only [f, V] using
      memLp_exponentialConcRamp_finsetSum (s.erase j) hY_meas h_indep hY_le hδ hab
  have hWV (j : I) (hj : j ∈ s) (ω : Ω) : W ω - Y j ω = V j ω := by
    have hsum := Finset.sum_erase_add s (fun k ↦ Y k ω) hj
    dsimp only [W, V]
    linarith
  have hYFW : ∀ j ∈ s, Integrable (fun ω ↦ Y j ω * f (W ω)) μ := by
    intro j hj
    convert (hY_mem j).integrable_mul hFW using 1
    ext ω
    rfl
  have hYFV : ∀ j ∈ s, Integrable (fun ω ↦ Y j ω * f (V j ω)) μ := by
    intro j hj
    convert (hY_mem j).integrable_mul (hFV j) using 1
    ext ω
    rfl
  have hdiff : ∀ j ∈ s, Integrable (fun ω ↦
      Y j ω * (f (W ω) - f (W ω - Y j ω))) μ := by
    intro j hj
    have hsub := (hYFW j hj).sub (hYFV j hj)
    convert hsub using 1
    ext ω
    rw [hWV j hj ω]
    simp only [Pi.sub_apply]
    ring
  have hfactor (j : I) (hj : j ∈ s) :
      ∫ ω, Y j ω * f (V j ω) ∂μ =
        (∫ ω, Y j ω ∂μ) * ∫ ω, f (V j ω) ∂μ := by
    have hV_meas : Measurable (V j) :=
      Finset.measurable_fun_sum (s.erase j) fun k hk ↦ hY_meas k
    have hInd : IndepFun (Y j) (V j) μ := by
      have h := (h_indep.indepFun_finsetSum_of_notMem hY_meas
        (Finset.notMem_erase j s)).symm
      convert h using 1
      ext ω
      simp only [V, Finset.sum_apply]
    have h := hInd.integral_fun_comp_mul_comp (f := (id : ℝ → ℝ)) (g := f)
      (hY_meas j).aemeasurable hV_meas.aemeasurable
      measurable_id.aestronglyMeasurable
      (continuous_exponentialConcRamp a b δ).aestronglyMeasurable
    simpa only [id_eq, Function.comp_apply] using h
  have hWint : ∫ ω, W ω * f (W ω) ∂μ =
      ∑ j ∈ s, ∫ ω, Y j ω * f (W ω) ∂μ := by
    rw [show (fun ω ↦ W ω * f (W ω)) =
        fun ω ↦ ∑ j ∈ s, Y j ω * f (W ω) by
      ext ω
      simp only [W, Finset.sum_mul]]
    exact integral_finsetSum s hYFW
  calc
    ∫ ω, ∑ j ∈ s, Y j ω *
        (exponentialConcRamp a b δ (∑ k ∈ s, Y k ω) -
          exponentialConcRamp a b δ ((∑ k ∈ s, Y k ω) - Y j ω)) ∂μ =
        ∫ ω, ∑ j ∈ s, Y j ω * (f (W ω) - f (W ω - Y j ω)) ∂μ := by
      rfl
    _ = ∑ j ∈ s, ∫ ω, Y j ω * (f (W ω) - f (W ω - Y j ω)) ∂μ :=
      integral_finsetSum s hdiff
    _ = ∑ j ∈ s, (∫ ω, Y j ω * f (W ω) ∂μ -
        ∫ ω, Y j ω * f (V j ω) ∂μ) := by
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      rw [show (fun ω ↦ Y j ω * (f (W ω) - f (W ω - Y j ω))) =
          fun ω ↦ Y j ω * f (W ω) - Y j ω * f (V j ω) by
        ext ω
        rw [hWV j hj ω]
        ring]
      exact integral_sub (hYFW j hj) (hYFV j hj)
    _ = (∑ j ∈ s, ∫ ω, Y j ω * f (W ω) ∂μ) -
        ∑ j ∈ s, ∫ ω, Y j ω * f (V j ω) ∂μ :=
      Finset.sum_sub_distrib _ _
    _ = ∫ ω, W ω * f (W ω) ∂μ -
        ∑ j ∈ s, (∫ ω, Y j ω ∂μ) * ∫ ω, f (V j ω) ∂μ := by
      rw [hWint]
      congr 1
      exact Finset.sum_congr rfl fun j hj ↦ hfactor j hj
    _ = ∫ ω, (∑ j ∈ s, Y j ω) *
          exponentialConcRamp a b δ (∑ j ∈ s, Y j ω) ∂μ -
        ∑ j ∈ s, (∫ ω, Y j ω ∂μ) *
          ∫ ω, exponentialConcRamp a b δ (∑ k ∈ s.erase j, Y k ω) ∂μ := by
      rfl

lemma integral_upperTruncated_exponentialExchange_le_five {X : I → Ω → ℝ}
    (hX_meas : ∀ j, Measurable (X j)) (h_indep : iIndepFun X μ)
    (hX_mem : ∀ j, MemLp (X j) 2 μ) (hX_mean : ∀ j, ∫ ω, X j ω ∂μ = 0)
    (hvar : ∑ j, variance (X j) μ = 1)
    (h3 : ∀ j, Integrable (fun ω ↦ |X j ω| ^ 3) μ)
    (i : I) {a b : ℝ} (hab : a ≤ b) (hγsmall : thirdMomentSum X μ ≤ 1 / 8) :
    ∫ ω, ∑ j ∈ Finset.univ.erase i, upperTruncateOne (X j ω) *
        (exponentialConcRamp a b (thirdMomentSum X μ)
            (∑ k ∈ Finset.univ.erase i, upperTruncateOne (X k ω)) -
          exponentialConcRamp a b (thirdMomentSum X μ)
            ((∑ k ∈ Finset.univ.erase i, upperTruncateOne (X k ω)) -
              upperTruncateOne (X j ω))) ∂μ ≤
      5 * (b - a + 2 * thirdMomentSum X μ) := by
  let γ := thirdMomentSum X μ
  let s : Finset I := Finset.univ.erase i
  let Y : I → Ω → ℝ := fun j ↦ upperTruncateOne ∘ X j
  let W : Ω → ℝ := fun ω ↦ ∑ j ∈ s, Y j ω
  let f : ℝ → ℝ := exponentialConcRamp a b γ
  let L : ℝ := b - a + 2 * γ
  have hγ0 : 0 ≤ γ := thirdMomentSum_nonneg h3
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hY_meas : ∀ j, Measurable (Y j) := fun j ↦
    measurable_upperTruncateOne_comp (hX_meas j)
  have hY_mem : ∀ j, MemLp (Y j) 2 μ := fun j ↦
    memLp_upperTruncateOne_comp (hX_meas j) (hX_mem j)
  have hY_indep : iIndepFun Y μ := iIndepFun_upperTruncateOne_comp h_indep
  have hY_mean : ∀ j, ∫ ω, Y j ω ∂μ ≤ 0 := fun j ↦
    integral_upperTruncateOne_comp_nonpos (hX_meas j) (hX_mem j) (hX_mean j)
  have hY_le : ∀ j, ∀ᵐ ω ∂μ, Y j ω ≤ 1 := fun j ↦
    ae_of_all μ fun ω ↦ upperTruncateOne_le_one (X j ω)
  have hsecond : ∑ j ∈ s, ∫ ω, (Y j ω) ^ 2 ∂μ ≤ 1 := by
    simpa only [s, Y, Function.comp_apply] using
      sum_integral_sq_upperTruncateOne_erase_le_one hX_meas hX_mem hX_mean hvar i
  have hsecond_erase (j : I) :
      ∑ k ∈ s.erase j, ∫ ω, (Y k ω) ^ 2 ∂μ ≤ 1 := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset j s)
      fun k hk hnot ↦ integral_nonneg fun ω ↦ sq_nonneg (Y k ω)).trans hsecond
  have hW_mem : MemLp W 2 μ :=
    memLp_finsetSum (s := s) fun j hj ↦ hY_mem j
  have hG : MemLp (fun ω ↦ Real.exp (W ω / 2)) 2 μ := by
    simpa only [W] using memLp_exp_half_finsetSum s hY_meas hY_indep hY_le
  have hFW : MemLp (fun ω ↦ f (W ω)) 2 μ := by
    simpa only [f, W] using
      memLp_exponentialConcRamp_finsetSum s hY_meas hY_indep hY_le hγ0 hab
  have hW2 : ∫ ω, (W ω) ^ 2 ∂μ ≤ 2 := by
    simpa only [W, s, Y, Function.comp_apply] using
      integral_sq_upperTruncated_leaveOneOut_le_two hX_meas h_indep hX_mem hX_mean hvar h3
        (by linarith : thirdMomentSum X μ ≤ 1) i
  have hmgf1 : mgf W μ 1 ≤ 3 := by
    have h := mgf_finsetSum_one_le_three s hY_meas hY_indep hY_mem hY_mean hY_le hsecond
    have hWeq : W = ∑ j ∈ s, Y j := by
      ext ω
      simp only [W, Finset.sum_apply]
    rw [hWeq]
    exact h
  have hG2 : ∫ ω, (Real.exp (W ω / 2)) ^ 2 ∂μ = mgf W μ 1 := by
    rw [mgf]
    congr 1
    ext ω
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hWG_int : Integrable (fun ω ↦ |W ω| * Real.exp (W ω / 2)) μ := by
    convert hW_mem.abs.integrable_mul hG using 1
    ext ω
    rfl
  have hWG : ∫ ω, |W ω| * Real.exp (W ω / 2) ∂μ ≤ 4 := by
    have hcs := abs_integral_mul_le_sqrt_sq hW_mem.abs hG
    change |∫ ω, |W ω| * Real.exp (W ω / 2) ∂μ| ≤
      √(∫ ω, |W ω| ^ 2 ∂μ) * √(∫ ω, Real.exp (W ω / 2) ^ 2 ∂μ) at hcs
    have hnonneg : 0 ≤ ∫ ω, |W ω| * Real.exp (W ω / 2) ∂μ :=
      integral_nonneg fun ω ↦ mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
    have hsqrtW : √(∫ ω, (|W ω|) ^ 2 ∂μ) ≤ 2 := by
      rw [show (fun ω ↦ |W ω| ^ 2) = fun ω ↦ (W ω) ^ 2 by
        ext ω; exact sq_abs (W ω)]
      exact (Real.sqrt_le_iff).2 ⟨by norm_num, by nlinarith [hW2]⟩
    have hsqrtG : √(∫ ω, (Real.exp (W ω / 2)) ^ 2 ∂μ) ≤ 2 := by
      rw [hG2]
      exact (Real.sqrt_le_iff).2 ⟨by norm_num, by nlinarith [hmgf1]⟩
    have hcs' : ∫ ω, |W ω| * Real.exp (W ω / 2) ∂μ ≤
        √(∫ ω, (|W ω|) ^ 2 ∂μ) *
          √(∫ ω, (Real.exp (W ω / 2)) ^ 2 ∂μ) := by
      simpa only [abs_of_nonneg hnonneg] using hcs
    calc
      ∫ ω, |W ω| * Real.exp (W ω / 2) ∂μ ≤
          √(∫ ω, (|W ω|) ^ 2 ∂μ) *
            √(∫ ω, (Real.exp (W ω / 2)) ^ 2 ∂μ) := hcs'
      _ ≤ 2 * 2 := mul_le_mul hsqrtW hsqrtG (Real.sqrt_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  have hWf_int : Integrable (fun ω ↦ W ω * f (W ω)) μ := by
    convert hW_mem.integrable_mul hFW using 1
    ext ω
    rfl
  have hWf : ∫ ω, W ω * f (W ω) ∂μ ≤ 4 * L := by
    have hrhs : Integrable (fun ω ↦ L * (|W ω| * Real.exp (W ω / 2))) μ :=
      hWG_int.const_mul L
    calc
      ∫ ω, W ω * f (W ω) ∂μ ≤
          ∫ ω, L * (|W ω| * Real.exp (W ω / 2)) ∂μ := by
        refine integral_mono hWf_int hrhs fun ω ↦ ?_
        have hf0 : 0 ≤ f (W ω) := exponentialConcRamp_nonneg hγ0 hab
        have hfle : f (W ω) ≤ Real.exp (W ω / 2) * L := by
          simpa only [f, L] using
            exponentialConcRamp_le (a := a) (b := b) (δ := γ) (w := W ω) hγ0 hab
        calc
          W ω * f (W ω) ≤ |W ω| * f (W ω) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hf0
          _ ≤ |W ω| * (Real.exp (W ω / 2) * L) :=
            mul_le_mul_of_nonneg_left hfle (abs_nonneg _)
          _ = L * (|W ω| * Real.exp (W ω / 2)) := by ring
      _ = L * ∫ ω, |W ω| * Real.exp (W ω / 2) ∂μ := integral_const_mul _ _
      _ ≤ L * 4 := mul_le_mul_of_nonneg_left hWG hL
      _ = 4 * L := by ring
  have hEf (j : I) : 0 ≤ ∫ ω, f (∑ k ∈ s.erase j, Y k ω) ∂μ :=
    integral_nonneg fun ω ↦ exponentialConcRamp_nonneg hγ0 hab
  have hEf_le (j : I) : ∫ ω, f (∑ k ∈ s.erase j, Y k ω) ∂μ ≤ 2 * L := by
    let V : Ω → ℝ := fun ω ↦ ∑ k ∈ s.erase j, Y k ω
    have hGV : MemLp (fun ω ↦ Real.exp (V ω / 2)) 2 μ := by
      simpa only [V] using memLp_exp_half_finsetSum (s.erase j) hY_meas hY_indep hY_le
    have hFV : MemLp (fun ω ↦ f (V ω)) 2 μ := by
      simpa only [f, V] using
        memLp_exponentialConcRamp_finsetSum (s.erase j) hY_meas hY_indep hY_le hγ0 hab
    have hmgf : mgf V μ (1 / 2) ≤ 2 := by
      have h := mgf_finsetSum_half_le_two (s.erase j) hY_meas hY_indep hY_mem hY_mean
        hY_le (hsecond_erase j)
      have hVeq : V = ∑ k ∈ s.erase j, Y k := by
        ext ω
        simp only [V, Finset.sum_apply]
      rw [hVeq]
      exact h
    have hGint : Integrable (fun ω ↦ Real.exp (V ω / 2)) μ := hGV.integrable (by norm_num)
    calc
      ∫ ω, f (V ω) ∂μ ≤ ∫ ω, Real.exp (V ω / 2) * L ∂μ := by
        refine integral_mono (hFV.integrable (by norm_num)) (hGint.mul_const L) fun ω ↦ ?_
        simpa only [f, L] using
          exponentialConcRamp_le (a := a) (b := b) (δ := γ) (w := V ω) hγ0 hab
      _ = L * ∫ ω, Real.exp (V ω / 2) ∂μ := by
        rw [integral_mul_const]
        ring
      _ = L * mgf V μ (1 / 2) := by rw [mgf]; congr 2; funext ω; ring_nf
      _ ≤ L * 2 := mul_le_mul_of_nonneg_left hmgf hL
      _ = 2 * L := by ring
  have hdrift : ∑ j ∈ s, -(∫ ω, Y j ω ∂μ) ≤ γ := by
    simpa only [s, Y, Function.comp_apply, γ] using
      sum_neg_integral_upperTruncateOne_erase_le_thirdMomentSum
        hX_meas hX_mem hX_mean h3 i
  have hcorr : -(∑ j ∈ s, (∫ ω, Y j ω ∂μ) *
      ∫ ω, f (∑ k ∈ s.erase j, Y k ω) ∂μ) ≤ L := by
    have hsum : ∑ j ∈ s, (-(∫ ω, Y j ω ∂μ)) *
        ∫ ω, f (∑ k ∈ s.erase j, Y k ω) ∂μ ≤
        ∑ j ∈ s, (-(∫ ω, Y j ω ∂μ)) * (2 * L) := by
      refine Finset.sum_le_sum fun j hj ↦ ?_
      exact mul_le_mul_of_nonneg_left (hEf_le j) (neg_nonneg.mpr (hY_mean j))
    have hsum' : -(∑ j ∈ s, (∫ ω, Y j ω ∂μ) *
        ∫ ω, f (∑ k ∈ s.erase j, Y k ω) ∂μ) ≤ 2 * L * γ := by
      calc
        -(∑ j ∈ s, (∫ ω, Y j ω ∂μ) *
            ∫ ω, f (∑ k ∈ s.erase j, Y k ω) ∂μ) =
            ∑ j ∈ s, (-(∫ ω, Y j ω ∂μ)) *
              ∫ ω, f (∑ k ∈ s.erase j, Y k ω) ∂μ := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun j hj ↦ by ring
        _ ≤ ∑ j ∈ s, (-(∫ ω, Y j ω ∂μ)) * (2 * L) := hsum
        _ = 2 * L * ∑ j ∈ s, -(∫ ω, Y j ω ∂μ) := by
          rw [← Finset.sum_mul]
          ring
        _ ≤ 2 * L * γ := mul_le_mul_of_nonneg_left hdrift (mul_nonneg (by norm_num) hL)
    have hslack : 0 ≤ L * (1 - 2 * γ) := mul_nonneg hL (by dsimp [γ]; linarith)
    nlinarith
  have hexchange := integral_exponentialExchange_eq s hY_meas hY_indep hY_mem hY_le hγ0 hab
  change (∫ ω, ∑ j ∈ s, Y j ω *
    (f (W ω) - f (W ω - Y j ω)) ∂μ) ≤ 5 * L
  rw [hexchange]
  linarith

lemma weightedKernelMass_integral_ge {X : I → Ω → ℝ}
    (hX_meas : ∀ j, Measurable (X j)) (h_indep : iIndepFun X μ)
    (hX_mem : ∀ j, MemLp (X j) 2 μ) (hX_mean : ∀ j, ∫ ω, X j ω ∂μ = 0)
    (hvar : ∑ j, variance (X j) μ = 1)
    (h3 : ∀ j, Integrable (fun ω ↦ |X j ω| ^ 3) μ)
    (i : I) {a b : ℝ} (hγsmall : thirdMomentSum X μ ≤ 1 / 8) :
    Real.exp (a / 2) *
          μ.real {ω | ∑ j ∈ Finset.univ.erase i, upperTruncateOne (X j ω) ∈ Icc a b} / 2 -
        2 * thirdMomentSum X μ ≤
      ∫ ω, exponentialIntervalWeight a b
          (fun ω ↦ ∑ j ∈ Finset.univ.erase i, upperTruncateOne (X j ω)) ω *
        upperTruncatedKernelMassSum (thirdMomentSum X μ) X i ω ∂μ := by
  let γ := thirdMomentSum X μ
  let s : Finset I := Finset.univ.erase i
  let Y : I → Ω → ℝ := fun j ↦ upperTruncateOne ∘ X j
  let W : Ω → ℝ := fun ω ↦ ∑ j ∈ s, Y j ω
  let S : Ω → ℝ := upperTruncatedKernelMassSum γ X i
  let H : Ω → ℝ := exponentialIntervalWeight a b W
  have hγ0 : 0 ≤ γ := thirdMomentSum_nonneg h3
  have hγpos : 0 < γ := thirdMomentSum_pos_of_variance_sum_eq_one hX_mem hX_mean hvar h3
  have hY_meas : ∀ j, Measurable (Y j) := fun j ↦
    measurable_upperTruncateOne_comp (hX_meas j)
  have hY_mem : ∀ j, MemLp (Y j) 2 μ := fun j ↦
    memLp_upperTruncateOne_comp (hX_meas j) (hX_mem j)
  have hY_indep : iIndepFun Y μ := iIndepFun_upperTruncateOne_comp h_indep
  have hY_mean : ∀ j, ∫ ω, Y j ω ∂μ ≤ 0 := fun j ↦
    integral_upperTruncateOne_comp_nonpos (hX_meas j) (hX_mem j) (hX_mean j)
  have hY_le : ∀ j, ∀ᵐ ω ∂μ, Y j ω ≤ 1 := fun j ↦
    ae_of_all μ fun ω ↦ upperTruncateOne_le_one (X j ω)
  have hsecond : ∑ j ∈ s, ∫ ω, (Y j ω) ^ 2 ∂μ ≤ 1 := by
    simpa only [s, Y, Function.comp_apply] using
      sum_integral_sq_upperTruncateOne_erase_le_one hX_meas hX_mem hX_mean hvar i
  have hW_meas : Measurable W := Finset.measurable_fun_sum s fun j hj ↦ hY_meas j
  have hG : MemLp (fun ω ↦ Real.exp (W ω / 2)) 2 μ := by
    simpa only [W] using memLp_exp_half_finsetSum s hY_meas hY_indep hY_le
  have hH_meas : Measurable H := measurable_exponentialIntervalWeight hW_meas a b
  have hH_mem : MemLp H 2 μ := memLp_exponentialIntervalWeight hW_meas hG a b
  have hS_meas : Measurable S := by
    simpa only [S, γ] using measurable_upperTruncatedKernelMassSum hX_meas γ i
  have hS_mem : MemLp S 2 μ := by
    simpa only [S] using memLp_upperTruncatedKernelMassSum hX_meas hX_mem hγ0 i
  have hvarS : variance S μ ≤ γ ^ 2 := by
    simpa only [S] using
      variance_upperTruncatedKernelMassSum_le hX_meas h_indep hX_mem hγ0 i hsecond
  have hES : (1 : ℝ) / 2 ≤ ∫ ω, S ω ∂μ := by
    simpa only [S, γ] using integral_upperTruncatedKernelMassSum_ge_half hX_meas hX_mem
      hX_mean hvar h3 hγpos hγsmall i
  have hmgf1 : mgf W μ 1 ≤ 3 := by
    have h := mgf_finsetSum_one_le_three s hY_meas hY_indep hY_mem hY_mean hY_le hsecond
    have hWeq : W = ∑ j ∈ s, Y j := by
      ext ω
      simp only [W, Finset.sum_apply]
    rw [hWeq]
    exact h
  have hExpW_int : Integrable (fun ω ↦ Real.exp (W ω)) μ := by
    have hG2 := hG.integrable_sq
    convert hG2 using 1
    ext ω
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hEH2 : ∫ ω, (H ω) ^ 2 ∂μ ≤ ∫ ω, Real.exp (W ω) ∂μ := by
    exact integral_mono hH_mem.integrable_sq hExpW_int fun ω ↦
      sq_exponentialIntervalWeight_le_exp a b W ω
  have hExpW_eq : ∫ ω, Real.exp (W ω) ∂μ = mgf W μ 1 := by
    rw [mgf]
    congr 1
    ext ω
    congr 1
    ring
  have hvarH : variance H μ ≤ 3 := by
    calc
      variance H μ ≤ ∫ ω, (H ω) ^ 2 ∂μ :=
        variance_le_expectation_sq hH_meas.aestronglyMeasurable
      _ ≤ ∫ ω, Real.exp (W ω) ∂μ := hEH2
      _ = mgf W μ 1 := hExpW_eq
      _ ≤ 3 := hmgf1
  have hcov : |covariance H S μ| ≤ 2 * γ := by
    have hbase := abs_covariance_le_sqrt_variance hH_mem hS_mem
    have hprod : variance H μ * variance S μ ≤ (2 * γ) ^ 2 := by
      calc
        variance H μ * variance S μ ≤ 3 * γ ^ 2 := by
          exact mul_le_mul hvarH hvarS (variance_nonneg _ _) (by norm_num)
        _ ≤ (2 * γ) ^ 2 := by nlinarith [sq_nonneg γ]
    have hsqrt : √(variance H μ * variance S μ) ≤ 2 * γ :=
      (Real.sqrt_le_iff).2 ⟨mul_nonneg (by norm_num) hγ0, hprod⟩
    exact hbase.trans hsqrt
  have hcovdef := covariance_eq_sub hH_mem hS_mem
  change covariance H S μ =
    (∫ ω, H ω * S ω ∂μ) - (∫ ω, H ω ∂μ) * ∫ ω, S ω ∂μ at hcovdef
  have hHS : (∫ ω, H ω ∂μ) * (∫ ω, S ω ∂μ) - 2 * γ ≤
      ∫ ω, H ω * S ω ∂μ := by
    have hcovlower : -(2 * γ) ≤ covariance H S μ := (neg_le_of_abs_le hcov)
    linarith
  have hEH : Real.exp (a / 2) * μ.real {ω | W ω ∈ Icc a b} ≤
      ∫ ω, H ω ∂μ := by
    simpa only [H] using
      exp_mul_measureReal_mem_Icc_le_integral_exponentialIntervalWeight hW_meas hG
  have hEH0 : 0 ≤ ∫ ω, H ω ∂μ :=
    integral_nonneg fun ω ↦ exponentialIntervalWeight_nonneg a b W ω
  have hA0 : 0 ≤ Real.exp (a / 2) * μ.real {ω | W ω ∈ Icc a b} :=
    mul_nonneg (Real.exp_pos _).le (measureReal_nonneg)
  have hprodmean :
      Real.exp (a / 2) * μ.real {ω | W ω ∈ Icc a b} / 2 ≤
        (∫ ω, H ω ∂μ) * ∫ ω, S ω ∂μ := by
    calc
      Real.exp (a / 2) * μ.real {ω | W ω ∈ Icc a b} / 2 =
          (Real.exp (a / 2) * μ.real {ω | W ω ∈ Icc a b}) * ((1 : ℝ) / 2) := by ring
      _ ≤ (∫ ω, H ω ∂μ) * ∫ ω, S ω ∂μ :=
        mul_le_mul hEH hES (by norm_num) hEH0
  change Real.exp (a / 2) * μ.real {ω | W ω ∈ Icc a b} / 2 - 2 * γ ≤
    ∫ ω, H ω * S ω ∂μ
  calc
    Real.exp (a / 2) * μ.real {ω | W ω ∈ Icc a b} / 2 - 2 * γ ≤
        (∫ ω, H ω ∂μ) * (∫ ω, S ω ∂μ) - 2 * γ :=
      sub_le_sub_right hprodmean _
    _ ≤ ∫ ω, H ω * S ω ∂μ := hHS

lemma weightedKernelMass_integral_le_exchange {X : I → Ω → ℝ}
    (hX_meas : ∀ j, Measurable (X j)) (h_indep : iIndepFun X μ)
    (hX_mem : ∀ j, MemLp (X j) 2 μ) (i : I)
    {a b δ : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) :
    ∫ ω, exponentialIntervalWeight a b
          (fun ω ↦ ∑ j ∈ Finset.univ.erase i, upperTruncateOne (X j ω)) ω *
        upperTruncatedKernelMassSum δ X i ω ∂μ ≤
      Real.exp (1 / 2) *
        ∫ ω, ∑ j ∈ Finset.univ.erase i, upperTruncateOne (X j ω) *
          (exponentialConcRamp a b δ
              (∑ k ∈ Finset.univ.erase i, upperTruncateOne (X k ω)) -
            exponentialConcRamp a b δ
              ((∑ k ∈ Finset.univ.erase i, upperTruncateOne (X k ω)) -
                upperTruncateOne (X j ω))) ∂μ := by
  let s : Finset I := Finset.univ.erase i
  let Y : I → Ω → ℝ := fun j ↦ upperTruncateOne ∘ X j
  let W : Ω → ℝ := fun ω ↦ ∑ j ∈ s, Y j ω
  let S : Ω → ℝ := upperTruncatedKernelMassSum δ X i
  let H : Ω → ℝ := exponentialIntervalWeight a b W
  let f : ℝ → ℝ := exponentialConcRamp a b δ
  let Q : Ω → ℝ := fun ω ↦ ∑ j ∈ s, Y j ω * (f (W ω) - f (W ω - Y j ω))
  have hY_meas : ∀ j, Measurable (Y j) := fun j ↦
    measurable_upperTruncateOne_comp (hX_meas j)
  have hY_mem : ∀ j, MemLp (Y j) 2 μ := fun j ↦
    memLp_upperTruncateOne_comp (hX_meas j) (hX_mem j)
  have hY_indep : iIndepFun Y μ := iIndepFun_upperTruncateOne_comp h_indep
  have hY_le : ∀ j, ∀ᵐ ω ∂μ, Y j ω ≤ 1 := fun j ↦
    ae_of_all μ fun ω ↦ upperTruncateOne_le_one (X j ω)
  have hW_meas : Measurable W := Finset.measurable_fun_sum s fun j hj ↦ hY_meas j
  have hG : MemLp (fun ω ↦ Real.exp (W ω / 2)) 2 μ := by
    simpa only [W] using memLp_exp_half_finsetSum s hY_meas hY_indep hY_le
  have hH_mem : MemLp H 2 μ := memLp_exponentialIntervalWeight hW_meas hG a b
  have hS_mem : MemLp S 2 μ := by
    simpa only [S] using memLp_upperTruncatedKernelMassSum hX_meas hX_mem hδ i
  have hFW : MemLp (fun ω ↦ f (W ω)) 2 μ := by
    simpa only [f, W] using
      memLp_exponentialConcRamp_finsetSum s hY_meas hY_indep hY_le hδ hab
  have hFV : ∀ j, MemLp (fun ω ↦ f (∑ k ∈ s.erase j, Y k ω)) 2 μ := fun j ↦ by
    simpa only [f] using
      memLp_exponentialConcRamp_finsetSum (s.erase j) hY_meas hY_indep hY_le hδ hab
  have hWV (j : I) (hj : j ∈ s) (ω : Ω) :
      W ω - Y j ω = ∑ k ∈ s.erase j, Y k ω := by
    have hsum := Finset.sum_erase_add s (fun k ↦ Y k ω) hj
    dsimp only [W]
    linarith
  have hQterm : ∀ j ∈ s, Integrable (fun ω ↦
      Y j ω * (f (W ω) - f (W ω - Y j ω))) μ := by
    intro j hj
    have hdiff : MemLp (fun ω ↦ f (W ω) - f (∑ k ∈ s.erase j, Y k ω)) 2 μ :=
      hFW.sub (hFV j)
    have hprod := (hY_mem j).integrable_mul hdiff
    convert hprod using 1
    ext ω
    rw [hWV j hj ω]
    rfl
  have hQint : Integrable Q μ := by
    exact integrable_finsetSum (s := s) hQterm
  have hHSint : Integrable (fun ω ↦ H ω * S ω) μ := by
    convert hH_mem.integrable_mul hS_mem using 1
    ext ω
    rfl
  have hpoint (ω : Ω) : H ω * S ω ≤ Real.exp (1 / 2) * Q ω := by
    by_cases hw : W ω ∈ Icc a b
    · have hsum : Real.exp ((W ω - 1) / 2) * S ω ≤ Q ω := by
        calc
          Real.exp ((W ω - 1) / 2) * S ω =
              ∑ j ∈ s, Real.exp ((W ω - 1) / 2) * kernelMass δ (Y j ω) := by
            simp only [S, upperTruncatedKernelMassSum, s, Y, Function.comp_apply,
              Finset.mul_sum]
          _ ≤ ∑ j ∈ s, Y j ω * (f (W ω) - f (W ω - Y j ω)) := by
            exact Finset.sum_le_sum fun j hj ↦ by
              simpa only [f, Y, Function.comp_apply] using exponentialConcRamp_exchange_ge hδ hab hw
                (upperTruncateOne_le_one (X j ω))
          _ = Q ω := rfl
      have hmul := mul_le_mul_of_nonneg_left hsum (Real.exp_pos (1 / 2)).le
      calc
        H ω * S ω = Real.exp (1 / 2) *
            (Real.exp ((W ω - 1) / 2) * S ω) := by
          rw [show H ω = Real.exp (W ω / 2) by
            simp only [H, exponentialIntervalWeight, if_pos hw]]
          rw [← mul_assoc, ← Real.exp_add]
          congr 1
          ring_nf
        _ ≤ Real.exp (1 / 2) * Q ω := hmul
    · have hQ0 : 0 ≤ Q ω := by
        exact Finset.sum_nonneg fun j hj ↦
          exponentialConcRamp_exchange_nonneg hδ hab
      rw [show H ω = 0 by simp only [H, exponentialIntervalWeight, if_neg hw], zero_mul]
      exact mul_nonneg (Real.exp_pos _).le hQ0
  change ∫ ω, H ω * S ω ∂μ ≤ Real.exp (1 / 2) * ∫ ω, Q ω ∂μ
  calc
    ∫ ω, H ω * S ω ∂μ ≤ ∫ ω, Real.exp (1 / 2) * Q ω ∂μ :=
      integral_mono hHSint (hQint.const_mul _) hpoint
    _ = Real.exp (1 / 2) * ∫ ω, Q ω ∂μ := integral_const_mul _ _

/-- Chen--Shao (2005), Proposition 6.1, with a corrected truncation-drift term and relaxed
absolute constants.

The paper states constants `5` and `7`.  The proof below retains the same exponentially weighted
shape while exposing the drift omitted by the displayed exchange equality in the paper. -/
theorem chenShao_exponentialConcentration_upperTruncated {X : I → Ω → ℝ}
    (hX_meas : ∀ j, Measurable (X j)) (h_indep : iIndepFun X μ)
    (hX_mem : ∀ j, MemLp (X j) 2 μ) (hX_mean : ∀ j, ∫ ω, X j ω ∂μ = 0)
    (hvar : ∑ j, variance (X j) μ = 1)
    (h3 : ∀ j, Integrable (fun ω ↦ |X j ω| ^ 3) μ)
    (i : I) {a b : ℝ} (hab : a ≤ b) :
    μ.real {ω | ∑ j ∈ Finset.univ.erase i, upperTruncateOne (X j ω) ∈ Icc a b} ≤
      Real.exp (-a / 2) *
        (24 * (b - a) + 48 * thirdMomentSum X μ) := by
  let γ := thirdMomentSum X μ
  let W : Ω → ℝ :=
    fun ω ↦ ∑ j ∈ Finset.univ.erase i, upperTruncateOne (X j ω)
  let S : Ω → ℝ := upperTruncatedKernelMassSum γ X i
  let H : Ω → ℝ := exponentialIntervalWeight a b W
  let Q : ℝ := ∫ ω, ∑ j ∈ Finset.univ.erase i, upperTruncateOne (X j ω) *
    (exponentialConcRamp a b γ (W ω) -
      exponentialConcRamp a b γ (W ω - upperTruncateOne (X j ω))) ∂μ
  let P : ℝ := μ.real {ω | W ω ∈ Icc a b}
  let L : ℝ := b - a + 2 * γ
  have hγ0 : 0 ≤ γ := thirdMomentSum_nonneg h3
  have hwidth : 0 ≤ b - a := sub_nonneg.mpr hab
  have hL : 0 ≤ L := by dsimp [L]; linarith
  by_cases hγsmall : γ ≤ 1 / 8
  · have hlower : Real.exp (a / 2) * P / 2 - 2 * γ ≤
        ∫ ω, H ω * S ω ∂μ := by
      simpa only [P, H, S, W, γ] using
        weightedKernelMass_integral_ge hX_meas h_indep hX_mem hX_mean hvar h3 i hγsmall
    have hmiddle : ∫ ω, H ω * S ω ∂μ ≤ Real.exp (1 / 2) * Q := by
      simpa only [H, S, Q, W, γ] using
        weightedKernelMass_integral_le_exchange hX_meas h_indep hX_mem i hγ0 hab
    have hupper : Q ≤ 5 * L := by
      simpa only [Q, W, L, γ] using
        integral_upperTruncated_exponentialExchange_le_five hX_meas h_indep hX_mem
          hX_mean hvar h3 i hab hγsmall
    have hexphalf : Real.exp (1 / 2) ≤ 2 := exp_half_le_two
    have hQ0 : 0 ≤ Q := by
      have hpoint : ∀ ω, 0 ≤ ∑ j ∈ Finset.univ.erase i, upperTruncateOne (X j ω) *
          (exponentialConcRamp a b γ (W ω) -
            exponentialConcRamp a b γ (W ω - upperTruncateOne (X j ω))) := by
        intro ω
        exact Finset.sum_nonneg fun j hj ↦ exponentialConcRamp_exchange_nonneg hγ0 hab
      exact integral_nonneg hpoint
    have hweighted : Real.exp (1 / 2) * Q ≤ 10 * L := by
      calc
        Real.exp (1 / 2) * Q ≤ 2 * Q := mul_le_mul_of_nonneg_right hexphalf hQ0
        _ ≤ 2 * (5 * L) := mul_le_mul_of_nonneg_left hupper (by norm_num)
        _ = 10 * L := by ring
    have hA : Real.exp (a / 2) * P ≤ 20 * L + 4 * γ := by
      linarith [hlower, hmiddle, hweighted]
    have hP : P ≤ Real.exp (-a / 2) * (20 * L + 4 * γ) := by
      have hmul := mul_le_mul_of_nonneg_left hA (Real.exp_pos (-a / 2)).le
      calc
        P = Real.exp (-a / 2) * (Real.exp (a / 2) * P) := by
          rw [← mul_assoc, ← Real.exp_add, show -a / 2 + a / 2 = 0 by ring,
            Real.exp_zero, one_mul]
        _ ≤ Real.exp (-a / 2) * (20 * L + 4 * γ) := hmul
    have hconst : 20 * L + 4 * γ ≤ 24 * (b - a) + 48 * γ := by
      dsimp [L]
      linarith
    change P ≤ Real.exp (-a / 2) * (24 * (b - a) + 48 * γ)
    exact hP.trans (mul_le_mul_of_nonneg_left hconst (Real.exp_pos _).le)
  · have hγlarge : (1 : ℝ) / 8 < γ := lt_of_not_ge hγsmall
    have hpre : P ≤ Real.exp (-a / 2 + Real.exp (1 / 2) - 3 / 2) := by
      simpa only [P, W] using
        measure_upperTruncated_leaveOneOut_mem_Icc_le_half hX_meas h_indep hX_mem
          hX_mean hvar i (a := a) (b := b)
    have hcoeff : Real.exp (Real.exp (1 / 2) - 3 / 2) ≤ 2 := by
      calc
        Real.exp (Real.exp (1 / 2) - 3 / 2) ≤ Real.exp (1 / 2) :=
          Real.exp_le_exp.mpr (by linarith [exp_half_le_two])
        _ ≤ 2 := exp_half_le_two
    have htwo : (2 : ℝ) ≤ 48 * γ := by linarith
    have hlarge : P ≤ Real.exp (-a / 2) * (48 * γ) := by
      calc
        P ≤ Real.exp (-a / 2 + Real.exp (1 / 2) - 3 / 2) := hpre
        _ = Real.exp (-a / 2) * Real.exp (Real.exp (1 / 2) - 3 / 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp (-a / 2) * 2 :=
          mul_le_mul_of_nonneg_left hcoeff (Real.exp_pos _).le
        _ ≤ Real.exp (-a / 2) * (48 * γ) :=
          mul_le_mul_of_nonneg_left htwo (Real.exp_pos _).le
    change P ≤ Real.exp (-a / 2) * (24 * (b - a) + 48 * γ)
    exact hlarge.trans (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le)

end ProbabilityTheory
