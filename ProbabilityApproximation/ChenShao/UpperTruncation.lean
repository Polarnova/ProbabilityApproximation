/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.ChenShao.ExponentialConcentration
import ProbabilityApproximation.ChenShao.ThirdMoment

/-!
# One-sided truncation of an independent family

This module packages the family `ξ̄ᵢ = ξᵢ 1_{ξᵢ ≤ 1}` used in Chen--Shao (2005), Section 6.
It records the probability and moment properties needed by the nonuniform concentration and Stein
arguments without introducing a second probability abstraction.
-/

open MeasureTheory

noncomputable section

namespace ProbabilityTheory

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The coordinatewise one-sided truncation `ξ̄ᵢ = ξᵢ 1_{ξᵢ ≤ 1}`. -/
def upperTruncatedFamily (X : ι → Ω → ℝ) : ι → Ω → ℝ :=
  fun i ↦ upperTruncateOne ∘ X i

/-- The sum of the one-sided truncated family. -/
def upperTruncatedSum (X : ι → Ω → ℝ) : Ω → ℝ :=
  sumX (upperTruncatedFamily X)

omit [Fintype ι] in
lemma measurable_upperTruncatedFamily {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i)) :
    ∀ i, Measurable (upperTruncatedFamily X i) :=
  fun i ↦ measurable_upperTruncateOne_comp (hX i)

omit [Fintype ι] [IsProbabilityMeasure μ] in
lemma memLp_upperTruncatedFamily {X : ι → Ω → ℝ} (hXmeas : ∀ i, Measurable (X i))
    (hX : ∀ i, MemLp (X i) 2 μ) :
    ∀ i, MemLp (upperTruncatedFamily X i) 2 μ :=
  fun i ↦ memLp_upperTruncateOne_comp (hXmeas i) (hX i)

omit [IsProbabilityMeasure μ] in
lemma iIndepFun_upperTruncatedFamily {X : ι → Ω → ℝ} (hX_indep : iIndepFun X μ) :
    iIndepFun (upperTruncatedFamily X) μ :=
  iIndepFun_upperTruncateOne_comp hX_indep

omit [Fintype ι] in
lemma integral_upperTruncatedFamily_nonpos {X : ι → Ω → ℝ}
    (hXmeas : ∀ i, Measurable (X i)) (hX : ∀ i, MemLp (X i) 2 μ)
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    ∀ i, ∫ ω, upperTruncatedFamily X i ω ∂μ ≤ 0 :=
  fun i ↦ integral_upperTruncateOne_comp_nonpos (hXmeas i) (hX i) (hX_mean i)

omit [Fintype ι] [IsProbabilityMeasure μ] in
lemma integral_sq_upperTruncatedFamily_le {X : ι → Ω → ℝ}
    (hXmeas : ∀ i, Measurable (X i)) (hX : ∀ i, MemLp (X i) 2 μ) (i : ι) :
    ∫ ω, (upperTruncatedFamily X i ω) ^ 2 ∂μ ≤ ∫ ω, (X i ω) ^ 2 ∂μ :=
  integral_sq_upperTruncateOne_comp_le (hXmeas i) (hX i)

lemma sum_integral_sq_upperTruncatedFamily_le {X : ι → Ω → ℝ}
    (hXmeas : ∀ i, Measurable (X i)) (hX : ∀ i, MemLp (X i) 2 μ)
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hX_variance : ∑ i, variance (X i) μ = 1) :
    ∑ i, ∫ ω, (upperTruncatedFamily X i ω) ^ 2 ∂μ ≤ 1 := by
  calc
    ∑ i, ∫ ω, (upperTruncatedFamily X i ω) ^ 2 ∂μ ≤
        ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ :=
      Finset.sum_le_sum fun i _ ↦ integral_sq_upperTruncatedFamily_le hXmeas hX i
    _ = 1 := sum_integral_sq_eq_one hX hX_mean hX_variance

omit [MeasurableSpace Ω] in
lemma upperTruncatedSum_le_sumX {X : ι → Ω → ℝ} (ω : Ω) :
    upperTruncatedSum X ω ≤ sumX X ω := by
  simp only [upperTruncatedSum, sumX, upperTruncatedFamily]
  exact Finset.sum_le_sum fun i _ ↦ upperTruncateOne_le_self (X i ω)

omit [MeasurableSpace Ω] in
lemma upperTruncatedSum_eq_sumX_of_forall_le_one {X : ι → Ω → ℝ} {ω : Ω}
    (hω : ∀ i, X i ω ≤ 1) : upperTruncatedSum X ω = sumX X ω := by
  simp only [upperTruncatedSum, sumX, upperTruncatedFamily, upperTruncateOne, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [if_pos (hω i)]

omit [MeasurableSpace Ω] in
/-- The event comparison in Chen--Shao (2005), (6.13): an original upper tail is contained in the
truncated upper tail together with the exceptional events having a summand larger than one. -/
lemma upperTail_subset_upperTruncatedTail_union_largeJump {X : ι → Ω → ℝ} (z : ℝ) :
    {ω | z < sumX X ω} ⊆
      {ω | z < upperTruncatedSum X ω} ∪ ⋃ i, {ω | z < sumX X ω ∧ 1 < X i ω} := by
  classical
  intro ω hω
  change z < sumX X ω at hω
  by_cases hall : ∀ i, X i ω ≤ 1
  · left
    change z < upperTruncatedSum X ω
    rwa [upperTruncatedSum_eq_sumX_of_forall_le_one hall]
  · right
    push Not at hall
    obtain ⟨i, hi⟩ := hall
    exact Set.mem_iUnion.2 ⟨i, by simpa using And.intro hω hi⟩

omit [MeasurableSpace Ω] in
/-- A large-jump event splits into a large coordinate or a simultaneous
leave-one-out tail and coordinate tail. -/
lemma largeJump_subset_coordinateTail_union_leaveOneOut [DecidableEq ι] {X : ι → Ω → ℝ}
    (i : ι) (z : ℝ) :
    {ω | z < sumX X ω ∧ 1 < X i ω} ⊆
    {ω | z / 2 < X i ω} ∪
        ({ω | z / 2 < leaveOneOut X i ω} ∩ {ω | 1 < X i ω}) := by
  classical
  intro ω hω
  change z < sumX X ω ∧ 1 < X i ω at hω
  by_cases hi : z / 2 < X i ω
  · exact Or.inl hi
  · right
    change z / 2 < leaveOneOut X i ω ∧ 1 < X i ω
    constructor
    · have hsum := leaveOneOut_add (X := X) i ω
      have hi' : X i ω ≤ z / 2 := le_of_not_gt hi
      linarith
    · exact hω.2

private lemma one_div_half_cube_le {z : ℝ} (hz : 2 ≤ z) :
    1 / (z / 2) ^ 3 ≤ 9 / (1 + z ^ 3) := by
  have hz0 : 0 ≤ z := by linarith
  have hzsq : (4 : ℝ) ≤ z ^ 2 := by nlinarith
  have hzcube : (8 : ℝ) ≤ z ^ 3 := by
    calc
      (8 : ℝ) ≤ 4 * z := by linarith
      _ ≤ z ^ 2 * z := mul_le_mul_of_nonneg_right hzsq hz0
      _ = z ^ 3 := by ring
  rw [div_le_div_iff₀ (by positivity : 0 < (z / 2) ^ 3) (by positivity : 0 < 1 + z ^ 3)]
  nlinarith

omit [Fintype ι] in
private lemma measureReal_coordinate_upperTail_le
    {X : ι → Ω → ℝ} (hXmeas : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (i : ι) {z : ℝ} (hz : 2 ≤ z) :
    μ.real {ω | z / 2 < X i ω} ≤
      9 * (∫ ω, |X i ω| ^ 3 ∂μ) / (1 + z ^ 3) := by
  have hzhalf : 0 < z / 2 := by linarith
  have hsub : {ω | z / 2 < X i ω} ⊆ {ω | z / 2 ≤ |X i ω|} := by
    intro ω hω
    change z / 2 < X i ω at hω
    change z / 2 ≤ |X i ω|
    exact hω.le.trans (le_abs_self (X i ω))
  have hmarkov := measureReal_abs_ge_le_integral_abs_pow_three
    (μ := μ) (hXmeas i) (hX3 i) hzhalf
  have hm : 0 ≤ ∫ ω, |X i ω| ^ 3 ∂μ :=
    integral_nonneg fun _ ↦ pow_nonneg (abs_nonneg _) 3
  calc
    μ.real {ω | z / 2 < X i ω} ≤ μ.real {ω | z / 2 ≤ |X i ω|} :=
      measureReal_mono hsub
    _ ≤ (∫ ω, |X i ω| ^ 3 ∂μ) / (z / 2) ^ 3 := hmarkov
    _ = (∫ ω, |X i ω| ^ 3 ∂μ) * (1 / (z / 2) ^ 3) := by ring
    _ ≤ (∫ ω, |X i ω| ^ 3 ∂μ) * (9 / (1 + z ^ 3)) :=
      mul_le_mul_of_nonneg_left (one_div_half_cube_le hz) hm
    _ = 9 * (∫ ω, |X i ω| ^ 3 ∂μ) / (1 + z ^ 3) := by ring

omit [Fintype ι] in
private lemma measureReal_coordinate_gt_one_le
    {X : ι → Ω → ℝ} (hXmeas : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (i : ι) :
    μ.real {ω | 1 < X i ω} ≤ ∫ ω, |X i ω| ^ 3 ∂μ := by
  have hsub : {ω | 1 < X i ω} ⊆ {ω | (1 : ℝ) ≤ |X i ω|} := by
    intro ω hω
    change 1 < X i ω at hω
    change (1 : ℝ) ≤ |X i ω|
    exact hω.le.trans (le_abs_self (X i ω))
  calc
    μ.real {ω | 1 < X i ω} ≤ μ.real {ω | (1 : ℝ) ≤ |X i ω|} :=
      measureReal_mono hsub
    _ ≤ (∫ ω, |X i ω| ^ 3 ∂μ) / (1 : ℝ) ^ 3 :=
      measureReal_abs_ge_le_integral_abs_pow_three (μ := μ) (hXmeas i) (hX3 i)
        (by norm_num)
    _ = ∫ ω, |X i ω| ^ 3 ∂μ := by ring

private lemma measureReal_leaveOneOut_upperTail_le [DecidableEq ι]
    {X : ι → Ω → ℝ} (hXmeas : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (hX_indep : iIndepFun X μ)
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hX_variance : ∑ i, variance (X i) μ = 1)
    (hgamma : (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) ≤ 1)
    (i : ι) {z : ℝ} (hz : 2 ≤ z) :
    μ.real {ω | z / 2 < leaveOneOut X i ω} ≤ 36 / (1 + z ^ 3) := by
  have hX2 : ∀ j, MemLp (X j) 2 μ := fun j ↦ (hX3 j).mono_exponent (by norm_num)
  have hsumSq : ∑ j, ∫ ω, (X j ω) ^ 2 ∂μ = 1 :=
    sum_integral_sq_eq_one hX2 hX_mean hX_variance
  have hpartSq : ∑ j ∈ Finset.univ.erase i, ∫ ω, (X j ω) ^ 2 ∂μ ≤ 1 := by
    rw [← hsumSq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i Finset.univ)
      fun j _ _ ↦ integral_nonneg fun ω ↦ sq_nonneg (X j ω)
  have hpartThird :
      ∑ j ∈ Finset.univ.erase i, ∫ ω, |X j ω| ^ 3 ∂μ ≤
        ∑ j, ∫ ω, |X j ω| ^ 3 ∂μ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i Finset.univ)
      fun j _ _ ↦ integral_nonneg fun ω ↦ pow_nonneg (abs_nonneg (X j ω)) 3
  have hmomentRaw := integral_abs_finsetSum_pow_three_le hXmeas hX3 hX_indep hX_mean
    hsumSq.le (Finset.univ.erase i)
  have hmoment : ∫ ω, |leaveOneOut X i ω| ^ 3 ∂μ ≤ 4 := by
    calc
      ∫ ω, |leaveOneOut X i ω| ^ 3 ∂μ ≤
          3 * (∑ j ∈ Finset.univ.erase i, ∫ ω, (X j ω) ^ 2 ∂μ) +
            ∑ j ∈ Finset.univ.erase i, ∫ ω, |X j ω| ^ 3 ∂μ := by
        simpa only [leaveOneOut] using hmomentRaw
      _ ≤ 3 * 1 + ∑ j, ∫ ω, |X j ω| ^ 3 ∂μ :=
        add_le_add (mul_le_mul_of_nonneg_left hpartSq (by norm_num)) hpartThird
      _ ≤ 4 := by linarith
  have hloo3 : MemLp (leaveOneOut X i) 3 μ := by
    change MemLp (fun ω ↦ ∑ j ∈ Finset.univ.erase i, X j ω) 3 μ
    exact memLp_finsetSum (Finset.univ.erase i) fun j _ ↦ hX3 j
  have hzhalf : 0 < z / 2 := by linarith
  have hsub : {ω | z / 2 < leaveOneOut X i ω} ⊆
      {ω | z / 2 ≤ |leaveOneOut X i ω|} := by
    intro ω hω
    change z / 2 < leaveOneOut X i ω at hω
    change z / 2 ≤ |leaveOneOut X i ω|
    exact hω.le.trans (le_abs_self _)
  have hmarkov := measureReal_abs_ge_le_integral_abs_pow_three
    (μ := μ) (measurable_leaveOneOut hXmeas i) hloo3 hzhalf
  have hrecip_nonneg : 0 ≤ 1 / (z / 2) ^ 3 := by positivity
  calc
    μ.real {ω | z / 2 < leaveOneOut X i ω} ≤
        μ.real {ω | z / 2 ≤ |leaveOneOut X i ω|} := measureReal_mono hsub
    _ ≤ (∫ ω, |leaveOneOut X i ω| ^ 3 ∂μ) / (z / 2) ^ 3 := hmarkov
    _ = (∫ ω, |leaveOneOut X i ω| ^ 3 ∂μ) * (1 / (z / 2) ^ 3) := by ring
    _ ≤ 4 * (1 / (z / 2) ^ 3) := mul_le_mul_of_nonneg_right hmoment hrecip_nonneg
    _ ≤ 4 * (9 / (1 + z ^ 3)) :=
      mul_le_mul_of_nonneg_left (one_div_half_cube_le hz) (by norm_num)
    _ = 36 / (1 + z ^ 3) := by ring

private lemma measureReal_largeJump_le [DecidableEq ι]
    {X : ι → Ω → ℝ} (hXmeas : ∀ i, Measurable (X i))
    (hX3 : ∀ i, MemLp (X i) 3 μ) (hX_indep : iIndepFun X μ)
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hX_variance : ∑ i, variance (X i) μ = 1)
    (hgamma : (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) ≤ 1)
    (i : ι) {z : ℝ} (hz : 2 ≤ z) :
    μ.real {ω | z < sumX X ω ∧ 1 < X i ω} ≤
      45 * (∫ ω, |X i ω| ^ 3 ∂μ) / (1 + z ^ 3) := by
  let A : Set Ω := {ω | z / 2 < leaveOneOut X i ω}
  let B : Set Ω := {ω | 1 < X i ω}
  have hprodENN := IndepFun.measure_inter_preimage_eq_mul
    (indepFun_leaveOneOut (X := X) (μ := μ) hXmeas hX_indep i)
    (Set.Ioi (z / 2)) (Set.Ioi 1) measurableSet_Ioi measurableSet_Ioi
  have hApre : leaveOneOut X i ⁻¹' Set.Ioi (z / 2) = A := by
    ext ω
    simp [A]
  have hBpre : X i ⁻¹' Set.Ioi 1 = B := by
    ext ω
    simp [B]
  rw [hApre, hBpre] at hprodENN
  have hprod : μ.real (A ∩ B) = μ.real A * μ.real B := by
    change ENNReal.toReal (μ (A ∩ B)) = ENNReal.toReal (μ A) * ENNReal.toReal (μ B)
    rw [hprodENN, ENNReal.toReal_mul]
  have hA : μ.real A ≤ 36 / (1 + z ^ 3) := by
    simpa only [A] using measureReal_leaveOneOut_upperTail_le hXmeas hX3 hX_indep hX_mean
      hX_variance hgamma i hz
  have hB : μ.real B ≤ ∫ ω, |X i ω| ^ 3 ∂μ := by
    simpa only [B] using measureReal_coordinate_gt_one_le hXmeas hX3 i
  have hinter :
      μ.real (A ∩ B) ≤ 36 * (∫ ω, |X i ω| ^ 3 ∂μ) / (1 + z ^ 3) := by
    rw [hprod]
    calc
      μ.real A * μ.real B ≤
          (36 / (1 + z ^ 3)) * (∫ ω, |X i ω| ^ 3 ∂μ) := by
        exact mul_le_mul hA hB measureReal_nonneg (by positivity)
      _ = 36 * (∫ ω, |X i ω| ^ 3 ∂μ) / (1 + z ^ 3) := by ring
  have hcoordinate := measureReal_coordinate_upperTail_le hXmeas hX3 i hz
  calc
    μ.real {ω | z < sumX X ω ∧ 1 < X i ω} ≤
        μ.real ({ω | z / 2 < X i ω} ∪ (A ∩ B)) :=
      measureReal_mono (by
        simpa only [A, B] using
          largeJump_subset_coordinateTail_union_leaveOneOut (X := X) i z)
    _ ≤ μ.real {ω | z / 2 < X i ω} + μ.real (A ∩ B) :=
      measureReal_union_le _ _
    _ ≤ 9 * (∫ ω, |X i ω| ^ 3 ∂μ) / (1 + z ^ 3) +
          36 * (∫ ω, |X i ω| ^ 3 ∂μ) / (1 + z ^ 3) :=
      add_le_add hcoordinate hinter
    _ = 45 * (∫ ω, |X i ω| ^ 3 ∂μ) / (1 + z ^ 3) := by ring

/-- Chen--Shao (2005), (6.13)--(6.14), with explicit constants: when the total third moment is at
most one and `z ≥ 2`, replacing every summand by its one-sided truncation changes the upper tail by
at most `45 γ / (1 + z³)`. -/
lemma measureReal_sumX_upperTail_le_upperTruncatedTail_add
    [DecidableEq ι] {X : ι → Ω → ℝ}
    (hXmeas : ∀ i, Measurable (X i)) (hX3 : ∀ i, MemLp (X i) 3 μ)
    (hX_indep : iIndepFun X μ) (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hX_variance : ∑ i, variance (X i) μ = 1)
    (hgamma : (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) ≤ 1)
    {z : ℝ} (hz : 2 ≤ z) :
    μ.real {ω | z < sumX X ω} ≤
      μ.real {ω | z < upperTruncatedSum X ω} +
        45 * (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) / (1 + z ^ 3) := by
  classical
  let J : ι → Set Ω := fun i ↦ {ω | z < sumX X ω ∧ 1 < X i ω}
  have hJ (i : ι) :
      μ.real (J i) ≤ 45 * (∫ ω, |X i ω| ^ 3 ∂μ) / (1 + z ^ 3) := by
    simpa only [J] using
      measureReal_largeJump_le hXmeas hX3 hX_indep hX_mean hX_variance hgamma i hz
  calc
    μ.real {ω | z < sumX X ω} ≤
        μ.real ({ω | z < upperTruncatedSum X ω} ∪ ⋃ i, J i) :=
      measureReal_mono (by
        simpa only [J] using
          upperTail_subset_upperTruncatedTail_union_largeJump (X := X) z)
    _ ≤ μ.real {ω | z < upperTruncatedSum X ω} + μ.real (⋃ i, J i) :=
      measureReal_union_le _ _
    _ ≤ μ.real {ω | z < upperTruncatedSum X ω} + ∑ i, μ.real (J i) :=
      by
        gcongr
        exact measureReal_iUnion_fintype_le J
    _ ≤ μ.real {ω | z < upperTruncatedSum X ω} +
          ∑ i, 45 * (∫ ω, |X i ω| ^ 3 ∂μ) / (1 + z ^ 3) :=
      by
        gcongr with i
        exact hJ i
    _ = μ.real {ω | z < upperTruncatedSum X ω} +
          45 * (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) / (1 + z ^ 3) := by
      rw [Finset.mul_sum]
      simp only [Finset.sum_div]

/-- CDF form of the one-sided truncation comparison.  Any normal-approximation bound for the
upper-truncated sum transfers to the original sum with the explicit large-jump error. -/
lemma abs_cdf_sumX_sub_gaussian_le_upperTruncated_add
    [DecidableEq ι] {X : ι → Ω → ℝ}
    (hXmeas : ∀ i, Measurable (X i)) (hX3 : ∀ i, MemLp (X i) 3 μ)
    (hX_indep : iIndepFun X μ) (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hX_variance : ∑ i, variance (X i) μ = 1)
    (hgamma : (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) ≤ 1)
    {z : ℝ} (hz : 2 ≤ z) :
    |cdf (μ.map (sumX X)) z - cdf (gaussianReal 0 1) z| ≤
    |cdf (μ.map (upperTruncatedSum X)) z - cdf (gaussianReal 0 1) z| +
        45 * (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) / (1 + z ^ 3) := by
  have hBmeas : Measurable (upperTruncatedSum X) := by
    simpa only [upperTruncatedSum] using
      measurable_sumX (measurable_upperTruncatedFamily hXmeas)
  letI : IsProbabilityMeasure (μ.map (sumX X)) :=
    Measure.isProbabilityMeasure_map (measurable_sumX hXmeas).aemeasurable
  letI : IsProbabilityMeasure (μ.map (upperTruncatedSum X)) :=
    Measure.isProbabilityMeasure_map hBmeas.aemeasurable
  let FS := cdf (μ.map (sumX X)) z
  let FB := cdf (μ.map (upperTruncatedSum X)) z
  let Φ := cdf (gaussianReal 0 1) z
  let E := 45 * (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) / (1 + z ^ 3)
  have hFS : FS = μ.real {ω | sumX X ω ≤ z} := by
    change cdf (μ.map (sumX X)) z = μ.real {ω | sumX X ω ≤ z}
    rw [cdf_eq_real, map_measureReal_apply (measurable_sumX hXmeas) measurableSet_Iic]
    rfl
  have hFB : FB = μ.real {ω | upperTruncatedSum X ω ≤ z} := by
    change cdf (μ.map (upperTruncatedSum X)) z =
      μ.real {ω | upperTruncatedSum X ω ≤ z}
    rw [cdf_eq_real, map_measureReal_apply hBmeas measurableSet_Iic]
    rfl
  have hmeasS : MeasurableSet {ω | sumX X ω ≤ z} :=
    measurableSet_le (measurable_sumX hXmeas) measurable_const
  have hmeasB : MeasurableSet {ω | upperTruncatedSum X ω ≤ z} :=
    measurableSet_le hBmeas measurable_const
  have htailS : μ.real {ω | z < sumX X ω} = 1 - FS := by
    rw [show {ω | z < sumX X ω} = {ω | sumX X ω ≤ z}ᶜ by ext ω; simp]
    rw [probReal_compl_eq_one_sub hmeasS, hFS]
  have htailB : μ.real {ω | z < upperTruncatedSum X ω} = 1 - FB := by
    rw [show {ω | z < upperTruncatedSum X ω} =
        {ω | upperTruncatedSum X ω ≤ z}ᶜ by ext ω; simp]
    rw [probReal_compl_eq_one_sub hmeasB, hFB]
  have htail := measureReal_sumX_upperTail_le_upperTruncatedTail_add hXmeas hX3 hX_indep
    hX_mean hX_variance hgamma hz
  have hgap : FB - FS ≤ E := by
    rw [htailS, htailB] at htail
    simpa only [E] using (show FB - FS ≤
        45 * (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) / (1 + z ^ 3) by linarith)
  have hmono : FS ≤ FB := by
    rw [hFS, hFB]
    exact measureReal_mono fun ω hω ↦
      (upperTruncatedSum_le_sumX (X := X) ω).trans hω
  calc
    |cdf (μ.map (sumX X)) z - cdf (gaussianReal 0 1) z| = |FS - Φ| := by rfl
    _ = |(FB - Φ) - (FB - FS)| := by
      congr 1
      ring
    _ ≤ |FB - Φ| + |FB - FS| := abs_sub _ _
    _ = |FB - Φ| + (FB - FS) := by rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
    _ ≤ |FB - Φ| + E := by gcongr
    _ = |cdf (μ.map (upperTruncatedSum X)) z - cdf (gaussianReal 0 1) z| +
        45 * (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) / (1 + z ^ 3) := by rfl

end ProbabilityTheory
