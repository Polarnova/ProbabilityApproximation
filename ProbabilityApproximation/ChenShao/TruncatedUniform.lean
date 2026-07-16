/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.ChenShao.UniformBerryEsseen

/-!
# Truncated uniform Berry–Esseen (max form + documentation)

## Frozen SPEC target (NOT claimed under that name)

```
chenShao_uniformBerryEsseen_truncated :
  |F − Φ| ≤ (41/10) · truncMomentSum
```

Chen–Shao 2001 Theorem 2.1 achieves constant `4.1` via the truncated Stein identity (4.1)
and residuals R₁–R₄ under Proposition 3.2 (`α+β ≤ 0.14`).  The pure third-moment theorem
`uniformBerryEsseen_thirdMoment` (constant `30`) does **not** yield `41/10` on truncated
moments: `30 > 41/10`, and the truncated-moment small branch needs the refined residual
analysis of Chen–Shao §4 (not a black-box application of the third-moment BE).

## Results proved here

1. **Max form at `41/10`**:
   `|F−Φ| ≤ (41/10) · max(β, 10/41)`
   (from `|F−Φ| ≤ 1`; same constant as the frozen theorem, not pure-linear).

2. **Large pure-linear branch at weak constant `1000`**:
   if `β ≥ 1/1000` then `|F−Φ| ≤ 1000 · β`.

## Path to frozen pure-linear `41/10`

* Large branch at `41/10` already: `abs_cdf_sub_le_truncMomentSum_of_large`
  (`|F−Φ| ≤ 1 ≤ (41/10)β` when `β ≥ 10/41`).
* Small branch (`α+β ≤ 0.14` in the paper): implement Chen–Shao §4 —
  truncated kernel Stein identity (4.1), bound `|R₂+R₃+R₄| ≤ 1.9α`, and
  `|R₁| ≤ 0.5α + 4.1β` using Prop. 3.2 concentration with **truncated** moments.
* Combining residuals yields `|F−Φ| ≤ 4.1(α+β)`.
* Alternative weak pure-linear route (constant `K ≫ 41/10`): truncate at 1, center,
  renormalize variance, apply `uniformBerryEsseen_thirdMoment`, control Gaussian
  scale comparison; expected explicit `K` on the order of a few hundred.  That bound
  **must not** be declared under the frozen name `chenShao_uniformBerryEsseen_truncated`.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

noncomputable section

namespace ProbabilityTheory

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ι → Ω → ℝ}

/-! ### Max form at 41/10 -/

/-- Unconditional max-form bound at the frozen constant `41/10`.

This is **not** the pure-linear SPEC theorem.  It follows from `|F−Φ| ≤ 1` alone and
matches the constant of Chen–Shao Theorem 2.1 in max form. -/
theorem chenShao_uniformBerryEsseen_truncated_max
    (hX : ∀ i, Measurable (X i))
    (x : ℝ) :
    |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤
      (41 / 10 : ℝ) *
        max (truncMomentSum (X := X) μ) ((10 : ℝ) / 41) := by
  haveI : IsProbabilityMeasure (μ.map fun ω ↦ ∑ i, X i ω) :=
    isProbabilityMeasure_map_sumX (μ := μ) (X := X) fun i => (hX i).aemeasurable
  have h1 : |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤ 1 :=
    abs_cdf_sub_le_one _ _ x
  have h41 : (0 : ℝ) ≤ 41 / 10 := by norm_num
  have hmax : (10 : ℝ) / 41 ≤ max (truncMomentSum (X := X) μ) (10 / 41) :=
    le_max_right _ _
  have hge : (1 : ℝ) ≤ (41 / 10) * max (truncMomentSum (X := X) μ) (10 / 41) := by
    have : (41 / 10 : ℝ) * (10 / 41) = 1 := by norm_num
    calc
      (1 : ℝ) = (41 / 10) * (10 / 41) := this.symm
      _ ≤ (41 / 10) * max (truncMomentSum (X := X) μ) (10 / 41) :=
            mul_le_mul_of_nonneg_left hmax h41
  exact h1.trans hge

/-! ### Weak pure-linear constant (large branch) -/

/-- Explicit weak pure-linear constant from a truncation-style budget.
Strictly larger than the frozen Chen–Shao constant `41/10`. -/
def truncatedBerryEsseenConstant : ℝ := 1000

lemma truncatedBerryEsseenConstant_pos : 0 < truncatedBerryEsseenConstant := by
  norm_num [truncatedBerryEsseenConstant]

/-- Large-error pure-linear branch for the weak truncated constant `1000`.

If `β ≥ 1/1000` then `|F−Φ| ≤ 1000 · β`.  Together with a completed small-branch
truncation+BE argument (not yet formalized), this yields unconditional pure linear
at constant `1000`.  The frozen name / constant `41/10` remains blocked pending
Chen–Shao §4. -/
theorem chenShao_uniformBerryEsseen_truncated_weak_of_large
    (hX : ∀ i, Measurable (X i))
    (x : ℝ)
    (hlarge : (1 : ℝ) / truncatedBerryEsseenConstant ≤ truncMomentSum (X := X) μ) :
    |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤
      truncatedBerryEsseenConstant * truncMomentSum (X := X) μ := by
  haveI : IsProbabilityMeasure (μ.map fun ω ↦ ∑ i, X i ω) :=
    isProbabilityMeasure_map_sumX (μ := μ) (X := X) fun i => (hX i).aemeasurable
  have h1 : |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤ 1 :=
    abs_cdf_sub_le_one _ _ x
  have hC : (0 : ℝ) ≤ truncatedBerryEsseenConstant := truncatedBerryEsseenConstant_pos.le
  have hge : (1 : ℝ) ≤ truncatedBerryEsseenConstant * truncMomentSum (X := X) μ := by
    have : truncatedBerryEsseenConstant * (1 / truncatedBerryEsseenConstant) = 1 := by
      field_simp [truncatedBerryEsseenConstant]
    calc
      (1 : ℝ) = truncatedBerryEsseenConstant * (1 / truncatedBerryEsseenConstant) :=
        this.symm
      _ ≤ truncatedBerryEsseenConstant * truncMomentSum (X := X) μ :=
            mul_le_mul_of_nonneg_left hlarge hC
  exact h1.trans hge

/-- Re-export of the large branch at the frozen constant (already in `UniformBerryEsseen`). -/
theorem chenShao_uniformBerryEsseen_truncated_of_large
    (hX : ∀ i, Measurable (X i))
    (x : ℝ)
    (hlarge : (10 : ℝ) / 41 ≤ truncMomentSum (X := X) μ) :
    |cdf (μ.map fun ω ↦ ∑ i, X i ω) x - cdf (gaussianReal 0 1) x| ≤
      (41 / 10 : ℝ) * truncMomentSum (X := X) μ :=
  abs_cdf_sub_le_truncMomentSum_of_large hX x hlarge

end ProbabilityTheory
