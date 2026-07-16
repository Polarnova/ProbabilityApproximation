/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.Bentkus.GaussianCompanions

/-!
# Canonical probability-space transport for the Bentkus replacement argument

An independent family can be replaced by the coordinate family on the product of its marginal
laws.  Taking one further product with the canonical Gaussian-companion law supplies the original
summands and all matched Gaussian companions on a single probability space.  This realizes the
enlargement implicit in Bentkus (2004), equations (3.2)--(3.5), without imposing an atomless or
"sufficiently rich" hypothesis on the user's probability space.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace ProbabilityTheory

/-- Independence is preserved by precomposition with a measure-preserving map. -/
lemma iIndepFun_comp_measurePreserving
    {I Ω Ω' E : Type*} [Fintype I]
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : I → Ω → E} (hf : ∀ i, Measurable (f i))
    (h_indep : iIndepFun f μ) {g : Ω' → Ω}
    (hg : MeasurePreserving g ν μ) :
    iIndepFun (fun i ↦ f i ∘ g) ν := by
  have hF : Measurable (fun ω i ↦ f i ω) := measurable_pi_lambda _ hf
  have hfg : ∀ i, AEMeasurable (f i ∘ g) ν := fun i ↦
    ((hf i).comp hg.measurable).aemeasurable
  refine (iIndepFun_iff_map_fun_eq_pi_map hfg).2 ?_
  calc
    ν.map (fun ω i ↦ (f i ∘ g) ω) =
        (ν.map g).map (fun ω i ↦ f i ω) := by
          rw [Measure.map_map hF hg.measurable]
          rfl
    _ = μ.map (fun ω i ↦ f i ω) := by rw [hg.map_eq]
    _ = Measure.pi (fun i ↦ μ.map (f i)) :=
      h_indep.map_fun_eq_pi_map (fun i ↦ (hf i).aemeasurable)
    _ = Measure.pi (fun i ↦ ν.map (f i ∘ g)) := by
      congr 1
      funext i
      rw [← Measure.map_map (hf i) hg.measurable, hg.map_eq]

/-- Product of the marginal laws of a finite family. -/
def independentLawProduct {n : ℕ} {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Fin n → Ω → E) : Measure (Fin n → E) :=
  Measure.pi fun i ↦ μ.map (X i)

/-- The product of marginal laws is a probability measure when the original family is
measurable. -/
lemma isProbabilityMeasure_independentLawProduct
    {n : ℕ} {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → E} (hX : ∀ i, Measurable (X i)) :
    IsProbabilityMeasure (independentLawProduct μ X) := by
  letI (i : Fin n) : IsProbabilityMeasure (μ.map (X i)) :=
    Measure.isProbabilityMeasure_map (hX i).aemeasurable
  unfold independentLawProduct
  infer_instance

/-- The coordinate family on the product of marginal laws is independent. -/
lemma iIndepFun_independentLawProduct
    {n : ℕ} {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → E} (hX : ∀ i, Measurable (X i)) :
    iIndepFun (fun i (x : Fin n → E) ↦ x i) (independentLawProduct μ X) := by
  letI (i : Fin n) : IsProbabilityMeasure (μ.map (X i)) :=
    Measure.isProbabilityMeasure_map (hX i).aemeasurable
  unfold independentLawProduct
  exact iIndepFun_pi (X := fun _ : Fin n ↦ id) (fun _ ↦ aemeasurable_id)

/-- Each coordinate of the marginal-law product has the corresponding original marginal law. -/
lemma map_coordinate_independentLawProduct
    {n : ℕ} {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → E} (hX : ∀ i, Measurable (X i)) (i : Fin n) :
    (independentLawProduct μ X).map (fun x ↦ x i) = μ.map (X i) := by
  letI (j : Fin n) : IsProbabilityMeasure (μ.map (X j)) :=
    Measure.isProbabilityMeasure_map (hX j).aemeasurable
  unfold independentLawProduct
  exact (measurePreserving_eval (fun j ↦ μ.map (X j)) i).map_eq

/-- The joint law of an independent family is the product of its marginal laws. -/
lemma map_family_eq_independentLawProduct
    {n : ℕ} {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → E} (hX : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ) :
    μ.map (fun ω i ↦ X i ω) = independentLawProduct μ X := by
  exact h_indep.map_fun_eq_pi_map (fun i ↦ (hX i).aemeasurable)

/-- Transport of the finite sum from the user's probability space to the canonical product of
marginal laws. -/
lemma map_sum_eq_map_sum_independentLawProduct
    {n : ℕ} {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [NormedAddCommGroup E] [MeasurableAdd₂ E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → E} (hX : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ) :
    μ.map (fun ω ↦ ∑ i, X i ω) =
      (independentLawProduct μ X).map (fun x ↦ ∑ i, x i) := by
  have hF : Measurable (fun ω i ↦ X i ω) := measurable_pi_lambda _ hX
  have hsum : Measurable (fun x : Fin n → E ↦ ∑ i, x i) := by
    simpa using Finset.measurable_sum Finset.univ
      (fun i _ ↦ measurable_pi_apply i :
        ∀ i ∈ (Finset.univ : Finset (Fin n)), Measurable (fun x : Fin n → E ↦ x i))
  rw [← map_family_eq_independentLawProduct hX h_indep,
    Measure.map_map hsum hF]
  rfl

/-- Product probability space carrying both the canonical original summands and their Gaussian
companions. -/
def bentkusReplacementMeasure {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)) :
    Measure ((Fin n → EuclideanSpace ℝ (Fin d)) ×
      (Fin n → EuclideanSpace ℝ (Fin d))) :=
  (independentLawProduct μ X).prod (gaussianCompanionMeasureOf μ X)

/-- The original-coordinate family on the replacement space. -/
def replacementOriginal {n d : ℕ} (i : Fin n) :
    ((Fin n → EuclideanSpace ℝ (Fin d)) ×
      (Fin n → EuclideanSpace ℝ (Fin d))) → EuclideanSpace ℝ (Fin d) :=
  fun ω ↦ ω.1 i

/-- The Gaussian-coordinate family on the replacement space. -/
def replacementGaussian {n d : ℕ} (i : Fin n) :
    ((Fin n → EuclideanSpace ℝ (Fin d)) ×
      (Fin n → EuclideanSpace ℝ (Fin d))) → EuclideanSpace ℝ (Fin d) :=
  fun ω ↦ ω.2 i

/-- The two coordinate blocks of the replacement space are independent. -/
lemma indepFun_replacement_blocks
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, Measurable (X i)) :
    (Prod.fst :
        ((Fin n → EuclideanSpace ℝ (Fin d)) ×
          (Fin n → EuclideanSpace ℝ (Fin d))) →
        (Fin n → EuclideanSpace ℝ (Fin d))) ⟂ᵢ[bentkusReplacementMeasure μ X]
      (Prod.snd :
        ((Fin n → EuclideanSpace ℝ (Fin d)) ×
          (Fin n → EuclideanSpace ℝ (Fin d))) →
        (Fin n → EuclideanSpace ℝ (Fin d))) := by
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hX
  simpa only [bentkusReplacementMeasure, id_eq] using
    (indepFun_prod (X := id) (Y := id)
      (measurable_id : Measurable (id : (Fin n → EuclideanSpace ℝ (Fin d)) → _))
      (measurable_id : Measurable (id : (Fin n → EuclideanSpace ℝ (Fin d)) → _)))

/-- Every original coordinate is independent of every Gaussian coordinate on the replacement
space. -/
lemma indepFun_replacementOriginal_replacementGaussian
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, Measurable (X i)) (i j : Fin n) :
    replacementOriginal (d := d) i ⟂ᵢ[bentkusReplacementMeasure μ X]
      replacementGaussian (d := d) j := by
  change ((fun f : Fin n → EuclideanSpace ℝ (Fin d) ↦ f i) ∘ Prod.fst)
      ⟂ᵢ[bentkusReplacementMeasure μ X]
    ((fun f : Fin n → EuclideanSpace ℝ (Fin d) ↦ f j) ∘ Prod.snd)
  exact (indepFun_replacement_blocks hX).comp
    (measurable_pi_apply i) (measurable_pi_apply j)

/-- The original coordinate on the enlarged space has its original marginal law. -/
lemma map_replacementOriginal
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, Measurable (X i)) (i : Fin n) :
    (bentkusReplacementMeasure μ X).map (replacementOriginal (d := d) i) =
      μ.map (X i) := by
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hX
  have hfst : MeasurePreserving Prod.fst (bentkusReplacementMeasure μ X)
      (independentLawProduct μ X) := by
    unfold bentkusReplacementMeasure
    exact measurePreserving_fst
  have hmap := Measure.map_map (measurable_pi_apply i) measurable_fst
    (μ := bentkusReplacementMeasure μ X)
  rw [hfst.map_eq] at hmap
  rw [← map_coordinate_independentLawProduct hX i]
  change (bentkusReplacementMeasure μ X).map
      ((fun f : Fin n → EuclideanSpace ℝ (Fin d) ↦ f i) ∘ Prod.fst) =
    (independentLawProduct μ X).map (fun f ↦ f i)
  exact hmap.symm

/-- The Gaussian coordinate on the enlarged space has the prescribed companion law. -/
lemma map_replacementGaussian
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, Measurable (X i)) (i : Fin n) :
    (bentkusReplacementMeasure μ X).map (replacementGaussian (d := d) i) =
      multivariateGaussian 0 (summandCovarianceMatrix μ X i) := by
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hX
  have hsnd : MeasurePreserving Prod.snd (bentkusReplacementMeasure μ X)
      (gaussianCompanionMeasureOf μ X) := by
    unfold bentkusReplacementMeasure
    exact measurePreserving_snd
  have hmap := Measure.map_map (measurable_gaussianCompanion i) measurable_snd
    (μ := bentkusReplacementMeasure μ X)
  rw [hsnd.map_eq] at hmap
  rw [← map_gaussianCompanionMeasure_gaussianCompanion
    (summandCovarianceMatrix μ X) i]
  change (bentkusReplacementMeasure μ X).map
      (gaussianCompanion (d := d) i ∘ Prod.snd) =
    (gaussianCompanionMeasure (summandCovarianceMatrix μ X)).map
      (gaussianCompanion (d := d) i)
  exact hmap.symm

/-- The original replacement coordinate is measure-preserving onto its original marginal law. -/
lemma measurePreserving_replacementOriginal
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, Measurable (X i)) (i : Fin n) :
    MeasurePreserving (replacementOriginal (d := d) i)
      (bentkusReplacementMeasure μ X) (μ.map (X i)) :=
  ⟨(measurable_pi_apply i).comp measurable_fst, map_replacementOriginal hX i⟩

/-- The Gaussian replacement coordinate is measure-preserving onto its prescribed Gaussian law. -/
lemma measurePreserving_replacementGaussian
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, Measurable (X i)) (i : Fin n) :
    MeasurePreserving (replacementGaussian (d := d) i)
      (bentkusReplacementMeasure μ X)
      (multivariateGaussian 0 (summandCovarianceMatrix μ X i)) :=
  ⟨(measurable_pi_apply i).comp measurable_snd, map_replacementGaussian hX i⟩

/-- Moments of each original summand are preserved on the canonical replacement space. -/
lemma memLp_replacementOriginal
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, Measurable (X i)) {p : ℝ≥0∞} (hp : ∀ i, MemLp (X i) p μ)
    (i : Fin n) :
    MemLp (replacementOriginal (d := d) i) p (bentkusReplacementMeasure μ X) := by
  have hid : MemLp id p (μ.map (X i)) :=
    (memLp_map_measure_iff aestronglyMeasurable_id (hX i).aemeasurable).2 (by
      simpa only [Function.comp_def, id_eq] using hp i)
  simpa only [Function.comp_def, id_eq] using
    hid.comp_measurePreserving (measurePreserving_replacementOriginal hX i)

/-- Gaussian replacement coordinates have finite third moments. -/
lemma memLp_three_replacementGaussian
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, Measurable (X i)) (i : Fin n) :
    MemLp (replacementGaussian (d := d) i) 3 (bentkusReplacementMeasure μ X) := by
  have hid : MemLp id 3
      (multivariateGaussian 0 (summandCovarianceMatrix μ X i)) :=
    IsGaussian.memLp_id _ 3 (by simp)
  simpa only [Function.comp_def, id_eq] using
    hid.comp_measurePreserving (measurePreserving_replacementGaussian hX i)

/-- The enlarged original coordinate has the same Bochner mean as the original summand. -/
lemma integral_replacementOriginal_eq
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, Measurable (X i)) (i : Fin n) :
    ∫ ω, replacementOriginal (d := d) i ω ∂(bentkusReplacementMeasure μ X) =
      ∫ ω, X i ω ∂μ := by
  calc
    ∫ ω, replacementOriginal (d := d) i ω ∂(bentkusReplacementMeasure μ X) =
        ∫ x, x ∂((bentkusReplacementMeasure μ X).map
          (replacementOriginal (d := d) i)) :=
      (integral_map
        ((measurePreserving_replacementOriginal (μ := μ) (X := X) hX i).measurable.aemeasurable)
        aestronglyMeasurable_id).symm
    _ = ∫ x, x ∂(μ.map (X i)) := by rw [map_replacementOriginal hX i]
    _ = ∫ ω, X i ω ∂μ := by
      simpa only [id_eq] using integral_map (hX i).aemeasurable aestronglyMeasurable_id

/-- Every Gaussian coordinate remains centered on the enlarged replacement space. -/
lemma integral_replacementGaussian_eq_zero
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, Measurable (X i)) (i : Fin n) :
    ∫ ω, replacementGaussian (d := d) i ω ∂(bentkusReplacementMeasure μ X) = 0 := by
  calc
    ∫ ω, replacementGaussian (d := d) i ω ∂(bentkusReplacementMeasure μ X) =
        ∫ x, x ∂((bentkusReplacementMeasure μ X).map
          (replacementGaussian (d := d) i)) :=
      (integral_map
        ((measurePreserving_replacementGaussian (μ := μ) (X := X) hX i).measurable.aemeasurable)
        aestronglyMeasurable_id).symm
    _ = ∫ x, x ∂(multivariateGaussian 0 (summandCovarianceMatrix μ X i)) := by
      rw [map_replacementGaussian hX i]
    _ = 0 := integral_id_multivariateGaussian

/-- Original and Gaussian replacement coordinates have identical covariance bilinear forms. -/
lemma covarianceBilin_replacementGaussian_eq_replacementOriginal
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, Measurable (X i)) (i : Fin n)
    (x y : EuclideanSpace ℝ (Fin d)) :
    covarianceBilin
        ((bentkusReplacementMeasure μ X).map (replacementGaussian (d := d) i)) x y =
      covarianceBilin
        ((bentkusReplacementMeasure μ X).map (replacementOriginal (d := d) i)) x y := by
  rw [map_replacementGaussian hX i, map_replacementOriginal hX i,
    show summandCovarianceMatrix μ X i = covarianceMatrix (μ.map (X i)) from rfl,
    covarianceBilin_multivariateGaussian (covarianceMatrix_posSemidef (μ.map (X i)))]
  exact dotProduct_covarianceMatrix_mulVec (μ.map (X i)) x y

/-- The canonical original coordinates remain mutually independent on the enlarged replacement
space. -/
lemma iIndepFun_replacementOriginal
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, Measurable (X i)) :
    iIndepFun (fun i ↦ replacementOriginal (d := d) i)
      (bentkusReplacementMeasure μ X) := by
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hX
  letI : IsProbabilityMeasure (bentkusReplacementMeasure μ X) := by
    unfold bentkusReplacementMeasure
    infer_instance
  have hcoord : iIndepFun
      (fun i (x : Fin n → EuclideanSpace ℝ (Fin d)) ↦ x i)
      (independentLawProduct μ X) :=
    iIndepFun_independentLawProduct hX
  exact iIndepFun_comp_measurePreserving
    (μ := independentLawProduct μ X) (ν := bentkusReplacementMeasure μ X)
    (g := Prod.fst) (fun i ↦ measurable_pi_apply i) hcoord measurePreserving_fst

/-- The Gaussian coordinates remain mutually independent on the enlarged replacement space. -/
lemma iIndepFun_replacementGaussian
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ i, Measurable (X i)) :
    iIndepFun (fun i ↦ replacementGaussian (d := d) i)
      (bentkusReplacementMeasure μ X) := by
  letI : IsProbabilityMeasure (independentLawProduct μ X) :=
    isProbabilityMeasure_independentLawProduct hX
  letI : IsProbabilityMeasure (bentkusReplacementMeasure μ X) := by
    unfold bentkusReplacementMeasure
    infer_instance
  have hcoord : iIndepFun (fun i ↦ gaussianCompanion (d := d) i)
      (gaussianCompanionMeasureOf μ X) :=
    iIndepFun_gaussianCompanion_of μ X
  exact iIndepFun_comp_measurePreserving
    (μ := gaussianCompanionMeasureOf μ X) (ν := bentkusReplacementMeasure μ X)
    (g := Prod.snd) (fun i ↦ measurable_gaussianCompanion i) hcoord measurePreserving_snd

end ProbabilityTheory
