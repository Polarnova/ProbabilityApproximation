/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.Basic
import Mathlib.LinearAlgebra.SesquilinearForm.Star

/-!
# Canonical Gaussian companions

This module constructs a finite independent family of centered Gaussian vectors with prescribed
positive-semidefinite covariance matrices on the canonical product probability space.  The
construction is the probability-space enlargement used in Bentkus's replacement argument; no
Gaussian random variables are assumed to exist on the original sample space.
-/

open MeasureTheory Matrix
open scoped ENNReal MatrixOrder RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

/-- The covariance matrix of a probability law on Euclidean space, written in the canonical
orthonormal basis.  This definition remains meaningful without moment hypotheses because
`covarianceBilin` is defined to be zero when the second moment is infinite. -/
def covarianceMatrix {d : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin d))) :
    Matrix (Fin d) (Fin d) ℝ :=
  LinearMap.BilinForm.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
    (covarianceBilin ν).toBilinForm

/-- Every covariance matrix is positive semidefinite, including in the singular case. -/
lemma covarianceMatrix_posSemidef {d : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin d))) :
    (covarianceMatrix ν).PosSemidef := by
  exact (LinearMap.isPosSemidef_iff_posSemidef_toMatrix
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis).mp
      (LinearMap.BilinForm.isPosSemidef_iff.mp isPosSemidef_covarianceBilin)

/-- The matrix form of `covarianceMatrix` recovers the covariance bilinear form. -/
lemma dotProduct_covarianceMatrix_mulVec {d : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (x y : EuclideanSpace ℝ (Fin d)) :
    x ⬝ᵥ covarianceMatrix ν *ᵥ y = covarianceBilin ν x y := by
  let b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  have h := apply_eq_star_dotProduct_toMatrix₂_mulVec
    (B := (covarianceBilin ν).toBilinForm) b x y
  have hx : ⇑(b.repr x) = x := by
    funext i
    simp [b]
  have hy : ⇑(b.repr y) = y := by
    funext i
    simp [b]
  rw [hx, hy] at h
  change x ⬝ᵥ
      (LinearMap.toMatrix₂ (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
        (covarianceBilin ν).toBilinForm) *ᵥ y =
    (covarianceBilin ν).toBilinForm x y
  simpa only [map_mul, starRingEnd_apply, star_id_of_comm] using h.symm

/-- The canonical product law of centered Gaussian companions with covariance matrices `S i`. -/
def gaussianCompanionMeasure {n d : ℕ}
    (S : Fin n → Matrix (Fin d) (Fin d) ℝ) :
    Measure (Fin n → EuclideanSpace ℝ (Fin d)) :=
  Measure.pi fun i ↦ multivariateGaussian 0 (S i)

/-- The `i`th coordinate on the canonical Gaussian-companion product space. -/
def gaussianCompanion {n d : ℕ}
    (i : Fin n) : (Fin n → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) :=
  fun ω ↦ ω i

instance {n d : ℕ} (S : Fin n → Matrix (Fin d) (Fin d) ℝ) :
    IsProbabilityMeasure (gaussianCompanionMeasure S) := by
  unfold gaussianCompanionMeasure
  infer_instance

lemma measurable_gaussianCompanion {n d : ℕ} (i : Fin n) :
    Measurable (gaussianCompanion (d := d) i) := by
  change Measurable (fun ω : Fin n → EuclideanSpace ℝ (Fin d) ↦ ω i)
  exact measurable_pi_apply i

/-- Each canonical coordinate has exactly its prescribed multivariate Gaussian law. -/
lemma map_gaussianCompanionMeasure_gaussianCompanion {n d : ℕ}
    (S : Fin n → Matrix (Fin d) (Fin d) ℝ) (i : Fin n) :
    (gaussianCompanionMeasure S).map (gaussianCompanion (d := d) i) =
      multivariateGaussian 0 (S i) := by
  change (Measure.pi fun j ↦ multivariateGaussian 0 (S j)).map
      (fun ω ↦ ω i) = multivariateGaussian 0 (S i)
  exact (measurePreserving_eval
    (fun j ↦ multivariateGaussian 0 (S j)) i).map_eq

/-- The canonical Gaussian companions are mutually independent. -/
lemma iIndepFun_gaussianCompanion {n d : ℕ}
    (S : Fin n → Matrix (Fin d) (Fin d) ℝ) :
    iIndepFun (fun i ↦ gaussianCompanion (d := d) i) (gaussianCompanionMeasure S) := by
  change iIndepFun (fun i ω ↦ ω i)
    (Measure.pi fun i ↦ multivariateGaussian 0 (S i))
  exact iIndepFun_pi
    (X := fun _ : Fin n ↦ id)
    (μ := fun i ↦ multivariateGaussian 0 (S i))
    (fun _ ↦ aemeasurable_id)

/-- Every canonical companion has finite moments of every finite order. -/
lemma memLp_gaussianCompanion {n d : ℕ}
    (S : Fin n → Matrix (Fin d) (Fin d) ℝ) (i : Fin n)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (gaussianCompanion (d := d) i) p (gaussianCompanionMeasure S) := by
  have hId : MemLp id p (multivariateGaussian 0 (S i)) :=
    IsGaussian.memLp_id _ p hp
  have hEval := measurePreserving_eval
    (fun j ↦ multivariateGaussian 0 (S j)) i
  change MemLp (fun ω : Fin n → EuclideanSpace ℝ (Fin d) ↦ ω i) p
    (Measure.pi fun j ↦ multivariateGaussian 0 (S j))
  simpa only [Function.comp_def, id_eq] using hId.comp_measurePreserving hEval

/-- In particular, every canonical companion has a finite third absolute moment. -/
lemma memLp_three_gaussianCompanion {n d : ℕ}
    (S : Fin n → Matrix (Fin d) (Fin d) ℝ) (i : Fin n) :
    MemLp (gaussianCompanion (d := d) i) 3 (gaussianCompanionMeasure S) :=
  memLp_gaussianCompanion S i 3 (by simp)

/-- Every canonical companion is centered. -/
lemma integral_gaussianCompanion_eq_zero {n d : ℕ}
    (S : Fin n → Matrix (Fin d) (Fin d) ℝ) (i : Fin n) :
    ∫ ω, gaussianCompanion (d := d) i ω ∂(gaussianCompanionMeasure S) = 0 := by
  have hEval := measurePreserving_eval
    (fun j ↦ multivariateGaussian 0 (S j)) i
  have hmap :
      (∫ x : EuclideanSpace ℝ (Fin d), x ∂(multivariateGaussian 0 (S i))) =
        ∫ ω : Fin n → EuclideanSpace ℝ (Fin d), ω i
          ∂(Measure.pi fun j ↦ multivariateGaussian 0 (S j)) := by
    have h := integral_map hEval.aemeasurable
      (f := id) (by
        rw [hEval.map_eq]
        exact aestronglyMeasurable_id)
    rw [hEval.map_eq] at h
    simpa only [Function.comp_def, id_eq] using h
  rw [integral_id_multivariateGaussian] at hmap
  change (∫ ω : Fin n → EuclideanSpace ℝ (Fin d), ω i
    ∂(Measure.pi fun j ↦ multivariateGaussian 0 (S j))) = 0
  exact hmap.symm

/-- The covariance bilinear form of a canonical companion is the prescribed matrix form. -/
lemma covarianceBilin_map_gaussianCompanion {n d : ℕ}
    (S : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (hS : ∀ i, (S i).PosSemidef) (i : Fin n)
    (x y : EuclideanSpace ℝ (Fin d)) :
    covarianceBilin
        ((gaussianCompanionMeasure S).map (gaussianCompanion (d := d) i)) x y =
      x ⬝ᵥ (S i) *ᵥ y := by
  rw [map_gaussianCompanionMeasure_gaussianCompanion]
  exact covarianceBilin_multivariateGaussian (hS i) x y

/-- The canonical Gaussian companion associated with an arbitrary law has exactly that law's
covariance bilinear form.  No nonsingularity assumption is needed. -/
lemma covarianceBilin_map_gaussianCompanion_covarianceMatrix {n d : ℕ}
    (ν : Fin n → Measure (EuclideanSpace ℝ (Fin d))) (i : Fin n)
    (x y : EuclideanSpace ℝ (Fin d)) :
    covarianceBilin
        ((gaussianCompanionMeasure (fun j ↦ covarianceMatrix (ν j))).map
          (gaussianCompanion (d := d) i)) x y =
      covarianceBilin (ν i) x y := by
  rw [covarianceBilin_map_gaussianCompanion _
    (fun j ↦ covarianceMatrix_posSemidef (ν j))]
  exact dotProduct_covarianceMatrix_mulVec (ν i) x y

/-- The covariance matrix of the `i`th summand law. -/
def summandCovarianceMatrix {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Fin n → Ω → EuclideanSpace ℝ (Fin d))
    (i : Fin n) : Matrix (Fin d) (Fin d) ℝ :=
  covarianceMatrix (μ.map (X i))

/-- The canonical product law for the Gaussian companions of a given summand family.  This is the
probability-space realization of the family `Y₁, …, Yₙ` introduced in Bentkus (2004), (3.2). -/
def gaussianCompanionMeasureOf {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)) :
    Measure (Fin n → EuclideanSpace ℝ (Fin d)) :=
  gaussianCompanionMeasure (summandCovarianceMatrix μ X)

instance {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)) :
    IsProbabilityMeasure (gaussianCompanionMeasureOf μ X) := by
  unfold gaussianCompanionMeasureOf
  infer_instance

/-- The companion coordinates associated with a summand family are mutually independent. -/
lemma iIndepFun_gaussianCompanion_of {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)) :
    iIndepFun (fun i ↦ gaussianCompanion (d := d) i)
      (gaussianCompanionMeasureOf μ X) := by
  exact iIndepFun_gaussianCompanion (summandCovarianceMatrix μ X)

/-- Every companion associated with a summand family is centered. -/
lemma integral_gaussianCompanion_of_eq_zero {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (i : Fin n) :
    ∫ ω, gaussianCompanion (d := d) i ω ∂(gaussianCompanionMeasureOf μ X) = 0 := by
  exact integral_gaussianCompanion_eq_zero (summandCovarianceMatrix μ X) i

/-- Every companion associated with a summand family has a finite third moment. -/
lemma memLp_three_gaussianCompanion_of {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (i : Fin n) :
    MemLp (gaussianCompanion (d := d) i) 3 (gaussianCompanionMeasureOf μ X) := by
  exact memLp_three_gaussianCompanion (summandCovarianceMatrix μ X) i

/-- Each canonical Gaussian companion has exactly the covariance bilinear form of the
corresponding summand law, including when that covariance is singular. -/
lemma covarianceBilin_map_gaussianCompanion_of {n d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (i : Fin n)
    (x y : EuclideanSpace ℝ (Fin d)) :
    covarianceBilin
        ((gaussianCompanionMeasureOf μ X).map (gaussianCompanion (d := d) i)) x y =
      covarianceBilin (μ.map (X i)) x y := by
  exact covarianceBilin_map_gaussianCompanion_covarianceMatrix
    (fun j ↦ μ.map (X j)) i x y

end ProbabilityTheory
