/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The rotation-invariant probability measure on a Euclidean sphere

Ball's Gaussian-perimeter proof averages orthogonal projections over the unit sphere with
rotation-invariant probability measure.  Mathlib's `Measure.toSphere` supplies the canonical
unnormalized Haar surface measure.  This module normalizes it once and records the exact measure
identity used by the radial-majorant and projection-area arguments.
-/

open Set Metric MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

/-- A canonical point of the unit sphere in a nonzero Euclidean dimension. -/
def standardUnitSpherePoint (d : ℕ) (hd : d ≠ 0) :
    sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
  ⟨EuclideanSpace.single ⟨0, Nat.pos_of_ne_zero hd⟩ 1, by
    rw [mem_sphere_zero_iff_norm]
    simp⟩

/-- The finite rotation-invariant surface measure on the Euclidean unit sphere. -/
def standardSphereSurfaceFiniteMeasure (d : ℕ) :
    FiniteMeasure (sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
  ⟨volume.toSphere, inferInstance⟩

/-- Rotation-invariant surface measure normalized to total mass one.  The proof `d ≠ 0`
provides the point required by `FiniteMeasure.normalize`; proof irrelevance makes the resulting
measure independent of its particular witness. -/
def standardSphereProbability (d : ℕ) (hd : d ≠ 0) :
    ProbabilityMeasure (sphere (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  letI : Nonempty (sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    ⟨standardUnitSpherePoint d hd⟩
  exact (standardSphereSurfaceFiniteMeasure d).normalize

theorem standardSphereSurfaceFiniteMeasure_ne_zero (d : ℕ) (hd : d ≠ 0) :
    standardSphereSurfaceFiniteMeasure d ≠ 0 := by
  let i : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
  letI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    ⟨⟨0, EuclideanSpace.single i 1, by
      intro h
      have hi := congr_arg (fun x : EuclideanSpace ℝ (Fin d) ↦ x i) h
      simp [i] at hi⟩⟩
  intro hzero
  have hmeasure := congr_arg FiniteMeasure.toMeasure hzero
  change volume.toSphere = 0 at hmeasure
  exact Measure.toSphere_ne_zero volume hmeasure

/-- The normalized sphere probability is inverse total surface mass times Mathlib's canonical
surface measure. -/
theorem standardSphereProbability_toMeasure (d : ℕ) (hd : d ≠ 0) :
    (standardSphereProbability d hd).toMeasure =
      (standardSphereSurfaceFiniteMeasure d).mass⁻¹ • volume.toSphere := by
  letI : Nonempty (sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    ⟨standardUnitSpherePoint d hd⟩
  exact FiniteMeasure.toMeasure_normalize_eq_of_nonzero
    (standardSphereSurfaceFiniteMeasure d)
    (standardSphereSurfaceFiniteMeasure_ne_zero d hd)

@[simp]
theorem standardSphereProbability_apply_univ (d : ℕ) (hd : d ≠ 0) :
    standardSphereProbability d hd univ = 1 := by
  exact ProbabilityMeasure.coeFn_univ _

end ProbabilityTheory
