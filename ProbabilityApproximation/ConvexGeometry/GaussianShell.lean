/-
Copyright (c) 2026 ProbabilityApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProbabilityApproximation contributors
-/
import ProbabilityApproximation.Bentkus.GaussianDensityDerivatives
import ProbabilityApproximation.Bentkus.SmoothingInequality
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Standard-Gaussian convex shells

This file isolates the domain-completion and coarea output needed around Ball's Gaussian-perimeter
theorem.  Ball (1993), Theorem 4, printed pp. 415--419, proves the boundary-density estimate
`4 * d ^ (1 / 4)` for convex bodies in dimension `d ≥ 2`.  Raič (2019), Proposition 3.1 and its
proof on printed pp. 2843--2845, identifies the supremum of those boundary integrals with both the
outer- and inner-shell difference quotients by the coarea formula for signed distance.

The declarations below prove the parts that do not require the missing codimension-one coarea
theorem in Mathlib:

* standard Gaussian measure is dominated by Euclidean volume in every finite dimension;
* convex frontiers therefore have zero standard-Gaussian measure;
* signed distance is almost everywhere differentiable with derivative norm one, and its positive,
  zero, and negative fibers are identified with the correct parallel-set frontiers;
* outer and inner shells are identified, up to null boundaries, with signed-distance slabs;
* the outer and inner shell estimates are complete in dimensions zero and one;
* Gaussian-weighted Hausdorff boundary profiles and a precise interval-integral lemma package the
  remaining Ball/coarea composition.

The one-dimensional proof is independent of Ball's theorem.  It splits each shell into its two
ordered boundary pieces, each of diameter at most `ε`; the standard Gaussian density is at most
one.  Thus it obtains the stronger constant `2`, and hence the required constant `4`.
-/

open Set MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

local instance {d : ℕ} :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

local instance {d : ℕ} :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.ofModule

private lemma gaussianPDF_zero_one_le_one (x : ℝ) : gaussianPDF 0 1 x ≤ 1 := by
  rw [gaussianPDF, ENNReal.ofReal_le_one]
  rw [gaussianPDFReal]
  have hsqrt : 1 ≤ √(2 * Real.pi) := by
    have hpi : 2 ≤ Real.pi := Real.two_le_pi
    have hsqrt_nonneg : 0 ≤ √(2 * Real.pi) := Real.sqrt_nonneg _
    have hsqrt_sq : (√(2 * Real.pi)) ^ 2 = 2 * Real.pi := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith
  have hinv : (√(2 * Real.pi))⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).2 hsqrt
  have hexp : Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by norm_num)
  calc
    (√(2 * Real.pi * (1 : ℝ)))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ))) ≤
        1 * 1 := by
      simpa using mul_le_mul hinv hexp (Real.exp_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The one-dimensional standard Gaussian measure is bounded above by Lebesgue measure. -/
lemma gaussianReal_zero_one_le_volume : gaussianReal 0 1 ≤ volume := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
  calc
    volume.withDensity (gaussianPDF 0 1) ≤ volume.withDensity 1 :=
      withDensity_mono (ae_of_all _ gaussianPDF_zero_one_le_one)
    _ = volume := by simp

private lemma piGaussian_le_volume : ∀ d : ℕ,
    Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1) ≤ volume
  | 0 => by
      change Measure.pi (fun _ : Fin 0 ↦ gaussianReal 0 1) ≤
        Measure.pi (fun _ : Fin 0 ↦ volume)
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | d + 1 => by
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) ↦ ℝ) (0 : Fin (d + 1))
      have hGaussian := measurePreserving_piFinSuccAbove
        (fun _ : Fin (d + 1) ↦ gaussianReal 0 1) (0 : Fin (d + 1))
      have hVolume := volume_preserving_piFinSuccAbove
        (fun _ : Fin (d + 1) ↦ ℝ) (0 : Fin (d + 1))
      have hprod :
          (gaussianReal 0 1).prod
              (Measure.pi fun j : Fin d ↦ gaussianReal 0 1) ≤
            volume.prod (volume : Measure (Fin d → ℝ)) :=
        Measure.prod_mono gaussianReal_zero_one_le_volume (piGaussian_le_volume d)
      have hmap := Measure.map_mono hprod e.symm.measurable
      calc
        Measure.pi (fun _ : Fin (d + 1) ↦ gaussianReal 0 1) =
            Measure.map e.symm
              ((gaussianReal 0 1).prod
                (Measure.pi fun j : Fin d ↦ gaussianReal 0 1)) :=
          (MeasurePreserving.symm e hGaussian).map_eq.symm
        _ ≤ Measure.map e.symm (volume.prod (volume : Measure (Fin d → ℝ))) := hmap
        _ = volume := (MeasurePreserving.symm e hVolume).map_eq

/-- Standard Gaussian measure on Euclidean space is bounded above by Euclidean volume. -/
lemma stdGaussian_le_volume {d : ℕ} :
    stdGaussian (EuclideanSpace ℝ (Fin d)) ≤ volume := by
  rw [← map_pi_eq_stdGaussian]
  have h := Measure.map_mono (piGaussian_le_volume d)
    (WithLp.measurable_toLp 2 (Fin d → ℝ))
  rw [(PiLp.volume_preserving_toLp (Fin d)).map_eq] at h
  exact h

private lemma legacyConvex_of_isConvexSet {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : Convexity.IsConvexSet ℝ s) :
    Convex ℝ s := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  simpa [Convexity.convexCombPair_eq_sum] using
    hs.convexCombPair_mem hx hy ha hb hab

/-- The frontier of a convex Euclidean set has zero standard-Gaussian measure. -/
lemma stdGaussian_frontier_eq_zero {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : Convexity.IsConvexSet ℝ s) :
    stdGaussian (EuclideanSpace ℝ (Fin d)) (frontier s) = 0 := by
  apply le_zero_iff.mp
  calc
    stdGaussian (EuclideanSpace ℝ (Fin d)) (frontier s) ≤ volume (frontier s) :=
      stdGaussian_le_volume (d := d) (frontier s)
    _ = 0 := (legacyConvex_of_isConvexSet hs).addHaar_frontier volume

/-- Closing a convex Euclidean set does not change its standard-Gaussian measure. -/
lemma stdGaussian_closure_eq {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : Convexity.IsConvexSet ℝ s) :
    stdGaussian (EuclideanSpace ℝ (Fin d)) (closure s) =
      stdGaussian (EuclideanSpace ℝ (Fin d)) s := by
  exact (measure_eq_measure_of_null_sdiff subset_closure (by
    apply measure_mono_null _ (stdGaussian_frontier_eq_zero hs)
    intro x hx
    exact ⟨hx.1, fun hxi ↦ hx.2 (interior_subset hxi)⟩)).symm

/-- The signed distance to a set, negative on its interior side and positive on its exterior
side.  This is Raič's signed-distance function before restricting to a convex set. -/
def setSignedDistance {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Metric.infDist x s - Metric.infDist x sᶜ

/-- On the exterior of a set, signed distance is ordinary distance to that set. -/
lemma setSignedDistance_eq_infDist_of_notMem {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∉ s) : setSignedDistance s x = Metric.infDist x s := by
  have hxcompl : x ∈ sᶜ := hx
  rw [setSignedDistance, Metric.infDist_zero_of_mem hxcompl, sub_zero]

/-- On a set, signed distance is minus distance to its complement. -/
lemma setSignedDistance_eq_neg_infDist_compl_of_mem {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ s) : setSignedDistance s x = -Metric.infDist x sᶜ := by
  rw [setSignedDistance, Metric.infDist_zero_of_mem hx, zero_sub]

/-- Signed distance is continuous. -/
lemma continuous_setSignedDistance {d : ℕ}
    (s : Set (EuclideanSpace ℝ (Fin d))) : Continuous (setSignedDistance s) :=
  (Metric.continuous_infDist_pt s).sub (Metric.continuous_infDist_pt sᶜ)

/-- Signed distance is measurable. -/
lemma measurable_setSignedDistance {d : ℕ}
    (s : Set (EuclideanSpace ℝ (Fin d))) : Measurable (setSignedDistance s) :=
  (continuous_setSignedDistance s).measurable

/-- The elementary global Lipschitz bound for signed distance.  The sharp constant is one; the
constant two already suffices to invoke Rademacher before the sharp norm-one derivative is proved
on the outer region. -/
lemma setSignedDistance_lipschitzWith_two {d : ℕ}
    (s : Set (EuclideanSpace ℝ (Fin d))) : LipschitzWith 2 (setSignedDistance s) := by
  have hs : LipschitzWith 1
      (fun x : EuclideanSpace ℝ (Fin d) ↦ Metric.infDist x s) :=
    Metric.lipschitz_infDist_pt s
  have hsc : LipschitzWith 1
      (fun x : EuclideanSpace ℝ (Fin d) ↦ Metric.infDist x sᶜ) :=
    Metric.lipschitz_infDist_pt sᶜ
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Real.dist_eq]
  change |(Metric.infDist x s - Metric.infDist x sᶜ) -
      (Metric.infDist y s - Metric.infDist y sᶜ)| ≤ (2 : ℝ) * dist x y
  calc
    |(Metric.infDist x s - Metric.infDist x sᶜ) -
        (Metric.infDist y s - Metric.infDist y sᶜ)| =
        |(Metric.infDist x s - Metric.infDist y s) -
          (Metric.infDist x sᶜ - Metric.infDist y sᶜ)| := by ring_nf
    _ ≤ |Metric.infDist x s - Metric.infDist y s| +
        |Metric.infDist x sᶜ - Metric.infDist y sᶜ| := abs_sub _ _
    _ ≤ dist x y + dist x y := by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
        add_le_add (hs.dist_le_mul x y) (hsc.dist_le_mul x y)
    _ = 2 * dist x y := by ring

/-- Signed distance is Fréchet differentiable almost everywhere by Rademacher's theorem. -/
lemma setSignedDistance_ae_differentiableAt {d : ℕ}
    (s : Set (EuclideanSpace ℝ (Fin d))) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      DifferentiableAt ℝ (setSignedDistance s) x :=
  (setSignedDistance_lipschitzWith_two s).ae_differentiableAt

/-- Outside the closure, signed distance agrees locally with ordinary distance to the closure. -/
lemma setSignedDistance_eventuallyEq_infDist_closure_of_notMem {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∉ closure s) :
    setSignedDistance s =ᶠ[nhds x] fun y ↦ Metric.infDist y (closure s) := by
  have hnhds : ∀ᶠ y in nhds x, y ∈ (closure s)ᶜ :=
    isClosed_closure.isOpen_compl.mem_nhds hx
  filter_upwards [hnhds] with y hy
  rw [setSignedDistance_eq_infDist_of_notMem (fun hys ↦ hy (subset_closure hys))]
  exact Metric.infDist_closure.symm

/-- At every point outside a nonempty convex set's closure, signed distance has the explicit
normalized projection-residual derivative. -/
lemma hasFDerivAt_setSignedDistance_of_notMem_closure {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hne : s.Nonempty)
    (hs : Convexity.IsConvexSet ℝ s) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∉ closure s) :
    HasFDerivAt (setSignedDistance s)
      ((Metric.infDist x (closure s))⁻¹ •
        ((innerSL ℝ) (x - metricProjection (closure s) isClosed_closure hne.closure x))) x := by
  exact (hasFDerivAt_infDist_of_notMem isClosed_closure hne.closure
    (closure_isConvexSet hs) hx).congr_of_eventuallyEq
      (setSignedDistance_eventuallyEq_infDist_closure_of_notMem hx)

/-- The Fréchet derivative of signed distance has norm one everywhere outside the closure of a
nonempty convex set.  This closes the outer-region gradient input of Raič, Proposition 3.3. -/
lemma norm_fderiv_setSignedDistance_of_notMem_closure {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hne : s.Nonempty)
    (hs : Convexity.IsConvexSet ℝ s) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∉ closure s) :
    ‖fderiv ℝ (setSignedDistance s) x‖ = 1 := by
  rw [(setSignedDistance_eventuallyEq_infDist_closure_of_notMem hx).fderiv_eq]
  exact norm_fderiv_infDist_of_notMem isClosed_closure hne.closure
    (closure_isConvexSet hs) hx

/-- Distance to the complement decreases linearly on a shortest segment from a point to the
frontier. -/
lemma infDist_compl_segment_to_frontier {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {x y : EuclideanSpace ℝ (Fin d)}
    (hy : y ∈ frontier s) (hxy : Metric.infDist x sᶜ = dist x y)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Metric.infDist (x + t • (y - x)) sᶜ = (1 - t) * Metric.infDist x sᶜ := by
  let r := Metric.infDist x sᶜ
  let v := y - x
  let z := x + t • v
  have hycompl : y ∈ closure sᶜ := by
    rw [frontier_eq_closure_inter_closure] at hy
    exact hy.2
  have hvnorm : ‖v‖ = r := by
    dsimp [v, r]
    rw [norm_sub_rev, ← dist_eq_norm]
    exact hxy.symm
  have hxz : dist x z = t * r := by
    calc
      dist x z = dist (x + 0) (x + t • v) := by simp [z]
      _ = dist 0 (t • v) := dist_add_left x 0 (t • v)
      _ = ‖t • v‖ := dist_zero_left _
      _ = t * r := by rw [norm_smul, Real.norm_of_nonneg ht.1, hvnorm]
  have hy_eq : y = x + v := by
    dsimp [v]
    abel
  have hzy : dist z y = (1 - t) * r := by
    calc
      dist z y = dist (x + t • v) (x + v) := by rw [hy_eq]
      _ = dist (t • v) v := dist_add_left x (t • v) v
      _ = ‖t • v - v‖ := by rw [dist_eq_norm]
      _ = ‖(t - 1) • v‖ := by rw [sub_smul, one_smul]
      _ = (1 - t) * r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr ht.2), hvnorm]
        ring
  have hlower0 : r ≤ Metric.infDist z sᶜ + dist x z :=
    Metric.infDist_le_infDist_add_dist
  have hlower : (1 - t) * r ≤ Metric.infDist z sᶜ := by
    rw [hxz] at hlower0
    linarith
  have hupper : Metric.infDist z sᶜ ≤ (1 - t) * r := by
    have h := Metric.infDist_le_dist_of_mem (x := z) hycompl
    rw [Metric.infDist_closure, hzy] at h
    exact h
  exact le_antisymm hupper hlower

/-- At an interior point where distance to the complement is differentiable, its derivative has
norm one.  The proof follows a shortest segment from the point to the frontier and compares the
one-sided derivative with the global one-Lipschitz bound. -/
lemma norm_fderiv_infDist_compl_of_mem_interior {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hsne : s ≠ univ)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ interior s)
    (hdiff : DifferentiableAt ℝ (fun y ↦ Metric.infDist y sᶜ) x) :
    ‖fderiv ℝ (fun y ↦ Metric.infDist y sᶜ) x‖ = 1 := by
  let L := fderiv ℝ (fun y ↦ Metric.infDist y sᶜ) x
  let r := Metric.infDist x sᶜ
  have hxmem : x ∈ s := interior_subset hx
  have hxnot : x ∉ closure sᶜ := by
    rw [interior_eq_compl_closure_compl] at hx
    exact hx
  have hcompne : sᶜ.Nonempty := nonempty_compl.2 hsne
  have hr : 0 < r := (Metric.infDist_pos_iff_notMem_closure hcompne).1 hxnot
  obtain ⟨y, hyfront, hxy⟩ := exists_mem_frontier_infDist_compl_eq_dist hxmem hsne
  let v := y - x
  have hvnorm : ‖v‖ = r := by
    dsimp [v, r]
    rw [norm_sub_rev, ← dist_eq_norm]
    exact hxy.symm
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Metric.infDist (x + t • v) sᶜ = (1 - t) * r := by
    exact infDist_compl_segment_to_frontier hyfront hxy ht
  have hcomp : HasDerivAt (fun t : ℝ ↦ Metric.infDist (x + t • v) sᶜ) (L v) 0 := by
    exact hdiff.hasFDerivAt.hasLineDerivAt v
  have hlinear : HasDerivAt (fun t : ℝ ↦ (1 - t) * r) (-r) 0 := by
    simpa only [Pi.sub_apply, id_eq, zero_sub, one_mul, neg_mul] using
      ((hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub
        (hasDerivAt_id (𝕜 := ℝ) 0)).mul_const r
  have hpathDeriv : HasDerivWithinAt
      (fun t : ℝ ↦ Metric.infDist (x + t • v) sᶜ) (-r) (Icc 0 1) 0 :=
    hlinear.hasDerivWithinAt.congr hpath (hpath 0 (by norm_num))
  have hLv : L v = -r := by
    exact ((uniqueDiffOn_Icc zero_lt_one).uniqueDiffWithinAt (by norm_num)).eq_deriv
      (Icc (0 : ℝ) 1) hcomp.hasDerivWithinAt hpathDeriv
  have hupper : ‖L‖ ≤ 1 := by
    simpa only [NNReal.coe_one] using
      hdiff.hasFDerivAt.le_of_lipschitz (Metric.lipschitz_infDist_pt sᶜ)
  have hop : r ≤ ‖L‖ * r := by
    simpa [hLv, hvnorm, Real.norm_of_nonneg hr.le] using L.le_opNorm v
  have hlower : 1 ≤ ‖L‖ := by
    exact le_of_mul_le_mul_right (by simpa only [one_mul] using hop) hr
  exact le_antisymm hupper hlower

/-- On the interior of a set, signed distance agrees locally with minus distance to the
complement. -/
lemma setSignedDistance_eventuallyEq_neg_infDist_compl_of_mem_interior {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ interior s) :
    setSignedDistance s =ᶠ[nhds x] -(fun y ↦ Metric.infDist y sᶜ) := by
  have hnhds : ∀ᶠ y in nhds x, y ∈ interior s := isOpen_interior.mem_nhds hx
  filter_upwards [hnhds] with y hy
  simpa only [Pi.neg_apply] using
    setSignedDistance_eq_neg_infDist_compl_of_mem (interior_subset hy)

/-- At every interior differentiability point, the Fréchet derivative of signed distance has
norm one. -/
lemma norm_fderiv_setSignedDistance_of_mem_interior {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hsne : s ≠ univ)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ interior s)
    (hdiff : DifferentiableAt ℝ (setSignedDistance s) x) :
    ‖fderiv ℝ (setSignedDistance s) x‖ = 1 := by
  let f : EuclideanSpace ℝ (Fin d) → ℝ := fun y ↦ Metric.infDist y sᶜ
  have heq : setSignedDistance s =ᶠ[nhds x] -f := by
    simpa only [f] using
      setSignedDistance_eventuallyEq_neg_infDist_compl_of_mem_interior hx
  have hnegdiff : DifferentiableAt ℝ (-f) x := heq.differentiableAt_iff.mp hdiff
  have hfdiff : DifferentiableAt ℝ f x := by
    simpa only [Pi.neg_apply, neg_neg] using hnegdiff.neg
  calc
    ‖fderiv ℝ (setSignedDistance s) x‖ = ‖fderiv ℝ (-f) x‖ :=
      congrArg norm heq.fderiv_eq
    _ = ‖-fderiv ℝ f x‖ := by rw [fderiv_neg]
    _ = ‖fderiv ℝ f x‖ := norm_neg _
    _ = 1 := norm_fderiv_infDist_compl_of_mem_interior hsne hx hfdiff

/-- The signed-distance derivative has norm one almost everywhere in the interior of a proper
set. -/
lemma ae_norm_fderiv_setSignedDistance_eq_one_of_mem_interior {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hsne : s ≠ univ) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      x ∈ interior s → ‖fderiv ℝ (setSignedDistance s) x‖ = 1 := by
  filter_upwards [setSignedDistance_ae_differentiableAt s] with x hdiff
  exact fun hx ↦ norm_fderiv_setSignedDistance_of_mem_interior hsne hx hdiff

/-- Raič (2019), Proposition 3.3's eikonal conclusion for a nonempty proper convex Euclidean
set: the Fréchet derivative of signed distance has norm one almost everywhere. -/
theorem ae_norm_fderiv_setSignedDistance_eq_one {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hne : s.Nonempty) (hsne : s ≠ univ)
    (hs : Convexity.IsConvexSet ℝ s) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      ‖fderiv ℝ (setSignedDistance s) x‖ = 1 := by
  have hfrontier : volume (frontier s) = 0 :=
    (legacyConvex_of_isConvexSet hs).addHaar_frontier volume
  have haefrontier : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      x ∉ frontier s := by
    rw [MeasureTheory.ae_iff]
    simpa only [Classical.not_not, setOf_mem_eq] using hfrontier
  filter_upwards [setSignedDistance_ae_differentiableAt s, haefrontier] with x hdiff hxfrontier
  by_cases hxs : x ∈ s
  · exact norm_fderiv_setSignedDistance_of_mem_interior hsne
      ((mem_interior_iff_notMem_frontier hxs).2 hxfrontier) hdiff
  · have hxclosure : x ∉ closure s := by
      intro hxc
      exact hxfrontier ⟨hxc, fun hxi ↦ hxs (interior_subset hxi)⟩
    exact norm_fderiv_setSignedDistance_of_notMem_closure hne hs hxclosure

/-- Along the outward ray from a metric projection onto a closed convex set, distance to the set
grows exactly linearly. -/
lemma infDist_metricProjection_ray {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hclosed : IsClosed s) (hne : s.Nonempty)
    (hs : Convexity.IsConvexSet ℝ s) (x : EuclideanSpace ℝ (Fin d))
    {a : ℝ} (ha : 0 ≤ a) :
    Metric.infDist
        (metricProjection s hclosed hne x + a • (x - metricProjection s hclosed hne x)) s =
      a * Metric.infDist x s := by
  let p := metricProjection s hclosed hne x
  let y := p + a • (x - p)
  let q := metricProjection s hclosed hne y
  have hp : p ∈ s := (metricProjection_isNearestPoint s hclosed hne x).1
  have hq : q ∈ s := (metricProjection_isNearestPoint s hclosed hne y).1
  have hvar : inner ℝ (x - p) (q - p) ≤ 0 :=
    metricProjection_variational hclosed hne hs x hq
  have hsquare : ‖a • (x - p)‖ ^ 2 ≤ ‖a • (x - p) - (q - p)‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_left, norm_smul, Real.norm_of_nonneg ha]
    nlinarith [sq_nonneg ‖q - p‖]
  have hnorm : ‖a • (x - p)‖ ≤ ‖a • (x - p) - (q - p)‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsquare
  have hdist : dist y p ≤ dist y q := by
    rw [dist_eq_norm, dist_eq_norm]
    have hyp : y - p = a • (x - p) := by dsimp [y]; abel
    have hyq : y - q = a • (x - p) - (q - p) := by dsimp [y]; abel
    rwa [hyp, hyq]
  apply le_antisymm
  · calc
      Metric.infDist y s ≤ dist y p := Metric.infDist_le_dist_of_mem hp
      _ = a * Metric.infDist x s := by
        rw [dist_eq_norm]
        have hyp : y - p = a • (x - p) := by dsimp [y]; abel
        rw [hyp, norm_smul, Real.norm_of_nonneg ha,
          infDist_eq_dist_metricProjection s hclosed hne x, dist_eq_norm]
  · calc
      a * Metric.infDist x s = dist y p := by
        rw [dist_eq_norm]
        have hyp : y - p = a • (x - p) := by dsimp [y]; abel
        rw [hyp, norm_smul, Real.norm_of_nonneg ha,
          infDist_eq_dist_metricProjection s hclosed hne x, dist_eq_norm]
      _ ≤ dist y q := hdist
      _ = Metric.infDist y s :=
        (infDist_eq_dist_metricProjection s hclosed hne y).symm

private lemma notMem_interior_cthickening_of_infDist_eq {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hclosed : IsClosed s) (hne : s.Nonempty)
    (hs : Convexity.IsConvexSet ℝ s) {t : ℝ} (ht : 0 < t)
    {x : EuclideanSpace ℝ (Fin d)} (hdist : Metric.infDist x s = t) :
    x ∉ interior (Metric.cthickening t s) := by
  intro hxint
  obtain ⟨rho, hrho, hball⟩ :=
    Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hxint)
  let p := metricProjection s hclosed hne x
  let a := 1 + rho / (2 * t)
  let y := p + a • (x - p)
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hrnorm : ‖x - p‖ = t := by
    calc
      ‖x - p‖ = dist x p := (dist_eq_norm x p).symm
      _ = Metric.infDist x s :=
        (infDist_eq_dist_metricProjection s hclosed hne x).symm
      _ = t := hdist
  have ha1 : 0 ≤ a - 1 := by
    dsimp [a]
    have : 0 ≤ rho / (2 * t) := (div_nonneg hrho.le (by positivity))
    linarith
  have hyx : dist y x = rho / 2 := by
    calc
      dist y x = dist (a • (x - p)) (x - p) := by
        have h := dist_add_left p (a • (x - p)) (x - p)
        have hpx : p + (x - p) = x := by abel
        rw [hpx] at h
        exact h
      _ = ‖a • (x - p) - (x - p)‖ := by rw [dist_eq_norm]
      _ = ‖(a - 1) • (x - p)‖ := by rw [sub_smul, one_smul]
      _ = (a - 1) * t := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha1, hrnorm]
      _ = rho / 2 := by
        dsimp [a]
        field_simp
        ring
  have hyball : y ∈ Metric.ball x rho := by
    rw [Metric.mem_ball, hyx]
    linarith
  have hyct : y ∈ Metric.cthickening t s := hball hyball
  have hyle : Metric.infDist y s ≤ t := ENNReal.toReal_le_of_le_ofReal ht.le hyct
  have hyray : Metric.infDist y s = a * Metric.infDist x s := by
    simpa only [p, y] using infDist_metricProjection_ray hclosed hne hs x ha
  rw [hyray, hdist] at hyle
  have hfrac : 0 < rho / (2 * t) := by positivity
  dsimp [a] at hyle
  nlinarith [mul_pos hfrac ht]

/-- A positive signed-distance level set is exactly the frontier of the corresponding closed
outer parallel set.  This is Raič (2019), Proposition 3.3's outer level-set identification. -/
lemma signedDistance_level_pos_eq_frontier_cthickening {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hne : s.Nonempty)
    (hs : Convexity.IsConvexSet ℝ s) {t : ℝ} (ht : 0 < t) :
    {x | setSignedDistance s x = t} = frontier (Metric.cthickening t (closure s)) := by
  ext x
  constructor
  · intro hx
    have hnot : x ∉ closure s := by
      intro hxs
      have hnonpos : setSignedDistance s x ≤ 0 := by
        rw [setSignedDistance, Metric.infDist_zero_of_mem_closure hxs, zero_sub]
        exact neg_nonpos.mpr Metric.infDist_nonneg
      rw [mem_setOf_eq] at hx
      rw [hx] at hnonpos
      linarith
    have hdist : Metric.infDist x (closure s) = t := by
      rw [Metric.infDist_closure]
      rw [mem_setOf_eq,
        setSignedDistance_eq_infDist_of_notMem (fun hxs ↦ hnot (subset_closure hxs))] at hx
      exact hx
    have hmem : x ∈ Metric.cthickening t (closure s) := by
      rw [Metric.cthickening, mem_setOf_eq,
        ENNReal.le_ofReal_iff_toReal_le (Metric.infEDist_ne_top hne.closure) ht.le]
      change Metric.infDist x (closure s) ≤ t
      exact hdist.le
    have hnotint : x ∉ interior (Metric.cthickening t (closure s)) :=
      notMem_interior_cthickening_of_infDist_eq isClosed_closure hne.closure
        (closure_isConvexSet hs) ht hdist
    exact ⟨subset_closure hmem, hnotint⟩
  · intro hx
    have hlevel := Metric.frontier_cthickening_subset (closure s) hx
    change Metric.infEDist x (closure s) = ENNReal.ofReal t at hlevel
    have hnot : x ∉ closure s := by
      intro hxs
      have hzero : Metric.infEDist x (closure s) = 0 := Metric.infEDist_zero_of_mem hxs
      rw [hzero] at hlevel
      exact (ENNReal.ofReal_pos.2 ht).ne' hlevel.symm
    rw [mem_setOf_eq,
      setSignedDistance_eq_infDist_of_notMem (fun hxs ↦ hnot (subset_closure hxs)),
      ← Metric.infDist_closure]
    change (Metric.infEDist x (closure s)).toReal = t
    rw [hlevel, ENNReal.toReal_ofReal ht.le]

private lemma notMem_interior_convexInnerParallel_of_infDist_eq {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hsne : s ≠ univ)
    {r : ℝ} (hr : 0 < r) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ s)
    (hdist : Metric.infDist x sᶜ = r) :
    x ∉ interior (convexInnerParallel s r) := by
  intro hxint
  obtain ⟨rho, hrho, hball⟩ :=
    Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hxint)
  obtain ⟨y, hyfront, hxy⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hsne
  let a := min (1 / 2 : ℝ) (rho / (2 * r))
  let z := x + a • (y - x)
  have ha : 0 < a := by
    dsimp [a]
    exact lt_min (by norm_num) (by positivity)
  have ha1 : a ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hanorm : ‖y - x‖ = r := by
    rw [norm_sub_rev, ← dist_eq_norm, ← hxy, hdist]
  have hax : dist x z = a * r := by
    calc
      dist x z = dist (x + 0) (x + a • (y - x)) := by simp [z]
      _ = dist 0 (a • (y - x)) := dist_add_left x 0 _
      _ = ‖a • (y - x)‖ := dist_zero_left _
      _ = a * r := by rw [norm_smul, Real.norm_of_nonneg ha.le, hanorm]
  have harho : a * r < rho := by
    have hle := mul_le_mul_of_nonneg_right
      (min_le_right (1 / 2 : ℝ) (rho / (2 * r))) hr.le
    have heq : (rho / (2 * r)) * r = rho / 2 := by
      field_simp
    rw [heq] at hle
    linarith
  have hzball : z ∈ Metric.ball x rho := by
    rw [Metric.mem_ball, dist_comm, hax]
    exact harho
  have hzinner : z ∈ convexInnerParallel s r := hball hzball
  have hzdist : Metric.infDist z sᶜ = (1 - a) * r := by
    simpa only [z, hdist] using
      infDist_compl_segment_to_frontier hyfront hxy ⟨ha.le, ha1⟩
  have hzlt : Metric.infDist z sᶜ < r := by
    rw [hzdist]
    nlinarith [mul_pos ha hr]
  have hcompne : sᶜ.Nonempty := nonempty_compl.2 hsne
  have hzthick : z ∈ Metric.thickening r sᶜ :=
    (Metric.mem_thickening_iff_infDist_lt hcompne).2 hzlt
  exact hzinner hzthick

/-- A negative signed-distance level set is exactly the frontier of the corresponding inner
parallel set.  This is Raič (2019), Proposition 3.3's inner level-set identification. -/
lemma signedDistance_level_neg_eq_frontier_innerParallel {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hsne : s ≠ univ)
    {t : ℝ} (ht : t < 0) :
    {x | setSignedDistance s x = t} = frontier (convexInnerParallel s (-t)) := by
  have hr : 0 < -t := neg_pos.mpr ht
  have hcompne : sᶜ.Nonempty := nonempty_compl.2 hsne
  ext x
  constructor
  · intro hx
    rw [mem_setOf_eq] at hx
    have hxs : x ∈ s := by
      by_contra hxs
      have hnonneg : 0 ≤ setSignedDistance s x := by
        rw [setSignedDistance_eq_infDist_of_notMem hxs]
        exact Metric.infDist_nonneg
      rw [hx] at hnonneg
      linarith
    have hdist : Metric.infDist x sᶜ = -t := by
      rw [setSignedDistance_eq_neg_infDist_compl_of_mem hxs] at hx
      linarith
    have hmem : x ∈ convexInnerParallel s (-t) := by
      have hnot : x ∉ Metric.thickening (-t) sᶜ := by
        rw [Metric.mem_thickening_iff_infDist_lt hcompne, hdist]
        exact lt_irrefl _
      exact hnot
    have hnotint : x ∉ interior (convexInnerParallel s (-t)) :=
      notMem_interior_convexInnerParallel_of_infDist_eq hsne hr hxs hdist
    exact ⟨subset_closure hmem, hnotint⟩
  · intro hx
    have hxthick : x ∈ frontier (Metric.thickening (-t) sᶜ) := by
      simpa only [convexInnerParallel, frontier_compl] using hx
    have hlevel := Metric.frontier_thickening_subset sᶜ hxthick
    change Metric.infEDist x sᶜ = ENNReal.ofReal (-t) at hlevel
    have hdist : Metric.infDist x sᶜ = -t := by
      change (Metric.infEDist x sᶜ).toReal = -t
      rw [hlevel, ENNReal.toReal_ofReal hr.le]
    have hxnot : x ∉ closure sᶜ :=
      (Metric.infDist_pos_iff_notMem_closure hcompne).2 (by rw [hdist]; exact hr)
    have hxint : x ∈ interior s := by
      rw [interior_eq_compl_closure_compl]
      exact hxnot
    rw [mem_setOf_eq,
      setSignedDistance_eq_neg_infDist_compl_of_mem (interior_subset hxint), hdist]
    ring

/-- The zero signed-distance fiber is exactly the frontier of a nonempty proper set. -/
lemma signedDistance_level_zero_eq_frontier {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hne : s.Nonempty) (hsne : s ≠ univ) :
    {x | setSignedDistance s x = 0} = frontier s := by
  have hcompne : sᶜ.Nonempty := nonempty_compl.2 hsne
  ext x
  constructor
  · intro hx
    rw [mem_setOf_eq, setSignedDistance] at hx
    by_cases hxs : x ∈ s
    · have hzero : Metric.infDist x sᶜ = 0 := by
        rw [Metric.infDist_zero_of_mem hxs, zero_sub] at hx
        linarith
      rw [frontier_eq_closure_inter_closure]
      exact ⟨subset_closure hxs, (Metric.mem_closure_iff_infDist_zero hcompne).2 hzero⟩
    · have hxcomp : x ∈ sᶜ := hxs
      have hzero : Metric.infDist x s = 0 := by
        rw [Metric.infDist_zero_of_mem hxcomp, sub_zero] at hx
        exact hx
      rw [frontier_eq_closure_inter_closure]
      exact ⟨(Metric.mem_closure_iff_infDist_zero hne).2 hzero, subset_closure hxcomp⟩
  · intro hx
    rw [frontier_eq_closure_inter_closure] at hx
    rw [mem_setOf_eq, setSignedDistance,
      Metric.infDist_zero_of_mem_closure hx.1,
      Metric.infDist_zero_of_mem_closure hx.2, sub_zero]

/-- For a nonempty set, the closed outer shell with its null boundary removed is exactly the
positive signed-distance slab `(0, ε]`. -/
lemma outerShell_closed_eq_signedDistance_preimage_Ioc {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hne : s.Nonempty)
    {ε : ℝ} (hε : 0 ≤ ε) :
    Metric.cthickening ε (closure s) \ closure s =
      setSignedDistance s ⁻¹' Ioc 0 ε := by
  ext x
  constructor
  · intro hx
    have hpos : 0 < Metric.infDist x (closure s) :=
      (isClosed_closure.notMem_iff_infDist_pos hne.closure).1 hx.2
    have hle : Metric.infDist x (closure s) ≤ ε :=
      ENNReal.toReal_le_of_le_ofReal hε hx.1
    rw [mem_preimage, mem_Ioc,
      setSignedDistance_eq_infDist_of_notMem (fun hxs ↦ hx.2 (subset_closure hxs)),
      ← Metric.infDist_closure]
    exact ⟨hpos, hle⟩
  · intro hx
    rw [mem_preimage, mem_Ioc] at hx
    have hnot : x ∉ closure s := by
      intro hxs
      have hnonpos : setSignedDistance s x ≤ 0 := by
        rw [setSignedDistance, Metric.infDist_zero_of_mem_closure hxs, zero_sub]
        exact neg_nonpos.mpr Metric.infDist_nonneg
      exact (not_lt_of_ge hnonpos) hx.1
    refine ⟨?_, hnot⟩
    rw [Metric.cthickening, mem_setOf_eq,
      ENNReal.le_ofReal_iff_toReal_le (Metric.infEDist_ne_top hne.closure) hε]
    change Metric.infDist x (closure s) ≤ ε
    rw [Metric.infDist_closure]
    rw [setSignedDistance_eq_infDist_of_notMem
      (fun hxs ↦ hnot (subset_closure hxs))] at hx
    exact hx.2

/-- For a proper set, the inner shell is exactly the part of the nonpositive signed-distance slab
which lies in the set.  The remaining points of the full slab are boundary points omitted by a
nonclosed set. -/
lemma innerShell_eq_inter_signedDistance_preimage_Ioc {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hsne : s ≠ univ) (ε : ℝ) :
    s \ convexInnerParallel s ε =
      s ∩ setSignedDistance s ⁻¹' Ioc (-ε) 0 := by
  have hcompne : sᶜ.Nonempty := nonempty_compl.2 hsne
  ext x
  constructor
  · intro hx
    have hthick : x ∈ Metric.thickening ε sᶜ := by
      simpa [convexInnerParallel] using hx.2
    have hdist : Metric.infDist x sᶜ < ε :=
      (Metric.mem_thickening_iff_infDist_lt hcompne).1 hthick
    refine ⟨hx.1, ?_⟩
    rw [mem_preimage, mem_Ioc,
      setSignedDistance_eq_neg_infDist_compl_of_mem hx.1]
    exact ⟨neg_lt_neg hdist, neg_nonpos.mpr Metric.infDist_nonneg⟩
  · intro hx
    have hsigned := hx.2
    rw [mem_preimage, mem_Ioc,
      setSignedDistance_eq_neg_infDist_compl_of_mem hx.1] at hsigned
    refine ⟨hx.1, ?_⟩
    have hthick : x ∈ Metric.thickening ε sᶜ :=
      (Metric.mem_thickening_iff_infDist_lt hcompne).2
        (neg_lt_neg_iff.mp hsigned.1)
    simpa [convexInnerParallel] using hthick

private lemma innerSignedSlab_sdiff_innerShell_subset_frontier {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hne : s.Nonempty) (hsne : s ≠ univ)
    (ε : ℝ) :
    setSignedDistance s ⁻¹' Ioc (-ε) 0 \ (s \ convexInnerParallel s ε) ⊆
      frontier s := by
  intro x hx
  have hxs : x ∉ s := by
    intro hxs
    have hinter : x ∈ s ∩ setSignedDistance s ⁻¹' Ioc (-ε) 0 := ⟨hxs, hx.1⟩
    apply hx.2
    rw [innerShell_eq_inter_signedDistance_preimage_Ioc hsne ε]
    exact hinter
  have hsigned : setSignedDistance s x = Metric.infDist x s :=
    setSignedDistance_eq_infDist_of_notMem hxs
  have hzero : Metric.infDist x s = 0 := by
    have hnonneg : 0 ≤ Metric.infDist x s := Metric.infDist_nonneg
    have hslab := hx.1
    rw [mem_preimage, mem_Ioc, hsigned] at hslab
    exact le_antisymm hslab.2 hnonneg
  have hxclosure : x ∈ closure s := (Metric.mem_closure_iff_infDist_zero hne).2 hzero
  exact ⟨hxclosure, fun hxi ↦ hxs (interior_subset hxi)⟩

/-- Replacing a convex set by its closure in the subtracted part of the outer shell does not
change standard-Gaussian mass, in every dimension. -/
lemma stdGaussian_outer_shell_eq_closed_shell {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : Convexity.IsConvexSet ℝ s) (ε : ℝ) :
    stdGaussian (EuclideanSpace ℝ (Fin d))
        (Metric.cthickening ε (closure s) \ s) =
      stdGaussian (EuclideanSpace ℝ (Fin d))
        (Metric.cthickening ε (closure s) \ closure s) := by
  apply (measure_eq_measure_of_null_sdiff ?_ ?_).symm
  · exact sdiff_subset_sdiff_right subset_closure
  · apply measure_mono_null _ (stdGaussian_frontier_eq_zero hs)
    intro x hx
    refine ⟨?_, fun hxi ↦ hx.1.2 (interior_subset hxi)⟩
    by_contra hxc
    exact hx.2 ⟨hx.1.1, hxc⟩

/-- The outer shell has exactly the standard-Gaussian mass of the positive signed-distance slab.
This is the set/measure input to Raič's coarea argument. -/
lemma stdGaussian_outer_shell_eq_signedDistance_slab {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hne : s.Nonempty)
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 ≤ ε) :
    stdGaussian (EuclideanSpace ℝ (Fin d))
        (Metric.cthickening ε (closure s) \ s) =
      stdGaussian (EuclideanSpace ℝ (Fin d))
        (setSignedDistance s ⁻¹' Ioc 0 ε) := by
  rw [stdGaussian_outer_shell_eq_closed_shell hs ε,
    outerShell_closed_eq_signedDistance_preimage_Ioc hne hε]

/-- The inner shell has exactly the standard-Gaussian mass of the nonpositive signed-distance
slab.  Boundary points added by passing from the shell to the full slab are Gaussian-null. -/
lemma stdGaussian_inner_shell_eq_signedDistance_slab {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hne : s.Nonempty) (hsne : s ≠ univ)
    (hs : Convexity.IsConvexSet ℝ s) (ε : ℝ) :
    stdGaussian (EuclideanSpace ℝ (Fin d))
        (s \ convexInnerParallel s ε) =
      stdGaussian (EuclideanSpace ℝ (Fin d))
        (setSignedDistance s ⁻¹' Ioc (-ε) 0) := by
  apply measure_eq_measure_of_null_sdiff
  · rw [innerShell_eq_inter_signedDistance_preimage_Ioc hsne ε]
    exact inter_subset_right
  · apply measure_mono_null
      (innerSignedSlab_sdiff_innerShell_subset_frontier hne hsne ε)
    exact stdGaussian_frontier_eq_zero hs

/-- The standard Gaussian density used in Ball's boundary integral, written in a form convenient
for finite-dimensional Lean proofs. -/
def standardGaussianDensityReal {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (√(2 * Real.pi))⁻¹ ^ d * Real.exp (-‖x‖ ^ 2 / 2)

/-- Ball's coordinate formula is definitionally the same density as the finite-dimensional
normalization used by the Bentkus derivative and integration-by-parts modules. -/
lemma standardGaussianDensityReal_eq_standardGaussianDensity {d : ℕ}
    (x : EuclideanSpace ℝ (Fin d)) :
    standardGaussianDensityReal x =
      standardGaussianDensity (EuclideanSpace ℝ (Fin d)) x := by
  unfold standardGaussianDensityReal standardGaussianDensity
    standardGaussianDensityNormalization
  rw [finrank_euclideanSpace]
  simp only [Fintype.card_fin]
  congr 1
  rw [inv_pow, ← Real.rpow_natCast, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (by positivity : 0 ≤ 2 * Real.pi),
    Real.rpow_def_of_pos (by positivity : 0 < 2 * Real.pi), ← Real.exp_neg]
  congr 1
  ring

lemma standardGaussianDensityReal_nonneg {d : ℕ}
    (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ standardGaussianDensityReal x := by
  unfold standardGaussianDensityReal
  positivity

lemma continuous_standardGaussianDensityReal {d : ℕ} :
    Continuous (standardGaussianDensityReal (d := d)) := by
  unfold standardGaussianDensityReal
  fun_prop

lemma measurable_standardGaussianDensityReal {d : ℕ} :
    Measurable (standardGaussianDensityReal (d := d)) :=
  continuous_standardGaussianDensityReal.measurable

/-- The radial density is the product of the one-dimensional standard-Gaussian densities in
Euclidean coordinates. -/
lemma prod_gaussianPDFReal_zero_one_eq_standardGaussianDensityReal {d : ℕ}
    (x : EuclideanSpace ℝ (Fin d)) :
    (∏ i : Fin d, gaussianPDFReal 0 1 (x i)) = standardGaussianDensityReal x := by
  have hpdf (z : ℝ) : gaussianPDFReal 0 1 z =
      (√(2 * Real.pi))⁻¹ * Real.exp (-z ^ 2 / 2) := by
    rw [gaussianPDFReal]
    norm_num
  simp_rw [hpdf]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Real.exp_sum]
  unfold standardGaussianDensityReal
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq, ← Finset.sum_neg_distrib, Finset.sum_div]

private lemma map_withDensity_measurableEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (g : β → ℝ≥0∞) (hg : Measurable g) :
    (μ.withDensity (g ∘ e)).map e = (μ.map e).withDensity g := by
  ext u hu
  rw [e.map_apply, withDensity_apply _ (e.measurable hu), withDensity_apply _ hu]
  rw [← lintegral_indicator (e.measurable hu), ← lintegral_indicator hu]
  rw [lintegral_map (hg.indicator hu) e.measurable]
  apply lintegral_congr
  intro x
  rfl

private def gaussianProductDensity (d : ℕ) (x : Fin d → ℝ) : ℝ≥0∞ :=
  ∏ i, gaussianPDF 0 1 (x i)

private lemma measurable_gaussianProductDensity (d : ℕ) :
    Measurable (gaussianProductDensity d) := by
  apply Finset.measurable_prod
  intro i _hi
  exact (measurable_gaussianPDF 0 1).comp (measurable_pi_apply i)

private lemma piGaussian_eq_withDensity : ∀ d : ℕ,
    Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1) =
      volume.withDensity (gaussianProductDensity d)
  | 0 => by
      rw [Measure.pi_of_empty]
      ext u hu
      rcases u.eq_empty_or_singleton_of_subsingleton with rfl | ⟨x, rfl⟩
      · simp
      · rw [Subsingleton.eq_univ_of_nonempty (singleton_nonempty x)]
        simp [gaussianProductDensity, volume_pi]
  | d + 1 => by
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) ↦ ℝ) (0 : Fin (d + 1))
      have hGaussian := measurePreserving_piFinSuccAbove
        (fun _ : Fin (d + 1) ↦ gaussianReal 0 1) (0 : Fin (d + 1))
      have hVolume := volume_preserving_piFinSuccAbove
        (fun _ : Fin (d + 1) ↦ ℝ) (0 : Fin (d + 1))
      rw [← (MeasurePreserving.symm e hGaussian).map_eq]
      rw [piGaussian_eq_withDensity d, gaussianReal_of_var_ne_zero 0 one_ne_zero,
        prod_withDensity (measurable_gaussianPDF 0 1)
          (measurable_gaussianProductDensity d)]
      have hdensity :
          (fun z : ℝ × (Fin d → ℝ) ↦
            gaussianPDF 0 1 z.1 * gaussianProductDensity d z.2) =
          gaussianProductDensity (d + 1) ∘ e.symm := by
        funext z
        change gaussianPDF 0 1 z.1 * ∏ i : Fin d, gaussianPDF 0 1 (z.2 i) =
          ∏ i : Fin (d + 1), gaussianPDF 0 1 (e.symm z i)
        rw [Fin.prod_univ_succAbove _ 0]
        simp [e]
      rw [hdensity, map_withDensity_measurableEquiv e.symm]
      · rw [← Measure.volume_eq_prod, (MeasurePreserving.symm e hVolume).map_eq]
      · exact measurable_gaussianProductDensity (d + 1)

private lemma gaussianProductDensity_eq_standardGaussianDensityReal {d : ℕ}
    (x : Fin d → ℝ) :
    gaussianProductDensity d x =
      ENNReal.ofReal (standardGaussianDensityReal (WithLp.toLp 2 x)) := by
  unfold gaussianProductDensity
  simp_rw [gaussianPDF_def]
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · congr 1
    simpa using prod_gaussianPDFReal_zero_one_eq_standardGaussianDensityReal
      (WithLp.toLp 2 x)
  · intro i _hi
    exact gaussianPDFReal_nonneg 0 1 (x i)

private def toLpMeasurableEquiv (d : ℕ) :
    (Fin d → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin d) :=
  MeasurableEquiv.mk ((WithLp.equiv 2 (Fin d → ℝ)).symm)
    (WithLp.measurable_toLp 2 (Fin d → ℝ))
    (WithLp.measurable_ofLp 2 (Fin d → ℝ))

/-- Standard Gaussian measure is Euclidean volume weighted by Ball's radial density.  This is the
measure-theoretic density bridge required before applying coarea to signed distance. -/
theorem stdGaussian_eq_withDensity_standardGaussianDensityReal {d : ℕ} :
    stdGaussian (EuclideanSpace ℝ (Fin d)) =
      volume.withDensity
        (fun x ↦ ENNReal.ofReal (standardGaussianDensityReal x)) := by
  rw [← map_pi_eq_stdGaussian, piGaussian_eq_withDensity d]
  let e := toLpMeasurableEquiv d
  have he : (e : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) = WithLp.toLp 2 := rfl
  have hdensity : gaussianProductDensity d =
      (fun x : EuclideanSpace ℝ (Fin d) ↦
        ENNReal.ofReal (standardGaussianDensityReal x)) ∘ e := by
    funext x
    exact gaussianProductDensity_eq_standardGaussianDensityReal x
  rw [show WithLp.toLp 2 = (e : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) from he.symm,
    hdensity, map_withDensity_measurableEquiv e]
  · rw [he, (PiLp.volume_preserving_toLp (Fin d)).map_eq]
  · exact measurable_standardGaussianDensityReal.ennreal_ofReal

/-- Ball's radial density is normalized to total mass one in every Euclidean dimension. -/
lemma lintegral_standardGaussianDensityReal_eq_one {d : ℕ} :
    ∫⁻ x : EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal (standardGaussianDensityReal x) = 1 := by
  have h := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin d)) ↦ μ univ)
    (stdGaussian_eq_withDensity_standardGaussianDensityReal (d := d))
  simpa [withDensity_apply] using h.symm

private def radialGaussianDensity {E : Type*} [NormedAddCommGroup E]
    (n : ℕ) (x : E) : ℝ :=
  (√(2 * Real.pi))⁻¹ ^ n * Real.exp (-‖x‖ ^ 2 / 2)

private lemma measurable_radialGaussianDensity
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (n : ℕ) : Measurable (radialGaussianDensity (E := E) n) := by
  unfold radialGaussianDensity
  fun_prop

private lemma lintegral_radialGaussianDensity_finrank_eq_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] :
    ∫⁻ x : E, ENNReal.ofReal (radialGaussianDensity (Module.finrank ℝ E) x) = 1 := by
  let b := stdOrthonormalBasis ℝ E
  have hcomp :
      (fun x : E ↦ ENNReal.ofReal (radialGaussianDensity (Module.finrank ℝ E) x)) =
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ↦
        ENNReal.ofReal (standardGaussianDensityReal y)) ∘ b.repr := by
    funext x
    unfold radialGaussianDensity standardGaussianDensityReal
    change ENNReal.ofReal
      ((√(2 * Real.pi))⁻¹ ^ Module.finrank ℝ E * Real.exp (-‖x‖ ^ 2 / 2)) =
      ENNReal.ofReal
        ((√(2 * Real.pi))⁻¹ ^ Module.finrank ℝ E * Real.exp (-‖b.repr x‖ ^ 2 / 2))
    rw [b.repr.norm_map]
  rw [hcomp]
  change ∫⁻ x : E,
    ENNReal.ofReal (standardGaussianDensityReal (b.repr x)) = 1
  calc
    _ = ∫⁻ y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
        ENNReal.ofReal (standardGaussianDensityReal y) :=
      b.repr.measurePreserving.lintegral_comp
        measurable_standardGaussianDensityReal.ennreal_ofReal
    _ = 1 := lintegral_standardGaussianDensityReal_eq_one

/-- Exact codimension-one affine slicing of Euclidean volume.  This is the affine base case of
the coarea cluster: the parameter `x` runs along `v`, while the fiber is the perpendicular affine
hyperplane through `x • v + p`.  The normalization uses Mathlib's Euclidean Hausdorff measure, so
top-dimensional measure is exactly `volume` and no dimension-dependent scale factor is hidden. -/
theorem euclideanVolume_eq_lintegral_codimOneSections {d : ℕ}
    (p v : EuclideanSpace ℝ (Fin d)) (hv : v ≠ 0)
    {t : Set (EuclideanSpace ℝ (Fin d))} (ht : MeasurableSet t) :
    volume t = ‖v‖ₑ * ∫⁻ (x : ℝ),
      Measure.euclideanHausdorffMeasure (d - 1)
        (t ∩ AffineSubspace.mk' (x • v + p) (ℝ ∙ v)ᗮ) := by
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume d]
  simpa using EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral p hv ht

private def affineSectionMap {d : ℕ}
    (p v : EuclideanSpace ℝ (Fin d)) (x : ℝ) :
    (ℝ ∙ v)ᗮ → EuclideanSpace ℝ (Fin d) :=
  fun z ↦ z.1 + (x • v + p)

private def affineSectionMeasure {d : ℕ}
    (p v : EuclideanSpace ℝ (Fin d)) (x : ℝ) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  volume.map (affineSectionMap p v x)

private lemma isometry_affineSectionMap {d : ℕ}
    (p v : EuclideanSpace ℝ (Fin d)) (x : ℝ) :
    Isometry (affineSectionMap p v x) := by
  rw [isometry_iff_dist_eq]
  intro z w
  rw [dist_eq_norm, dist_eq_norm]
  change ‖(z.1 + (x • v + p)) - (w.1 + (x • v + p))‖ = ‖z - w‖
  rw [add_sub_add_right_eq_sub]
  rfl

private lemma finrank_orthogonal_span_singleton {d : ℕ}
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    Module.finrank ℝ (ℝ ∙ v)ᗮ = d - 1 := by
  have hspan : Module.finrank ℝ (ℝ ∙ v) = 1 := finrank_span_singleton hv
  have hsum := (ℝ ∙ v).finrank_add_finrank_orthogonal
  rw [hspan] at hsum
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hsum
  omega

private lemma affineSectionMeasure_eq_restrict_euclideanHausdorff {d : ℕ}
    (p : EuclideanSpace ℝ (Fin d)) {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0)
    (x : ℝ) :
    affineSectionMeasure p v x =
      (Measure.euclideanHausdorffMeasure (d - 1)).restrict
        (AffineSubspace.mk' (x • v + p) (ℝ ∙ v)ᗮ) := by
  have hrank := finrank_orthogonal_span_singleton (d := d) hv
  have himage : Set.range (affineSectionMap p v x) =
      (AffineSubspace.mk' (x • v + p) (ℝ ∙ v)ᗮ : Set _) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      change z.1 + (x • v + p) - (x • v + p) ∈ (ℝ ∙ v)ᗮ
      simpa only [add_sub_cancel_right] using z.2
    · intro hy
      change y - (x • v + p) ∈ (ℝ ∙ v)ᗮ at hy
      refine ⟨⟨y - (x • v + p), hy⟩, ?_⟩
      change y - (x • v + p) + (x • v + p) = y
      abel
  unfold affineSectionMeasure
  rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  rw [hrank]
  rw [(isometry_affineSectionMap p v x).map_euclideanHausdorffMeasure]
  rw [himage]

/-- Integration over a codimension-one affine hyperplane is integration over its orthogonal
direction after translation.  This is the weighted transport form of the affine section
identification and is reusable independently of Gaussian weights. -/
theorem lintegral_affineHyperplane_eq_lintegral_orthogonal {d : ℕ}
    (p : EuclideanSpace ℝ (Fin d)) {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0)
    (x : ℝ) (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ y in (AffineSubspace.mk' (x • v + p) (ℝ ∙ v)ᗮ :
        Set (EuclideanSpace ℝ (Fin d))), w y
        ∂(Measure.euclideanHausdorffMeasure (d - 1))) =
      ∫⁻ z : (ℝ ∙ v)ᗮ, w (z.1 + (x • v + p)) := by
  rw [← affineSectionMeasure_eq_restrict_euclideanHausdorff p hv x]
  unfold affineSectionMeasure
  rw [lintegral_map hw (isometry_affineSectionMap p v x).continuous.measurable]
  rfl

/-- The Gaussian surface integral over an affine hyperplane perpendicular to a unit vector is
the one-dimensional standard-Gaussian density at its signed offset. -/
lemma standardGaussianDensity_affineHyperplane {n : ℕ}
    (u : EuclideanSpace ℝ (Fin (n + 1))) (hu : ‖u‖ = 1) (a : ℝ) :
    ∫⁻ y in (AffineSubspace.mk' (a • u) (ℝ ∙ u)ᗮ :
        Set (EuclideanSpace ℝ (Fin (n + 1)))),
        ENNReal.ofReal (standardGaussianDensityReal y)
          ∂(Measure.euclideanHausdorffMeasure n) =
      ENNReal.ofReal (gaussianPDFReal 0 1 a) := by
  have hu0 : u ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hu
    norm_num at hu
  let W := (ℝ ∙ u)ᗮ
  have hrank : Module.finrank ℝ W = n := by
    simpa [W] using finrank_orthogonal_span_singleton (d := n + 1) hu0
  have hmap := affineSectionMeasure_eq_restrict_euclideanHausdorff
    (d := n + 1) (0 : EuclideanSpace ℝ (Fin (n + 1))) hu0 a
  simp only [add_zero, Nat.add_sub_cancel] at hmap
  rw [← hmap]
  unfold affineSectionMeasure
  have hsectionMeasurable : Measurable
      (affineSectionMap (0 : EuclideanSpace ℝ (Fin (n + 1))) u a) :=
    (isometry_affineSectionMap (0 : EuclideanSpace ℝ (Fin (n + 1))) u a).continuous.measurable
  rw [lintegral_map measurable_standardGaussianDensityReal.ennreal_ofReal
    hsectionMeasurable]
  have hfactor (z : W) :
      ENNReal.ofReal (standardGaussianDensityReal
        (affineSectionMap (0 : EuclideanSpace ℝ (Fin (n + 1))) u a z)) =
        ENNReal.ofReal (gaussianPDFReal 0 1 a) *
          ENNReal.ofReal (radialGaussianDensity n z) := by
    have hzorth : inner ℝ z.1 u = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.mp z.2
    have hnorm : ‖(z.1 : EuclideanSpace ℝ (Fin (n + 1))) + a • u‖ ^ 2 =
        ‖z‖ ^ 2 + a ^ 2 := by
      rw [norm_add_sq_real, real_inner_smul_right, hzorth, mul_zero, mul_zero, add_zero,
        norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs]
      rfl
    have hexp : -(‖z‖ ^ 2 + a ^ 2) / 2 = -a ^ 2 / 2 + -‖z‖ ^ 2 / 2 := by ring
    have hreal : standardGaussianDensityReal
        (affineSectionMap (0 : EuclideanSpace ℝ (Fin (n + 1))) u a z) =
        gaussianPDFReal 0 1 a * radialGaussianDensity n z := by
      unfold affineSectionMap standardGaussianDensityReal radialGaussianDensity
      rw [add_zero, hnorm, hexp, Real.exp_add, pow_succ']
      rw [gaussianPDFReal]
      norm_num
      ring
    rw [hreal, ENNReal.ofReal_mul
      (gaussianPDFReal_nonneg 0 1 a)]
  simp_rw [hfactor]
  rw [lintegral_const_mul _
    (measurable_radialGaussianDensity (E := W) n).ennreal_ofReal]
  have hnormW : ∫⁻ z : W,
      ENNReal.ofReal (radialGaussianDensity n z) = 1 := by
    have h := lintegral_radialGaussianDensity_finrank_eq_one (E := W)
    simpa only [hrank] using h
  rw [hnormW, mul_one]

private lemma affineHyperplane_add_base_eq {n : ℕ}
    (p u : EuclideanSpace ℝ (Fin (n + 1))) (hu : ‖u‖ = 1) (t : ℝ) :
    (AffineSubspace.mk' (t • u + p) (ℝ ∙ u)ᗮ :
        Set (EuclideanSpace ℝ (Fin (n + 1)))) =
      (AffineSubspace.mk' ((t + inner ℝ p u) • u) (ℝ ∙ u)ᗮ :
        Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  ext y
  constructor <;> intro hy
  · apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
    have h := Submodule.mem_orthogonal_singleton_iff_inner_left.mp hy
    change inner ℝ (y - (t • u + p)) u = 0 at h
    change inner ℝ (y - (t + inner ℝ p u) • u) u = 0
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hu, one_pow, mul_one] at h ⊢
    linarith
  · apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
    have h := Submodule.mem_orthogonal_singleton_iff_inner_left.mp hy
    change inner ℝ (y - (t + inner ℝ p u) • u) u = 0 at h
    change inner ℝ (y - (t • u + p)) u = 0
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hu, one_pow, mul_one] at h ⊢
    linarith

/-- Translating an affine hyperplane tangentially does not change it; its Gaussian surface
integral depends only on the signed normal offset. -/
lemma standardGaussianDensity_affineHyperplane_add_base {n : ℕ}
    (p u : EuclideanSpace ℝ (Fin (n + 1))) (hu : ‖u‖ = 1) (t : ℝ) :
    ∫⁻ y in (AffineSubspace.mk' (t • u + p) (ℝ ∙ u)ᗮ :
        Set (EuclideanSpace ℝ (Fin (n + 1)))),
        ENNReal.ofReal (standardGaussianDensityReal y)
          ∂(Measure.euclideanHausdorffMeasure n) =
      ENNReal.ofReal (gaussianPDFReal 0 1 (t + inner ℝ p u)) := by
  rw [affineHyperplane_add_base_eq p u hu t]
  exact standardGaussianDensity_affineHyperplane u hu _

/-- Every affine hyperplane has standard-Gaussian surface content at most one. -/
lemma standardGaussianDensity_affineHyperplane_le_one {n : ℕ}
    (u : EuclideanSpace ℝ (Fin (n + 1))) (hu : ‖u‖ = 1) (a : ℝ) :
    ∫⁻ y in (AffineSubspace.mk' (a • u) (ℝ ∙ u)ᗮ :
        Set (EuclideanSpace ℝ (Fin (n + 1)))),
        ENNReal.ofReal (standardGaussianDensityReal y)
          ∂(Measure.euclideanHausdorffMeasure n) ≤ 1 := by
  rw [standardGaussianDensity_affineHyperplane u hu a]
  simpa [gaussianPDF_def] using gaussianPDF_zero_one_le_one a

private lemma measurable_affineSectionMeasure {d : ℕ}
    (p v : EuclideanSpace ℝ (Fin d)) :
    Measurable (affineSectionMeasure p v) := by
  refine Measure.measurable_of_measurable_coe _ ?_
  intro t ht
  have hmap (x : ℝ) :
      affineSectionMeasure p v x t =
        volume ((affineSectionMap p v x) ⁻¹' t) := by
    rw [affineSectionMeasure, Measure.map_apply
      (isometry_affineSectionMap p v x).continuous.measurable ht]
  simp_rw [hmap]
  let T : Set (ℝ × (ℝ ∙ v)ᗮ) :=
    {z | affineSectionMap p v z.1 z.2 ∈ t}
  have hT : MeasurableSet T := by
    apply ht.preimage
    dsimp [T, affineSectionMap]
    fun_prop
  have heq (x : ℝ) :
      volume ((affineSectionMap p v x) ⁻¹' t) =
        volume (Prod.mk x ⁻¹' T) := by rfl
  simp_rw [heq]
  exact measurable_measure_prodMk_left hT

private lemma smul_bind_affineSectionMeasure_eq_volume {d : ℕ}
    (p : EuclideanSpace ℝ (Fin d)) {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    ‖v‖ₑ • (volume.bind (affineSectionMeasure p v)) = volume := by
  ext t ht
  rw [Measure.smul_apply, Measure.bind_apply ht
    (measurable_affineSectionMeasure p v).aemeasurable, smul_eq_mul]
  simp_rw [affineSectionMeasure_eq_restrict_euclideanHausdorff p hv]
  rw [euclideanVolume_eq_lintegral_codimOneSections p v hv ht]
  congr 2 with x
  rw [Measure.restrict_apply ht]

/-- Weighted affine codimension-one coarea.  This strengthens the set-slicing identity to every
nonnegative measurable density by constructing the measurable family of Euclidean surface
measures on parallel fibers and integrating it with the Giry bind operation. -/
theorem lintegral_eq_lintegral_codimOneSections {d : ℕ}
    (p : EuclideanSpace ℝ (Fin d)) {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0)
    (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hw : Measurable w) :
    ∫⁻ y, w y ∂volume = ‖v‖ₑ * ∫⁻ (x : ℝ),
      ∫⁻ y in AffineSubspace.mk' (x • v + p) (ℝ ∙ v)ᗮ, w y
        ∂(Measure.euclideanHausdorffMeasure (d - 1)) := by
  rw [← smul_bind_affineSectionMeasure_eq_volume p hv]
  rw [lintegral_smul_measure, smul_eq_mul]
  rw [Measure.lintegral_bind (measurable_affineSectionMeasure p v).aemeasurable
    hw.aemeasurable]
  congr 2 with x
  rw [affineSectionMeasure_eq_restrict_euclideanHausdorff p hv]

private lemma inner_sub_eq_of_mem_affineHyperplane {d : ℕ}
    {p u y : EuclideanSpace ℝ (Fin d)} {t : ℝ} (hu : ‖u‖ = 1)
    (hy : y ∈ AffineSubspace.mk' (t • u + p) (ℝ ∙ u)ᗮ) :
    inner ℝ (y - p) u = t := by
  have hz : inner ℝ (y - (t • u + p)) u = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp hy
  have hdecomp : y - p = (y - (t • u + p)) + t • u := by abel
  rw [hdecomp, inner_add_left, hz, zero_add, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hu]
  ring

/-- Coarea for a slab cut out by a unit affine signed coordinate.  This is the exact
signed-distance formula for an affine hyperplane and the piecewise-affine base case needed by a
polyhedral approximation of the nonlinear signed-distance formula. -/
theorem lintegral_affineSignedCoordinate_slab {d : ℕ}
    (p u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1)
    (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hw : Measurable w) (a b : ℝ) :
    ∫⁻ y in {y | inner ℝ (y - p) u ∈ Ioc a b}, w y ∂volume =
      ∫⁻ t in Ioc a b,
        ∫⁻ y in AffineSubspace.mk' (t • u + p) (ℝ ∙ u)ᗮ, w y
          ∂(Measure.euclideanHausdorffMeasure (d - 1)) := by
  have hu0 : u ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hu
    norm_num at hu
  let slab : Set (EuclideanSpace ℝ (Fin d)) :=
    {y | inner ℝ (y - p) u ∈ Ioc a b}
  have hslab : MeasurableSet slab := by
    apply measurableSet_Ioc.preimage
    fun_prop
  let fiber : ℝ → ℝ≥0∞ := fun t ↦
    ∫⁻ y in AffineSubspace.mk' (t • u + p) (ℝ ∙ u)ᗮ, w y
      ∂(Measure.euclideanHausdorffMeasure (d - 1))
  have hfiber_measurable : Measurable fiber := by
    have h := (Measure.measurable_lintegral hw).comp
      (measurable_affineSectionMeasure p u)
    convert h using 1
    funext t
    simp only [fiber, Function.comp_apply]
    rw [affineSectionMeasure_eq_restrict_euclideanHausdorff p hu0]
  have hfiber (t : ℝ) :
      ∫⁻ y in AffineSubspace.mk' (t • u + p) (ℝ ∙ u)ᗮ,
          slab.indicator w y
          ∂(Measure.euclideanHausdorffMeasure (d - 1)) =
        (Ioc a b).indicator fiber t := by
    let H : Set (EuclideanSpace ℝ (Fin d)) :=
      AffineSubspace.mk' (t • u + p) (ℝ ∙ u)ᗮ
    have hH : MeasurableSet H :=
      (AffineSubspace.mk' (t • u + p) (ℝ ∙ u)ᗮ).closed_of_finiteDimensional.measurableSet
    by_cases ht : t ∈ Ioc a b
    · rw [indicator_of_mem ht]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hH] with y hy
      have hyslab : y ∈ slab := by
        change inner ℝ (y - p) u ∈ Ioc a b
        rw [inner_sub_eq_of_mem_affineHyperplane hu hy]
        exact ht
      rw [indicator_of_mem hyslab]
    · rw [indicator_of_notMem ht]
      calc
        (∫⁻ y in H, slab.indicator w y
            ∂(Measure.euclideanHausdorffMeasure (d - 1))) =
            ∫⁻ _y in H, 0 ∂(Measure.euclideanHausdorffMeasure (d - 1)) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem hH] with y hy
          have hyslab : y ∉ slab := by
            change inner ℝ (y - p) u ∉ Ioc a b
            rw [inner_sub_eq_of_mem_affineHyperplane hu hy]
            exact ht
          rw [indicator_of_notMem hyslab]
        _ = 0 := by simp
  rw [← lintegral_indicator hslab]
  rw [lintegral_eq_lintegral_codimOneSections p hu0 (slab.indicator w)
    (hw.indicator hslab)]
  have henorm : ‖u‖ₑ = 1 := by
    rw [← ofReal_norm, hu]
    norm_num
  rw [henorm, one_mul]
  simp_rw [hfiber]
  rw [lintegral_indicator measurableSet_Ioc]

/-- A standard Gaussian affine signed coordinate is exactly a shifted one-dimensional standard
Gaussian.  This is the complete Gaussian shell formula for affine halfspaces. -/
theorem stdGaussian_affineSignedCoordinate_slab {n : ℕ}
    (p u : EuclideanSpace ℝ (Fin (n + 1))) (hu : ‖u‖ = 1) (a b : ℝ) :
    stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))
        {y | inner ℝ (y - p) u ∈ Ioc a b} =
      ∫⁻ t in Ioc a b,
        ENNReal.ofReal (gaussianPDFReal 0 1 (t + inner ℝ p u)) := by
  have hslab : MeasurableSet
      {y : EuclideanSpace ℝ (Fin (n + 1)) | inner ℝ (y - p) u ∈ Ioc a b} := by
    apply measurableSet_Ioc.preimage
    fun_prop
  rw [stdGaussian_eq_withDensity_standardGaussianDensityReal,
    withDensity_apply _ hslab]
  rw [lintegral_affineSignedCoordinate_slab p u hu
    (fun y ↦ ENNReal.ofReal (standardGaussianDensityReal y))
    measurable_standardGaussianDensityReal.ennreal_ofReal a b]
  simp_rw [Nat.add_sub_cancel,
    standardGaussianDensity_affineHyperplane_add_base p u hu]

/-- Affine signed coordinates satisfy a dimension-free Gaussian anti-concentration bound with
constant one. -/
theorem stdGaussian_affineSignedCoordinate_slab_le_length {n : ℕ}
    (p u : EuclideanSpace ℝ (Fin (n + 1))) (hu : ‖u‖ = 1) (a b : ℝ) :
    stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))
        {y | inner ℝ (y - p) u ∈ Ioc a b} ≤ ENNReal.ofReal (b - a) := by
  rw [stdGaussian_affineSignedCoordinate_slab p u hu a b]
  calc
    (∫⁻ t in Ioc a b,
        ENNReal.ofReal (gaussianPDFReal 0 1 (t + inner ℝ p u))) ≤
        ∫⁻ _t in Ioc a b, 1 := by
      apply lintegral_mono
      intro t
      simpa [gaussianPDF_def] using
        gaussianPDF_zero_one_le_one (t + inner ℝ p u)
    _ = volume (Ioc a b) := by simp
    _ = ENNReal.ofReal (b - a) := Real.volume_Ioc

/-- Standard Gaussian mass disintegrates exactly into Gaussian-weighted Euclidean surface
integrals over any family of parallel affine hyperplanes. -/
theorem stdGaussian_apply_eq_lintegral_codimOneSections {d : ℕ}
    (p : EuclideanSpace ℝ (Fin d)) {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0)
    {t : Set (EuclideanSpace ℝ (Fin d))} (ht : MeasurableSet t) :
    stdGaussian (EuclideanSpace ℝ (Fin d)) t = ‖v‖ₑ * ∫⁻ (x : ℝ),
      ∫⁻ y in t ∩ AffineSubspace.mk' (x • v + p) (ℝ ∙ v)ᗮ,
        ENNReal.ofReal (standardGaussianDensityReal y)
          ∂(Measure.euclideanHausdorffMeasure (d - 1)) := by
  rw [stdGaussian_eq_withDensity_standardGaussianDensityReal, withDensity_apply _ ht]
  rw [← lintegral_indicator ht]
  rw [lintegral_eq_lintegral_codimOneSections p hv
    (t.indicator fun y ↦ ENNReal.ofReal (standardGaussianDensityReal y))
    (measurable_standardGaussianDensityReal.ennreal_ofReal.indicator ht)]
  congr 2 with x
  rw [lintegral_indicator ht]
  rw [Measure.restrict_restrict ht]

/-- The Gaussian-weighted codimension-one Hausdorff content of a frontier.  Ball's Theorem 4 is
the bound `standardGaussianBoundaryContent s ≤ 4 * d^(1/4)` for convex bodies in dimension at
least two. -/
def standardGaussianBoundaryContent {d : ℕ}
    (s : Set (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ∫⁻ x in frontier s, ENNReal.ofReal (standardGaussianDensityReal x)
    ∂(Measure.euclideanHausdorffMeasure (d - 1))

/-- The outer parallel-frontier profile occurring in Raič's coarea formula. -/
def outerGaussianBoundaryProfile {d : ℕ}
    (s : Set (EuclideanSpace ℝ (Fin d))) (t : ℝ) : ℝ≥0∞ :=
  standardGaussianBoundaryContent (Metric.cthickening t (closure s))

/-- The inner parallel-frontier profile occurring in Raič's coarea formula. -/
def innerGaussianBoundaryProfile {d : ℕ}
    (s : Set (EuclideanSpace ℝ (Fin d))) (t : ℝ) : ℝ≥0∞ :=
  standardGaussianBoundaryContent (convexInnerParallel s (-t))

/-- At a positive level, the outer boundary profile is the Gaussian-weighted Hausdorff integral
over the corresponding signed-distance fiber. -/
lemma outerGaussianBoundaryProfile_eq_levelLIntegral {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hne : s.Nonempty)
    (hs : Convexity.IsConvexSet ℝ s) {t : ℝ} (ht : 0 < t) :
    outerGaussianBoundaryProfile s t =
      ∫⁻ x in {x | setSignedDistance s x = t},
        ENNReal.ofReal (standardGaussianDensityReal x)
        ∂(Measure.euclideanHausdorffMeasure (d - 1)) := by
  rw [outerGaussianBoundaryProfile, standardGaussianBoundaryContent,
    signedDistance_level_pos_eq_frontier_cthickening hne hs ht]

/-- At a negative level, the inner boundary profile is the Gaussian-weighted Hausdorff integral
over the corresponding signed-distance fiber. -/
lemma innerGaussianBoundaryProfile_eq_levelLIntegral {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hsne : s ≠ univ)
    {t : ℝ} (ht : t < 0) :
    innerGaussianBoundaryProfile s t =
      ∫⁻ x in {x | setSignedDistance s x = t},
        ENNReal.ofReal (standardGaussianDensityReal x)
        ∂(Measure.euclideanHausdorffMeasure (d - 1)) := by
  rw [innerGaussianBoundaryProfile, standardGaussianBoundaryContent,
    signedDistance_level_neg_eq_frontier_innerParallel hsne ht]

private abbrev E1 := EuclideanSpace ℝ (Fin 1)

private abbrev coord (x : E1) : ℝ := x 0

private lemma coord_dist_eq (x y : E1) : dist (coord x) (coord y) = dist x y := by
  rw [PiLp.dist_eq_of_L2]
  simp only [Fin.sum_univ_one]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg]

private lemma coord_isometry : Isometry coord :=
  Isometry.of_dist_eq fun x y ↦ coord_dist_eq x y

private def coordMeasurableEquiv : E1 ≃ᵐ ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans
    (MeasurableEquiv.piUnique fun _ : Fin 1 ↦ ℝ)

private lemma coordMeasurableEquiv_apply (x : E1) : coordMeasurableEquiv x = coord x := by
  rfl

private lemma coord_measurePreserving : MeasurePreserving coord := by
  have h := (volume_preserving_piUnique fun _ : Fin 1 ↦ ℝ).comp
    (PiLp.volume_preserving_ofLp (Fin 1))
  exact h

private lemma volume_le_ediam_finOne (s : Set E1) : volume s ≤ Metric.ediam s := by
  let e := coordMeasurableEquiv
  have heq : (e : E1 → ℝ) = coord := by
    funext x
    exact coordMeasurableEquiv_apply x
  have hmap : volume.map e = volume := by
    simpa only [heq] using coord_measurePreserving.map_eq
  calc
    volume s = (volume.map e) (e '' s) := by
      rw [e.map_apply]
      simp
    _ = volume (coord '' s) := by rw [hmap, heq]
    _ ≤ Metric.ediam (coord '' s) := Real.volume_le_diam _
    _ = Metric.ediam s := coord_isometry.ediam_image s

private lemma mem_of_coord_between {s : Set E1} (hs : Convexity.IsConvexSet ℝ s)
    {x y z : E1} (hx : x ∈ s) (hy : y ∈ s)
    (hxz : coord x ≤ coord z) (hzy : coord z ≤ coord y) : z ∈ s := by
  have hlegacy := legacyConvex_of_isConvexSet hs
  have himage : Convex ℝ (EuclideanSpace.projₗ (𝕜 := ℝ) (0 : Fin 1) '' s) :=
    hlegacy.linear_image (EuclideanSpace.projₗ (𝕜 := ℝ) (0 : Fin 1))
  have hord := himage.ordConnected
  have hz : coord z ∈ EuclideanSpace.projₗ (𝕜 := ℝ) (0 : Fin 1) '' s :=
    hord.out ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ⟨hxz, hzy⟩
  obtain ⟨w, hw, hwz⟩ := hz
  have hw_eq : w = z := by
    ext i
    fin_cases i
    exact hwz
  rwa [← hw_eq]

private lemma exists_near_of_mem_cthickening {s : Set E1} (hclosed : IsClosed s)
    (hne : s.Nonempty) {ε : ℝ} (hε : 0 ≤ ε) {x : E1}
    (hx : x ∈ Metric.cthickening ε s) : ∃ z ∈ s, dist x z ≤ ε := by
  obtain ⟨z, hz, hdist⟩ := hclosed.exists_infDist_eq_dist hne x
  refine ⟨z, hz, ?_⟩
  rw [← hdist]
  change (Metric.infEDist x s).toReal ≤ ε
  rw [← ENNReal.toReal_ofReal hε]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hx

private lemma ediam_le_of_ordered_coord_dist_le {t : Set E1} {K : ℝ}
    (_hK : 0 ≤ K)
    (h : ∀ x ∈ t, ∀ y ∈ t, coord x ≤ coord y → dist x y ≤ K) :
    Metric.ediam t ≤ ENNReal.ofReal K := by
  apply Metric.ediam_le_of_forall_dist_le
  intro x hx y hy
  rcases le_total (coord x) (coord y) with hxy | hyx
  · exact h x hx y hy hxy
  · simpa only [dist_comm] using h y hy x hx hyx

private lemma outer_left_ediam_le {s : Set E1} (hclosed : IsClosed s)
    (hne : s.Nonempty) (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 ≤ ε)
    (a : E1) (ha : a ∈ s) :
    Metric.ediam ((Metric.cthickening ε s \ s) ∩ {x | coord x ≤ coord a}) ≤
      ENNReal.ofReal ε := by
  apply ediam_le_of_ordered_coord_dist_le hε
  intro x hx y hy hxy
  obtain ⟨z, hz, hxz⟩ := exists_near_of_mem_cthickening hclosed hne hε hx.1.1
  have hyz : coord y ≤ coord z := by
    by_contra h
    have hzy : coord z ≤ coord y := le_of_lt (lt_of_not_ge h)
    exact hy.1.2 (mem_of_coord_between hs hz ha hzy hy.2)
  calc
    dist x y = dist (coord x) (coord y) := (coord_dist_eq x y).symm
    _ ≤ dist (coord x) (coord z) := by
      rw [Real.dist_eq, Real.dist_eq]
      simp only [abs_of_nonpos (sub_nonpos.mpr hxy), abs_of_nonpos (sub_nonpos.mpr
        (hxy.trans hyz))]
      linarith
    _ = dist x z := coord_dist_eq x z
    _ ≤ ε := hxz

private lemma outer_right_ediam_le {s : Set E1} (hclosed : IsClosed s)
    (hne : s.Nonempty) (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 ≤ ε)
    (a : E1) (ha : a ∈ s) :
    Metric.ediam ((Metric.cthickening ε s \ s) ∩ {x | coord a ≤ coord x}) ≤
      ENNReal.ofReal ε := by
  apply ediam_le_of_ordered_coord_dist_le hε
  intro x hx y hy hxy
  obtain ⟨z, hz, hyz⟩ := exists_near_of_mem_cthickening hclosed hne hε hy.1.1
  have hzx : coord z ≤ coord x := by
    by_contra h
    have hxz : coord x ≤ coord z := le_of_lt (lt_of_not_ge h)
    exact hx.1.2 (mem_of_coord_between hs ha hz hx.2 hxz)
  calc
    dist x y = dist (coord x) (coord y) := (coord_dist_eq x y).symm
    _ ≤ dist (coord z) (coord y) := by
      rw [Real.dist_eq, Real.dist_eq]
      simp only [abs_of_nonpos (sub_nonpos.mpr hxy), abs_of_nonpos (sub_nonpos.mpr
        (hzx.trans hxy))]
      linarith
    _ = dist z y := coord_dist_eq z y
    _ = dist y z := dist_comm z y
    _ ≤ ε := hyz

private lemma outer_shell_volume_le_two_mul {s : Set E1}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 ≤ ε) :
    volume (Metric.cthickening ε (closure s) \ closure s) ≤ ENNReal.ofReal (2 * ε) := by
  rcases (closure s).eq_empty_or_nonempty with h | hne
  · simp [h]
  obtain ⟨a, ha⟩ := hne
  let L := (Metric.cthickening ε (closure s) \ closure s) ∩ {x | coord x ≤ coord a}
  let R := (Metric.cthickening ε (closure s) \ closure s) ∩ {x | coord a ≤ coord x}
  have hsubset : Metric.cthickening ε (closure s) \ closure s ⊆ L ∪ R := by
    intro x hx
    rcases le_total (coord x) (coord a) with hxa | hax
    · exact Or.inl ⟨hx, hxa⟩
    · exact Or.inr ⟨hx, hax⟩
  have hconv : Convexity.IsConvexSet ℝ (closure s) := closure_isConvexSet hs
  have hL : volume L ≤ ENNReal.ofReal ε :=
    (volume_le_ediam_finOne L).trans
      (outer_left_ediam_le isClosed_closure ⟨a, ha⟩ hconv hε a ha)
  have hR : volume R ≤ ENNReal.ofReal ε :=
    (volume_le_ediam_finOne R).trans
      (outer_right_ediam_le isClosed_closure ⟨a, ha⟩ hconv hε a ha)
  calc
    volume (Metric.cthickening ε (closure s) \ closure s) ≤ volume (L ∪ R) :=
      measure_mono hsubset
    _ ≤ volume L + volume R := measure_union_le L R
    _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε := add_le_add hL hR
    _ = ENNReal.ofReal (2 * ε) := by
      rw [← ENNReal.ofReal_add hε hε]
      congr 1
      ring

/-- In dimension one, the outer standard-Gaussian shell of a measurable convex set has mass at
most `2 * ε`.  This includes empty, whole-space, unbounded, open, closed, and singleton sets. -/
theorem stdGaussian_outer_shell_finOne_le_two_mul {s : Set E1}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 ≤ ε) :
    (stdGaussian E1).real (Metric.cthickening ε (closure s) \ s) ≤ 2 * ε := by
  change (stdGaussian E1 (Metric.cthickening ε (closure s) \ s)).toReal ≤ 2 * ε
  rw [stdGaussian_outer_shell_eq_closed_shell hs ε]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc
    stdGaussian E1 (Metric.cthickening ε (closure s) \ closure s) ≤
        volume (Metric.cthickening ε (closure s) \ closure s) :=
      stdGaussian_le_volume (d := 1) _
    _ ≤ ENNReal.ofReal (2 * ε) := outer_shell_volume_le_two_mul hs hε

private lemma exists_compl_near_of_notMem_inner {s : Set E1} {ε : ℝ} {x : E1}
    (hx : x ∉ convexInnerParallel s ε) : ∃ z, z ∉ s ∧ dist x z < ε := by
  have hx' : x ∈ Metric.thickening ε sᶜ := by
    simpa [convexInnerParallel] using hx
  obtain ⟨z, hz, hxz⟩ :=
    (Metric.mem_thickening_iff (E := sᶜ) (x := x)).1 hx'
  exact ⟨z, hz, hxz⟩

private lemma inner_left_ediam_le {s : Set E1} (hs : Convexity.IsConvexSet ℝ s)
    {ε : ℝ} (hε : 0 < ε) (a : E1) (ha : a ∈ convexInnerParallel s ε) :
    Metric.ediam ((s \ convexInnerParallel s ε) ∩ {x | coord x ≤ coord a}) ≤
      ENNReal.ofReal ε := by
  have has : a ∈ s := convexInnerParallel_subset s hε ha
  apply ediam_le_of_ordered_coord_dist_le hε.le
  intro x hx y hy hxy
  obtain ⟨z, hzs, hyz⟩ := exists_compl_near_of_notMem_inner hy.1.2
  have hzx : coord z ≤ coord x := by
    by_contra hnot
    have hxz : coord x < coord z := lt_of_not_ge hnot
    rcases le_total (coord z) (coord a) with hza | haz
    · exact hzs (mem_of_coord_between hs hx.1.1 has hxz.le hza)
    · have hza_dist : dist a z ≤ dist y z := by
        rw [← coord_dist_eq, ← coord_dist_eq, Real.dist_eq, Real.dist_eq]
        have hya : coord y ≤ coord a := hy.2
        rw [abs_of_nonpos (sub_nonpos.mpr haz),
          abs_of_nonpos (sub_nonpos.mpr (hya.trans haz))]
        linarith
      have hzball : z ∈ Metric.ball a ε := by
        rw [Metric.mem_ball]
        simpa only [dist_comm] using hza_dist.trans_lt hyz
      exact hzs ((mem_convexInnerParallel_iff_ball_subset.mp ha) hzball)
  calc
    dist x y = dist (coord x) (coord y) := (coord_dist_eq x y).symm
    _ ≤ dist (coord z) (coord y) := by
      rw [Real.dist_eq, Real.dist_eq]
      rw [abs_of_nonpos (sub_nonpos.mpr hxy),
        abs_of_nonpos (sub_nonpos.mpr (hzx.trans hxy))]
      linarith
    _ = dist z y := coord_dist_eq z y
    _ = dist y z := dist_comm z y
    _ ≤ ε := hyz.le

private lemma inner_right_ediam_le {s : Set E1} (hs : Convexity.IsConvexSet ℝ s)
    {ε : ℝ} (hε : 0 < ε) (a : E1) (ha : a ∈ convexInnerParallel s ε) :
    Metric.ediam ((s \ convexInnerParallel s ε) ∩ {x | coord a ≤ coord x}) ≤
      ENNReal.ofReal ε := by
  have has : a ∈ s := convexInnerParallel_subset s hε ha
  apply ediam_le_of_ordered_coord_dist_le hε.le
  intro x hx y hy hxy
  obtain ⟨z, hzs, hxz⟩ := exists_compl_near_of_notMem_inner hx.1.2
  have hyz : coord y ≤ coord z := by
    by_contra hnot
    have hzy : coord z < coord y := lt_of_not_ge hnot
    rcases le_total (coord a) (coord z) with haz | hza
    · exact hzs (mem_of_coord_between hs has hy.1.1 haz hzy.le)
    · have hza_dist : dist a z ≤ dist x z := by
        rw [← coord_dist_eq, ← coord_dist_eq, Real.dist_eq, Real.dist_eq]
        have hax : coord a ≤ coord x := hx.2
        rw [abs_of_nonneg (sub_nonneg.mpr hza),
          abs_of_nonneg (sub_nonneg.mpr (hza.trans hax))]
        linarith
      have hzball : z ∈ Metric.ball a ε := by
        rw [Metric.mem_ball]
        simpa only [dist_comm] using hza_dist.trans_lt hxz
      exact hzs ((mem_convexInnerParallel_iff_ball_subset.mp ha) hzball)
  calc
    dist x y = dist (coord x) (coord y) := (coord_dist_eq x y).symm
    _ ≤ dist (coord x) (coord z) := by
      rw [Real.dist_eq, Real.dist_eq]
      rw [abs_of_nonpos (sub_nonpos.mpr hxy),
        abs_of_nonpos (sub_nonpos.mpr (hxy.trans hyz))]
      linarith
    _ = dist x z := coord_dist_eq x z
    _ ≤ ε := hxz.le

private lemma inner_empty_ediam_le_two_mul {s : Set E1}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 < ε)
    (hempty : convexInnerParallel s ε = ∅) :
    Metric.ediam s ≤ ENNReal.ofReal (2 * ε) := by
  apply ediam_le_of_ordered_coord_dist_le (mul_nonneg (by norm_num) hε.le)
  intro x hx y hy hxy
  let m := Convexity.convexCombPair (1 / 2 : ℝ) (1 / 2 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) x y
  have hm : m ∈ s := hs.convexCombPair_mem hx hy (by norm_num) (by norm_num) (by norm_num)
  have hmnot : m ∉ convexInnerParallel s ε := by
    rw [hempty]
    simp
  obtain ⟨z, hzs, hmz⟩ := exists_compl_near_of_notMem_inner hmnot
  have hmcoord : coord m = (coord x + coord y) / 2 := by
    simp only [m, Convexity.convexCombPair_eq_sum, PiLp.add_apply, PiLp.smul_apply]
    ring
  have hzoutside : coord z < coord x ∨ coord y < coord z := by
    by_cases hzx : coord z < coord x
    · exact Or.inl hzx
    · right
      have hxz : coord x ≤ coord z := le_of_not_gt hzx
      by_contra hzy
      exact hzs (mem_of_coord_between hs hx hy hxz (le_of_not_gt hzy))
  have hmzcoord : dist (coord m) (coord z) < ε := by
    simpa only [coord_dist_eq] using hmz
  have hlength : coord y - coord x ≤ 2 * ε := by
    rcases hzoutside with hzx | hyz
    · have hzm : coord z ≤ coord m := by rw [hmcoord]; linarith
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hzm), hmcoord] at hmzcoord
      linarith
    · have hmz' : coord m ≤ coord z := by rw [hmcoord]; linarith
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hmz'), hmcoord] at hmzcoord
      linarith
  calc
    dist x y = dist (coord x) (coord y) := (coord_dist_eq x y).symm
    _ = coord y - coord x := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)]
      ring
    _ ≤ 2 * ε := hlength

private lemma inner_shell_volume_le_two_mul {s : Set E1}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 ≤ ε) :
    volume (s \ convexInnerParallel s ε) ≤ ENNReal.ofReal (2 * ε) := by
  rcases hε.eq_or_lt with rfl | hε
  · simp [convexInnerParallel, Metric.thickening_of_nonpos]
  rcases (convexInnerParallel s ε).eq_empty_or_nonempty with hempty | hne
  · calc
      volume (s \ convexInnerParallel s ε) = volume s := by rw [hempty]; simp
      _ ≤ Metric.ediam s := volume_le_ediam_finOne s
      _ ≤ ENNReal.ofReal (2 * ε) := inner_empty_ediam_le_two_mul hs hε hempty
  · obtain ⟨a, ha⟩ := hne
    let L := (s \ convexInnerParallel s ε) ∩ {x | coord x ≤ coord a}
    let R := (s \ convexInnerParallel s ε) ∩ {x | coord a ≤ coord x}
    have hsubset : s \ convexInnerParallel s ε ⊆ L ∪ R := by
      intro x hx
      rcases le_total (coord x) (coord a) with hxa | hax
      · exact Or.inl ⟨hx, hxa⟩
      · exact Or.inr ⟨hx, hax⟩
    have hL : volume L ≤ ENNReal.ofReal ε :=
      (volume_le_ediam_finOne L).trans (inner_left_ediam_le hs hε a ha)
    have hR : volume R ≤ ENNReal.ofReal ε :=
      (volume_le_ediam_finOne R).trans (inner_right_ediam_le hs hε a ha)
    calc
      volume (s \ convexInnerParallel s ε) ≤ volume (L ∪ R) := measure_mono hsubset
      _ ≤ volume L + volume R := measure_union_le L R
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε := add_le_add hL hR
      _ = ENNReal.ofReal (2 * ε) := by
        rw [← ENNReal.ofReal_add hε.le hε.le]
        congr 1
        ring

/-- In dimension one, the inner standard-Gaussian shell of a measurable convex set has mass at
most `2 * ε`.  This includes empty, whole-space, unbounded, open, closed, and singleton sets. -/
theorem stdGaussian_inner_shell_finOne_le_two_mul {s : Set E1}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 ≤ ε) :
    (stdGaussian E1).real (s \ convexInnerParallel s ε) ≤ 2 * ε := by
  change (stdGaussian E1 (s \ convexInnerParallel s ε)).toReal ≤ 2 * ε
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc
    stdGaussian E1 (s \ convexInnerParallel s ε) ≤
        volume (s \ convexInnerParallel s ε) :=
      stdGaussian_le_volume (d := 1) _
    _ ≤ ENNReal.ofReal (2 * ε) := inner_shell_volume_le_two_mul hs hε

/-- Ball's dimension-dependent Gaussian-perimeter constant. -/
def ballGaussianPerimeterConstant (d : ℕ) : ℝ :=
  4 * (d : ℝ) ^ (1 / 4 : ℝ)

private abbrev E0 := EuclideanSpace ℝ (Fin 0)

private lemma finZero_set_eq_empty_or_univ (s : Set E0) : s = ∅ ∨ s = univ := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · exact Or.inl hs
  · exact Or.inr (Subsingleton.eq_univ_of_nonempty hs)

/-- Every outer shell in dimension zero has zero standard-Gaussian mass. -/
theorem stdGaussian_outer_shell_finZero_eq_zero (s : Set E0) (ε : ℝ) :
    (stdGaussian E0).real (Metric.cthickening ε (closure s) \ s) = 0 := by
  rcases finZero_set_eq_empty_or_univ s with rfl | rfl <;> simp

/-- Every inner shell in dimension zero has zero standard-Gaussian mass. -/
theorem stdGaussian_inner_shell_finZero_eq_zero (s : Set E0) (ε : ℝ) :
    (stdGaussian E0).real (s \ convexInnerParallel s ε) = 0 := by
  rcases finZero_set_eq_empty_or_univ s with rfl | rfl
  · simp
  · simp [convexInnerParallel]

/-- The dimension-zero outer-shell estimate with Ball's exact displayed constant. -/
theorem stdGaussian_outer_shell_finZero_le_ball (s : Set E0) (ε : ℝ) :
    (stdGaussian E0).real (Metric.cthickening ε (closure s) \ s) ≤
      ballGaussianPerimeterConstant 0 * ε := by
  rw [stdGaussian_outer_shell_finZero_eq_zero]
  simp [ballGaussianPerimeterConstant]

/-- The dimension-zero inner-shell estimate with Ball's exact displayed constant. -/
theorem stdGaussian_inner_shell_finZero_le_ball (s : Set E0) (ε : ℝ) :
    (stdGaussian E0).real (s \ convexInnerParallel s ε) ≤
      ballGaussianPerimeterConstant 0 * ε := by
  rw [stdGaussian_inner_shell_finZero_eq_zero]
  simp [ballGaussianPerimeterConstant]

/-- The dimension-one outer-shell estimate with Ball's exact displayed constant. -/
theorem stdGaussian_outer_shell_finOne_le_ball {s : Set E1}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 ≤ ε) :
    (stdGaussian E1).real (Metric.cthickening ε (closure s) \ s) ≤
      ballGaussianPerimeterConstant 1 * ε := by
  calc
    (stdGaussian E1).real (Metric.cthickening ε (closure s) \ s) ≤ 2 * ε :=
      stdGaussian_outer_shell_finOne_le_two_mul hs hε
    _ ≤ ballGaussianPerimeterConstant 1 * ε := by
      simp [ballGaussianPerimeterConstant]
      linarith

/-- The dimension-one inner-shell estimate with Ball's exact displayed constant. -/
theorem stdGaussian_inner_shell_finOne_le_ball {s : Set E1}
    (hs : Convexity.IsConvexSet ℝ s) {ε : ℝ} (hε : 0 ≤ ε) :
    (stdGaussian E1).real (s \ convexInnerParallel s ε) ≤
      ballGaussianPerimeterConstant 1 * ε := by
  calc
    (stdGaussian E1).real (s \ convexInnerParallel s ε) ≤ 2 * ε :=
      stdGaussian_inner_shell_finOne_le_two_mul hs hε
    _ ≤ ballGaussianPerimeterConstant 1 * ε := by
      simp [ballGaussianPerimeterConstant]
      linarith

/-- A nonnegative coarea profile bounded by `K` gives the corresponding measure bound over an
interval.  This ENNReal form is the direct composition point for a measure-theoretic coarea
formula and avoids an unnecessary detour through Bochner interval integrals. -/
lemma measure_le_of_lintegral_Ioc {α : Type*} [MeasurableSpace α]
    (mu : Measure α) (shell : Set α) {a b K : ℝ} {profile : ℝ → ℝ≥0∞}
    (hK : 0 ≤ K)
    (hcoarea : mu shell = ∫⁻ t in Ioc a b, profile t)
    (hbound : ∀ t ∈ Ioc a b, profile t ≤ ENNReal.ofReal K) :
    mu shell ≤ ENNReal.ofReal (K * (b - a)) := by
  rw [hcoarea]
  calc
    (∫⁻ t in Ioc a b, profile t) ≤ ∫⁻ _t in Ioc a b, ENNReal.ofReal K := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hbound t ht
    _ = ENNReal.ofReal K * volume (Ioc a b) := by simp
    _ = ENNReal.ofReal K * ENNReal.ofReal (b - a) := by rw [Real.volume_Ioc]
    _ = ENNReal.ofReal (K * (b - a)) := by
      rw [ENNReal.ofReal_mul hK]

/-- ENNReal-valued final composition boundary between Ball's boundary-density estimate and the
signed-distance coarea identities. -/
theorem stdGaussian_shell_pair_le_ball_of_lintegral {d : ℕ}
    (s : Set (EuclideanSpace ℝ (Fin d))) {ε : ℝ} (hε : 0 ≤ ε)
    {outerProfile innerProfile : ℝ → ℝ≥0∞}
    (hOuterCoarea :
      stdGaussian (EuclideanSpace ℝ (Fin d))
          (Metric.cthickening ε (closure s) \ s) =
        ∫⁻ t in Ioc (0 : ℝ) ε, outerProfile t)
    (hInnerCoarea :
      stdGaussian (EuclideanSpace ℝ (Fin d))
          (s \ convexInnerParallel s ε) =
        ∫⁻ t in Ioc (0 : ℝ) ε, innerProfile t)
    (hOuterBound : ∀ t ∈ Ioc (0 : ℝ) ε,
      outerProfile t ≤ ENNReal.ofReal (ballGaussianPerimeterConstant d))
    (hInnerBound : ∀ t ∈ Ioc (0 : ℝ) ε,
      innerProfile t ≤ ENNReal.ofReal (ballGaussianPerimeterConstant d)) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).real
          (Metric.cthickening ε (closure s) \ s) ≤
        ballGaussianPerimeterConstant d * ε ∧
      (stdGaussian (EuclideanSpace ℝ (Fin d))).real
          (s \ convexInnerParallel s ε) ≤
        ballGaussianPerimeterConstant d * ε := by
  have hK : 0 ≤ ballGaussianPerimeterConstant d := by
    unfold ballGaussianPerimeterConstant
    positivity
  constructor
  · change (stdGaussian (EuclideanSpace ℝ (Fin d))
      (Metric.cthickening ε (closure s) \ s)).toReal ≤
        ballGaussianPerimeterConstant d * ε
    apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg hK hε)
    simpa only [sub_zero] using
      (measure_le_of_lintegral_Ioc
        (stdGaussian (EuclideanSpace ℝ (Fin d)))
        (Metric.cthickening ε (closure s) \ s) hK hOuterCoarea hOuterBound)
  · change (stdGaussian (EuclideanSpace ℝ (Fin d))
      (s \ convexInnerParallel s ε)).toReal ≤ ballGaussianPerimeterConstant d * ε
    apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg hK hε)
    simpa only [sub_zero] using
      (measure_le_of_lintegral_Ioc
        (stdGaussian (EuclideanSpace ℝ (Fin d)))
        (s \ convexInnerParallel s ε) hK hInnerCoarea hInnerBound)

/-- The analytic output of the coarea step in Raič (2019), Proposition 3.1: if a shell's
measure is the interval integral of a boundary-density profile bounded by `K`, then its mass is at
most `K` times the interval length.  Establishing the coarea identity itself requires the
codimension-one area formula, which is not presently in Mathlib. -/
lemma shell_measureReal_le_of_intervalIntegral {α : Type*} [MeasurableSpace α]
    (mu : Measure α) (shell : Set α) {a b K : ℝ} {p : ℝ → ℝ}
    (hab : a ≤ b) (hp : IntervalIntegrable p volume a b)
    (hcoarea : mu.real shell = ∫ t in a..b, p t)
    (hbound : ∀ t ∈ Icc a b, p t ≤ K) :
    mu.real shell ≤ K * (b - a) := by
  rw [hcoarea]
  calc
    (∫ t in a..b, p t) ≤ ∫ _t in a..b, K :=
      intervalIntegral.integral_mono_on hab hp intervalIntegrable_const hbound
    _ = K * (b - a) := by simp [mul_comm]

/-- The final composition boundary between Ball's boundary-density estimate and Raič's coarea
identities.  The two profiles are parameterized over `[0, ε]`; for the inner shell this amounts to
reversing the negative signed-distance parameter used in Raič's proof. -/
theorem stdGaussian_shell_pair_le_ball_of_coarea {d : ℕ}
    (s : Set (EuclideanSpace ℝ (Fin d))) {ε : ℝ} (hε : 0 ≤ ε)
    {outerProfile innerProfile : ℝ → ℝ}
    (hOuterIntegrable : IntervalIntegrable outerProfile volume 0 ε)
    (hInnerIntegrable : IntervalIntegrable innerProfile volume 0 ε)
    (hOuterCoarea :
      (stdGaussian (EuclideanSpace ℝ (Fin d))).real
          (Metric.cthickening ε (closure s) \ s) =
        ∫ t in (0 : ℝ)..ε, outerProfile t)
    (hInnerCoarea :
      (stdGaussian (EuclideanSpace ℝ (Fin d))).real
          (s \ convexInnerParallel s ε) =
        ∫ t in (0 : ℝ)..ε, innerProfile t)
    (hOuterBound : ∀ t ∈ Icc (0 : ℝ) ε,
      outerProfile t ≤ ballGaussianPerimeterConstant d)
    (hInnerBound : ∀ t ∈ Icc (0 : ℝ) ε,
      innerProfile t ≤ ballGaussianPerimeterConstant d) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).real
          (Metric.cthickening ε (closure s) \ s) ≤
        ballGaussianPerimeterConstant d * ε ∧
      (stdGaussian (EuclideanSpace ℝ (Fin d))).real
          (s \ convexInnerParallel s ε) ≤
        ballGaussianPerimeterConstant d * ε := by
  constructor
  · simpa using shell_measureReal_le_of_intervalIntegral
      (stdGaussian (EuclideanSpace ℝ (Fin d)))
      (Metric.cthickening ε (closure s) \ s) hε hOuterIntegrable
      hOuterCoarea hOuterBound
  · simpa using shell_measureReal_le_of_intervalIntegral
      (stdGaussian (EuclideanSpace ℝ (Fin d)))
      (s \ convexInnerParallel s ε) hε hInnerIntegrable
      hInnerCoarea hInnerBound

end ProbabilityTheory
