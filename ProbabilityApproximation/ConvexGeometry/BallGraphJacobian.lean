/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import ProbabilityApproximation.ConvexGeometry.BallProjectionJacobian

/-!
# Jacobian cancellation for a hyperplane graph

If a linear map from `θ⊥` into Euclidean space is a right inverse to orthogonal projection
back to `θ⊥`, its range is a hyperplane.  Choosing a unit normal `u` to that range and
applying Ball's projection-Jacobian identity shows

`|<θ,u>| * normDet L = 1`.

This is the pointwise cancellation used after parameterizing a strict supporting-normal patch as
a Lipschitz graph over its orthogonal projection.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace ProbabilityTheory

/-- A right inverse to orthogonal projection is a codimension-one graph, and its surface
Jacobian cancels the absolute normal component in the projection direction. -/
theorem exists_unit_normal_normDet_mul_eq_one_of_projection_comp_eq_id {d : ℕ}
    (hd : 2 ≤ d) {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1)
    (L : (ℝ ∙ θ)ᗮ →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (hcomp : ((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto.toLinearMap.comp L =
      LinearMap.id) :
    ∃ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 ∧
      L.range = (ℝ ∙ u)ᗮ ∧ |inner ℝ θ u| * L.normDet = 1 := by
  have hθ0 : θ ≠ 0 := norm_ne_zero_iff.mp (by rw [hθ]; exact one_ne_zero)
  have hLinj : Function.Injective L := by
    intro x y hxy
    have hp := congr_arg (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto.toLinearMap) hxy
    change (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto.toLinearMap.comp L) x =
      (((ℝ ∙ θ)ᗮ).orthogonalProjectionOnto.toLinearMap.comp L) y at hp
    rw [hcomp] at hp
    exact hp
  have hker : L.ker = ⊥ := LinearMap.ker_eq_bot.mpr hLinj
  have hspanrank : Module.finrank ℝ (ℝ ∙ θ) = 1 := finrank_span_singleton hθ0
  have hambient : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by
    simp [finrank_euclideanSpace]
  have hdomain : Module.finrank ℝ ((ℝ ∙ θ)ᗮ) = d - 1 := by
    have hsum := (ℝ ∙ θ).finrank_add_finrank_orthogonal
    rw [hspanrank, hambient] at hsum
    omega
  have hrange : Module.finrank ℝ L.range = d - 1 := by
    have hrank := L.finrank_range_add_finrank_ker
    rw [hker, finrank_bot, add_zero, hdomain] at hrank
    exact hrank
  have hrangePerp : Module.finrank ℝ L.rangeᗮ = 1 := by
    apply Submodule.finrank_add_finrank_orthogonal'
    rw [hrange, hambient]
    omega
  have hrangePerp_ne : L.rangeᗮ ≠ ⊥ := by
    intro hzero
    rw [hzero, finrank_bot] at hrangePerp
    omega
  obtain ⟨v, hvperp, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hrangePerp_ne
  let u : EuclideanSpace ℝ (Fin d) := ‖v‖⁻¹ • v
  have hu0 : u ≠ 0 := by
    dsimp [u]
    exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hv0)) hv0
  have huperp : u ∈ L.rangeᗮ := L.rangeᗮ.smul_mem _ hvperp
  have hunorm : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  have hperp : L.rangeᗮ = ℝ ∙ u :=
    eq_span_singleton_of_mem_of_finrank_eq_one hrangePerp huperp hu0
  have hrange_eq : L.range = (ℝ ∙ u)ᗮ := by
    calc
      L.range = L.rangeᗮᗮ := (Submodule.orthogonal_orthogonal L.range).symm
      _ = (ℝ ∙ u)ᗮ := by rw [hperp]
  let L' : (ℝ ∙ θ)ᗮ →ₗ[ℝ] (ℝ ∙ u)ᗮ :=
    L.codRestrict ((ℝ ∙ u)ᗮ) (fun x ↦ by
      rw [← hrange_eq]
      exact LinearMap.mem_range_self L x)
  have hcomp' : (hyperplaneOrthogonalProjection u θ).comp L' = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun hcomp x
  have hspanU : Module.finrank ℝ (ℝ ∙ u) = 1 := finrank_span_singleton hu0
  have hcodomain : Module.finrank ℝ ((ℝ ∙ u)ᗮ) = d - 1 := by
    have hsum := (ℝ ∙ u).finrank_add_finrank_orthogonal
    rw [hspanU, hambient] at hsum
    omega
  have hfinrank : Module.finrank ℝ ((ℝ ∙ θ)ᗮ) =
      Module.finrank ℝ ((ℝ ∙ u)ᗮ) := by rw [hdomain, hcodomain]
  have hnormDet := LinearMap.normDet_comp_of_finrank_eq L'
    (hyperplaneOrthogonalProjection u θ) hfinrank
  rw [hcomp', LinearMap.normDet_id,
    normDet_hyperplaneOrthogonalProjection hunorm hθ] at hnormDet
  have hL' : L'.normDet = L.normDet := by
    exact LinearMap.normDet_codRestrict _
  rw [hL'] at hnormDet
  exact ⟨u, hunorm, hrange_eq, hnormDet.symm⟩

end ProbabilityTheory
