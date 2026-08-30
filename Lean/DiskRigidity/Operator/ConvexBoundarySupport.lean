/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.ConvexBoundaryParametrization
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Supporting normals for the radial convex-boundary parametrization

At every differentiability point of the radial function, the clockwise
rotation of the counterclockwise tangent is the outward supporting normal.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set Topology
open scoped InnerProductSpace NNReal Pointwise

namespace DiskRigidity.Operator

attribute [local instance] Complex.finrank_real_complex_fact

/-- The clockwise rotation of a polar tangent pairs positively with the
radial direction. -/
theorem real_inner_neg_I_mul_radial_tangent
    (rho r' t : ℝ) :
    ⟪(-Complex.I) *
        (rho • (circleMap 0 1 t * Complex.I) + r' • circleMap 0 1 t),
      rho • circleMap 0 1 t⟫_ℝ = rho ^ 2 := by
  simp [Complex.inner, circleMap, Complex.mul_re,
    Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re,
    Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_re, Complex.exp_im,
    Complex.conj_re, Complex.conj_im]
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- Clockwise rotation is orthogonal to the original vector in the real
Euclidean plane. -/
theorem real_inner_self_neg_I_mul (d : ℂ) :
    ⟪d, (-Complex.I) * d⟫_ℝ = 0 := by
  rw [Complex.inner]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- At a differentiability point of the radial function, the unit clockwise
normal is a supporting normal of the convex body. -/
theorem radialOutwardUnitNormal_supports_of_hasDerivAt
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    {t r' : ℝ} (hr : HasDerivAt (radialBoundaryRadius K c) r' t) :
    ∀ w ∈ K,
      (star (radialOutwardUnitNormal K c t) * w).re ≤
        (star (radialOutwardUnitNormal K c t) *
          radialBoundaryParametrization K c t).re := by
  let sigma := radialBoundaryParametrization K c
  let rho := radialBoundaryRadius K c t
  let u := circleMap 0 1 t
  let d : ℂ := rho • (u * Complex.I) + r' • u
  let b : ℂ := (-Complex.I) * d
  have hsigma : HasDerivAt sigma d t := by
    exact hasDerivAt_radialBoundaryParametrization hconv hc hcompact hr
  have hd : d ≠ 0 := by
    exact radialBoundary_tangent_ne_zero hconv hc hcompact t r'
  have hxfront : sigma t ∈ frontier K :=
    radialBoundaryParametrization_mem_frontier hconv hc hcompact t
  have hxnot : sigma t ∉ interior K := hxfront.2
  obtain ⟨f, hfne, hf⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point hconv hxnot ⟨c, hc⟩
  have hfc_lt : f c < f (sigma t) := by
    have himage : f '' interior K ⊆ Set.Iic (f (sigma t)) := by
      rintro _ ⟨z, hz, rfl⟩
      exact hf z (interior_subset hz)
    have hopen : IsOpen (f '' interior K) :=
      f.isOpenMap_of_ne_zero hfne (interior K) isOpen_interior
    have hmem : f c ∈ f '' interior K := ⟨c, hc, rfl⟩
    have hinterior : f c ∈ interior (Set.Iic (f (sigma t))) :=
      interior_maximal himage hopen hmem
    simpa using hinterior
  have hlocal : IsLocalMax (fun s ↦ f (sigma s)) t := by
    exact Filter.Eventually.of_forall fun s ↦
      hf (sigma s)
        (by
          rw [← hcompact.isClosed.closure_eq]
          exact frontier_subset_closure
            (radialBoundaryParametrization_mem_frontier hconv hc hcompact s))
  have hcomp : HasDerivAt (fun s ↦ f (sigma s)) (f d) t := by
    simpa [Function.comp_def] using
      (f.hasFDerivAt.comp t hsigma.hasFDerivAt).hasDerivAt
  have hfd : f d = 0 := hlocal.hasDerivAt_eq_zero hcomp
  let a : ℂ := (InnerProductSpace.toDual ℝ ℂ).symm f
  have hfa (z : ℂ) : ⟪a, z⟫_ℝ = f z := by
    exact InnerProductSpace.toDual_symm_apply
  have ha : a ≠ 0 := by
    intro ha0
    apply hfne
    ext z
    rw [← hfa z, ha0]
    simp
  have hda : ⟪d, a⟫_ℝ = 0 := by
    rw [real_inner_comm, hfa]
    exact hfd
  have hb : b ≠ 0 := mul_ne_zero (by norm_num) hd
  have hdb : ⟪d, b⟫_ℝ = 0 := real_inner_self_neg_I_mul d
  have haspan : a ∈ ℝ ∙ b :=
    Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero
      hd hb hda hdb
  obtain ⟨r, hra⟩ := Submodule.mem_span_singleton.mp haspan
  have hrho : 0 < rho := radialBoundaryRadius_pos hconv hc hcompact t
  have hb_radial : ⟪b, sigma t - c⟫_ℝ = rho ^ 2 := by
    change ⟪b, radialBoundaryParametrization K c t - c⟫_ℝ = rho ^ 2
    rw [radialBoundaryParametrization_eq_radius_mul_circleMap
      hconv hc hcompact]
    simp only [add_sub_cancel_left]
    change ⟪b, rho • u⟫_ℝ = rho ^ 2
    exact real_inner_neg_I_mul_radial_tangent rho r' t
  have ha_radial : 0 < ⟪a, sigma t - c⟫_ℝ := by
    rw [hfa, map_sub]
    linarith
  have hrpos : 0 < r := by
    rw [← hra, inner_smul_left, hb_radial] at ha_radial
    simp only [starRingEnd_apply, star_trivial] at ha_radial
    nlinarith [sq_pos_of_pos hrho]
  have hb_support : ∀ w ∈ K, ⟪b, w⟫_ℝ ≤ ⟪b, sigma t⟫_ℝ := by
    intro w hw
    have hfw := hf w hw
    rw [← hfa w, ← hfa (sigma t), ← hra,
      inner_smul_left, inner_smul_left] at hfw
    simp only [starRingEnd_apply, star_trivial] at hfw
    nlinarith
  have hspeed : 0 < radialBoundarySpeed K c t := by
    rw [radialBoundarySpeed, hsigma.deriv]
    exact norm_pos_iff.mpr hd
  have hnormal : radialOutwardUnitNormal K c t =
      (radialBoundarySpeed K c t)⁻¹ • b := by
    rw [radialOutwardUnitNormal, hsigma.deriv]
    simp [b, div_eq_mul_inv, mul_comm]
  intro w hw
  have hscaled := mul_le_mul_of_nonneg_left (hb_support w hw)
    (inv_nonneg.mpr hspeed.le)
  have hnormal_support :
      ⟪radialOutwardUnitNormal K c t, w⟫_ℝ ≤
        ⟪radialOutwardUnitNormal K c t, sigma t⟫_ℝ := by
    rw [hnormal, inner_smul_left, inner_smul_left]
    simpa only [starRingEnd_apply, star_trivial] using hscaled
  simpa [Complex.inner, mul_comm] using hnormal_support

/-- The supporting-half-plane property holds almost everywhere along the
rectifiable convex boundary. -/
theorem ae_radialOutwardUnitNormal_supports
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K) :
    ∀ᵐ t : ℝ ∂volume, ∀ w ∈ K,
      (star (radialOutwardUnitNormal K c t) * w).re ≤
        (star (radialOutwardUnitNormal K c t) *
          radialBoundaryParametrization K c t).re := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_radialBoundaryRadius
    hconv hc hcompact
  filter_upwards [hC.ae_differentiableAt_real] with t ht
  exact radialOutwardUnitNormal_supports_of_hasDerivAt
    hconv hc hcompact ht.hasDerivAt

end DiskRigidity.Operator
