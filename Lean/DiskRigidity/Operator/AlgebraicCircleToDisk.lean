/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.Conic
public import DiskRigidity.Operator.DiskFromBoundary
public import Mathlib.Analysis.Convex.ContinuousLinearEquiv
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# From the real algebraic circle to a complex disk

Proposition 7.1 is stated in real affine coordinates.  This file gives the
coordinate-free last step used in the main theorem: its circle equation is a
complex metric sphere, and a compact convex set with that frontier is the
corresponding closed disk.
-/

@[expose] public section

noncomputable section

open Metric Set

namespace DiskRigidity.Operator

/-- The standard real-linear coordinates of a complex number. -/
def complexPointContinuousLinearEquiv : ℂ ≃L[ℝ] (Fin 2 → ℝ) :=
  Complex.equivRealProdCLM.trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm

/-- The underlying homeomorphism of the standard real-linear coordinates. -/
def complexPointHomeomorph : ℂ ≃ₜ (Fin 2 → ℝ) :=
  complexPointContinuousLinearEquiv.toHomeomorph

/-- The coordinate homeomorphism is the same function as the coordinate
continuous linear equivalence. -/
theorem complexPointHomeomorph_apply (z : ℂ) :
    complexPointHomeomorph z = complexPointContinuousLinearEquiv z := rfl

@[simp]
theorem complexPointHomeomorph_apply_zero (z : ℂ) :
    complexPointHomeomorph z 0 = z.re := rfl

@[simp]
theorem complexPointHomeomorph_apply_one (z : ℂ) :
    complexPointHomeomorph z 1 = z.im := rfl

/-- A positive real affine circle equation pulls back to the corresponding
complex metric sphere. -/
theorem frontier_eq_sphere_of_realAffine_circle
    (K : Set ℂ) (q : Algebraic.Conic.Form) (hq : 0 < q.radiusSq)
    (hcircle : frontier (complexPointHomeomorph '' K) =
      {x | (x 0 - q.centerX) ^ 2 + (x 1 - q.centerY) ^ 2 = q.radiusSq}) :
    frontier K = sphere (q.centerX + q.centerY * Complex.I)
      (Real.sqrt q.radiusSq) := by
  let c : ℂ := q.centerX + q.centerY * Complex.I
  let r : ℝ := Real.sqrt q.radiusSq
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = q.radiusSq := by
    exact Real.sq_sqrt hq.le
  have himage : complexPointHomeomorph '' frontier K =
      {x | (x 0 - q.centerX) ^ 2 + (x 1 - q.centerY) ^ 2 = q.radiusSq} := by
    rw [complexPointHomeomorph.image_frontier]
    exact hcircle
  ext z
  constructor
  · intro hz
    have hzcoord : (complexPointHomeomorph z 0 - q.centerX) ^ 2 +
        (complexPointHomeomorph z 1 - q.centerY) ^ 2 = q.radiusSq := by
      have : complexPointHomeomorph z ∈ complexPointHomeomorph '' frontier K :=
        ⟨z, hz, rfl⟩
      rw [himage] at this
      exact this
    rw [mem_sphere_iff_norm]
    change ‖z - c‖ = r
    have hnormsq : ‖z - c‖ ^ 2 = q.radiusSq := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simpa [c, pow_two] using hzcoord
    nlinarith [norm_nonneg (z - c)]
  · intro hz
    rw [mem_sphere_iff_norm] at hz
    have hnormsq : ‖z - c‖ ^ 2 = q.radiusSq := by
      change ‖z - c‖ = r at hz
      nlinarith
    have hzcoord : (complexPointHomeomorph z 0 - q.centerX) ^ 2 +
        (complexPointHomeomorph z 1 - q.centerY) ^ 2 = q.radiusSq := by
      rw [Complex.sq_norm, Complex.normSq_apply] at hnormsq
      simpa [c, pow_two] using hnormsq
    have hzimage : complexPointHomeomorph z ∈
        complexPointHomeomorph '' frontier K := by
      rw [himage]
      exact hzcoord
    obtain ⟨w, hw, hwz⟩ := hzimage
    exact complexPointHomeomorph.injective hwz
      |>.symm ▸ hw

/-- The real affine circle conclusion of Proposition 7.1 gives the desired
closed complex disk. -/
theorem eq_closedBall_of_realAffine_circle
    {K : Set ℂ} (hcompact : IsCompact K) (hconvex : Convex ℝ K)
    (q : Algebraic.Conic.Form) (hq : 0 < q.radiusSq)
    (hcircle : frontier (complexPointHomeomorph '' K) =
      {x | (x 0 - q.centerX) ^ 2 + (x 1 - q.centerY) ^ 2 = q.radiusSq}) :
    K = closedBall (q.centerX + q.centerY * Complex.I)
      (Real.sqrt q.radiusSq) := by
  apply eq_closedBall_of_frontier_eq_sphere hcompact hconvex
    (q.centerX + q.centerY * Complex.I) (Real.sqrt_pos.2 hq)
  exact frontier_eq_sphere_of_realAffine_circle K q hq hcircle

end DiskRigidity.Operator
