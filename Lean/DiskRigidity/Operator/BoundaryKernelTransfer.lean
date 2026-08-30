/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.RationalCollapse
public import DiskRigidity.Operator.ResolventDilation

/-!
# From the double-layer kernel to the scalar transfer identity

This file contains the pointwise geometric part of Proposition 5.2.  The
Gram identity for the canonical square root turns its kernel into the kernel
of the positive double-layer density.  Resolvent congruence then turns that
into a support-vector equation.
-/

@[expose] public section

noncomputable section

open MeasureTheory WithLp
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A vector in the kernel of a boundary square-root factor is in the
kernel of the underlying positive density. -/
theorem PositiveBoundarySquareRoot.density_apply_eq_zero_of_factor_apply_eq_zero
    {i : Type*} [TopologicalSpace i] [MeasurableSpace i]
    {mu : Measure i} {D : PositiveBoundaryDensity (n := n) mu}
    (S : PositiveBoundarySquareRoot D) {t : i} {v : EuclideanVector n}
    (hgram : ContinuousLinearMap.adjoint (S.factor t) ∘L S.factor t =
      (2 : ℂ)⁻¹ • D.density t)
    (hkernel : S.factor t v = 0) :
    D.density t v = 0 := by
  have happ := DFunLike.congr_fun hgram v
  simp only [ContinuousLinearMap.comp_apply, hkernel, map_zero, smul_apply] at happ
  exact (smul_eq_zero.mp happ.symm).resolve_left (by norm_num)

/-- For a resolvent double layer, density-kernel membership is exactly the
support-matrix kernel equation after applying the resolvent. -/
theorem supportMatrix_apply_resolvent_eq_zero_of_density_apply_eq_zero
    (A R : SquareMatrix n) (sigma nu : ℂ)
    (hR : (sigma • (1 : SquareMatrix n) - A) * R = 1)
    {v : EuclideanVector n}
    (hdensity : normalizedDoubleLayerDensity R nu v = 0) :
    euclideanOperator (doubleLayerSupportMatrix A sigma nu)
        (euclideanOperator R v) = 0 := by
  have hraw : euclideanOperator (doubleLayerDensity R nu) v = 0 := by
    rw [normalizedDoubleLayerDensity,
      normalizedDoubleLayerDensityMatrix] at hdensity
    simp only [map_smul, smul_apply] at hdensity
    exact (smul_eq_zero.mp hdensity).resolve_left (by
      exact_mod_cast inv_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
        Real.pi_ne_zero))
  have hcongruence := congrArg (euclideanOperator (n := n))
    (doubleLayer_congruence_density_identity A R sigma nu hR)
  simp only [map_mul] at hcongruence
  have hproduct :
      (euclideanOperator Rᴴ *
        euclideanOperator (doubleLayerSupportMatrix A sigma nu) *
          euclideanOperator R) v = 0 := by
    rw [hcongruence]
    exact hraw
  have hright : R * (sigma • (1 : SquareMatrix n) - A) = 1 :=
    mul_eq_one_comm.mp hR
  have hleftAdjoint :
      (star sigma • (1 : SquareMatrix n) - Aᴴ) * Rᴴ = 1 := by
    have h := congrArg Matrix.conjTranspose hright
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      starRingEnd_apply, star_star] using h
  have hRstar : euclideanOperator Rᴴ
      (euclideanOperator (doubleLayerSupportMatrix A sigma nu)
        (euclideanOperator R v)) = 0 := by
    simpa only [mul_apply_eq_comp] using hproduct
  let L := euclideanOperator (star sigma • (1 : SquareMatrix n) - Aᴴ)
  have hLR : L * euclideanOperator Rᴴ = 1 := by
    dsimp only [L]
    rw [← map_mul, hleftAdjoint, map_one]
  calc
    euclideanOperator (doubleLayerSupportMatrix A sigma nu)
          (euclideanOperator R v) =
        (1 : EuclideanEndomorphism n)
          (euclideanOperator (doubleLayerSupportMatrix A sigma nu)
            (euclideanOperator R v)) := by simp
    _ = (L * euclideanOperator Rᴴ)
          (euclideanOperator (doubleLayerSupportMatrix A sigma nu)
            (euclideanOperator R v)) := by rw [hLR]
    _ = L (euclideanOperator Rᴴ
          (euclideanOperator (doubleLayerSupportMatrix A sigma nu)
            (euclideanOperator R v))) := by rw [mul_apply_eq_comp]
    _ = 0 := by rw [hRstar, map_zero]

/-- At a uniquely exposed support point, a nonzero vector in the support
matrix kernel realizes that boundary point as its numerical value. -/
theorem normalized_inner_eq_of_supportMatrix_apply_eq_zero
    (A : SquareMatrix n) (sigma nu : ℂ)
    (r : EuclideanVector n) (hr : r ≠ 0)
    (hzero : euclideanOperator (doubleLayerSupportMatrix A sigma nu) r = 0)
    (hunique : ∀ z ∈ numericalRange A,
      (star nu * z).re = (star nu * sigma).re → z = sigma) :
    let u : EuclideanVector n := (‖r‖⁻¹ : ℂ) • r
    ⟪u, euclideanOperator A u⟫_ℂ = sigma := by
  let u : EuclideanVector n := (‖r‖⁻¹ : ℂ) • r
  have huNorm : ‖u‖ = 1 := norm_smul_inv_norm hr
  let z : ℂ := ⟪u, euclideanOperator A u⟫_ℂ
  have hz : z ∈ numericalRange A := ⟨u, huNorm, rfl⟩
  apply hunique z hz
  have hzeroU :
      euclideanOperator (doubleLayerSupportMatrix A sigma nu) u = 0 := by
    dsimp only [u]
    rw [map_smul, hzero, smul_zero]
  let x : n → ℂ := ofLp u
  have hxunit : star x ⬝ᵥ x = 1 := by
    have huinner : ⟪u, u⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, huNorm]
      norm_num
    rw [EuclideanSpace.inner_eq_star_dotProduct] at huinner
    simpa only [x, dotProduct_comm] using huinner
  have hquadzero :
      star x ⬝ᵥ (doubleLayerSupportMatrix A sigma nu *ᵥ x) = 0 := by
    rw [← inner_euclideanOperator_eq_star_dotProduct]
    rw [hzeroU, inner_zero_right]
  rw [doubleLayerSupportMatrix_eq_two_smul_rePart,
    Matrix.smul_mulVec, dotProduct_smul] at hquadzero
  norm_num at hquadzero
  rw [quadratic_rePart] at hquadzero
  have hinside :
      star x ⬝ᵥ ((star nu • (sigma • (1 : SquareMatrix n) - A)) *ᵥ x) =
        star nu * (sigma - z) := by
    simp only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      dotProduct_smul, dotProduct_sub, hxunit, smul_eq_mul, mul_one]
    rw [← inner_euclideanOperator_eq_star_dotProduct]
  have hreLhs :
      (star x ⬝ᵥ ((star nu • (sigma • (1 : SquareMatrix n) - A)) *ᵥ x)).re = 0 :=
    Complex.ofReal_eq_zero.mp hquadzero
  change (star nu * z).re = (star nu * sigma).re
  have hre : (star nu * (sigma - z)).re = 0 := by
    calc
      (star nu * (sigma - z)).re =
          (star x ⬝ᵥ
            ((star nu • (sigma • (1 : SquareMatrix n) - A)) *ᵥ x)).re :=
        congrArg Complex.re hinside.symm
      _ = 0 := hreLhs
  rw [mul_sub, Complex.sub_re] at hre
  linarith

/-- The support-vector conclusion and the resolvent equation give the
vanishing quadratic form (5.5). -/
theorem boundary_quadratic_zero_of_supportMatrix_apply_resolvent_eq_zero
    (A R : SquareMatrix n) (sigma nu : ℂ)
    (hR : (sigma • (1 : SquareMatrix n) - A) * R = 1)
    (v : EuclideanVector n) (hv : v ≠ 0)
    (hsupportZero :
      euclideanOperator (doubleLayerSupportMatrix A sigma nu)
        (euclideanOperator R v) = 0)
    (hunique : ∀ z ∈ numericalRange A,
      (star nu * z).re = (star nu * sigma).re → z = sigma) :
    ⟪v, euclideanOperator R v⟫_ℂ = 0 := by
  let M : SquareMatrix n := sigma • (1 : SquareMatrix n) - A
  let r : EuclideanVector n := euclideanOperator R v
  have hMr : euclideanOperator M r = v := by
    dsimp only [M, r]
    calc
      euclideanOperator (sigma • (1 : SquareMatrix n) - A)
          (euclideanOperator R v) =
          (euclideanOperator
            ((sigma • (1 : SquareMatrix n) - A) * R)) v := by
        rw [map_mul, mul_apply_eq_comp]
      _ = v := by rw [hR, map_one, one_apply_eq_self]
  have hr : r ≠ 0 := by
    intro hrzero
    apply hv
    rw [← hMr, hrzero, map_zero]
  have hnum := normalized_inner_eq_of_supportMatrix_apply_eq_zero
    A sigma nu r hr hsupportZero hunique
  let a : ℝ := ‖r‖
  have ha : a ≠ 0 := norm_ne_zero_iff.mpr hr
  have hAr : ⟪r, euclideanOperator A r⟫_ℂ = sigma * (a : ℂ) ^ 2 := by
    dsimp only at hnum
    change ⟪((a : ℂ)⁻¹ • r),
      euclideanOperator A ((a : ℂ)⁻¹ • r)⟫_ℂ = sigma at hnum
    rw [map_smul, inner_smul_left, inner_smul_right] at hnum
    simp at hnum
    have hac : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
    field_simp [hac] at hnum
    simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hnum
  have hright : ⟪r, euclideanOperator M r⟫_ℂ = 0 := by
    dsimp only [M]
    simp only [map_sub, map_smul, map_one, sub_apply, smul_apply,
      one_apply_eq_self, inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hAr]
    change sigma * ((a : ℂ) ^ 2) - sigma * ((a : ℂ) ^ 2) = 0
    ring
  change ⟪v, r⟫_ℂ = 0
  rw [← hMr, ← inner_conj_symm, hright, map_zero]

end DiskRigidity.Operator
