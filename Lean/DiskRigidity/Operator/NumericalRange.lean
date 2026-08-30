/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact

/-!
# Numerical ranges of finite complex matrices

This module defines the numerical range and proves its elementary compactness,
boundedness, translation, and scalar-covariance properties.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator Pointwise

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The numerical range `W(A) = {x⁺Ax : ‖x‖ = 1}`. -/
def numericalRange (A : SquareMatrix n) : Set ℂ :=
  {z | ∃ x : EuclideanVector n, ‖x‖ = 1 ∧ ⟪x, euclideanOperator A x⟫_ℂ = z}

/-- In positive dimension the numerical range is nonempty. -/
theorem numericalRange_nonempty [Nonempty n] (A : SquareMatrix n) :
    (numericalRange A).Nonempty := by
  classical
  let i : n := Classical.choice (inferInstance : Nonempty n)
  let x : EuclideanVector n := EuclideanSpace.single i 1
  refine ⟨⟪x, euclideanOperator A x⟫_ℂ, x, ?_, rfl⟩
  simp [x]

/-- The numerical-range quadratic form is continuous. -/
theorem continuous_numericalRangeForm (A : SquareMatrix n) :
    Continuous (fun x : EuclideanVector n ↦ ⟪x, euclideanOperator A x⟫_ℂ) :=
  continuous_id.inner (euclideanOperator A).continuous

/-- The numerical range is the image of the Euclidean unit sphere. -/
theorem numericalRange_eq_image_sphere (A : SquareMatrix n) :
    numericalRange A =
      (fun x : EuclideanVector n ↦ ⟪x, euclideanOperator A x⟫_ℂ) ''
        Metric.sphere 0 1 := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, mem_sphere_zero_iff_norm.mpr hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, mem_sphere_zero_iff_norm.mp hx, rfl⟩

/-- The numerical range of a finite complex matrix is compact. -/
theorem isCompact_numericalRange (A : SquareMatrix n) :
    IsCompact (numericalRange A) := by
  rw [numericalRange_eq_image_sphere]
  exact (isCompact_sphere (0 : EuclideanVector n) 1).image
    (continuous_numericalRangeForm A)

/-- Every point of `W(A)` is bounded by the induced operator norm of `A`. -/
theorem norm_le_of_mem_numericalRange (A : SquareMatrix n) {z : ℂ}
    (hz : z ∈ numericalRange A) : ‖z‖ ≤ ‖A‖ := by
  obtain ⟨x, hx, rfl⟩ := hz
  calc
    ‖⟪x, euclideanOperator A x⟫_ℂ‖ ≤ ‖x‖ * ‖euclideanOperator A x‖ :=
      norm_inner_le_norm x (euclideanOperator A x)
    _ ≤ ‖x‖ * (‖euclideanOperator A‖ * ‖x‖) := by
      gcongr
      exact (euclideanOperator A).le_opNorm x
    _ = ‖euclideanOperator A‖ := by rw [hx, one_mul, mul_one]
    _ = ‖A‖ := (matrix_norm_eq_operator_norm A).symm

/-- Translation of a matrix translates its numerical range. -/
theorem numericalRange_add_scalar (A : SquareMatrix n) (b : ℂ) :
    numericalRange (A + b • 1) =
      {z | ∃ w ∈ numericalRange A, z = b + w} := by
  ext z
  constructor
  · rintro ⟨x, hx, hzx⟩
    refine ⟨⟪x, euclideanOperator A x⟫_ℂ, ⟨x, hx, rfl⟩, ?_⟩
    have hform :
        ⟪x, euclideanOperator (A + b • 1) x⟫_ℂ =
          ⟪x, euclideanOperator A x⟫_ℂ + b := by
      simp only [map_add, map_smul, map_one, add_apply, smul_apply,
        one_apply_eq_self, inner_add_right, inner_smul_right,
        inner_self_eq_norm_sq_to_K, hx]
      norm_num
    rw [hform] at hzx
    linear_combination hzx.symm
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, hwx⟩ := hw
    refine ⟨x, hx, ?_⟩
    simp only [map_add, map_smul, map_one, add_apply, smul_apply,
      one_apply_eq_self, inner_add_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hx]
    norm_num
    rw [hwx, add_comm]

/-- Nonzero scalar multiplication rotates and dilates the numerical range. -/
theorem numericalRange_smul (A : SquareMatrix n) (a : ℂ) :
    numericalRange (a • A) =
      {z | ∃ w ∈ numericalRange A, z = a * w} := by
  ext z
  constructor
  · rintro ⟨x, hx, hzx⟩
    refine ⟨⟪x, euclideanOperator A x⟫_ℂ, ⟨x, hx, rfl⟩, ?_⟩
    simpa only [map_smul, smul_apply, inner_smul_right] using hzx.symm
  · rintro ⟨w, ⟨x, hx, hwx⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    simp only [map_smul, smul_apply, inner_smul_right, hwx]

end DiskRigidity.Operator
