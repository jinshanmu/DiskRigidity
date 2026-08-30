/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.AdjugateDegree
public import DiskRigidity.Operator.FoundationGeometry
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Diagonal resolvent coefficients outside the numerical range

The diagonal scalar resolvent of a nonzero vector cannot vanish outside the
numerical range.  This elementary observation gives the zero-location input
of Lemma 6.2 directly, without an auxiliary representing measure.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
/-- A diagonal scalar coefficient of `(zI-A)⁻¹` is nonzero whenever `z` lies
outside `W(A)`. -/
theorem inner_matrix_inv_ne_zero_of_not_mem_numericalRange
    (A : SquareMatrix n) (x : EuclideanVector n) (hx : x ≠ 0)
    {z : ℂ} (hz : z ∉ numericalRange A) :
    ⟪x, euclideanOperator ((z • (1 : SquareMatrix n) - A)⁻¹) x⟫_ℂ ≠ 0 := by
  let M : SquareMatrix n := z • 1 - A
  have hzSpectrum : z ∉ spectrum ℂ A :=
    fun hzSpec ↦ hz (spectrum_subset_numericalRange A hzSpec)
  have hzResolvent : z ∈ resolventSet ℂ A := by
    simpa [spectrum] using hzSpectrum
  have hMunit : IsUnit M := by
    have hunit : IsUnit (↑hzResolvent.unit : SquareMatrix n) := Units.isUnit _
    rw [hzResolvent.unit_spec] at hunit
    simpa only [M, Algebra.algebraMap_eq_smul_one] using hunit
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hMunit
  let v : EuclideanVector n := euclideanOperator M⁻¹ x
  have hMv : euclideanOperator M v = x := by
    dsimp only [v]
    calc
      euclideanOperator M (euclideanOperator M⁻¹ x) =
          (euclideanOperator M * euclideanOperator M⁻¹) x :=
        (mul_apply_eq_comp _ _ _).symm
      _ = euclideanOperator (M * M⁻¹) x := by rw [map_mul]
      _ = x := by rw [Matrix.mul_nonsing_inv M hdet]; simp
  have hv : v ≠ 0 := by
    intro hvzero
    apply hx
    rw [← hMv, hvzero]
    exact map_zero _
  intro hcoefficient
  have hinner : ⟪euclideanOperator M v, v⟫_ℂ = 0 := by
    rw [hMv]
    exact hcoefficient
  have hinner' : ⟪v, euclideanOperator M v⟫_ℂ = 0 := by
    rw [← inner_conj_symm]
    rw [hinner]
    exact map_zero _
  have hform : ⟪v, euclideanOperator A v⟫_ℂ = z * ‖v‖ ^ 2 := by
    simp only [M, map_sub, map_smul, map_one, sub_apply, smul_apply,
      one_apply_eq_self, inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K] at hinner'
    linear_combination -hinner'
  let u : EuclideanVector n := (‖v‖⁻¹ : ℂ) • v
  have huNorm : ‖u‖ = 1 := norm_smul_inv_norm hv
  apply hz
  refine ⟨u, huNorm, ?_⟩
  simp only [u, map_smul, inner_smul_left, inner_smul_right,
    starRingEnd_apply, hform]
  have hvNorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hvNormComplex : (‖v‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hvNorm
  have hstar : star (‖v‖ : ℂ) = (‖v‖ : ℂ) := by
    exact Complex.conj_ofReal ‖v‖
  rw [star_inv₀, hstar]
  field_simp

/-- Consequently, the diagonal adjugate numerator of the scalar resolvent has
no zero outside the numerical range. -/
theorem adjugateScalarNumerator_ne_zero_off_numericalRange
    {N : ℕ} (A : SquareMatrix (Fin (N + 1)))
    (x : EuclideanVector (Fin (N + 1))) (hx : x ≠ 0)
    {z : ℂ} (hz : z ∉ numericalRange A) :
    (adjugateScalarNumerator A x x).eval z ≠ 0 := by
  intro hzero
  have hresolvent :=
    inner_matrix_inv_ne_zero_of_not_mem_numericalRange A x hx hz
  have hcoefficient :=
    adjugateScalarNumerator_div_charpoly_eq_resolventCoefficient A x x z
  rw [hzero, zero_div] at hcoefficient
  exact hresolvent hcoefficient.symm

end DiskRigidity.Operator
