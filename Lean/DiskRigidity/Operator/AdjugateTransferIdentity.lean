/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.AdjugateDegree
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Clearing the common resolvent denominator

This is the coordinate passage in Proposition 5.2 from the scalar resolvent
identity to its polynomial-numerator form.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace Matrix

namespace DiskRigidity.Operator

/-- Away from the spectrum, equation (5.7) is equivalent to the same
identity for the two scalar adjugate numerators. -/
theorem adjugate_transfer_identity_of_resolvent_identity
    {N : ℕ} (A : SquareMatrix (Fin (N + 1)))
    (x y : EuclideanVector (Fin (N + 1)))
    (z f : ℂ) (hz : z ∉ spectrum ℂ A)
    (hidentity :
      f * ⟪y, euclideanOperator ((z • (1 : SquareMatrix (Fin (N + 1))) - A)⁻¹) x⟫_ℂ =
        2 * ⟪x, euclideanOperator ((z • (1 : SquareMatrix (Fin (N + 1))) - A)⁻¹) x⟫_ℂ) :
    (adjugateScalarNumerator A y x).eval z * f =
      2 * (adjugateScalarNumerator A x x).eval z := by
  have hdet : A.charpoly.eval z ≠ 0 := by
    intro hzero
    apply hz
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
    exact hzero
  rw [← adjugateScalarNumerator_div_charpoly_eq_resolventCoefficient
      A y x z,
    ← adjugateScalarNumerator_div_charpoly_eq_resolventCoefficient
      A x x z] at hidentity
  field_simp [hdet] at hidentity
  linear_combination hidentity

/-- Variant using any explicitly supplied right inverse of `zI-A`. -/
theorem adjugate_transfer_identity_of_right_resolvent_identity
    {N : ℕ} (A R : SquareMatrix (Fin (N + 1)))
    (x y : EuclideanVector (Fin (N + 1)))
    (z f : ℂ) (hz : z ∉ spectrum ℂ A)
    (hR : (z • (1 : SquareMatrix (Fin (N + 1))) - A) * R = 1)
    (hidentity :
      f * ⟪y, euclideanOperator R x⟫_ℂ =
        2 * ⟪x, euclideanOperator R x⟫_ℂ) :
    (adjugateScalarNumerator A y x).eval z * f =
      2 * (adjugateScalarNumerator A x x).eval z := by
  have hinv :
      (z • (1 : SquareMatrix (Fin (N + 1))) - A)⁻¹ = R :=
    Matrix.inv_eq_right_inv hR
  rw [← hinv] at hidentity
  exact adjugate_transfer_identity_of_resolvent_identity
    A x y z f hz hidentity

end DiskRigidity.Operator
