/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Polynomial

/-!
# Degree of scalar coefficients of the matrix resolvent

This file formalizes the final degree computation in Proposition 5.2.  The
adjugate of `zI - A` has degree at most one less than the matrix size, and its
top coefficient is the identity matrix.  Consequently a unit diagonal scalar
coefficient has degree exactly `N - 1`, whereas an orthogonal cross coefficient
has smaller degree.
-/

@[expose] public section

noncomputable section

open Matrix Polynomial
open scoped ComplexConjugate InnerProductSpace Matrix

namespace DiskRigidity.Operator

/-- A deleted minor of the characteristic matrix is an affine polynomial
matrix in `X`. -/
theorem charmatrix_submatrix_succAbove
    {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (i j : Fin (N + 1)) :
    (Matrix.charmatrix A).submatrix j.succAbove i.succAbove =
      (X : ℂ[X]) •
          ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ).submatrix
            j.succAbove i.succAbove).map C +
        ((-A).submatrix j.succAbove i.succAbove).map C := by
  ext r s
  simp only [Matrix.charmatrix, Matrix.submatrix_apply, Matrix.sub_apply,
    Matrix.scalar_apply, RingHom.mapMatrix_apply, Matrix.smul_apply,
    Matrix.add_apply, Matrix.map_apply]
  by_cases h : j.succAbove r = i.succAbove s
  · rw [h]
    rw [sub_eq_add_neg]
    simp
  · simp [h]

/-- Every entry of `adj (XI - A)` has degree at most `N`, for a matrix of
size `N + 1`. -/
theorem natDegree_adjugate_charmatrix_apply_le
    {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (i j : Fin (N + 1)) :
    ((Matrix.charmatrix A).adjugate i j).natDegree ≤ N := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix,
    charmatrix_submatrix_succAbove]
  have hsign : ((-1 : ℂ[X]) ^ ((j : ℕ) + (i : ℕ))) =
      C ((-1 : ℂ) ^ ((j : ℕ) + (i : ℕ))) := by simp
  rw [hsign]
  exact (Polynomial.natDegree_C_mul_le _ _).trans <| by
    simpa using Polynomial.natDegree_det_X_add_C_le
      ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ).submatrix
        j.succAbove i.succAbove)
      ((-A).submatrix j.succAbove i.succAbove)

/-- The determinant of the deleted identity minor is the Kronecker delta. -/
theorem det_one_submatrix_succAbove
    {N : ℕ} (i j : Fin (N + 1)) :
    ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ).submatrix
      j.succAbove i.succAbove).det = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [Matrix.submatrix_one i.succAbove Fin.succAbove_right_injective,
      Matrix.det_one, if_pos rfl]
  · rw [if_neg hij]
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
    apply Matrix.det_eq_zero_of_column_eq_zero k
    intro r
    simp only [Matrix.submatrix_apply, Matrix.one_apply]
    rw [hk]
    exact if_neg (Fin.succAbove_ne j r)

/-- The coefficient of degree `N` in `adj (XI-A)` is the identity matrix. -/
theorem coeff_adjugate_charmatrix_apply_card_sub_one
    {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (i j : Fin (N + 1)) :
    ((Matrix.charmatrix A).adjugate i j).coeff N = if i = j then 1 else 0 := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix,
    charmatrix_submatrix_succAbove]
  have hsign : ((-1 : ℂ[X]) ^ ((j : ℕ) + (i : ℕ))) =
      C ((-1 : ℂ) ^ ((j : ℕ) + (i : ℕ))) := by simp
  rw [hsign]
  rw [Polynomial.coeff_C_mul]
  have htop :
      (((X : ℂ[X]) •
          ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ).submatrix
            j.succAbove i.succAbove).map C +
        ((-A).submatrix j.succAbove i.succAbove).map C).det.coeff N) =
      ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ).submatrix
        j.succAbove i.succAbove).det := by
    simpa using Polynomial.coeff_det_X_add_C_card
      ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ).submatrix
        j.succAbove i.succAbove)
      ((-A).submatrix j.succAbove i.succAbove)
  rw [htop, det_one_submatrix_succAbove]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- The polynomial numerator `y* adj(XI-A) x` of a scalar resolvent
coefficient. -/
def adjugateScalarNumerator
    {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (y x : EuclideanVector (Fin (N + 1))) : ℂ[X] :=
  ∑ i, ∑ j,
    C ((starRingEnd ℂ) (y i)) * (Matrix.charmatrix A).adjugate i j * C (x j)

/-- A scalar adjugate numerator has degree at most one less than the matrix
size. -/
theorem natDegree_adjugateScalarNumerator_le
    {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (y x : EuclideanVector (Fin (N + 1))) :
    (adjugateScalarNumerator A y x).natDegree ≤ N := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact (Polynomial.natDegree_mul_C_le _ _).trans <|
    (Polynomial.natDegree_C_mul_le _ _).trans <|
      natDegree_adjugate_charmatrix_apply_le A i j

/-- Its top coefficient is the Hilbert-space scalar product `y*x`. -/
theorem coeff_adjugateScalarNumerator_card_sub_one
    {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (y x : EuclideanVector (Fin (N + 1))) :
    (adjugateScalarNumerator A y x).coeff N = ⟪y, x⟫_ℂ := by
  simp only [adjugateScalarNumerator, Polynomial.finsetSum_coeff,
    Polynomial.coeff_mul_C, Polynomial.coeff_C_mul,
    coeff_adjugate_charmatrix_apply_card_sub_one]
  rw [PiLp.inner_apply]
  simp [mul_comm]

/-- For a unit vector, the diagonal scalar resolvent numerator has the exact
degree asserted in Proposition 5.2. -/
theorem natDegree_adjugateScalarNumerator_self_eq
    {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (x : EuclideanVector (Fin (N + 1))) (hx : ‖x‖ = 1) :
    (adjugateScalarNumerator A x x).natDegree = N := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_adjugateScalarNumerator_le A x x)
  rw [coeff_adjugateScalarNumerator_card_sub_one,
    inner_self_eq_norm_sq_to_K, hx]
  norm_num

/-- For orthogonal vectors, the cross scalar resolvent numerator has strictly
smaller degree. -/
theorem natDegree_adjugateScalarNumerator_lt_of_inner_eq_zero
    {N : ℕ} (hN : 0 < N)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (y x : EuclideanVector (Fin (N + 1))) (hyx : ⟪y, x⟫_ℂ = 0) :
    (adjugateScalarNumerator A y x).natDegree < N := by
  let P := adjugateScalarNumerator A y x
  change P.natDegree < N
  by_cases hP : P = 0
  · simp [P, hP, hN]
  · have hcoeff : P.coeff N = 0 := by
      simpa [P] using (coeff_adjugateScalarNumerator_card_sub_one A y x).trans hyx
    have hne : P.natDegree ≠ N := by
      intro heq
      have hlc : P.coeff P.natDegree ≠ 0 := by
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hP
      rw [heq, hcoeff] at hlc
      exact hlc rfl
    have hle : P.natDegree ≤ N := natDegree_adjugateScalarNumerator_le A y x
    omega

/-- Equivalently, the cross numerator has degree at most `N - 1`. -/
theorem natDegree_adjugateScalarNumerator_le_card_sub_two
    {N : ℕ} (hN : 0 < N)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (y x : EuclideanVector (Fin (N + 1))) (hyx : ⟪y, x⟫_ℂ = 0) :
    (adjugateScalarNumerator A y x).natDegree ≤ N - 1 := by
  have hlt := natDegree_adjugateScalarNumerator_lt_of_inner_eq_zero hN A y x hyx
  omega

/-- Cancelling a rational transfer identity preserves its strict numerator
degree advantage.  This is the last sentence of Proposition 5.2, expressed
without choosing a particular gcd. -/
theorem reduced_transfer_numerator_degree_gt
    {U V A C : ℂ[X]} (hU : U ≠ 0) (hV : V ≠ 0)
    (hA : A ≠ 0) (hC : C ≠ 0)
    (htransfer : U * C = (Polynomial.C 2 * A) * V)
    (hdegree : C.natDegree < A.natDegree) :
    V.natDegree < U.natDegree := by
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hdeg : U.natDegree + C.natDegree =
      A.natDegree + V.natDegree := by
    calc
      U.natDegree + C.natDegree = (U * C).natDegree :=
        (Polynomial.natDegree_mul hU hC).symm
      _ = ((Polynomial.C 2 * A) * V).natDegree := congrArg _ htransfer
      _ = (Polynomial.C 2 * A).natDegree + V.natDegree :=
        Polynomial.natDegree_mul
          (mul_ne_zero (Polynomial.C_ne_zero.mpr htwo) hA) hV
      _ = A.natDegree + V.natDegree := by
        rw [Polynomial.natDegree_C_mul htwo]
  omega

/-- The scalar matrix coefficient written in coordinates. -/
def matrixScalarCoefficient
    {N : ℕ} (B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (y x : EuclideanVector (Fin (N + 1))) : ℂ :=
  ∑ i, (starRingEnd ℂ) (y i) * ∑ j, B i j * x j

/-- The coordinate expression agrees with the Hilbert-space coefficient. -/
theorem matrixScalarCoefficient_eq_inner
    {N : ℕ} (B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (y x : EuclideanVector (Fin (N + 1))) :
    matrixScalarCoefficient B y x = ⟪y, euclideanOperator B x⟫_ℂ := by
  rw [PiLp.inner_apply]
  simp only [matrixScalarCoefficient, euclideanOperator,
    Matrix.ofLp_toEuclideanCLM, RCLike.inner_apply]
  congr 1
  funext i
  simp only [Matrix.mulVec, dotProduct]
  ring

/-- Evaluating the characteristic matrix gives `zI-A`. -/
theorem map_charmatrix_evalRingHom
    {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (z : ℂ) :
    (Matrix.charmatrix A).map (Polynomial.evalRingHom z) = z • 1 - A := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- Scalar multiplication pulls out of a scalar matrix coefficient. -/
theorem matrixScalarCoefficient_smul
    {N : ℕ} (c : ℂ) (B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (y x : EuclideanVector (Fin (N + 1))) :
    matrixScalarCoefficient (c • B) y x = c * matrixScalarCoefficient B y x := by
  simp only [matrixScalarCoefficient, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Evaluation commutes with the adjugate of the characteristic matrix. -/
theorem eval_adjugate_charmatrix_apply
    {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (z : ℂ) (i j : Fin (N + 1)) :
    ((Matrix.charmatrix A).adjugate i j).eval z =
      (z • 1 - A).adjugate i j := by
  have hmap := RingHom.map_adjugate (Polynomial.evalRingHom z)
    (Matrix.charmatrix A)
  have happ := congrArg (fun M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ ↦ M i j)
    hmap
  have hmatrix : (Polynomial.evalRingHom z).mapMatrix (Matrix.charmatrix A) =
      z • 1 - A := map_charmatrix_evalRingHom A z
  rw [hmatrix] at happ
  change (Polynomial.evalRingHom z) ((Matrix.charmatrix A).adjugate i j) =
    (z • 1 - A).adjugate i j at happ
  simpa only [Polynomial.coe_evalRingHom] using happ

/-- Evaluating the scalar adjugate numerator gives the corresponding matrix
coefficient of `adj(zI-A)`. -/
theorem eval_adjugateScalarNumerator
    {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (y x : EuclideanVector (Fin (N + 1))) (z : ℂ) :
    (adjugateScalarNumerator A y x).eval z =
      matrixScalarCoefficient ((z • 1 - A).adjugate) y x := by
  simp only [adjugateScalarNumerator, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C,
    eval_adjugate_charmatrix_apply, matrixScalarCoefficient]
  congr 1
  funext i
  rw [Finset.mul_sum]
  simp only [mul_assoc]

/-- The characteristic polynomial is the common denominator of the scalar
resolvent coefficients. -/
theorem adjugateScalarNumerator_div_charpoly_eq_resolventCoefficient
    {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (y x : EuclideanVector (Fin (N + 1))) (z : ℂ) :
    (adjugateScalarNumerator A y x).eval z / A.charpoly.eval z =
      ⟪y, euclideanOperator ((z • 1 - A)⁻¹) x⟫_ℂ := by
  rw [eval_adjugateScalarNumerator, ← matrixScalarCoefficient_eq_inner,
    Matrix.inv_def]
  have hdet : (z • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) - A).det =
      A.charpoly.eval z := by
    rw [Matrix.eval_charpoly]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [matrixScalarCoefficient_smul, hdet, Ring.inverse_eq_inv,
    div_eq_mul_inv]
  ring

end DiskRigidity.Operator
