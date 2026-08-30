/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.FoundationUnitary
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Invariance under a change of finite index type

Relabelling the coordinates of a finite matrix is a unitary equivalence.
This file records the resulting invariance of the numerical range and of the
polynomial functional-calculus constant.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

variable {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

/-- Relabelling coordinates is a linear isometry of Euclidean column
spaces. -/
def euclideanReindex (e : n ≃ m) :
    EuclideanVector n ≃ₗᵢ[ℂ] EuclideanVector m :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

omit [DecidableEq n] [DecidableEq m] in
@[simp]
theorem euclideanReindex_apply (e : n ≃ m) (x : EuclideanVector n)
    (j : m) :
    euclideanReindex e x j = x (e.symm j) :=
  rfl

omit [DecidableEq n] [DecidableEq m] in
@[simp]
theorem euclideanReindex_symm_apply (e : n ≃ m) (x : EuclideanVector m)
    (i : n) :
    (euclideanReindex e).symm x i = x (e i) := by
  rw [euclideanReindex, LinearIsometryEquiv.piLpCongrLeft_symm]
  rfl

/-- Matrix reindexing is the operator conjugation induced by the coordinate
isometry. -/
theorem euclideanOperator_reindex (e : n ≃ m) (A : SquareMatrix n) :
    euclideanOperator (Matrix.reindex e e A) =
      (euclideanReindex e).conjStarAlgEquiv (euclideanOperator A) := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro j
  simp only [euclideanOperator, Matrix.ofLp_toEuclideanCLM,
    Matrix.mulVec, dotProduct, Matrix.reindex_apply,
    Matrix.submatrix_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    euclideanReindex_apply, euclideanReindex_symm_apply]
  exact Fintype.sum_equiv e.symm _ _ (fun i ↦ by simp)

/-- Relabelling coordinates preserves the numerical range. -/
theorem numericalRange_reindex
    (e : n ≃ m) (A : SquareMatrix n) :
    numericalRange (Matrix.reindex e e A) = numericalRange A := by
  let E := euclideanReindex e
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨E.symm x, E.symm.norm_map x |>.trans hx, ?_⟩
    rw [euclideanOperator_reindex]
    change ⟪E.symm x, euclideanOperator A (E.symm x)⟫_ℂ =
      ⟪x, E (euclideanOperator A (E.symm x))⟫_ℂ
    simpa only [E.apply_symm_apply] using
      (E.inner_map_map (E.symm x)
        (euclideanOperator A (E.symm x))).symm
  · rintro ⟨x, hx, rfl⟩
    refine ⟨E x, E.norm_map x |>.trans hx, ?_⟩
    rw [euclideanOperator_reindex]
    simp [E, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

/-- Polynomial evaluation commutes with reindexing. -/
theorem polynomialEval_reindex (e : n ≃ m)
    (A : SquareMatrix n) (p : Polynomial ℂ) :
    euclideanOperator (polynomialEval p (Matrix.reindex e e A)) =
      (euclideanReindex e).conjStarAlgEquiv
        (euclideanOperator (polynomialEval p A)) := by
  rw [euclideanOperator_polynomialEval, euclideanOperator_reindex,
    euclideanOperator_polynomialEval]
  exact AlgHom.congr_fun
    (Polynomial.aeval_algHom
      (euclideanReindex e).conjStarAlgEquiv.toAlgEquiv.toAlgHom
      (euclideanOperator A)) p

/-- Polynomial matrix norms are unchanged by relabelling. -/
theorem norm_polynomialEval_reindex (e : n ≃ m)
    (A : SquareMatrix n) (p : Polynomial ℂ) :
    ‖polynomialEval p (Matrix.reindex e e A)‖ =
      ‖polynomialEval p A‖ := by
  rw [matrix_norm_eq_operator_norm, matrix_norm_eq_operator_norm,
    polynomialEval_reindex]
  exact StarAlgEquiv.norm_map (euclideanReindex e).conjStarAlgEquiv
    (euclideanOperator (polynomialEval p A))

/-- The polynomial maximum on the numerical range is unchanged by
relabelling. -/
theorem maxPolynomialModulus_reindex
    (e : n ≃ m) (A : SquareMatrix n) (p : Polynomial ℂ) :
    maxPolynomialModulus (Matrix.reindex e e A) p =
      maxPolynomialModulus A p := by
  simp only [maxPolynomialModulus, numericalRange_reindex e A]

/-- The Crouzeix functional-calculus constant is invariant under a change
of finite index type. -/
theorem crouzeixConstant_reindex
    (e : n ≃ m) (A : SquareMatrix n) :
    crouzeixConstant (Matrix.reindex e e A) = crouzeixConstant A := by
  rw [crouzeixConstant]
  congr 1
  ext r
  constructor <;> rintro ⟨p, hp, rfl⟩
  · refine ⟨p, ?_, (norm_polynomialEval_reindex e A p).symm⟩
    rwa [maxPolynomialModulus_reindex e A p] at hp
  · refine ⟨p, ?_, norm_polynomialEval_reindex e A p⟩
    rwa [maxPolynomialModulus_reindex e A p]

/-- Reindexing preserves the matrix spectrum. -/
theorem spectrum_reindex (e : n ≃ m) (A : SquareMatrix n) :
    spectrum ℂ (Matrix.reindex e e A) = spectrum ℂ A := by
  exact AlgEquiv.spectrum_eq (Matrix.reindexAlgEquiv ℂ ℂ e) A

end DiskRigidity.Operator
