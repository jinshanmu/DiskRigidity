/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Basic matrix conventions

This module fixes the Euclidean vector, square-matrix, operator, adjoint, and
Hermitian-real-part conventions used throughout the formalization.
-/

@[expose] public section

noncomputable section

open WithLp
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

/-- The column Hilbert space `\mathbb C^n` used in the manuscript. -/
abbrev EuclideanVector (n : Type*) := EuclideanSpace ℂ n

/-- Square complex matrices. -/
abbrev SquareMatrix (n : Type*) := Matrix n n ℂ

/-- A matrix acting on its Euclidean column Hilbert space. -/
def euclideanOperator {n : Type*} [Fintype n] [DecidableEq n] :
    SquareMatrix n ≃⋆ₐ[ℂ] (EuclideanVector n →L[ℂ] EuclideanVector n) :=
  Matrix.toEuclideanCLM

/-- The matrix norm is the induced Euclidean operator norm. -/
theorem matrix_norm_eq_operator_norm {n : Type*} [Fintype n] [DecidableEq n]
    (A : SquareMatrix n) : ‖A‖ = ‖euclideanOperator A‖ :=
  rfl

/-- Conjugate transpose corresponds to the Hilbert-space adjoint. -/
theorem euclideanOperator_conjTranspose {n : Type*} [Fintype n] [DecidableEq n]
    (A : SquareMatrix n) :
    euclideanOperator Aᴴ = ContinuousLinearMap.adjoint (euclideanOperator A) := by
  exact map_star (euclideanOperator (n := n)) A

/-- The Hermitian real part `(A + A⁺) / 2`. -/
def rePart {n : Type*} (A : SquareMatrix n) : SquareMatrix n :=
  (2 : ℂ)⁻¹ • (A + Aᴴ)

end DiskRigidity.Operator
