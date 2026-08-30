/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.BoundarySpectrum
public import DiskRigidity.Operator.FoundationGeometry
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Peeling boundary eigenvalues

This file completes Lemma 3.4 of the manuscript.  The span of all unit
boundary eigenvectors is shown to reduce the matrix, and every eigenvalue on
its orthogonal complement is in the interior of the numerical range.
-/

noncomputable section

open WithLp
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator

@[expose] public section

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Unit eigenvectors whose eigenvalues lie on the numerical-range boundary. -/
def boundaryEigenvectors (A : SquareMatrix n) : Set (EuclideanVector n) :=
  {x | ‖x‖ = 1 ∧ ∃ lambda ∈ frontier (numericalRange A),
    euclideanOperator A x = lambda • x}

/-- The subspace peeled off in Lemma 3.4. -/
def boundaryEigenspaceSpan (A : SquareMatrix n) :
    Submodule ℂ (EuclideanVector n) :=
  Submodule.span ℂ (boundaryEigenvectors A)

omit [Nonempty n] in
/-- Coordinate conversion for an eigenvector of the Euclidean operator. -/
theorem mulVec_eq_smul_of_euclideanOperator_eq_smul
    (A : SquareMatrix n) {lambda : ℂ} {x : EuclideanVector n}
    (hx : euclideanOperator A x = lambda • x) :
    A *ᵥ ofLp x = lambda • ofLp x := by
  exact congrArg ofLp hx

omit [Nonempty n] in
/-- Coordinate conversion back from a matrix-vector identity. -/
theorem euclideanOperator_eq_smul_of_mulVec_eq_smul
    (A : SquareMatrix n) {lambda : ℂ} {x : EuclideanVector n}
    (hx : A *ᵥ ofLp x = lambda • ofLp x) :
    euclideanOperator A x = lambda • x := by
  apply WithLp.ofLp_injective
  exact hx

omit [Nonempty n] in
/-- Every boundary eigenvector is also an adjoint eigenvector. -/
theorem euclideanOperator_conjTranspose_eq_smul_of_mem_boundaryEigenvectors
    (A : SquareMatrix n) (hInt : (interior (numericalRange A)).Nonempty)
    {x : EuclideanVector n} (hx : x ∈ boundaryEigenvectors A) :
    euclideanOperator Aᴴ x = star (Classical.choose hx.2) • x := by
  let lambda : ℂ := Classical.choose hx.2
  have hlambda : lambda ∈ frontier (numericalRange A) :=
    (Classical.choose_spec hx.2).1
  have hAx : euclideanOperator A x = lambda • x :=
    (Classical.choose_spec hx.2).2
  apply euclideanOperator_eq_smul_of_mulVec_eq_smul
  exact conjTranspose_mulVec_eq_of_eigenvalue_mem_frontier
    A x hx.1 (mulVec_eq_smul_of_euclideanOperator_eq_smul A hAx)
      hInt hlambda

omit [Nonempty n] in
/-- The boundary-eigenvector span is invariant under the matrix. -/
theorem map_boundaryEigenspaceSpan_le (A : SquareMatrix n) :
    (boundaryEigenspaceSpan A).map (euclideanOperator A).toLinearMap ≤
      boundaryEigenspaceSpan A := by
  rw [boundaryEigenspaceSpan, LinearMap.map_span_le]
  intro x hx
  have hxspan : x ∈ Submodule.span ℂ (boundaryEigenvectors A) :=
    Submodule.subset_span hx
  obtain ⟨-, lambda, -, hAx⟩ := hx
  change euclideanOperator A x ∈ Submodule.span ℂ (boundaryEigenvectors A)
  rw [hAx]
  exact (Submodule.span ℂ (boundaryEigenvectors A)).smul_mem lambda
    hxspan

omit [Nonempty n] in
/-- The boundary-eigenvector span is invariant under the adjoint. -/
theorem map_conjTranspose_boundaryEigenspaceSpan_le
    (A : SquareMatrix n) (hInt : (interior (numericalRange A)).Nonempty) :
    (boundaryEigenspaceSpan A).map (euclideanOperator Aᴴ).toLinearMap ≤
      boundaryEigenspaceSpan A := by
  rw [boundaryEigenspaceSpan, LinearMap.map_span_le]
  intro x hx
  change euclideanOperator Aᴴ x ∈ Submodule.span ℂ (boundaryEigenvectors A)
  rw [euclideanOperator_conjTranspose_eq_smul_of_mem_boundaryEigenvectors A hInt hx]
  exact (Submodule.span ℂ (boundaryEigenvectors A)).smul_mem _
    (Submodule.subset_span hx)

omit [DecidableEq n] [Nonempty n] in
/-- If the adjoint preserves a subspace, the original operator preserves its
orthogonal complement. -/
theorem map_orthogonal_le_of_map_adjoint_le
    {S : Submodule ℂ (EuclideanVector n)}
    (T : EuclideanVector n →L[ℂ] EuclideanVector n)
    (hT : S.map T.adjoint.toLinearMap ≤ S) :
    Sᗮ.map T.toLinearMap ≤ Sᗮ := by
  rintro z ⟨x, hx, rfl⟩
  rw [Submodule.mem_orthogonal]
  intro y hy
  change ⟪y, T x⟫_ℂ = 0
  rw [← T.adjoint_inner_left x y]
  exact Submodule.inner_right_of_mem_orthogonal
    (hT ⟨y, hy, rfl⟩) hx

omit [Nonempty n] in
/-- The orthogonal complement of the boundary span is invariant under `A`. -/
theorem map_boundaryEigenspaceSpan_orthogonal_le
    (A : SquareMatrix n) (hInt : (interior (numericalRange A)).Nonempty) :
    (boundaryEigenspaceSpan A)ᗮ.map (euclideanOperator A).toLinearMap ≤
      (boundaryEigenspaceSpan A)ᗮ := by
  apply map_orthogonal_le_of_map_adjoint_le
  rw [← euclideanOperator_conjTranspose A]
  exact map_conjTranspose_boundaryEigenspaceSpan_le A hInt

omit [Nonempty n] in
/-- The orthogonal complement of the boundary span is also invariant under
the adjoint. -/
theorem map_conjTranspose_boundaryEigenspaceSpan_orthogonal_le
    (A : SquareMatrix n) :
    (boundaryEigenspaceSpan A)ᗮ.map (euclideanOperator Aᴴ).toLinearMap ≤
      (boundaryEigenspaceSpan A)ᗮ := by
  apply map_orthogonal_le_of_map_adjoint_le
  rw [euclideanOperator_conjTranspose A, ContinuousLinearMap.adjoint_adjoint]
  exact map_boundaryEigenspaceSpan_le A

omit [Nonempty n] in
/-- A nonzero eigenvector in the orthogonal complement cannot have a
boundary eigenvalue. -/
theorem eigenvalue_not_mem_frontier_of_mem_boundaryEigenspaceSpan_orthogonal
    (A : SquareMatrix n) {lambda : ℂ} {v : EuclideanVector n}
    (hvS : v ∈ (boundaryEigenspaceSpan A)ᗮ) (hv0 : v ≠ 0)
    (hAv : euclideanOperator A v = lambda • v) :
    lambda ∉ frontier (numericalRange A) := by
  intro hlambda
  let x : EuclideanVector n := (‖v‖⁻¹ : ℂ) • v
  have hxnorm : ‖x‖ = 1 := norm_smul_inv_norm hv0
  have hAx : euclideanOperator A x = lambda • x := by
    simp only [x, map_smul, hAv, smul_smul]
    rw [mul_comm]
  have hxBoundary : x ∈ boundaryEigenvectors A :=
    ⟨hxnorm, lambda, hlambda, hAx⟩
  have hxS : x ∈ boundaryEigenspaceSpan A :=
    Submodule.subset_span hxBoundary
  have hxOrth : x ∈ (boundaryEigenspaceSpan A)ᗮ := by
    exact (boundaryEigenspaceSpan A)ᗮ.smul_mem (‖v‖⁻¹ : ℂ) hvS
  have hxx : ⟪x, x⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hxS hxOrth
  have hx0 : x = 0 := inner_self_eq_zero.mp hxx
  rw [hx0, norm_zero] at hxnorm
  exact zero_ne_one hxnorm

omit [Nonempty n] in
/-- Every eigenvalue left after peeling the boundary span lies in the
interior of the original numerical range. -/
theorem eigenvalue_mem_interior_of_mem_boundaryEigenspaceSpan_orthogonal
    (A : SquareMatrix n) {lambda : ℂ} {v : EuclideanVector n}
    (hvS : v ∈ (boundaryEigenspaceSpan A)ᗮ) (hv0 : v ≠ 0)
    (hAv : euclideanOperator A v = lambda • v) :
    lambda ∈ interior (numericalRange A) := by
  let x : EuclideanVector n := (‖v‖⁻¹ : ℂ) • v
  have hxnorm : ‖x‖ = 1 := norm_smul_inv_norm hv0
  have hAx : euclideanOperator A x = lambda • x := by
    simp only [x, map_smul, hAv, smul_smul]
    rw [mul_comm]
  have hlambdaW : lambda ∈ numericalRange A := by
    refine ⟨x, hxnorm, ?_⟩
    rw [hAx, inner_smul_right, inner_self_eq_norm_sq_to_K, hxnorm]
    norm_num
  exact (mem_interior_iff_notMem_frontier hlambdaW).2
    (eigenvalue_not_mem_frontier_of_mem_boundaryEigenspaceSpan_orthogonal
      A hvS hv0 hAv)

/-- A bundled version of the complete reducing decomposition in Lemma 3.4. -/
structure BoundaryReducingDecomposition (A : SquareMatrix n) where
  map_matrix : (boundaryEigenspaceSpan A).map
      (euclideanOperator A).toLinearMap ≤ boundaryEigenspaceSpan A
  map_adjoint : (boundaryEigenspaceSpan A).map
      (euclideanOperator Aᴴ).toLinearMap ≤ boundaryEigenspaceSpan A
  map_matrix_orthogonal : (boundaryEigenspaceSpan A)ᗮ.map
      (euclideanOperator A).toLinearMap ≤ (boundaryEigenspaceSpan A)ᗮ
  map_adjoint_orthogonal : (boundaryEigenspaceSpan A)ᗮ.map
      (euclideanOperator Aᴴ).toLinearMap ≤ (boundaryEigenspaceSpan A)ᗮ
  complement_eigenvalue_interior :
    ∀ {lambda : ℂ} {v : EuclideanVector n},
      v ∈ (boundaryEigenspaceSpan A)ᗮ → v ≠ 0 →
      euclideanOperator A v = lambda • v → lambda ∈ interior (numericalRange A)

omit [Nonempty n] in
/-- Lemma 3.4, complete reducing decomposition. -/
theorem boundaryReducingDecomposition
    (A : SquareMatrix n) (hInt : (interior (numericalRange A)).Nonempty) :
    BoundaryReducingDecomposition A where
  map_matrix := map_boundaryEigenspaceSpan_le A
  map_adjoint := map_conjTranspose_boundaryEigenspaceSpan_le A hInt
  map_matrix_orthogonal := map_boundaryEigenspaceSpan_orthogonal_le A hInt
  map_adjoint_orthogonal := map_conjTranspose_boundaryEigenspaceSpan_orthogonal_le A
  complement_eigenvalue_interior :=
    eigenvalue_mem_interior_of_mem_boundaryEigenspaceSpan_orthogonal A

end DiskRigidity.Operator
