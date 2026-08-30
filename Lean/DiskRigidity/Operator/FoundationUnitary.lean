/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.FoundationAffine
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Unitary invariance of the numerical-range calculus

We express a unitary change of coordinates by a linear isometric equivalence
of the Euclidean column space.  This is equivalent to the unitary-matrix
formulation in Lemma 2.1(3), while avoiding a second coordinate calculation.
-/

noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator

@[expose] public section

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix/operator identification, restricted to its multiplicative
star structure. -/
def euclideanStarMonoidHom :
    SquareMatrix n →⋆* (EuclideanVector n →L[ℂ] EuclideanVector n) :=
  StarMonoidHom.mk euclideanOperator.toAlgEquiv.toMonoidHom
    (fun A ↦ map_star euclideanOperator A)

/-- The linear isometric equivalence represented by a unitary matrix. -/
def unitaryMatrixIsometry (U : Matrix.unitaryGroup n ℂ) :
    EuclideanVector n ≃ₗᵢ[ℂ] EuclideanVector n :=
  Unitary.linearIsometryEquiv
    (Unitary.map (euclideanStarMonoidHom (n := n)) U)

/-- The forward map of the isometry represented by `U`. -/
@[simp]
theorem unitaryMatrixIsometry_toContinuousLinearMap
    (U : Matrix.unitaryGroup n ℂ) :
    (unitaryMatrixIsometry U :
      EuclideanVector n →L[ℂ] EuclideanVector n) =
      euclideanOperator (U : SquareMatrix n) := by
  rfl

/-- The inverse isometry is represented by `U⁺`. -/
theorem unitaryMatrixIsometry_symm_toContinuousLinearMap
    (U : Matrix.unitaryGroup n ℂ) :
    ((unitaryMatrixIsometry U).symm :
      EuclideanVector n →L[ℂ] EuclideanVector n) =
      euclideanOperator (star (U : SquareMatrix n)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply (unitaryMatrixIsometry U).injective
  change (unitaryMatrixIsometry U) ((unitaryMatrixIsometry U).symm x) =
    (unitaryMatrixIsometry U) (euclideanOperator (star (U : SquareMatrix n)) x)
  rw [(unitaryMatrixIsometry U).apply_symm_apply]
  change x = euclideanOperator (U : SquareMatrix n)
    (euclideanOperator (star (U : SquareMatrix n)) x)
  have h := congrArg
    (fun M : SquareMatrix n ↦ euclideanOperator M x)
    (Unitary.coe_mul_star_self U)
  simpa only [map_mul, mul_apply_eq_comp, map_one,
    one_apply_eq_self, Unitary.coe_star] using h.symm

/-- Conjugation of a matrix by a unitary coordinate change. -/
def unitaryConjugate
    (e : EuclideanVector n ≃ₗᵢ[ℂ] EuclideanVector n)
    (A : SquareMatrix n) : SquareMatrix n :=
  euclideanOperator.symm
    (e.symm.conjStarAlgEquiv (euclideanOperator A))

/-- Operator form of unitary conjugation. -/
@[simp]
theorem euclideanOperator_unitaryConjugate
    (e : EuclideanVector n ≃ₗᵢ[ℂ] EuclideanVector n)
    (A : SquareMatrix n) :
    euclideanOperator (unitaryConjugate e A) =
      e.symm.conjStarAlgEquiv (euclideanOperator A) := by
  simp [unitaryConjugate]

/-- The coordinate-free definition is exactly the usual matrix expression
`U⁺ A U`. -/
theorem unitaryConjugate_unitaryMatrixIsometry
    (U : Matrix.unitaryGroup n ℂ) (A : SquareMatrix n) :
    unitaryConjugate (unitaryMatrixIsometry U) A =
      star (U : SquareMatrix n) * A * (U : SquareMatrix n) := by
  apply euclideanOperator.injective
  change euclideanOperator (unitaryConjugate (unitaryMatrixIsometry U) A) =
    euclideanOperator (star (U : SquareMatrix n) * A * (U : SquareMatrix n))
  rw [euclideanOperator_unitaryConjugate,
    LinearIsometryEquiv.conjStarAlgEquiv_apply,
    LinearIsometryEquiv.symm_symm, map_mul, map_mul,
    unitaryMatrixIsometry_toContinuousLinearMap,
    unitaryMatrixIsometry_symm_toContinuousLinearMap]
  rfl

/-- A unitary change of coordinates preserves the numerical range. -/
theorem numericalRange_unitaryConjugate
    (e : EuclideanVector n ≃ₗᵢ[ℂ] EuclideanVector n)
    (A : SquareMatrix n) :
    numericalRange (unitaryConjugate e A) = numericalRange A := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨e x, e.norm_map x |>.trans hx, ?_⟩
    rw [euclideanOperator_unitaryConjugate,
      LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
    have hinner := e.inner_map_map x
      (e.symm ((euclideanOperator A) (e x)))
    simpa only [LinearIsometryEquiv.symm_symm,
      e.apply_symm_apply] using hinner
  · rintro ⟨x, hx, rfl⟩
    refine ⟨e.symm x, e.symm.norm_map x |>.trans hx, ?_⟩
    rw [euclideanOperator_unitaryConjugate,
      LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
    have hinner := e.inner_map_map (e.symm x)
      (e.symm ((euclideanOperator A) x))
    simpa only [LinearIsometryEquiv.symm_symm,
      e.apply_symm_apply] using hinner.symm

/-- Evaluation commutes with the matrix/operator identification. -/
theorem euclideanOperator_polynomialEval
    (A : SquareMatrix n) (p : Polynomial ℂ) :
    euclideanOperator (polynomialEval p A) =
      Polynomial.aeval (euclideanOperator A) p := by
  have h := Polynomial.aeval_algHom
    euclideanOperator.toAlgEquiv.toAlgHom A
  exact (AlgHom.congr_fun h p).symm

/-- Polynomial evaluation is carried to unitary conjugation. -/
theorem polynomialEval_unitaryConjugate
    (e : EuclideanVector n ≃ₗᵢ[ℂ] EuclideanVector n)
    (A : SquareMatrix n) (p : Polynomial ℂ) :
    euclideanOperator (polynomialEval p (unitaryConjugate e A)) =
      e.symm.conjStarAlgEquiv
        (euclideanOperator (polynomialEval p A)) := by
  rw [euclideanOperator_polynomialEval,
    euclideanOperator_unitaryConjugate,
    euclideanOperator_polynomialEval]
  have h := Polynomial.aeval_algHom
    (e.symm.conjStarAlgEquiv.toAlgEquiv.toAlgHom) (euclideanOperator A)
  exact AlgHom.congr_fun h p

/-- Unitary conjugation preserves the norm of every polynomial value. -/
theorem norm_polynomialEval_unitaryConjugate
    (e : EuclideanVector n ≃ₗᵢ[ℂ] EuclideanVector n)
    (A : SquareMatrix n) (p : Polynomial ℂ) :
    ‖polynomialEval p (unitaryConjugate e A)‖ = ‖polynomialEval p A‖ := by
  rw [matrix_norm_eq_operator_norm, matrix_norm_eq_operator_norm,
    polynomialEval_unitaryConjugate]
  exact StarAlgEquiv.norm_map e.symm.conjStarAlgEquiv
    (euclideanOperator (polynomialEval p A))

/-- Unitary conjugation preserves polynomial maximum modulus. -/
theorem maxPolynomialModulus_unitaryConjugate
    (e : EuclideanVector n ≃ₗᵢ[ℂ] EuclideanVector n)
    (A : SquareMatrix n) (p : Polynomial ℂ) :
    maxPolynomialModulus (unitaryConjugate e A) p =
      maxPolynomialModulus A p := by
  simp only [maxPolynomialModulus, numericalRange_unitaryConjugate]

/-- The normalized polynomial values are unitarily invariant. -/
theorem normalizedPolynomialValues_unitaryConjugate
    (e : EuclideanVector n ≃ₗᵢ[ℂ] EuclideanVector n)
    (A : SquareMatrix n) :
    normalizedPolynomialValues (unitaryConjugate e A) =
      normalizedPolynomialValues A := by
  ext r
  constructor
  · rintro ⟨p, hp, hr⟩
    rw [maxPolynomialModulus_unitaryConjugate] at hp
    exact ⟨p, hp, by
      rw [norm_polynomialEval_unitaryConjugate] at hr
      exact hr⟩
  · rintro ⟨p, hp, hr⟩
    refine ⟨p, ?_, ?_⟩
    · rw [maxPolynomialModulus_unitaryConjugate]
      exact hp
    · rw [norm_polynomialEval_unitaryConjugate]
      exact hr

/-- Lemma 2.1(3), unitary invariance of the Crouzeix constant. -/
theorem crouzeixConstant_unitaryConjugate
    (e : EuclideanVector n ≃ₗᵢ[ℂ] EuclideanVector n)
    (A : SquareMatrix n) :
    crouzeixConstant (unitaryConjugate e A) = crouzeixConstant A := by
  simp only [crouzeixConstant,
    normalizedPolynomialValues_unitaryConjugate]

/-- Matrix-coordinate form of unitary numerical-range invariance. -/
theorem numericalRange_unitary_similarity
    (U : Matrix.unitaryGroup n ℂ) (A : SquareMatrix n) :
    numericalRange
        (star (U : SquareMatrix n) * A * (U : SquareMatrix n)) =
      numericalRange A := by
  rw [← unitaryConjugate_unitaryMatrixIsometry,
    numericalRange_unitaryConjugate]

/-- Matrix-coordinate form of unitary invariance of `ψ`. -/
theorem crouzeixConstant_unitary_similarity
    (U : Matrix.unitaryGroup n ℂ) (A : SquareMatrix n) :
    crouzeixConstant
        (star (U : SquareMatrix n) * A * (U : SquareMatrix n)) =
      crouzeixConstant A := by
  rw [← unitaryConjugate_unitaryMatrixIsometry,
    crouzeixConstant_unitaryConjugate]

end DiskRigidity.Operator
