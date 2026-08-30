/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.FoundationGeometry
public import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# Adjoint symmetry of the numerical range and functional calculus

This file formalizes the adjoint part of Lemma 2.1(3).  Coefficientwise
conjugation of a polynomial implements the reflected scalar function and
turns evaluation at `Aᴴ` into the adjoint of evaluation at `A`.
-/

noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator

@[expose] public section

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Taking the conjugate transpose reflects the numerical range in the real
axis. -/
theorem numericalRange_conjTranspose (A : SquareMatrix n) :
    numericalRange Aᴴ = starRingEnd ℂ '' numericalRange A := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟪x, euclideanOperator A x⟫_ℂ, ⟨x, hx, rfl⟩, ?_⟩
    rw [euclideanOperator_conjTranspose,
      ContinuousLinearMap.adjoint_inner_right]
    exact inner_conj_symm (𝕜 := ℂ) (euclideanOperator A x) x
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [euclideanOperator_conjTranspose,
      ContinuousLinearMap.adjoint_inner_right]
    exact (inner_conj_symm (𝕜 := ℂ) (euclideanOperator A x) x).symm

/-- Coefficientwise complex conjugation, representing
`z ↦ conj (p (conj z))`. -/
def conjugatePolynomial (p : Polynomial ℂ) : Polynomial ℂ :=
  p.map (starRingEnd ℂ)

/-- The reflected polynomial has the expected scalar values. -/
theorem conjugatePolynomial_eval (p : Polynomial ℂ) (z : ℂ) :
    (conjugatePolynomial p).eval z =
      starRingEnd ℂ (p.eval (starRingEnd ℂ z)) := by
  have h := Polynomial.eval_map_apply (p := p) (starRingEnd ℂ)
    (starRingEnd ℂ z)
  simpa only [conjugatePolynomial, starRingEnd_apply, star_star] using h

/-- Coefficientwise conjugation is an involution. -/
@[simp]
theorem conjugatePolynomial_conjugatePolynomial (p : Polynomial ℂ) :
    conjugatePolynomial (conjugatePolynomial p) = p := by
  ext k
  simp [conjugatePolynomial]

/-- The maximum modulus is unchanged by simultaneous reflection of the
matrix and polynomial. -/
theorem maxPolynomialModulus_conjTranspose_conjugate_le [Nonempty n]
    (A : SquareMatrix n) (p : Polynomial ℂ) :
    maxPolynomialModulus Aᴴ (conjugatePolynomial p) ≤
      maxPolynomialModulus A p := by
  obtain ⟨z, hz, hmax⟩ :=
    exists_norm_eval_eq_maxPolynomialModulus Aᴴ (conjugatePolynomial p)
  rw [← hmax]
  rw [numericalRange_conjTranspose] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [conjugatePolynomial_eval]
  simp only [starRingEnd_apply, star_star, norm_star]
  exact norm_eval_le_maxPolynomialModulus A p hw

/-- Exact maximum-modulus invariance under adjoints. -/
theorem maxPolynomialModulus_conjTranspose_conjugate [Nonempty n]
    (A : SquareMatrix n) (p : Polynomial ℂ) :
    maxPolynomialModulus Aᴴ (conjugatePolynomial p) =
      maxPolynomialModulus A p := by
  apply le_antisymm
  · exact maxPolynomialModulus_conjTranspose_conjugate_le A p
  · simpa using
      maxPolynomialModulus_conjTranspose_conjugate_le Aᴴ
        (conjugatePolynomial p)

/-- Polynomial evaluation intertwines adjoints and coefficientwise
conjugation. -/
theorem polynomialEval_conjugate_conjTranspose
    (A : SquareMatrix n) (p : Polynomial ℂ) :
    polynomialEval (conjugatePolynomial p) Aᴴ =
      (polynomialEval p A)ᴴ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [conjugatePolynomial, Polynomial.map_add, polynomialEval,
        map_add, Matrix.conjTranspose_add] using congrArg₂ (fun X Y ↦ X + Y) hp hq
  | monomial k a =>
      simp [conjugatePolynomial, polynomialEval, Polynomial.aeval_def,
        Matrix.conjTranspose_pow]
      simp [Algebra.algebraMap_eq_smul_one]

/-- The normalized values defining `ψ` are identical for a matrix and its
adjoint. -/
theorem normalizedPolynomialValues_conjTranspose [Nonempty n]
    (A : SquareMatrix n) :
    normalizedPolynomialValues Aᴴ = normalizedPolynomialValues A := by
  ext r
  constructor
  · rintro ⟨p, hp, hr⟩
    refine ⟨conjugatePolynomial p, ?_, ?_⟩
    · simpa using
        (show maxPolynomialModulus (Aᴴ)ᴴ (conjugatePolynomial p) ≤ 1 by
          rw [maxPolynomialModulus_conjTranspose_conjugate]
          exact hp)
    · have hEval := polynomialEval_conjugate_conjTranspose Aᴴ p
      rw [Matrix.conjTranspose_conjTranspose] at hEval
      rw [hEval, Matrix.l2_opNorm_conjTranspose]
      exact hr
  · rintro ⟨p, hp, hr⟩
    refine ⟨conjugatePolynomial p, ?_, ?_⟩
    · rw [maxPolynomialModulus_conjTranspose_conjugate]
      exact hp
    · rw [polynomialEval_conjugate_conjTranspose,
        Matrix.l2_opNorm_conjTranspose]
      exact hr

/-- Lemma 2.1(3), adjoint invariance of the Crouzeix constant. -/
theorem crouzeixConstant_conjTranspose [Nonempty n] (A : SquareMatrix n) :
    crouzeixConstant Aᴴ = crouzeixConstant A := by
  simp only [crouzeixConstant, normalizedPolynomialValues_conjTranspose]

end DiskRigidity.Operator
