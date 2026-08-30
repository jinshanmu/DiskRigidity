/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.FoundationSymmetries
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Affine invariance of the numerical-range calculus

This file proves the affine part of Lemma 2.1(3).  The proof follows the
manuscript literally: precomposition by the affine polynomial identifies the
two normalized polynomial families.
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

@[expose] public section

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Precomposition of a polynomial with `z ↦ a z + b`. -/
def affinePullbackPolynomial (a b : ℂ) (p : Polynomial ℂ) : Polynomial ℂ :=
  p.comp (Polynomial.C a * Polynomial.X + Polynomial.C b)

/-- Scalar evaluation of affine precomposition. -/
@[simp]
theorem affinePullbackPolynomial_eval (a b : ℂ) (p : Polynomial ℂ) (z : ℂ) :
    (affinePullbackPolynomial a b p).eval z = p.eval (a * z + b) := by
  simp [affinePullbackPolynomial, Polynomial.eval_comp]

/-- The numerical range transforms by the same affine map as the matrix. -/
theorem numericalRange_affine
    (A : SquareMatrix n) (a b : ℂ) :
    numericalRange (a • A + b • 1) =
      (fun z : ℂ ↦ a * z + b) '' numericalRange A := by
  rw [numericalRange_add_scalar, numericalRange_smul]
  ext z
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, by ring⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨a * v, ⟨v, hv, rfl⟩, by ring⟩

/-- Matrix evaluation also intertwines affine precomposition. -/
theorem polynomialEval_affinePullback
    (A : SquareMatrix n) (a b : ℂ) (p : Polynomial ℂ) :
    polynomialEval (affinePullbackPolynomial a b p) A =
      polynomialEval p (a • A + b • 1) := by
  rw [polynomialEval, polynomialEval, affinePullbackPolynomial,
    Polynomial.aeval_comp]
  congr 1
  simp [Polynomial.aeval_def, Algebra.algebraMap_eq_smul_one]

/-- Affine precomposition preserves the maximum modulus on the corresponding
numerical ranges. -/
theorem maxPolynomialModulus_affinePullback [Nonempty n]
    (A : SquareMatrix n) (a b : ℂ) (p : Polynomial ℂ) :
    maxPolynomialModulus A (affinePullbackPolynomial a b p) =
      maxPolynomialModulus (a • A + b • 1) p := by
  apply le_antisymm
  · obtain ⟨z, hz, hmax⟩ :=
      exists_norm_eval_eq_maxPolynomialModulus A
        (affinePullbackPolynomial a b p)
    rw [← hmax, affinePullbackPolynomial_eval]
    apply norm_eval_le_maxPolynomialModulus
    rw [numericalRange_affine]
    exact ⟨z, hz, rfl⟩
  · obtain ⟨z, hz, hmax⟩ :=
      exists_norm_eval_eq_maxPolynomialModulus (a • A + b • 1) p
    rw [← hmax]
    rw [numericalRange_affine] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [← affinePullbackPolynomial_eval]
    exact norm_eval_le_maxPolynomialModulus A
      (affinePullbackPolynomial a b p) hw

omit [Fintype n] in
/-- The inverse affine matrix identity used to compare normalized families. -/
theorem inverse_affine_matrix (A : SquareMatrix n) {a : ℂ} (ha : a ≠ 0)
    (b : ℂ) :
    a⁻¹ • (a • A + b • 1) + (-a⁻¹ * b) • 1 = A := by
  rw [smul_add, smul_smul, inv_mul_cancel₀ ha, one_smul, smul_smul]
  module

/-- The normalized values defining `ψ` are unchanged by a nondegenerate
affine transformation. -/
theorem normalizedPolynomialValues_affine [Nonempty n]
    (A : SquareMatrix n) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    normalizedPolynomialValues (a • A + b • 1) =
      normalizedPolynomialValues A := by
  let B : SquareMatrix n := a • A + b • 1
  have hBA : a⁻¹ • B + (-a⁻¹ * b) • 1 = A := by
    exact inverse_affine_matrix A ha b
  ext r
  constructor
  · rintro ⟨p, hp, hr⟩
    refine ⟨affinePullbackPolynomial a b p, ?_, ?_⟩
    · rw [maxPolynomialModulus_affinePullback]
      exact hp
    · rw [polynomialEval_affinePullback]
      exact hr
  · rintro ⟨p, hp, hr⟩
    refine ⟨affinePullbackPolynomial a⁻¹ (-a⁻¹ * b) p, ?_, ?_⟩
    · rw [maxPolynomialModulus_affinePullback, hBA]
      exact hp
    · rw [polynomialEval_affinePullback, hBA]
      exact hr

/-- Lemma 2.1(3), affine invariance of the Crouzeix constant. -/
theorem crouzeixConstant_affine [Nonempty n]
    (A : SquareMatrix n) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    crouzeixConstant (a • A + b • 1) = crouzeixConstant A := by
  simp only [crouzeixConstant, normalizedPolynomialValues_affine A ha b]

end DiskRigidity.Operator
