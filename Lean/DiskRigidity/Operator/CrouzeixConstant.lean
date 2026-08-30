/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.NumericalRange
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Topology.Algebra.Polynomial

/-!
# The polynomial functional-calculus constant

This file formalizes the definitions in the opening paragraph of
`preprint/disk_rigidity.tex`.  The supremum is deliberately taken over the
same normalized family of polynomials as in the paper.
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

@[expose] public section

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Evaluation of a complex polynomial at a square matrix. -/
def polynomialEval (p : Polynomial ℂ) (A : SquareMatrix n) : SquareMatrix n :=
  Polynomial.aeval A p

/-- Maximum modulus of a polynomial on the numerical range.  Compactness and
nonemptiness show below that this supremum is an attained maximum. -/
def maxPolynomialModulus (A : SquareMatrix n) (p : Polynomial ℂ) : ℝ :=
  sSup ((fun z : ℂ ↦ ‖p.eval z‖) '' numericalRange A)

/-- The set of normalized polynomial-functional-calculus values occurring in
the definition of `ψ(A)`. -/
def normalizedPolynomialValues (A : SquareMatrix n) : Set ℝ :=
  {r | ∃ p : Polynomial ℂ,
    maxPolynomialModulus A p ≤ 1 ∧ ‖polynomialEval p A‖ = r}

/-- The Crouzeix functional-calculus constant `ψ(A)` from the manuscript. -/
def crouzeixConstant (A : SquareMatrix n) : ℝ :=
  sSup (normalizedPolynomialValues A)

/-- A continuous polynomial attains its maximum modulus on a nonempty
numerical range. -/
theorem exists_norm_eval_eq_maxPolynomialModulus [Nonempty n]
    (A : SquareMatrix n) (p : Polynomial ℂ) :
    ∃ z ∈ numericalRange A, ‖p.eval z‖ = maxPolynomialModulus A p := by
  obtain ⟨z, hz, hmax⟩ :=
    (isCompact_numericalRange A).exists_isMaxOn (α := ℝ)
      (f := fun w : ℂ ↦ ‖p.eval w‖) (numericalRange_nonempty A)
      p.continuous.norm.continuousOn
  refine ⟨z, hz, ?_⟩
  have hgreatest :
      IsGreatest ((fun w : ℂ ↦ ‖p.eval w‖) '' numericalRange A) ‖p.eval z‖ := by
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hmax hw
  exact hgreatest.csSup_eq.symm

/-- Every numerical-range value is bounded by the attained maximum modulus. -/
theorem norm_eval_le_maxPolynomialModulus [Nonempty n]
    (A : SquareMatrix n) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ numericalRange A) :
    ‖p.eval z‖ ≤ maxPolynomialModulus A p := by
  obtain ⟨w, hw, hmax⟩ :=
    (isCompact_numericalRange A).exists_isMaxOn (α := ℝ)
      (f := fun y : ℂ ↦ ‖p.eval y‖) (numericalRange_nonempty A)
      p.continuous.norm.continuousOn
  have hgreatest :
      IsGreatest ((fun y : ℂ ↦ ‖p.eval y‖) '' numericalRange A) ‖p.eval w‖ := by
    refine ⟨⟨w, hw, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax hy
  rw [maxPolynomialModulus, hgreatest.csSup_eq]
  exact hmax hz

/-- The maximum modulus is nonnegative. -/
theorem maxPolynomialModulus_nonneg [Nonempty n]
    (A : SquareMatrix n) (p : Polynomial ℂ) :
    0 ≤ maxPolynomialModulus A p := by
  obtain ⟨z, -, hz⟩ := exists_norm_eval_eq_maxPolynomialModulus A p
  rw [← hz]
  exact norm_nonneg _

end DiskRigidity.Operator
