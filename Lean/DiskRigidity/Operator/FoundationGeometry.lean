/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.CrouzeixConstant
public import DiskRigidity.Operator.NumericalRangeConvexity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-!
# Degenerate numerical ranges

This file proves the second part of the numerical-range foundation lemma in
the manuscript.  The proof follows the text: normalize arbitrary vectors,
use complex polarization to recognize a Hermitian affine transform, and then
apply the isometric functional calculus for a normal matrix.
-/

noncomputable section

open scoped ContinuousFunctionalCalculus InnerProductSpace Matrix Matrix.Norms.L2Operator
  RealInnerProductSpace

@[expose] public section

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A concrete coordinate-free formulation that a subset of the complex
plane is contained in an affine real line. -/
def IsContainedInAffineLine (K : Set ℂ) : Prop :=
  ∃ a b : ℂ, a ≠ 0 ∧ ∀ z ∈ K, (a * (z - b)).im = 0

/-- A nonempty convex planar set with empty interior is contained in an
affine line.  This is the finite-dimensional affine-span argument used
implicitly in the manuscript's base case. -/
theorem isContainedInAffineLine_of_convex_of_interior_not_nonempty
    {K : Set ℂ} (hK : Convex ℝ K) (hKne : K.Nonempty)
    (hKint : ¬ (interior K).Nonempty) :
    IsContainedInAffineLine K := by
  obtain ⟨b, hb⟩ := hKne
  let P : AffineSubspace ℝ ℂ := affineSpan ℝ K
  have hPne : (P : Set ℂ).Nonempty :=
    ⟨b, mem_affineSpan ℝ hb⟩
  have hP_ne_top : P ≠ ⊤ := by
    intro hP
    apply hKint
    exact (hK.interior_nonempty_iff_affineSpan_eq_top).2 hP
  let S : Submodule ℝ ℂ := P.direction
  have hS_ne_top : S ≠ ⊤ := by
    intro hS
    apply hP_ne_top
    exact (AffineSubspace.direction_eq_top_iff_of_nonempty hPne).1 hS
  have hSortho_ne_bot : Sᗮ ≠ ⊥ := by
    intro hbot
    apply hS_ne_top
    exact Submodule.orthogonal_eq_bot_iff.mp hbot
  obtain ⟨c, hcS, hc0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hSortho_ne_bot
  refine ⟨Complex.I * star c, b, by simp [hc0], ?_⟩
  intro z hz
  have hzP : z ∈ P := mem_affineSpan ℝ hz
  have hbP : b ∈ P := mem_affineSpan ℝ hb
  have hdiff : z - b ∈ S := by
    simpa only [P, S, vsub_eq_sub] using
      AffineSubspace.vsub_mem_direction hzP hbP
  have hinner : ⟪c, z - b⟫_ℝ = 0 :=
    Submodule.inner_left_of_mem_orthogonal hdiff hcS
  rw [mul_assoc, Complex.I_mul_im]
  simpa only [Complex.inner, RCLike.star_def, mul_comm] using hinner

/-- Real quadratic forms on the unit sphere are real on every vector. -/
theorem isHermitian_of_unit_quadraticForm_real (A : SquareMatrix n)
    (hA : ∀ x : EuclideanVector n, ‖x‖ = 1 →
      starRingEnd ℂ ⟪Matrix.toEuclideanLin A x, x⟫_ℂ =
        ⟪Matrix.toEuclideanLin A x, x⟫_ℂ) :
    A.IsHermitian := by
  rw [← Matrix.isSymmetric_toEuclideanLin_iff]
  rw [LinearMap.isSymmetric_iff_inner_map_self_real]
  intro x
  by_cases hx : x = 0
  · simp [hx]
  let u : EuclideanVector n := (‖x‖⁻¹ : ℂ) • x
  have hu : ‖u‖ = 1 := by
    exact norm_smul_inv_norm hx
  have hreal := hA u hu
  have hx_eq : x = (‖x‖ : ℂ) • u := by
    simp only [u, smul_smul]
    rw [mul_inv_cancel₀ (mod_cast (norm_ne_zero_iff.mpr hx))]
    simp
  rw [hx_eq]
  simp only [map_smul, inner_smul_left, inner_smul_right]
  rw [map_mul, map_mul, hreal]
  simp only [starRingEnd_apply, star_star]
  rw [RCLike.star_def, Complex.conj_ofReal]

/-- If all numerical-range values are real, the matrix is Hermitian. -/
theorem isHermitian_of_numericalRange_subset_real
    (A : SquareMatrix n)
    (hA : ∀ z ∈ numericalRange A, z.im = 0) :
    A.IsHermitian := by
  apply isHermitian_of_unit_quadraticForm_real A
  intro x hx
  have hz : ⟪x, euclideanOperator A x⟫_ℂ ∈ numericalRange A :=
    ⟨x, hx, rfl⟩
  have him := hA _ hz
  have hreal : starRingEnd ℂ ⟪x, euclideanOperator A x⟫_ℂ =
      ⟪x, euclideanOperator A x⟫_ℂ :=
    Complex.conj_eq_iff_im.mpr him
  rw [inner_conj_symm] at hreal
  change ⟪Matrix.toEuclideanLin A x, x⟫_ℂ =
    ⟪x, Matrix.toEuclideanLin A x⟫_ℂ at hreal
  rw [inner_conj_symm]
  exact hreal.symm

/-- The affine transform that sends a line containing the numerical range to
the real axis is Hermitian. -/
theorem isHermitian_affine_transform_of_numericalRange_in_line
    (A : SquareMatrix n) (hline : IsContainedInAffineLine (numericalRange A)) :
    ∃ a b : ℂ, a ≠ 0 ∧ (a • (A - b • 1)).IsHermitian := by
  obtain ⟨a, b, ha, hline⟩ := hline
  refine ⟨a, b, ha, isHermitian_of_numericalRange_subset_real
    (a • (A - b • 1)) ?_⟩
  intro z hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hw : ⟪x, euclideanOperator A x⟫_ℂ ∈ numericalRange A := ⟨x, hx, rfl⟩
  simpa only [map_smul, map_sub, map_one, smul_apply, sub_apply, one_apply_eq_self,
    inner_smul_right, inner_sub_right, inner_self_eq_norm_sq_to_K, hx,
    norm_one, one_pow, mul_one, smul_eq_mul] using hline _ hw

/-- Every matrix whose numerical range is contained in a line is normal. -/
theorem isStarNormal_of_numericalRange_in_line
    (A : SquareMatrix n) (hline : IsContainedInAffineLine (numericalRange A)) :
    IsStarNormal A := by
  obtain ⟨a, b, ha, hB⟩ :=
    isHermitian_affine_transform_of_numericalRange_in_line A hline
  let B : SquareMatrix n := a • (A - b • 1)
  have hBnormal : IsStarNormal B := by
    refine ⟨?_⟩
    rw [show star B = B from hB.eq]
  have hsolve : A = a⁻¹ • B + b • 1 := by
    simp only [B, smul_smul, inv_mul_cancel₀ ha, one_smul]
    abel
  rw [hsolve]
  have hleft : IsStarNormal (a⁻¹ • B) :=
    IsStarNormal.smul a⁻¹ B (ha := hBnormal)
  have hright : IsStarNormal (b • (1 : SquareMatrix n)) :=
    IsStarNormal.smul b (1 : SquareMatrix n)
  apply Commute.isStarNormal_add (ha := hleft) (hb := hright)
  rw [star_smul, star_one]
  exact (Commute.one_right B).smul_left a⁻¹ |>.smul_right (star b)

/-- Every spectral value of a finite complex matrix is realized by a unit
eigenvector and hence belongs to its numerical range. -/
theorem spectrum_subset_numericalRange (A : SquareMatrix n) :
    spectrum ℂ A ⊆ numericalRange A := by
  intro lambda hlambda
  have heig : Module.End.HasEigenvalue (Matrix.toEuclideanLin A) lambda := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum]
    simpa only [Matrix.spectrum_toLpLin] using hlambda
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  let x : EuclideanVector n := (‖v‖⁻¹ : ℂ) • v
  have hvne : v ≠ 0 := hv.2
  have hxnorm : ‖x‖ = 1 := norm_smul_inv_norm hvne
  refine ⟨x, hxnorm, ?_⟩
  have hAx : Matrix.toEuclideanLin A x = lambda • x := by
    simp only [x, map_smul, hv.apply_eq_smul, smul_smul]
    rw [mul_comm]
  change ⟪x, Matrix.toEuclideanLin A x⟫_ℂ = lambda
  rw [hAx, inner_smul_right, inner_self_eq_norm_sq_to_K, hxnorm]
  norm_num

/-- Polynomial evaluation at a normal matrix is bounded by the maximum of
the polynomial on the numerical range. -/
theorem norm_polynomialEval_le_maxPolynomialModulus_of_isStarNormal
    [Nonempty n] (A : SquareMatrix n) (hA : IsStarNormal A)
    (p : Polynomial ℂ) :
    ‖polynomialEval p A‖ ≤ maxPolynomialModulus A p := by
  rw [polynomialEval, ← cfc_polynomial p A hA]
  apply norm_cfc_le (maxPolynomialModulus_nonneg A p)
  intro z hz
  exact norm_eval_le_maxPolynomialModulus A p
    (spectrum_subset_numericalRange A hz)

/-- A normal matrix has polynomial functional-calculus constant one. -/
theorem crouzeixConstant_eq_one_of_isStarNormal [Nonempty n]
    (A : SquareMatrix n) (hA : IsStarNormal A) :
    crouzeixConstant A = 1 := by
  have hOne : 1 ∈ normalizedPolynomialValues A := by
    refine ⟨Polynomial.C 1, ?_, ?_⟩
    · obtain ⟨z, -, hmax⟩ :=
        exists_norm_eval_eq_maxPolynomialModulus A (Polynomial.C 1)
      have hmax_eq : maxPolynomialModulus A (Polynomial.C 1) = 1 := by
        simpa using hmax.symm
      rw [hmax_eq]
    · simp [polynomialEval]
  apply le_antisymm
  · rw [crouzeixConstant]
    apply csSup_le ⟨1, hOne⟩
    rintro r ⟨p, hp, rfl⟩
    exact (norm_polynomialEval_le_maxPolynomialModulus_of_isStarNormal
      A hA p).trans hp
  · rw [crouzeixConstant]
    apply le_csSup
    · refine ⟨1, ?_⟩
      rintro r ⟨p, hp, rfl⟩
      exact (norm_polynomialEval_le_maxPolynomialModulus_of_isStarNormal
        A hA p).trans hp
    · exact hOne

/-- A line-contained numerical range has functional-calculus constant one. -/
theorem crouzeixConstant_eq_one_of_numericalRange_in_line [Nonempty n]
    (A : SquareMatrix n) (hline : IsContainedInAffineLine (numericalRange A)) :
    crouzeixConstant A = 1 := by
  have hnormal := isStarNormal_of_numericalRange_in_line A hline
  have hOne : 1 ∈ normalizedPolynomialValues A := by
    refine ⟨Polynomial.C 1, ?_, ?_⟩
    · obtain ⟨z, -, hmax⟩ :=
        exists_norm_eval_eq_maxPolynomialModulus A (Polynomial.C 1)
      have hmax_eq : maxPolynomialModulus A (Polynomial.C 1) = 1 := by
        simpa using hmax.symm
      rw [hmax_eq]
    · simp [polynomialEval]
  apply le_antisymm
  · rw [crouzeixConstant]
    apply csSup_le
    · exact ⟨1, hOne⟩
    · intro r hr
      obtain ⟨p, hp, rfl⟩ := hr
      exact (norm_polynomialEval_le_maxPolynomialModulus_of_isStarNormal
        A hnormal p).trans hp
  · rw [crouzeixConstant]
    apply le_csSup
    · refine bddAbove_def.mpr ⟨1, ?_⟩
      intro r hr
      obtain ⟨p, hp, rfl⟩ := hr
      exact (norm_polynomialEval_le_maxPolynomialModulus_of_isStarNormal
        A hnormal p).trans hp
    · exact hOne

/-- The exact degenerate base case of the manuscript: an empty-interior
numerical range has functional-calculus constant one. -/
theorem crouzeixConstant_eq_one_of_interior_numericalRange_not_nonempty
    [Nonempty n] (A : SquareMatrix n)
    (hInt : ¬ (interior (numericalRange A)).Nonempty) :
    crouzeixConstant A = 1 := by
  apply crouzeixConstant_eq_one_of_numericalRange_in_line A
  exact isContainedInAffineLine_of_convex_of_interior_not_nonempty
    (numericalRange_convex A) (numericalRange_nonempty A) hInt

end DiskRigidity.Operator
