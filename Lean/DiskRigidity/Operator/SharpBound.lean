/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.CrouzeixConstant
public import DiskRigidity.Operator.Dilation

/-!
# The sharp bound from double-layer dilation data

This file isolates the exact interface between the analytic double-layer
construction and the iterated-dilation lemma.  A `PolynomialDilationFamily`
contains precisely the multiplication contraction, boundary isometry, and
error estimates produced by formulas (3.5)--(3.7) in the manuscript.  No norm
conclusion is included in the data.
-/

@[expose] public section

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {n K : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The precise hypotheses furnished by one double-layer dilation.  The
structure records construction data only; its sharp norm and equality
consequences are proved below and in `EqualityData`. -/
structure DilationWitness (T : H →L[ℂ] H) where
  /-- Contractive multiplication operator on the dilation space. -/
  multiplication : K →L[ℂ] K
  /-- Isometric embedding into the dilation space. -/
  boundaryIsometry : H →ₗᵢ[ℂ] K
  contraction : ‖multiplication‖ ≤ 1
  errors_bounded : ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k →
    ‖dilationError T multiplication boundaryIsometry k‖ ≤ C
  errors_commute : ∀ k : ℕ, 1 ≤ k →
    Commute (dilationError T multiplication boundaryIsometry k) T

/-- The sharp norm conclusion extracted from a double-layer dilation witness. -/
theorem DilationWitness.norm_le_two [FiniteDimensional ℂ H] [Nontrivial H]
    {T : H →L[ℂ] H} (D : DilationWitness (K := K) T) :
    ‖T‖ ≤ 2 :=
  abstract_dilation_norm_le_two T D.multiplication D.boundaryIsometry
    D.contraction D.errors_bounded D.errors_commute

/-- A normalized estimate for a complex-linear functional calculus implies
the corresponding homogeneous estimate. -/
theorem complexLinear_bound_of_normalized_bound
    {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Phi : F →ₗ[ℂ] E)
    (hnormalized : ∀ f : F, ‖f‖ ≤ 1 → ‖Phi f‖ ≤ 2)
    (f : F) : ‖Phi f‖ ≤ 2 * ‖f‖ := by
  by_cases hf : f = 0
  · simp [hf]
  have hfnorm : 0 < ‖f‖ := norm_pos_iff.mpr hf
  let c : ℂ := (‖f‖ : ℂ)⁻¹
  have hcnorm : ‖c‖ = ‖f‖⁻¹ := by
    simp [c]
  have hunit : ‖c • f‖ ≤ 1 := by
    rw [norm_smul, hcnorm, inv_mul_cancel₀ hfnorm.ne']
  have hbound := hnormalized (c • f) hunit
  rw [map_smul, norm_smul, hcnorm] at hbound
  calc
    ‖Phi f‖ = ‖f‖ * (‖f‖⁻¹ * ‖Phi f‖) := by field_simp
    _ ≤ ‖f‖ * 2 := mul_le_mul_of_nonneg_left hbound (norm_nonneg f)
    _ = 2 * ‖f‖ := mul_comm _ _

/-- The general function-space form of Proposition 3.2.  It applies equally
to the disk algebra and to `H∞`: once every normalized function produces the
double-layer witness, complex-linearity gives the stated factor `2`. -/
theorem functionalCalculus_bound_of_dilations
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ H] [Nontrivial H]
    (Phi : F →ₗ[ℂ] (H →L[ℂ] H))
    (hwitness : ∀ f : F, ‖f‖ ≤ 1 →
      DilationWitness (K := K) (Phi f))
    (f : F) : ‖Phi f‖ ≤ 2 * ‖f‖ := by
  apply complexLinear_bound_of_normalized_bound Phi
  intro g hg
  exact (hwitness g hg).norm_le_two

/-- The exact output of the positive double-layer construction needed by the
abstract dilation lemma, simultaneously for all normalized polynomials. -/
structure PolynomialDilationFamily (A : SquareMatrix n) where
  /-- Multiplication operator associated with each polynomial. -/
  multiplication : Polynomial ℂ → K →L[ℂ] K
  /-- Common isometric boundary embedding for the polynomial family. -/
  boundaryIsometry : EuclideanVector n →ₗᵢ[ℂ] K
  contraction_of_normalized : ∀ p : Polynomial ℂ,
    maxPolynomialModulus A p ≤ 1 → ‖multiplication p‖ ≤ 1
  errors_bounded : ∀ p : Polynomial ℂ,
    maxPolynomialModulus A p ≤ 1 →
      ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k →
        ‖dilationError
          (euclideanOperator (polynomialEval p A))
          (multiplication p) boundaryIsometry k‖ ≤ C
  errors_commute : ∀ p : Polynomial ℂ,
    maxPolynomialModulus A p ≤ 1 →
      ∀ k : ℕ, 1 ≤ k →
        Commute
          (dilationError
            (euclideanOperator (polynomialEval p A))
            (multiplication p) boundaryIsometry k)
          (euclideanOperator (polynomialEval p A))

/-- The abstract dilation estimate applied to the concrete polynomial
functional-calculus operator. -/
theorem PolynomialDilationFamily.normalized_bound
    {A : SquareMatrix n} (D : PolynomialDilationFamily (K := K) A)
    (p : Polynomial ℂ) (hp : maxPolynomialModulus A p ≤ 1) :
    ‖polynomialEval p A‖ ≤ 2 := by
  rw [matrix_norm_eq_operator_norm]
  exact abstract_dilation_norm_le_two
    (euclideanOperator (polynomialEval p A))
    (D.multiplication p) D.boundaryIsometry
    (D.contraction_of_normalized p hp)
    (D.errors_bounded p hp) (D.errors_commute p hp)

/-- Maximum modulus on the numerical range is homogeneous. -/
theorem maxPolynomialModulus_smul
    (A : SquareMatrix n) (c : ℂ) (p : Polynomial ℂ) :
    maxPolynomialModulus A (c • p) = ‖c‖ * maxPolynomialModulus A p := by
  obtain ⟨z, hz, hzmax⟩ := exists_norm_eval_eq_maxPolynomialModulus A p
  obtain ⟨w, hw, hwmax⟩ :=
    exists_norm_eval_eq_maxPolynomialModulus A (c • p)
  apply le_antisymm
  · rw [← hwmax, Polynomial.eval_smul, norm_smul]
    gcongr
    exact norm_eval_le_maxPolynomialModulus A p hw
  · rw [← hzmax, ← norm_smul]
    simpa only [Polynomial.eval_smul] using
      norm_eval_le_maxPolynomialModulus A (c • p) hz

omit [Nonempty n] in
/-- Polynomial evaluation at a matrix is homogeneous in the polynomial. -/
@[simp]
theorem polynomialEval_smul (A : SquareMatrix n) (c : ℂ)
    (p : Polynomial ℂ) :
    polynomialEval (c • p) A = c • polynomialEval p A := by
  simp [polynomialEval]

/-- A normalized sharp estimate implies its homogeneous form, including the
zero-maximum case.  The latter is forced by applying the normalized estimate
to arbitrarily large scalar multiples. -/
theorem polynomial_bound_of_normalized_bound
    (A : SquareMatrix n)
    (hnormalized : ∀ p : Polynomial ℂ,
      maxPolynomialModulus A p ≤ 1 → ‖polynomialEval p A‖ ≤ 2)
    (p : Polynomial ℂ) :
    ‖polynomialEval p A‖ ≤ 2 * maxPolynomialModulus A p := by
  let m := maxPolynomialModulus A p
  have hm : 0 ≤ m := maxPolynomialModulus_nonneg A p
  rcases hm.eq_or_lt with hmzero | hmpos
  · have hevalzero : ‖polynomialEval p A‖ = 0 := by
      by_contra hne
      have hevalpos : 0 < ‖polynomialEval p A‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      let c : ℂ := ((3 / ‖polynomialEval p A‖ : ℝ) : ℂ)
      have hcpos : 0 < (3 / ‖polynomialEval p A‖ : ℝ) := div_pos (by norm_num) hevalpos
      have hmaxc : maxPolynomialModulus A (c • p) ≤ 1 := by
        rw [maxPolynomialModulus_smul]
        change ‖c‖ * m ≤ 1
        rw [← hmzero, mul_zero]
        norm_num
      have hbound := hnormalized (c • p) hmaxc
      rw [polynomialEval_smul, norm_smul] at hbound
      have hcnorm : ‖c‖ = 3 / ‖polynomialEval p A‖ := by
        simp [c]
      rw [hcnorm] at hbound
      have : (3 / ‖polynomialEval p A‖) * ‖polynomialEval p A‖ = 3 := by
        field_simp
      linarith
    change ‖polynomialEval p A‖ ≤ 2 * m
    rw [hevalzero, ← hmzero]
    norm_num
  · let c : ℂ := (m : ℂ)⁻¹
    have hcnorm : ‖c‖ = m⁻¹ := by
      simp [c, abs_of_pos hmpos]
    have hmaxc : maxPolynomialModulus A (c • p) ≤ 1 := by
      rw [maxPolynomialModulus_smul, hcnorm]
      exact (inv_mul_cancel₀ hmpos.ne').le
    have hbound := hnormalized (c • p) hmaxc
    rw [polynomialEval_smul, norm_smul, hcnorm] at hbound
    have hmne : m ≠ 0 := hmpos.ne'
    calc
      ‖polynomialEval p A‖ = m * (m⁻¹ * ‖polynomialEval p A‖) := by
        field_simp
      _ ≤ m * 2 := mul_le_mul_of_nonneg_left hbound hm
      _ = 2 * m := mul_comm _ _

/-- Proposition 3.2 for polynomials, once formulas (3.5)--(3.7) have supplied
the exact double-layer dilation family above. -/
theorem PolynomialDilationFamily.sharp_polynomial_bound
    {A : SquareMatrix n} (D : PolynomialDilationFamily (K := K) A)
    (p : Polynomial ℂ) :
    ‖polynomialEval p A‖ ≤ 2 * maxPolynomialModulus A p := by
  exact polynomial_bound_of_normalized_bound A D.normalized_bound p

end DiskRigidity.Operator
