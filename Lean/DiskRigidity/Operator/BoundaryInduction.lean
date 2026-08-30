/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.NumericalRangeExtremizer
public import DiskRigidity.Operator.BoundaryCompressionMatrix

/-!
# The equality constant on the interior spectral block

This file formalizes the quantitative step in Lemma 4.2 of the manuscript.
After all boundary eigenvectors are split off, the same normalized polynomial
sequence still tends to the sharp value two on the remaining nonzero block.
-/

@[expose] public section

noncomputable section

open Filter Set Topology
open scoped Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- A homogeneous sharp polynomial estimate bounds the Crouzeix constant by
two. -/
theorem crouzeixConstant_le_two_of_sharp_polynomial_bound
    (A : SquareMatrix n)
    (hsharp : ∀ p : Polynomial ℂ,
      ‖polynomialEval p A‖ ≤ 2 * maxPolynomialModulus A p) :
    crouzeixConstant A ≤ 2 := by
  rw [crouzeixConstant]
  apply csSup_le (Complex.normalizedPolynomialValues_nonempty A)
  rintro r ⟨p, hp, rfl⟩
  exact (hsharp p).trans (by nlinarith [maxPolynomialModulus_nonneg A p])

/-- Maximum modulus decreases when passing to the interior spectral block. -/
theorem maxPolynomialModulus_boundaryComplementMatrix_le
    (A : SquareMatrix n) (hInt : (interior (numericalRange A)).Nonempty)
    [Nonempty (boundaryComplementIndex A)] (p : Polynomial ℂ) :
    maxPolynomialModulus (boundaryComplementMatrix A hInt) p ≤
      maxPolynomialModulus A p := by
  obtain ⟨z, hz, hmax⟩ :=
    exists_norm_eval_eq_maxPolynomialModulus
      (boundaryComplementMatrix A hInt) p
  rw [← hmax]
  exact norm_eval_le_maxPolynomialModulus A p
    (numericalRange_boundaryComplementMatrix_subset A hInt hz)

/-- The normalized maximizing sequence for `A` still tends to two on the
interior spectral block. -/
theorem exists_boundaryComplement_polynomial_sequence_tendsto_two
    (A : SquareMatrix n) (hInt : (interior (numericalRange A)).Nonempty)
    (hpsi : crouzeixConstant A = 2)
    (hsharp : ∀ p : Polynomial ℂ,
      ‖polynomialEval p (boundaryComplementMatrix A hInt)‖ ≤
        2 * maxPolynomialModulus (boundaryComplementMatrix A hInt) p) :
    ∃ P : ℕ → Polynomial ℂ,
      (∀ m, maxPolynomialModulus A (P m) ≤ 1) ∧
      (∀ m, maxPolynomialModulus
        (boundaryComplementMatrix A hInt) (P m) ≤ 1) ∧
      Tendsto (fun m ↦
        ‖polynomialEval (P m) (boundaryComplementMatrix A hInt)‖)
        atTop (nhds 2) := by
  let _ : Nonempty (boundaryComplementIndex A) :=
    nonempty_boundaryComplementIndex_of_crouzeixConstant_eq_two A hInt hpsi
  obtain ⟨P, hP, hPA⟩ :=
    Complex.exists_normalizedPolynomial_sequence_tendsto_two A hpsi
  have hPB : ∀ m, maxPolynomialModulus
      (boundaryComplementMatrix A hInt) (P m) ≤ 1 := fun m ↦
    (maxPolynomialModulus_boundaryComplementMatrix_le A hInt (P m)).trans
      (hP m)
  let b : ℕ → ℝ := fun m ↦
    ‖polynomialEval (P m) (boundaryComplementMatrix A hInt)‖
  let c : ℕ → ℝ := fun m ↦ max 1 (b m)
  have hAc : ∀ m, ‖polynomialEval (P m) A‖ ≤ c m := by
    intro m
    exact (norm_polynomialEval_le_max_boundaryComplement A hInt (P m)).trans
      (max_le_max_right _ (hP m))
  have hbTwo : ∀ m, b m ≤ 2 := by
    intro m
    exact (hsharp (P m)).trans (by
      have hnonneg := maxPolynomialModulus_nonneg
        (boundaryComplementMatrix A hInt) (P m)
      nlinarith [hPB m])
  have hcTwo : ∀ m, c m ≤ 2 := by
    intro m
    exact max_le (by norm_num) (hbTwo m)
  have hc : Tendsto c atTop (nhds 2) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hPA tendsto_const_nhds
      hAc hcTwo
  have heventually : ∀ᶠ m in atTop, c m = b m := by
    filter_upwards [(tendsto_order.1 hc).1 1 (by norm_num)] with m hm
    change max 1 (b m) = b m
    rw [max_eq_right]
    by_contra hlt
    have hb_lt : b m < 1 := lt_of_not_ge hlt
    have hc_eq : c m = 1 := max_eq_left hb_lt.le
    linarith
  refine ⟨P, hP, hPB, ?_⟩
  exact hc.congr' heventually

/-- Any normalized sequence tending to two before a boundary peel still
tends to two on the interior spectral block.  This fixed-sequence form is
used for the second peel in Lemma 4.2. -/
theorem boundaryComplement_polynomial_sequence_tendsto_two
    (A : SquareMatrix n) (hInt : (interior (numericalRange A)).Nonempty)
    [Nonempty (boundaryComplementIndex A)]
    (hsharp : ∀ p : Polynomial ℂ,
      ‖polynomialEval p (boundaryComplementMatrix A hInt)‖ ≤
        2 * maxPolynomialModulus (boundaryComplementMatrix A hInt) p)
    (P : ℕ → Polynomial ℂ)
    (hP : ∀ m, maxPolynomialModulus A (P m) ≤ 1)
    (hlim : Tendsto (fun m ↦ ‖polynomialEval (P m) A‖)
      atTop (nhds 2)) :
    Tendsto (fun m ↦
      ‖polynomialEval (P m) (boundaryComplementMatrix A hInt)‖)
      atTop (nhds 2) := by
  let B := boundaryComplementMatrix A hInt
  have hPB : ∀ m, maxPolynomialModulus B (P m) ≤ 1 := fun m ↦
    (maxPolynomialModulus_boundaryComplementMatrix_le A hInt (P m)).trans
      (hP m)
  let b : ℕ → ℝ := fun m ↦ ‖polynomialEval (P m) B‖
  let c : ℕ → ℝ := fun m ↦ max 1 (b m)
  have hAc : ∀ m, ‖polynomialEval (P m) A‖ ≤ c m := by
    intro m
    exact (norm_polynomialEval_le_max_boundaryComplement A hInt (P m)).trans
      (max_le_max_right _ (hP m))
  have hbTwo : ∀ m, b m ≤ 2 := by
    intro m
    exact (hsharp (P m)).trans (by
      have hnonneg := maxPolynomialModulus_nonneg B (P m)
      nlinarith [hPB m])
  have hcTwo : ∀ m, c m ≤ 2 := by
    intro m
    exact max_le (by norm_num) (hbTwo m)
  have hc : Tendsto c atTop (nhds 2) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds
      hAc hcTwo
  have heventually : ∀ᶠ m in atTop, c m = b m := by
    filter_upwards [(tendsto_order.1 hc).1 1 (by norm_num)] with m hm
    change max 1 (b m) = b m
    rw [max_eq_right]
    by_contra hlt
    have hb_lt : b m < 1 := lt_of_not_ge hlt
    have hc_eq : c m = 1 := max_eq_left hb_lt.le
    linarith
  exact hc.congr' heventually

/-- The nonzero interior spectral block again has Crouzeix constant exactly
two.  The only global input used for the upper bound is the sharp polynomial
estimate on that block. -/
theorem crouzeixConstant_boundaryComplementMatrix_eq_two
    (A : SquareMatrix n) (hInt : (interior (numericalRange A)).Nonempty)
    (hpsi : crouzeixConstant A = 2)
    (hsharp : ∀ p : Polynomial ℂ,
      ‖polynomialEval p (boundaryComplementMatrix A hInt)‖ ≤
        2 * maxPolynomialModulus (boundaryComplementMatrix A hInt) p) :
    crouzeixConstant (boundaryComplementMatrix A hInt) = 2 := by
  let _ : Nonempty (boundaryComplementIndex A) :=
    nonempty_boundaryComplementIndex_of_crouzeixConstant_eq_two A hInt hpsi
  let B := boundaryComplementMatrix A hInt
  have hupper : crouzeixConstant B ≤ 2 :=
    crouzeixConstant_le_two_of_sharp_polynomial_bound B hsharp
  have hbounded : BddAbove (normalizedPolynomialValues B) :=
    Complex.bddAbove_normalizedPolynomialValues_of_bound B (C := 2) (by
      intro p hp
      exact (hsharp p).trans (by
        nlinarith [maxPolynomialModulus_nonneg B p]))
  obtain ⟨P, -, hPB, hlim⟩ :=
    exists_boundaryComplement_polynomial_sequence_tendsto_two
      A hInt hpsi hsharp
  have hmem : ∀ m, ‖polynomialEval (P m) B‖ ∈
      normalizedPolynomialValues B := fun m ↦ ⟨P m, hPB m, rfl⟩
  have hlower : 2 ≤ crouzeixConstant B := by
    rw [crouzeixConstant]
    exact le_of_tendsto' hlim (fun m ↦ le_csSup hbounded (hmem m))
  exact le_antisymm hupper hlower

end DiskRigidity.Operator
