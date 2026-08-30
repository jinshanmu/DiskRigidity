/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.RelativeCalculus
public import DiskRigidity.Complex.StrictHolomorphicMonotonicity
public import DiskRigidity.Operator.BoundaryDimension
public import DiskRigidity.Operator.BoundaryInduction
public import DiskRigidity.Operator.BoundaryInductionGeometry

/-!
# Boundary-spectrum induction

This is Lemma 4.2 of the manuscript.  A nonzero boundary spectral summand is
peeled off and the induction hypothesis makes the remaining block a disk.  A
second peel has the same numerical range.  The original maximizing polynomial
sequence remains extremal on that second block, so strict domain monotonicity
forces the first disk to be the whole numerical range.
-/

@[expose] public section

noncomputable section

open Filter Metric Set Topology
open scoped Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

/-- The relative form of the sharp holomorphic-calculus estimate needed in
the boundary-spectrum induction. -/
def HasRelativeSharpHolomorphicCalculusBound : Prop :=
  ∀ {m : Type} [Fintype m] [DecidableEq m] [Nonempty m]
      (M : SquareMatrix m) (U : Set ℂ),
    IsOpen U → Convex ℝ U → U.Nonempty → Bornology.IsBounded U →
    numericalRange M ⊆ closure U → spectrum ℂ M ⊆ U →
    Complex.HasHolomorphicCalculusBound M U 2

private theorem interior_numericalRange_eq_of_common_extremal_sequence
    {n m l : Type*}
    [Fintype n] [DecidableEq n] [Nonempty n]
    [Fintype m] [DecidableEq m] [Nonempty m]
    [Fintype l] [DecidableEq l] [Nonempty l]
    (A : SquareMatrix n) (B : SquareMatrix m) (D : SquareMatrix l)
    (hIntA : (interior (numericalRange A)).Nonempty)
    (hIntB : (interior (numericalRange B)).Nonempty)
    (hBA : numericalRange B ⊆ numericalRange A)
    (hspecDU : spectrum ℂ D ⊆ interior (numericalRange B))
    (P : ℕ → Polynomial ℂ)
    (hPA : ∀ k, maxPolynomialModulus A (P k) ≤ 1)
    (hPB : ∀ k, maxPolynomialModulus B (P k) ≤ 1)
    (hlimD : Tendsto (fun k ↦ ‖polynomialEval (P k) D‖)
      atTop (nhds 2))
    (hcalcU : Complex.HasHolomorphicCalculusBound D
      (interior (numericalRange B)) 2)
    (hcalcV : Complex.HasHolomorphicCalculusBound D
      (interior (numericalRange A)) 2) :
    interior (numericalRange B) = interior (numericalRange A) := by
  let U := interior (numericalRange B)
  let V := interior (numericalRange A)
  have hUV : U ⊆ V := interior_mono hBA
  have hUo : IsOpen U := isOpen_interior
  have hVo : IsOpen V := isOpen_interior
  have hUc : Convex ℝ U := (numericalRange_convex B).interior
  have hVc : Convex ℝ V := (numericalRange_convex A).interior
  have hUne : U.Nonempty := hIntB
  have hVne : V.Nonempty := hIntA
  have hUb : Bornology.IsBounded U :=
    (isCompact_numericalRange B).isBounded.subset interior_subset
  have hVb : Bornology.IsBounded V :=
    (isCompact_numericalRange A).isBounded.subset interior_subset
  have hschurU : ∀ k, Complex.IsSchurOn U (fun z ↦ (P k).eval z) := by
    intro k
    apply Complex.isSchurOn_polynomial_of_norm_le_on interior_subset
    intro z hz
    exact (norm_eval_le_maxPolynomialModulus B (P k) hz).trans (hPB k)
  have hschurV : ∀ k, Complex.IsSchurOn V (fun z ↦ (P k).eval z) := by
    intro k
    apply Complex.isSchurOn_polynomial_of_norm_le_on interior_subset
    intro z hz
    exact (norm_eval_le_maxPolynomialModulus A (P k) hz).trans (hPA k)
  have hnormU : Complex.holomorphicCalculusNorm D U = 2 :=
    Complex.holomorphicCalculusNorm_eq_two_of_polynomial_sequence
      D hcalcU P hschurU hlimD
  have hnormV : Complex.holomorphicCalculusNorm D V = 2 :=
    Complex.holomorphicCalculusNorm_eq_two_of_polynomial_sequence
      D hcalcV P hschurV hlimD
  apply Subset.antisymm hUV
  by_contra hnot
  have hproper : U ⊂ V := ⟨hUV, hnot⟩
  have hstrict := Complex.holomorphicCalculusNorm_strict_anti_of_ssubset
    D hUo hUc hUne hUb hVo hVc hVne hVb hproper hspecDU (by
      rw [hnormU]
      norm_num)
  rw [hnormU, hnormV] at hstrict
  exact (lt_irrefl (2 : ℝ)) hstrict

/-- Lemma 4.2: assuming disk rigidity in smaller dimensions, a matrix with a
nonzero boundary spectral summand and sharp constant two already has a disk
as its numerical range. -/
theorem numericalRange_eq_closedBall_of_boundaryEigenspaceSpan_ne_bot
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : SquareMatrix n)
    (hInt : (interior (numericalRange A)).Nonempty)
    (hpsi : crouzeixConstant A = 2)
    (hboundary : boundaryEigenspaceSpan A ≠ ⊥)
    (hsharp : ∀ {m : Type} [Fintype m] [DecidableEq m] [Nonempty m]
      (M : SquareMatrix m) (p : Polynomial ℂ),
      ‖polynomialEval p M‖ ≤ 2 * maxPolynomialModulus M p)
    (hrelative : HasRelativeSharpHolomorphicCalculusBound)
    (hind : ∀ {m : Type} [Fintype m] [DecidableEq m] [Nonempty m],
      Fintype.card m < Fintype.card n → ∀ M : SquareMatrix m,
      crouzeixConstant M = 2 →
        ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ numericalRange M = closedBall c r) :
    ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ numericalRange A = closedBall c r := by
  let _ : Nonempty (boundaryComplementIndex A) :=
    nonempty_boundaryComplementIndex_of_crouzeixConstant_eq_two A hInt hpsi
  let B := boundaryComplementMatrix A hInt
  have hsharpB : ∀ p : Polynomial ℂ,
      ‖polynomialEval p B‖ ≤ 2 * maxPolynomialModulus B p := fun p ↦
    hsharp (m := boundaryComplementIndex A) B p
  have hpsiB : crouzeixConstant B = 2 :=
    crouzeixConstant_boundaryComplementMatrix_eq_two A hInt hpsi hsharpB
  obtain ⟨c, r, hr, hWB⟩ :=
    hind (m := boundaryComplementIndex A)
      (card_boundaryComplementIndex_lt A hboundary) B hpsiB
  have hIntB : (interior (numericalRange B)).Nonempty := by
    rw [hWB, interior_closedBall c hr.ne']
    exact ⟨c, mem_ball_self hr⟩
  let _ : Nonempty (boundaryComplementIndex B) :=
    nonempty_boundaryComplementIndex_of_crouzeixConstant_eq_two B hIntB hpsiB
  let D := boundaryComplementMatrix B hIntB
  have hsharpD : ∀ p : Polynomial ℂ,
      ‖polynomialEval p D‖ ≤ 2 * maxPolynomialModulus D p := fun p ↦
    hsharp (m := boundaryComplementIndex B) D p
  have hWD : numericalRange D = numericalRange B :=
    numericalRange_boundaryComplementMatrix_eq_of_eq_closedBall
      B hIntB c hr hWB
  obtain ⟨P, hPA, hPB, hlimB⟩ :=
    exists_boundaryComplement_polynomial_sequence_tendsto_two
      A hInt hpsi hsharpB
  have hlimD : Tendsto (fun k ↦ ‖polynomialEval (P k) D‖)
      atTop (nhds 2) :=
    boundaryComplement_polynomial_sequence_tendsto_two
      B hIntB hsharpD P hPB hlimB
  have hBA : numericalRange B ⊆ numericalRange A :=
    numericalRange_boundaryComplementMatrix_subset A hInt
  have hUV : interior (numericalRange B) ⊆ interior (numericalRange A) :=
    interior_mono hBA
  have hspecDU : spectrum ℂ D ⊆ interior (numericalRange B) :=
    spectrum_boundaryComplementMatrix_subset_interior B hIntB
  have hWDU : numericalRange D ⊆ closure (interior (numericalRange B)) := by
    rw [hWD, (numericalRange_convex B).closure_interior_eq_closure_of_nonempty_interior
      hIntB, (isCompact_numericalRange B).isClosed.closure_eq]
  have hWDV : numericalRange D ⊆ closure (interior (numericalRange A)) := by
    rw [(numericalRange_convex A).closure_interior_eq_closure_of_nonempty_interior
      hInt, (isCompact_numericalRange A).isClosed.closure_eq]
    exact hWD ▸ hBA
  have hcalcU : Complex.HasHolomorphicCalculusBound D
      (interior (numericalRange B)) 2 :=
    hrelative (m := boundaryComplementIndex B) D _ isOpen_interior
      (numericalRange_convex B).interior hIntB
      ((isCompact_numericalRange B).isBounded.subset interior_subset)
      hWDU hspecDU
  have hcalcV : Complex.HasHolomorphicCalculusBound D
      (interior (numericalRange A)) 2 :=
    hrelative (m := boundaryComplementIndex B) D _ isOpen_interior
      (numericalRange_convex A).interior hInt
      ((isCompact_numericalRange A).isBounded.subset interior_subset)
      hWDV (hspecDU.trans hUV)
  have hUA := interior_numericalRange_eq_of_common_extremal_sequence
    A B D hInt hIntB hBA hspecDU P hPA hPB hlimD hcalcU hcalcV
  refine ⟨c, r, hr, ?_⟩
  have hclosure := congrArg closure hUA
  simpa [
    (numericalRange_convex B).closure_interior_eq_closure_of_nonempty_interior hIntB,
    (numericalRange_convex A).closure_interior_eq_closure_of_nonempty_interior hInt,
    (isCompact_numericalRange B).isClosed.closure_eq,
    (isCompact_numericalRange A).isClosed.closure_eq,
    hWB, interior_closedBall c hr.ne', closure_ball c hr.ne'] using hclosure.symm

end DiskRigidity.Operator
