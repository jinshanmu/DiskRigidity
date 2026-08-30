/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.BoundarySpectrumInduction
public import DiskRigidity.Operator.FoundationGeometry

/-!
# The dimension induction for disk rigidity

This file packages the induction in the final section of the manuscript.
The boundary-spectrum branch is discharged by the boundary-compression
argument.  Only the interior-spectrum branch is left as an input, so the
analytic and algebraic part of the proof can be assembled independently.
-/

@[expose] public section

noncomputable section

open Metric Set Topology
open scoped Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

/-- The induction in the proof of the main theorem, with the
interior-spectrum case isolated as its only geometric input. -/
theorem diskRigidity_of_interiorSpectrum_case
    (hsharp : ∀ {m : Type} [Fintype m] [DecidableEq m] [Nonempty m]
      (M : SquareMatrix m) (p : Polynomial ℂ),
      ‖polynomialEval p M‖ ≤ 2 * maxPolynomialModulus M p)
    (hrelative : HasRelativeSharpHolomorphicCalculusBound)
    (hinterior : ∀ {m : Type} [Fintype m] [DecidableEq m] [Nonempty m]
      (M : SquareMatrix m),
      (interior (numericalRange M)).Nonempty →
      spectrum ℂ M ⊆ interior (numericalRange M) →
      crouzeixConstant M = 2 →
      ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ numericalRange M = closedBall c r) :
    ∀ {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
      (A : SquareMatrix n), crouzeixConstant A = 2 →
      ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ numericalRange A = closedBall c r := by
  let P : ℕ → Prop := fun N ↦
    ∀ {n : Type} [Fintype n] [DecidableEq n] [Nonempty n],
      Fintype.card n = N → ∀ A : SquareMatrix n,
      crouzeixConstant A = 2 →
        ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ numericalRange A = closedBall c r
  have hP : ∀ N, P N := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro n _ _ _ hn A hpsi
      have hInt : (interior (numericalRange A)).Nonempty := by
        by_contra hnot
        have hone :=
          crouzeixConstant_eq_one_of_interior_numericalRange_not_nonempty A hnot
        rw [hpsi] at hone
        norm_num at hone
      by_cases hboundary : boundaryEigenspaceSpan A = ⊥
      · exact hinterior A hInt
          (spectrum_subset_interior_of_boundaryEigenspaceSpan_eq_bot A hboundary)
          hpsi
      · apply numericalRange_eq_closedBall_of_boundaryEigenspaceSpan_ne_bot
          A hInt hpsi hboundary hsharp hrelative
        intro m _ _ _ hm M hpsiM
        apply ih (Fintype.card m) (by simpa [hn] using hm)
        · rfl
        · exact hpsiM
  intro n _ _ _ A hpsi
  exact hP (Fintype.card n) rfl A hpsi

end DiskRigidity.Operator
