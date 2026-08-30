/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.InteriorSpectrumRigidity
public import DiskRigidity.Operator.MainTheoremBridge

/-!
# Disk rigidity at the extremal Crouzeix constant

This module closes the dimension induction with the fully constructed
interior-spectrum argument.
-/

@[expose] public section

noncomputable section

open Metric Set
open scoped Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

/-- If the Crouzeix constant of a nonempty finite complex matrix is `2`, then
its numerical range is a nondegenerate closed disk. -/
theorem diskRigidity
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : SquareMatrix n) (hpsi : crouzeixConstant A = 2) :
    ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ numericalRange A = closedBall c r := by
  exact diskRigidity_of_finSucc_interiorSpectrum
    (fun M hInt hspec hpsiM ↦
      interiorSpectrum_diskRigidity_finSucc M hInt hspec hpsiM)
    A hpsi

end DiskRigidity.Operator
