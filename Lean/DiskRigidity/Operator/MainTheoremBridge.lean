/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.ConvexPolynomialCauchy
public import DiskRigidity.Operator.InteriorSpectrumReindex
public import DiskRigidity.Operator.MainInduction
public import DiskRigidity.Operator.RelativeSharpBound

/-!
# Final bridge to disk rigidity

The concrete polynomial bound and relative holomorphic-calculus bound
discharge the two analytic inputs of the dimension induction.  Thus it is
enough to prove the interior-spectrum argument for matrices indexed by
`Fin (N + 1)`.
-/

@[expose] public section

noncomputable section

open Metric Set
open scoped Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

/-- The final disk-rigidity theorem, reduced solely to the concrete
interior-spectrum endpoint on positive standard finite index types. -/
theorem diskRigidity_of_finSucc_interiorSpectrum
    (hfin : ∀ {N : ℕ} (M : SquareMatrix (Fin (N + 1))),
      (interior (numericalRange M)).Nonempty →
      spectrum ℂ M ⊆ interior (numericalRange M) →
      crouzeixConstant M = 2 →
      ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ numericalRange M = closedBall c r) :
    ∀ {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
      (A : SquareMatrix n), crouzeixConstant A = 2 →
      ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ numericalRange A = closedBall c r := by
  apply diskRigidity_of_interiorSpectrum_case
    (fun M p ↦ sharp_polynomial_bound M p)
    hasRelativeSharpHolomorphicCalculusBound
  exact interiorSpectrum_diskRigidity_of_finSucc hfin

end DiskRigidity.Operator
