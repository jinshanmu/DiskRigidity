/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.FoundationReindex

/-!
# Reindexing the interior-spectrum case

The adjugate argument is naturally written for matrices indexed by
`Fin (N + 1)`.  This file transports that conclusion to an arbitrary
nonempty finite index type by relabelling coordinates.
-/

@[expose] public section

noncomputable section

open Metric Set
open scoped Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

/-- A disk-rigidity result proved for every positive standard finite index
type holds for every nonempty finite index type. -/
theorem interiorSpectrum_diskRigidity_of_finSucc
    (hfin : ∀ {N : ℕ} (M : SquareMatrix (Fin (N + 1))),
      (interior (numericalRange M)).Nonempty →
      spectrum ℂ M ⊆ interior (numericalRange M) →
      crouzeixConstant M = 2 →
      ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ numericalRange M = closedBall c r) :
    ∀ {m : Type} [Fintype m] [DecidableEq m] [Nonempty m]
      (M : SquareMatrix m),
      (interior (numericalRange M)).Nonempty →
      spectrum ℂ M ⊆ interior (numericalRange M) →
      crouzeixConstant M = 2 →
      ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ numericalRange M = closedBall c r := by
  intro m _ _ _ M hInt hspec hpsi
  have hcard : 0 < Fintype.card m := Fintype.card_pos
  obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero hcard.ne'
  let e : m ≃ Fin (N + 1) :=
    Fintype.equivFinOfCardEq (by simp [hN])
  let M' : SquareMatrix (Fin (N + 1)) := Matrix.reindex e e M
  have hW : numericalRange M' = numericalRange M :=
    numericalRange_reindex e M
  have hspec' : spectrum ℂ M' ⊆ interior (numericalRange M') := by
    rw [spectrum_reindex e M, hW]
    exact hspec
  have hpsi' : crouzeixConstant M' = 2 := by
    rw [crouzeixConstant_reindex e M]
    exact hpsi
  obtain ⟨c, r, hr, hdisk⟩ := hfin M' (by rwa [hW]) hspec' hpsi'
  exact ⟨c, r, hr, hW ▸ hdisk⟩

end DiskRigidity.Operator
