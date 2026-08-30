/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.BoundaryCompressionMatrix

/-!
# Dimension bookkeeping for boundary-spectrum induction

The nonzero boundary-eigenvector summand removes at least one dimension.  If
that summand is zero, every spectral value is already in the interior of the
numerical range.  These are the two alternatives used in Lemma 4.2.
-/

@[expose] public section

noncomputable section

open Set
open scoped Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
/-- A nonzero boundary spectral summand leaves a strictly smaller canonical
complement index. -/
theorem card_boundaryComplementIndex_lt
    (A : SquareMatrix n) (hboundary : boundaryEigenspaceSpan A ≠ ⊥) :
    Fintype.card (boundaryComplementIndex A) < Fintype.card n := by
  have hpositive : 0 < Module.finrank ℂ (boundaryEigenspaceSpan A) := by
    rw [Nat.lt_iff_add_one_le, add_comm, Nat.add_one_le_iff]
    exact Submodule.one_le_finrank_iff.mpr hboundary
  have hsum := (boundaryEigenspaceSpan A).finrank_add_finrank_orthogonal
  have hambient : Module.finrank ℂ (EuclideanVector n) = Fintype.card n := by
    exact finrank_euclideanSpace
  simp only [boundaryComplementIndex, Fintype.card_fin]
  change Module.finrank ℂ (boundaryEigenspaceSpan A) +
      Module.finrank ℂ (boundaryComplement A) =
        Module.finrank ℂ (EuclideanVector n) at hsum
  rw [hambient] at hsum
  omega

omit [Nonempty n] in
/-- If no boundary eigenvector occurs, the whole spectrum is in the interior
of the numerical range. -/
theorem spectrum_subset_interior_of_boundaryEigenspaceSpan_eq_bot
    (A : SquareMatrix n) (hboundary : boundaryEigenspaceSpan A = ⊥) :
    spectrum ℂ A ⊆ interior (numericalRange A) := by
  intro lambda hlambda
  have heig : Module.End.HasEigenvalue (Matrix.toEuclideanLin A) lambda := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum]
    simpa only [Matrix.spectrum_toLpLin] using hlambda
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  have hvorth : v ∈ (boundaryEigenspaceSpan A)ᗮ := by
    rw [hboundary, Submodule.bot_orthogonal_eq_top]
    exact Submodule.mem_top
  exact eigenvalue_mem_interior_of_mem_boundaryEigenspaceSpan_orthogonal
    A hvorth hv.2 hv.apply_eq_smul

end DiskRigidity.Operator
