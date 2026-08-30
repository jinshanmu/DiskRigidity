/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.ConvexHolomorphicBound
public import DiskRigidity.Operator.BoundarySpectrumInduction
public import DiskRigidity.Operator.ConvexHolomorphicCauchy

/-!
# The relative sharp holomorphic-calculus bound

The concrete radial Cauchy boundary on the closure of a bounded open convex
set gives the neighborhood estimate at constant two.  Convex radial
contraction then extends it to every bounded holomorphic function on the open
set.  This is the exact relative input used by the boundary-spectrum
induction.
-/

@[expose] public section

noncomputable section

open Bornology MeasureTheory Set Topology
open scoped Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

/-- The unconditional relative sharp holomorphic functional-calculus bound
needed by `MainInduction`. -/
theorem hasRelativeSharpHolomorphicCalculusBound :
    HasRelativeSharpHolomorphicCalculusBound := by
  intro m _instFintype _instDecidableEq _instNonempty M U
    hUo hUc hUne hUb hWU hspec
  have hUne' : U.Nonempty := hUne
  obtain ⟨c, hcU⟩ := hUne
  have hIntU : interior U = U := hUo.interior_eq
  have hIntCl : interior (closure U) = U := by
    rw [hUc.interior_closure_eq_interior_of_nonempty_interior]
    · exact hIntU
    · simpa only [hIntU] using hUne'
  have hcCl : c ∈ interior (closure U) := by
    rw [hIntCl]
    exact hcU
  have hClConv : Convex ℝ (closure U) := hUc.closure
  have hClCompact : IsCompact (closure U) := hUb.isCompact_closure
  have hspecCl : spectrum ℂ M ⊆ interior (closure U) := by
    rwa [hIntCl]
  let _ : IsFiniteMeasure
      (radialBoundaryArcLengthMeasure (closure U) c) :=
    isFiniteMeasure_radialBoundaryArcLengthMeasure
      hClConv hcCl hClCompact
  let B := neighborhoodHolomorphicCauchyBoundaryOfConvexBody
    M hClConv hcCl hClCompact hWU hspecCl
  have hroots : ∀ z ∈ M.charpoly.roots, z ∈ closure U :=
    DiskRigidity.Complex.charpoly_roots_subset_of_spectrum_subset
      M (hspec.trans subset_closure)
  have hnhd : DiskRigidity.Complex.HasNeighborhoodHolomorphicCalculusBound
      M (closure U) 2 := B.hasNeighborhoodHolomorphicCalculusBound hroots
  exact
    DiskRigidity.Complex.hasHolomorphicCalculusBound_of_neighborhoods_of_isOpen_convex
      M hUo hUc hUne' hspec hnhd

end DiskRigidity.Operator
