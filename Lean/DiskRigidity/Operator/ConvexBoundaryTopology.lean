/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.ConvexBoundaryParametrization

/-!
# Topology of a compact convex boundary

The radial parametrization gives a short proof that the frontier of a planar
compact convex body is connected.
-/

@[expose] public section

noncomputable section

open Set

namespace DiskRigidity.Operator

/-- The frontier of a compact convex subset of `ℂ` with nonempty interior is
connected. -/
theorem isConnected_frontier_of_compact_convex
    {K : Set ℂ} (hconv : Convex ℝ K) (hcompact : IsCompact K)
    (hinterior : (interior K).Nonempty) :
    IsConnected (frontier K) := by
  obtain ⟨c, hc⟩ := hinterior
  obtain ⟨L, hL⟩ :=
    exists_lipschitzWith_radialBoundaryParametrization hconv hc hcompact
  rw [← range_radialBoundaryParametrization hconv hc hcompact]
  exact isConnected_range hL.continuous

end DiskRigidity.Operator
