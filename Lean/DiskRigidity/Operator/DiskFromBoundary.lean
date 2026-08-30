/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Convex.Strict.Extreme
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Recovering a disk from its boundary circle

This is the final elementary convexity step in the proof of the main theorem.
-/

@[expose] public section

noncomputable section

open Metric Set

namespace DiskRigidity.Operator

/-- A compact convex subset of the complex plane whose frontier is a
nondegenerate circle is the corresponding closed disk. -/
theorem eq_closedBall_of_frontier_eq_sphere
    {K : Set ℂ} (hcompact : IsCompact K) (hconvex : Convex ℝ K)
    (c : ℂ) {r : ℝ} (hr : 0 < r)
    (hfrontier : frontier K = sphere c r) :
    K = closedBall c r := by
  have hclosed : IsClosed K := hcompact.isClosed
  have hsphereK : sphere c r ⊆ K := by
    rw [← hfrontier]
    exact frontier_subset_closure.trans_eq hclosed.closure_eq
  have hballK : closedBall c r ⊆ K := by
    rw [← convexHull_sphere_eq_closedBall c hr.le]
    exact convexHull_min hsphereK hconvex
  have hextremeFrontier : K.extremePoints ℝ ⊆ frontier K := by
    intro z hz
    rw [hclosed.frontier_eq]
    refine ⟨hz.1, ?_⟩
    intro hzint
    exact Set.disjoint_left.1 (disjoint_interior_extremePoints K)
      hzint hz
  have hKball : K ⊆ closedBall c r := by
    rw [← closure_convexHull_extremePoints hcompact hconvex]
    calc
      closure (convexHull ℝ (K.extremePoints ℝ)) ⊆
          closure (convexHull ℝ (sphere c r)) :=
        closure_mono (convexHull_mono
          (hextremeFrontier.trans (by rw [hfrontier])))
      _ = closedBall c r := by
        rw [convexHull_sphere_eq_closedBall c hr.le, closure_closedBall]
  exact Subset.antisymm hKball hballK

end DiskRigidity.Operator
