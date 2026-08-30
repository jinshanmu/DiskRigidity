/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Complex.Basic

/-!
# A boundary point inside a larger connected domain

The elementary topological lemma below is the precise boundary-exit fact used in strict-domain
monotonicity.  Convexity is needed only to supply connectedness of the larger domain, so the main
statement is recorded at its natural topological generality and followed by the convex corollary.
-/

open Set

namespace DiskRigidity.Complex

public section

/-- If a nonempty open set is a proper subset of a connected set, some point of its frontier lies
in the larger set. -/
theorem exists_mem_frontier_inter_of_isOpen_ssubset_isConnected {X : Type*}
    [TopologicalSpace X] {U V : Set X} (hUo : IsOpen U) (hUne : U.Nonempty)
    (hUV : U ⊂ V) (hVc : IsConnected V) : ∃ x, x ∈ frontier U ∩ V := by
  by_contra hnone
  have hno : ∀ x, x ∈ frontier U → x ∈ V → False := by
    intro x hxfr hxV
    exact hnone ⟨x, hxfr, hxV⟩
  obtain ⟨a, haU⟩ := hUne
  obtain ⟨b, hbV, hbU⟩ := Set.exists_of_ssubset hUV
  have hcover : V ⊆ U ∪ (closure U)ᶜ := by
    intro x hxV
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · refine Or.inr ?_
      intro hxcl
      have hxfr : x ∈ frontier U := by
        rw [hUo.frontier_eq]
        exact ⟨hxcl, hxU⟩
      exact hno x hxfr hxV
  have hmeetU : (V ∩ U).Nonempty := ⟨a, hUV.subset haU, haU⟩
  have hbcl : b ∉ closure U := by
    intro hb
    have hbfr : b ∈ frontier U := by
      rw [hUo.frontier_eq]
      exact ⟨hb, hbU⟩
    exact hno b hbfr hbV
  have hmeetC : (V ∩ (closure U)ᶜ).Nonempty := ⟨b, hbV, hbcl⟩
  obtain ⟨x, -, hxU, hxC⟩ := hVc.isPreconnected U (closure U)ᶜ hUo
    isClosed_closure.isOpen_compl hcover hmeetU hmeetC
  exact hxC (subset_closure hxU)

/-- A proper inclusion of nonempty open convex sets has a boundary point of the smaller set in the
larger one. -/
theorem exists_mem_frontier_inter_of_convex {U V : Set ℂ} (hUo : IsOpen U) (hUne : U.Nonempty)
    (hUV : U ⊂ V) (hVc : Convex ℝ V) :
    ∃ x, x ∈ frontier U ∩ V := by
  exact exists_mem_frontier_inter_of_isOpen_ssubset_isConnected hUo hUne hUV
    (hVc.isConnected (hUne.mono hUV.subset))

end

end DiskRigidity.Complex
