/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.RiemannMapping
public import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Montel selection for the Schur class

This file records the precise normal-family statement needed for the matrix
extremizer argument.  Its proof uses the Cauchy-estimate equicontinuity lemma
from `DiskRigidity.Complex.RiemannMapping` and Mathlib's compact-open
Arzelà--Ascoli theorem.
-/

open Complex Filter Function Metric Set Topology

namespace DiskRigidity.Complex

@[expose] public section

private theorem isClosedEmbedding_continuousMap_toUniformOnFun {X Y : Type*}
    [TopologicalSpace X] [CompactlyCoherentSpace X] [UniformSpace Y] :
    IsClosedEmbedding (⇑(UniformOnFun.ofFun {K : Set X | IsCompact K}) ∘
      (DFunLike.coe : C(X, Y) → (X → Y))) := by
  refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
  rw [show (⇑(UniformOnFun.ofFun {K : Set X | IsCompact K}) ∘
      (DFunLike.coe : C(X, Y) → (X → Y))) = ContinuousMap.toUniformOnFunIsCompact from rfl,
    ContinuousMap.range_toUniformOnFunIsCompact]
  exact UniformOnFun.isClosed_setOfPred_continuous CompactlyCoherentSpace.isCoherentWith

private theorem equicontinuous_subtype_range {X Y ι : Type*} [TopologicalSpace X]
    [UniformSpace Y] {f : ι → C(X, Y)} (hf : Equicontinuous fun i ↦ (f i : X → Y)) :
    Equicontinuous ((DFunLike.coe : C(X, Y) → (X → Y)) ∘
      (Subtype.val : ↑(Set.range f) → C(X, Y))) := by
  classical
  choose σ hσ using fun x : ↑(Set.range f) ↦ x.2
  have heq : ((DFunLike.coe : C(X, Y) → (X → Y)) ∘
      (Subtype.val : ↑(Set.range f) → C(X, Y))) =
      (fun i ↦ (f i : X → Y)) ∘ σ := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, hσ x]
  rw [heq]
  exact hf.comp σ

/-- Montel's selection theorem specialized to a uniformly bounded sequence
of scalar holomorphic functions.  This is the exact form used for sequences
in the Schur class. -/
theorem schurMontel {U : Set ℂ} {F : ℕ → ℂ → ℂ} (hU : IsOpen U)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hbound : ∀ n z, z ∈ U → ‖F n z‖ ≤ 1) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
      DifferentiableOn ℂ g U ∧
      TendstoLocallyUniformlyOn (fun n ↦ F (φ n)) g atTop U := by
  classical
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  let f : ℕ → C(U, ℂ) := fun n ↦
    ⟨U.domRestrict (F n), ((hF n).continuousOn).domRestrict⟩
  have hEqOn : EquicontinuousOn F U := by
    intro z hz
    exact (Complex.equicontinuousAt_of_forall_norm_le
      (hU.mem_nhds hz) hF ⟨1, hbound⟩).equicontinuousWithinAt U
  have hEq : Equicontinuous fun n ↦ (f n : U → ℂ) := by
    exact (equicontinuous_restrict_iff F).mpr hEqOn
  have hcpt : IsCompact (closure (Set.range f)) := by
    refine ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (fun K hK ↦ hK) isClosedEmbedding_continuousMap_toUniformOnFun
      (fun K _ ↦ (equicontinuous_subtype_range hEq).equicontinuousOn K) ?_
    intro K _ z _
    refine ⟨closedBall (0 : ℂ) 1, isCompact_closedBall _ _, ?_⟩
    intro q hq
    obtain ⟨n, hn⟩ := hq
    subst q
    change F n z ∈ closedBall 0 1
    simpa [mem_closedBall, dist_zero_right] using hbound n z z.2
  obtain ⟨a, -, φ, hφ, hconv⟩ :=
    hcpt.tendsto_subseq (x := f) fun n ↦ subset_closure ⟨n, rfl⟩
  let g : ℂ → ℂ := fun z ↦ if hz : z ∈ U then a ⟨z, hz⟩ else 0
  have hg : (g ∘ (Subtype.val : U → ℂ)) = fun x : U ↦ a x := by
    funext x
    simp [g, x.2]
  have hconvOn : TendstoLocallyUniformlyOn (fun n ↦ F (φ n)) g atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe, hg]
    exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hconv
  exact ⟨φ, g, hφ,
    hconvOn.differentiableOn (Eventually.of_forall fun n ↦ hF (φ n)) hU, hconvOn⟩

end

end DiskRigidity.Complex
