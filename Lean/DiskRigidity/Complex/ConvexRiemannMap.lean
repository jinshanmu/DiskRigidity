/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.RiemannMapping
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.GaugeRescale

/-!
# Riemann maps of bounded convex plane domains

This file packages the Riemann mapping theorem in the precise interior-domain form used by the
disk-rigidity argument.
-/

open Metric Set

namespace DiskRigidity.Complex

public section

/-- Data of a normalized holomorphic bijection from `Ω` to the open unit disc. -/
structure RiemannMap (Ω : Set ℂ) (z₀ : ℂ) where
  /-- The holomorphic map, extended arbitrarily away from `Ω`. -/
  toFun : ℂ → ℂ
  /-- Holomorphy on the domain. -/
  differentiableOn : DifferentiableOn ℂ toFun Ω
  /-- The restriction is a bijection onto the open unit disc. -/
  bijOn : Set.BijOn toFun Ω (ball 0 1)
  /-- The chosen base point maps to the origin. -/
  map_base : toFun z₀ = 0

/-- A nonempty convex subset of a real topological vector space is simply connected. -/
theorem isSimplyConnected_of_convex {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E] {s : Set E}
    (hs : Convex ℝ s) (hne : s.Nonempty) : IsSimplyConnected s := by
  let hcontract : ContractibleSpace s := hs.contractibleSpace hne
  exact @SimplyConnectedSpace.ofContractible s _ hcontract

/-- A bounded subset of `ℂ` is not the whole plane. -/
theorem ne_univ_of_isBounded {s : Set ℂ} (hs : Bornology.IsBounded s) : s ≠ univ := by
  rintro rfl
  exact NormedSpace.unbounded_univ ℂ ℂ hs

/-- The Riemann mapping theorem for a bounded nonempty convex open subset of `ℂ`. -/
theorem exists_riemannMap_of_convex {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hΩne : Ω.Nonempty) (hΩb : Bornology.IsBounded Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    Nonempty (RiemannMap Ω z₀) := by
  have hΩsc : IsSimplyConnected Ω := isSimplyConnected_of_convex hΩc hΩne
  have hΩu : Ω ≠ univ := ne_univ_of_isBounded hΩb
  rcases _root_.Complex.exists_bijOn_unitBall_map_eq_zero hΩo hΩsc hΩu hz₀ with
    ⟨f, hf, hfbij, hf₀⟩
  exact ⟨⟨f, hf, hfbij, hf₀⟩⟩

/-- Independently of conformality, the closure of a bounded convex plane domain is homeomorphic
to the closed unit disc.  This is the radial gauge-rescaling part of the convex-domain boundary
argument. -/
theorem exists_homeomorph_closure_closedBall_of_convex {Ω : Set ℂ}
    (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) (hΩne : Ω.Nonempty)
    (hΩb : Bornology.IsBounded Ω) : Nonempty (closure Ω ≃ₜ closedBall (0 : ℂ) 1) := by
  obtain ⟨e, -, hclosure, -⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hΩc
      (by rwa [hΩo.interior_eq]) hΩb
  exact ⟨(e.image (closure Ω)).trans (Homeomorph.setCongr hclosure)⟩

end

end DiskRigidity.Complex
