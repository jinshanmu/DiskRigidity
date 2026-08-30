/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.ConvexCaratheodory

/-!
# Boundary-arc uniqueness on bounded convex domains

Carathéodory transport and Jensen's formula imply that a function in
`A(closure U)` which vanishes on a nontrivial connected part of the frontier
vanishes throughout a bounded convex domain.
-/

noncomputable section

open Bornology Filter Function MeasureTheory Metric Set Topology
open scoped Real

namespace DiskRigidity.Complex

@[expose] public section

/-- Boundary uniqueness in the exact form needed for analytic equality
data.  A function holomorphic on a bounded open convex domain and continuous
on its closure is identically zero if it vanishes on any preconnected
frontier subset containing two distinct points. -/
theorem eqOn_zero_of_diffContOnCl_of_preconnected_frontier
    {U T : Set ℂ} {h : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hUb : IsBounded U)
    (hh : DiffContOnCl ℂ h U)
    (hTpre : IsPreconnected T) (hTfront : T ⊆ frontier U)
    (hzero : ∀ z ∈ T, h z = 0)
    {x y : ℂ} (hx : x ∈ T) (hy : y ∈ T) (hxy : x ≠ y) :
    EqOn h 0 U := by
  classical
  have hUne : U.Nonempty := by
    rw [← closure_nonempty_iff]
    exact ⟨x, frontier_subset_closure (hTfront hx)⟩
  obtain ⟨z₀, hz₀⟩ := hUne
  obtain ⟨R⟩ :=
    exists_riemannMap_of_convex hUo hUc ⟨z₀, hz₀⟩ hUb hz₀
  let phi : ℂ → ℂ := R.toFun
  have hphi : DifferentiableOn ℂ phi U := R.differentiableOn
  have hbij : BijOn phi U (ball 0 1) := R.bijOn
  obtain ⟨Phi, hPhiExt⟩ :=
    exists_homeomorph_closure_closedDisc_extends_riemannMap
      hUo hUc hUb hphi hbij
  let f : ℂ → ℂ := fun z ↦
    if hz : z ∈ closedBall (0 : ℂ) 1 then h (Phi.symm ⟨z, hz⟩) else 0
  have hfcont : ContinuousOn f (closedBall (0 : ℂ) 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun z : closedBall (0 : ℂ) 1 ↦
        h (Phi.symm z : ℂ)) :=
      hh.continuousOn.comp_continuous
        (continuous_subtype_val.comp Phi.symm.continuous)
        fun z ↦ (Phi.symm z).2
    convert hc using 1
    funext z
    simp only [Set.domRestrict_apply, f, dif_pos z.2]
  have hfEq (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
      f z = h (inverseRiemannMap U phi z) := by
    have hzClosed : z ∈ closedBall (0 : ℂ) 1 :=
      ball_subset_closedBall hz
    let w : ball (0 : ℂ) 1 := ⟨z, hz⟩
    let u : U := ⟨inverseRiemannMap U phi w,
      inverseRiemannMap_mem hbij w.2⟩
    have hPhiU : Phi ⟨u, subset_closure u.2⟩ =
        (⟨z, hzClosed⟩ : closedBall (0 : ℂ) 1) := by
      rw [hPhiExt]
      apply Subtype.ext
      exact riemannMap_inverseRiemannMap hbij w.2
    have hSymm : Phi.symm ⟨z, hzClosed⟩ =
        ⟨u, subset_closure u.2⟩ := by
      rw [← hPhiU]
      exact Phi.symm_apply_apply _
    dsimp [f]
    rw [dif_pos hzClosed, hSymm]
  have hfdiff : DifferentiableOn ℂ f (ball 0 1) := by
    have hcomp : DifferentiableOn ℂ
        (h ∘ inverseRiemannMap U phi) (ball 0 1) :=
      hh.differentiableOn.comp
        (differentiableOn_inverseRiemannMap hUo hphi hbij)
        fun _ hz ↦ inverseRiemannMap_mem hbij hz
    exact hcomp.congr hfEq
  by_contra hnotZero
  have hnonzero : ∃ z ∈ U, h z ≠ 0 := by
    simpa [EqOn] using hnotZero
  have hfnonzero : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0 := by
    obtain ⟨z, hz, hhz⟩ := hnonzero
    refine ⟨phi z, hbij.mapsTo hz, ?_⟩
    rw [hfEq _ (hbij.mapsTo hz), inverseRiemannMap_riemannMap hbij hz]
    exact hhz
  let Tbar : Set (closure U) := {z | (z : ℂ) ∈ T}
  have hTbarImage : ((↑) : closure U → ℂ) '' Tbar = T := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨⟨z, frontier_subset_closure (hTfront hz)⟩, hz, rfl⟩
  have hTbarPre : IsPreconnected Tbar := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [hTbarImage]
    exact hTpre
  let D : Set (closedBall (0 : ℂ) 1) := Phi.symm ⁻¹' Tbar
  have hDpre : IsPreconnected D :=
    Phi.symm.isPreconnected_preimage.mpr hTbarPre
  let S : Set ℂ := ((↑) : closedBall (0 : ℂ) 1 → ℂ) '' D
  have hSpre : IsPreconnected S :=
    hDpre.image _ continuous_subtype_val.continuousOn
  have hSsphere : S ⊆ sphere (0 : ℂ) 1 := by
    rintro _ ⟨d, hd, rfl⟩
    have hfront : (Phi.symm d : ℂ) ∈ frontier U :=
      hTfront hd
    simpa using homeomorph_closure_closedDisc_maps_frontier_to_sphere
      hUo hbij Phi hPhiExt hfront
  let xbar : closure U := ⟨x, frontier_subset_closure (hTfront hx)⟩
  let ybar : closure U := ⟨y, frontier_subset_closure (hTfront hy)⟩
  let xd : closedBall (0 : ℂ) 1 := Phi xbar
  let yd : closedBall (0 : ℂ) 1 := Phi ybar
  have hxdD : xd ∈ D := by
    change Phi.symm xd ∈ Tbar
    simpa [xd, xbar, Tbar] using hx
  have hydD : yd ∈ D := by
    change Phi.symm yd ∈ Tbar
    simpa [yd, ybar, Tbar] using hy
  have hxdS : (xd : ℂ) ∈ S := ⟨xd, hxdD, rfl⟩
  have hydS : (yd : ℂ) ∈ S := ⟨yd, hydD, rfl⟩
  have hxdyd : (xd : ℂ) ≠ (yd : ℂ) := by
    intro heq
    have hdEq : xd = yd := Subtype.ext heq
    have hbarEq : xbar = ybar := Phi.injective hdEq
    exact hxy (congrArg Subtype.val hbarEq)
  have hfzeroS : ∀ z ∈ S, f z = 0 := by
    rintro _ ⟨d, hd, rfl⟩
    dsimp [f]
    rw [dif_pos d.2]
    exact hzero _ hd
  by_cases hSproper : S ≠ sphere (0 : ℂ) 1
  · obtain ⟨a, b, hab, hwidth, harc⟩ :=
      exists_circleMap_interval_subset_of_preconnected
        hSpre hSsphere hxdS hydS hxdyd hSproper
    exact (not_boundary_interval_zero_of_nonzero_differentiableOn_unitDisc
      hfdiff hfcont hfnonzero hab hwidth) fun theta htheta ↦
        hfzeroS _ (harc theta htheta)
  · have hSsphereEq : S = sphere (0 : ℂ) 1 :=
      not_ne_iff.mp hSproper
    exact (not_boundary_arc_zero_of_nonzero_differentiableOn_unitDisc
      hfdiff hfcont hfnonzero Real.pi_pos (by linarith [Real.pi_pos]))
        fun theta _ ↦ hfzeroS _ (by
          rw [hSsphereEq]
          simpa only [abs_one] using
            circleMap_mem_sphere' (0 : ℂ) 1 theta)

/-- Parametric form: a continuous image of a real interval in the frontier
is enough for boundary uniqueness, provided its endpoints are distinct. -/
theorem eqOn_zero_of_diffContOnCl_of_frontier_arc
    {U : Set ℂ} {h : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hUb : IsBounded U)
    (hh : DiffContOnCl ℂ h U)
    {a b : ℝ} (hab : a ≤ b) {gamma : ℝ → ℂ}
    (hgamma : ContinuousOn gamma (Icc a b))
    (hfront : ∀ t ∈ Icc a b, gamma t ∈ frontier U)
    (hend : gamma a ≠ gamma b)
    (hzero : ∀ t ∈ Icc a b, h (gamma t) = 0) :
    EqOn h 0 U := by
  let T : Set ℂ := gamma '' Icc a b
  have hTpre : IsPreconnected T :=
    (ordConnected_Icc.isPreconnected.image gamma hgamma)
  have hTfront : T ⊆ frontier U := by
    rintro _ ⟨t, ht, rfl⟩
    exact hfront t ht
  apply eqOn_zero_of_diffContOnCl_of_preconnected_frontier
    hUo hUc hUb hh hTpre hTfront
    (fun _ ⟨t, ht, htg⟩ ↦ htg ▸ hzero t ht)
    (show gamma a ∈ T from ⟨a, ⟨le_rfl, hab⟩, rfl⟩)
    (show gamma b ∈ T from ⟨b, ⟨hab, le_rfl⟩, rfl⟩) hend

end

end DiskRigidity.Complex
