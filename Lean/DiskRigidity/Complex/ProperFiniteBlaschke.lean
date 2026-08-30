/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.SchurReduction
public import DiskRigidity.Complex.BiholomorphicBasics

/-!
# Properness of finite Blaschke products

The compact-sublevel formulation below is the boundary fact actually needed in strict-domain
monotonicity.  It avoids invoking a boundary extension of a Riemann map: a finite Blaschke product
cannot remain uniformly inside the target disc while its argument escapes to the source circle.
-/

open Function Metric Set

namespace DiskRigidity.Complex

@[expose] public section

/-- The closed-disc sublevel of a function. -/
def closedDiscSublevel (B : ℂ → ℂ) (r : ℝ) : Set ℂ :=
  {z ∈ closedBall (0 : ℂ) 1 | ‖B z‖ ≤ r}

/-- A continuous function has compact sublevels in the closed unit disc. -/
theorem isCompact_closedDiscSublevel_of_continuousOn {B : ℂ → ℂ}
    (hB : ContinuousOn B (closedBall (0 : ℂ) 1)) (r : ℝ) :
    IsCompact (closedDiscSublevel B r) := by
  have hcont : ContinuousOn (fun z => ‖B z‖) (closedBall (0 : ℂ) 1) := hB.norm
  have hclosed : IsClosed (closedDiscSublevel B r) :=
    isClosed_closedBall.isClosed_le hcont continuousOn_const
  exact (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset hclosed fun z hz => hz.1

/-- If a function has modulus one on the unit circle, every strict closed-disc sublevel misses the
circle. -/
theorem closedDiscSublevel_subset_ball_of_norm_eq_one {B : ℂ → ℂ} {r : ℝ}
    (hB : ∀ z ∈ sphere (0 : ℂ) 1, ‖B z‖ = 1) (hr : r < 1) :
    closedDiscSublevel B r ⊆ ball (0 : ℂ) 1 := by
  rintro z ⟨hzclosed, hzB⟩
  rw [mem_closedBall_zero_iff] at hzclosed
  rw [mem_ball_zero_iff]
  exact lt_of_le_of_ne hzclosed fun heq => by
    have hzsphere : z ∈ sphere (0 : ℂ) 1 := by
      simpa [mem_sphere_zero_iff_norm] using heq
    have := hB z hzsphere
    linarith

/-- A finite Blaschke product has compact closed-disc sublevels. -/
theorem IsSchurFiniteBlaschke.isCompact_closedDiscSublevel {B : ℂ → ℂ}
    (hB : IsSchurFiniteBlaschke B) (r : ℝ) : IsCompact (closedDiscSublevel B r) := by
  exact isCompact_closedDiscSublevel_of_continuousOn hB.analyticOnNhd.continuousOn r

/-- A strict sublevel of a finite Blaschke product misses the unit circle. -/
theorem IsSchurFiniteBlaschke.closedDiscSublevel_subset_ball {B : ℂ → ℂ}
    (hB : IsSchurFiniteBlaschke B) {r : ℝ} (hr : r < 1) :
    closedDiscSublevel B r ⊆ ball (0 : ℂ) 1 := by
  exact closedDiscSublevel_subset_ball_of_norm_eq_one
    (fun z hz => hB.norm_eq_one hz) hr

/-- Properness in compact-sublevel form. -/
theorem IsSchurFiniteBlaschke.isCompact_sublevel_in_ball {B : ℂ → ℂ}
    (hB : IsSchurFiniteBlaschke B) {r : ℝ} (hr : r < 1) :
    IsCompact (closedDiscSublevel B r) ∧ closedDiscSublevel B r ⊆ ball (0 : ℂ) 1 :=
  ⟨hB.isCompact_closedDiscSublevel r, hB.closedDiscSublevel_subset_ball hr⟩

/-- A boundary-modulus theorem for any continuous closed-disc inner function.  The hypotheses are
exactly compactness of strict sublevels: continuity on the closed disc, a closed-disc bound in the
interior, and modulus one on the circle. -/
theorem norm_eq_one_at_frontier_of_eqOn_discInner_comp
    {U : Set ℂ} {phi B F : ℂ → ℂ} {xi : ℂ}
    (hU : IsOpen U) (hphi : DifferentiableOn ℂ phi U)
    (hphibij : BijOn phi U (ball 0 1))
    (hBcont : ContinuousOn B (closedBall 0 1))
    (hBball : MapsTo B (ball 0 1) (closedBall 0 1))
    (hBsphere : ∀ z ∈ sphere (0 : ℂ) 1, ‖B z‖ = 1)
    (hF : ContinuousAt F xi) (hFeq : EqOn F (B ∘ phi) U) (hxi : xi ∈ frontier U) :
    ‖F xi‖ = 1 := by
  have hxicl : xi ∈ closure U := frontier_subset_closure hxi
  have hxinot : xi ∉ U := by
    rw [hU.frontier_eq] at hxi
    exact hxi.2
  have hle : ‖F xi‖ ≤ 1 := by
    apply ContinuousWithinAt.closure_le hxicl hF.norm.continuousWithinAt
      continuousWithinAt_const
    intro z hz
    rw [hFeq hz]
    exact (by simpa [mem_closedBall_zero_iff] using hBball (hphibij.mapsTo hz))
  apply le_antisymm hle
  apply le_of_not_gt
  intro hlt
  let r : ℝ := (‖F xi‖ + 1) / 2
  have hFr : ‖F xi‖ < r := by dsimp only [r]; linarith
  have hr1 : r < 1 := by dsimp only [r]; linarith
  have hKcompact := isCompact_closedDiscSublevel_of_continuousOn hBcont r
  have hKball := closedDiscSublevel_subset_ball_of_norm_eq_one hBsphere hr1
  let e : U ≃ₜ ball (0 : ℂ) 1 :=
    homeomorphOfDifferentiableOnBijOn hU hphi hphibij
  let K : Set (ball (0 : ℂ) 1) :=
    {z | (z : ℂ) ∈ closedDiscSublevel B r}
  have hKcoe : ((↑) '' K : Set ℂ) = closedDiscSublevel B r := by
    ext z
    constructor
    · rintro ⟨z', hz', rfl⟩
      exact hz'
    · intro hz
      exact ⟨⟨z, hKball hz⟩, hz, rfl⟩
  have hKcompact' : IsCompact K := by
    rw [Subtype.isCompact_iff, hKcoe]
    exact hKcompact
  let C : Set ℂ := (↑) '' (e.symm '' K)
  have hCcompact : IsCompact C := by
    change IsCompact ((↑) '' (e.symm '' K) : Set ℂ)
    rw [← Subtype.isCompact_iff]
    exact hKcompact'.image e.symm.continuous
  let P : Set ℂ := {z ∈ U | ‖F z‖ ≤ r}
  have hPC : P ⊆ C := by
    rintro z ⟨hzU, hzF⟩
    let zU : U := ⟨z, hzU⟩
    let u : ball (0 : ℂ) 1 := e zU
    have hueq : (u : ℂ) = phi z := by
      exact homeomorphOfDifferentiableOnBijOn_apply hU hphi hphibij zU
    have huK : u ∈ K := by
      change (u : ℂ) ∈ closedDiscSublevel B r
      refine ⟨ball_subset_closedBall u.2, ?_⟩
      rw [hueq]
      simpa [Function.comp_apply] using
        (congrArg norm (hFeq hzU)).symm.trans_le hzF
    refine ⟨e.symm u, ⟨u, huK, rfl⟩, ?_⟩
    simp only [u, zU, Homeomorph.symm_apply_apply]
  have hxiP : xi ∈ closure P := by
    rw [mem_closure_iff_frequently]
    have hfreqU : ∃ᶠ z in nhds xi, z ∈ U := mem_closure_iff_frequently.mp hxicl
    have hev : ∀ᶠ z in nhds xi, ‖F z‖ < r :=
      hF.norm (Iio_mem_nhds hFr)
    exact (hfreqU.and_eventually hev).mono fun z hz => ⟨hz.1, hz.2.le⟩
  have hxiC : xi ∈ C := by
    have : xi ∈ closure C := closure_mono hPC hxiP
    rwa [hCcompact.isClosed.closure_eq] at this
  apply hxinot
  obtain ⟨z, -, hz⟩ := hxiC
  rw [← hz]
  exact z.2

/-- If a finite-Blaschke composition through a biholomorphism continues continuously to a source
boundary point, its value there has modulus one.  This is the properness replacement for invoking
a full Carathéodory extension in strict-domain monotonicity. -/
theorem norm_eq_one_at_frontier_of_eqOn_finiteBlaschke_comp
    {U : Set ℂ} {phi B F : ℂ → ℂ} {xi : ℂ}
    (hU : IsOpen U) (hphi : DifferentiableOn ℂ phi U)
    (hphibij : BijOn phi U (ball 0 1)) (hB : IsSchurFiniteBlaschke B)
    (hF : ContinuousAt F xi) (hFeq : EqOn F (B ∘ phi) U) (hxi : xi ∈ frontier U) :
    ‖F xi‖ = 1 := by
  exact norm_eq_one_at_frontier_of_eqOn_discInner_comp hU hphi hphibij
    hB.analyticOnNhd.continuousOn hB.isSchur.2
    (fun z hz => hB.norm_eq_one hz) hF hFeq hxi

/-- Explicit-product form of the boundary-modulus theorem. -/
theorem norm_eq_one_at_frontier_of_eqOn_finiteBlaschkeProduct_comp
    {U : Set ℂ} {phi F : ℂ → ℂ} {xi : ℂ} {ι : Type*}
    (s : Finset ι) (a : ι → ℂ) (c : ℂ)
    (hc : ‖c‖ = 1) (ha : ∀ i ∈ s, a i ∈ ball 0 1)
    (hU : IsOpen U) (hphi : DifferentiableOn ℂ phi U)
    (hphibij : BijOn phi U (ball 0 1))
    (hF : ContinuousAt F xi)
    (hFeq : EqOn F (finiteBlaschkeProduct s a c ∘ phi) U)
    (hxi : xi ∈ frontier U) : ‖F xi‖ = 1 := by
  apply norm_eq_one_at_frontier_of_eqOn_discInner_comp hU hphi hphibij
    (analyticOnNhd_finiteBlaschkeProduct s a c ha).continuousOn
    (mapsTo_ball_closedBall_finiteBlaschkeProduct s a c hc ha)
    (fun z hz => norm_finiteBlaschkeProduct_eq_one s a c z hc ha hz)
    hF hFeq hxi

end

end DiskRigidity.Complex
