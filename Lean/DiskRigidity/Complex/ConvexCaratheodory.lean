/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.BiholomorphicBasics
public import DiskRigidity.Complex.BoundaryArcUniqueness
public import DiskRigidity.Complex.ConformalShortCircle
public import DiskRigidity.Complex.ConvexRiemannMap
public import DiskRigidity.Complex.NestedContinuum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Carathéodory extension for bounded convex domains

This file proves the boundary extension needed by the disk-rigidity argument
directly in the convex case.  The analytic input is the length--area short
crosscut theorem from `ConformalShortCircle`; convexity supplies the separating
segments.  No Jordan-curve or prime-end theorem is assumed.
-/

noncomputable section

open Bornology Filter Function Metric Set Topology
open scoped ComplexConjugate Real

namespace DiskRigidity.Complex

@[expose] public section

/-- The set-theoretic inverse of a Riemann map, extended arbitrarily off the
open unit disc. -/
def inverseRiemannMap (U : Set ℂ) (phi : ℂ → ℂ) : ℂ → ℂ :=
  Function.invFunOn phi U

theorem inverseRiemannMap_mem {U : Set ℂ} {phi : ℂ → ℂ}
    (hbij : BijOn phi U (ball 0 1)) {z : ℂ} (hz : z ∈ ball 0 1) :
    inverseRiemannMap U phi z ∈ U := by
  exact hbij.surjOn.mapsTo_invFunOn hz

theorem riemannMap_inverseRiemannMap {U : Set ℂ} {phi : ℂ → ℂ}
    (hbij : BijOn phi U (ball 0 1)) {z : ℂ} (hz : z ∈ ball 0 1) :
    phi (inverseRiemannMap U phi z) = z := by
  exact hbij.surjOn.rightInvOn_invFunOn hz

theorem inverseRiemannMap_riemannMap {U : Set ℂ} {phi : ℂ → ℂ}
    (hbij : BijOn phi U (ball 0 1)) {z : ℂ} (hz : z ∈ U) :
    inverseRiemannMap U phi (phi z) = z := by
  exact hbij.injOn.leftInvOn_invFunOn hz

theorem differentiableOn_inverseRiemannMap {U : Set ℂ} {phi : ℂ → ℂ}
    (hUo : IsOpen U) (hphi : DifferentiableOn ℂ phi U)
    (hbij : BijOn phi U (ball 0 1)) :
    DifferentiableOn ℂ (inverseRiemannMap U phi) (ball 0 1) := by
  exact differentiableOn_invFunOn_of_bijOn hUo hphi hbij

theorem injOn_inverseRiemannMap {U : Set ℂ} {phi : ℂ → ℂ}
    (hbij : BijOn phi U (ball 0 1)) :
    InjOn (inverseRiemannMap U phi) (ball 0 1) := by
  intro z hz w hw hzw
  rw [← riemannMap_inverseRiemannMap hbij hz,
    ← riemannMap_inverseRiemannMap hbij hw, hzw]

/-- The inverse Riemann map as a homeomorphism between the open unit disc and
its target domain. -/
def inverseRiemannMapHomeomorph
    {U : Set ℂ} {phi : ℂ → ℂ}
    (hUo : IsOpen U) (hphi : DifferentiableOn ℂ phi U)
    (hbij : BijOn phi U (ball 0 1)) :
    ball (0 : ℂ) 1 ≃ₜ U where
  toFun z := ⟨inverseRiemannMap U phi z,
    inverseRiemannMap_mem hbij z.2⟩
  invFun w := ⟨phi w, hbij.mapsTo w.2⟩
  left_inv z := by
    apply Subtype.ext
    exact riemannMap_inverseRiemannMap hbij z.2
  right_inv w := by
    apply Subtype.ext
    exact inverseRiemannMap_riemannMap hbij w.2
  continuous_toFun :=
    ((differentiableOn_inverseRiemannMap hUo hphi hbij).continuousOn.comp_continuous
      continuous_subtype_val fun z ↦ z.2).subtype_mk _
  continuous_invFun :=
    (hphi.continuousOn.comp_continuous continuous_subtype_val fun w ↦ w.2).subtype_mk _

private def inwardCrosscutPoint (zeta : ℂ) (rho : ℝ) : ℂ :=
  (1 - rho) • zeta

private theorem norm_eq_one_of_mem_unitSphere {zeta : ℂ}
    (hzeta : zeta ∈ sphere (0 : ℂ) 1) : ‖zeta‖ = 1 := by
  simpa only [mem_sphere, dist_zero_right] using hzeta

private theorem inwardCrosscutPoint_mem
    {zeta : ℂ} (hzeta : zeta ∈ sphere (0 : ℂ) 1)
    {rho : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1) :
    inwardCrosscutPoint zeta rho ∈
      ball (0 : ℂ) 1 ∩ sphere zeta rho := by
  have hzetaNorm := norm_eq_one_of_mem_unitSphere hzeta
  constructor
  · rw [mem_ball, dist_zero_right, inwardCrosscutPoint, norm_smul,
      Real.norm_eq_abs, hzetaNorm, mul_one, abs_of_pos (sub_pos.mpr hrhoOne)]
    linarith
  · rw [mem_sphere, Complex.dist_eq, inwardCrosscutPoint]
    have hsub : (1 - rho) • zeta - zeta = (-rho) • zeta := by module
    rw [hsub, norm_smul, Real.norm_eq_abs, hzetaNorm, mul_one,
      abs_neg, abs_of_pos hrho]

private theorem tendsto_inwardCrosscutPoint {zeta : ℂ} {rho : ℕ → ℝ}
    (hrho : Tendsto rho atTop (nhds 0)) :
    Tendsto (fun n ↦ inwardCrosscutPoint zeta (rho n)) atTop (nhds zeta) := by
  have hcoef : Tendsto (fun n ↦ (1 - rho n : ℝ)) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hrho)
  simpa only [inwardCrosscutPoint, one_smul] using
    hcoef.smul_const zeta

/-- A nontrivial proper preconnected subset of the unit circle contains a
closed circular arc of positive angular length. -/
theorem exists_circleMap_interval_subset_of_preconnected
    {T : Set ℂ} (hTpre : IsPreconnected T)
    (hTsphere : T ⊆ sphere (0 : ℂ) 1)
    {z w : ℂ} (hzT : z ∈ T) (hwT : w ∈ T) (hzw : z ≠ w)
    (hTproper : T ≠ sphere (0 : ℂ) 1) :
    ∃ a b : ℝ, a < b ∧ b - a < 2 * Real.pi ∧
      ∀ theta ∈ Icc a b, circleMap 0 1 theta ∈ T := by
  have hTssub : T ⊂ sphere (0 : ℂ) 1 :=
    hTsphere.ssubset_of_ne hTproper
  obtain ⟨q, hqSphere, hqNotT⟩ := Set.exists_of_ssubset hTssub
  have hqNorm : ‖q‖ = 1 := norm_eq_one_of_mem_unitSphere hqSphere
  have hqNe : q ≠ 0 := norm_ne_zero_iff.mp (by rw [hqNorm]; norm_num)
  let u : ℂ := -q⁻¹
  have huNorm : ‖u‖ = 1 := by simp [u, hqNorm]
  have huNe : u ≠ 0 := norm_ne_zero_iff.mp (by rw [huNorm]; norm_num)
  have huq : u * q = -1 := by simp [u, hqNe]
  have hrotNorm {x : ℂ} (hx : x ∈ T) : ‖u * x‖ = 1 := by
    rw [norm_mul, huNorm, norm_eq_one_of_mem_unitSphere (hTsphere hx), one_mul]
  have hrotNeNegOne {x : ℂ} (hx : x ∈ T) : u * x ≠ -1 := by
    intro heq
    have huxuq : u * x = u * q := heq.trans huq.symm
    have hxq : x = q := mul_left_cancel₀ huNe huxuq
    exact hqNotT (hxq ▸ hx)
  have hrotSlit {x : ℂ} (hx : x ∈ T) : u * x ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff_arg]
    constructor
    · intro harg
      apply hrotNeNegOne hx
      exact Complex.ext_norm_arg
        (by rw [hrotNorm hx, norm_neg, norm_one])
        (by rw [harg, Complex.arg_neg_one])
    · exact norm_ne_zero_iff.mp (by rw [hrotNorm hx]; norm_num)
  let angle : ℂ → ℝ := fun x ↦ Complex.arg (u * x)
  have hangleCont : ContinuousOn angle T := by
    exact Complex.continuousOn_arg.comp
      (continuous_const.mul continuous_id).continuousOn
      (fun x hx ↦ hrotSlit hx)
  have hangleNe : angle z ≠ angle w := by
    intro heq
    have hrotEq : u * z = u * w := Complex.ext_norm_arg
      (by rw [hrotNorm hzT, hrotNorm hwT]) heq
    exact hzw (mul_left_cancel₀ huNe hrotEq)
  have hwidth : |angle z - angle w| < 2 * Real.pi :=
    Complex.abs_arg_sub_arg_lt (u * z) (u * w)
  have huInvNorm : ‖u⁻¹‖ = 1 := by simp [huNorm]
  let alpha : ℝ := Complex.arg u⁻¹
  have huInvCircle : u⁻¹ = circleMap 0 1 alpha := by
    have hpolar := Complex.norm_mul_exp_arg_mul_I u⁻¹
    rw [huInvNorm] at hpolar
    norm_num at hpolar
    rw [circleMap_zero]
    norm_num
    exact hpolar.symm
  have harc (x y : ℂ) (hx : x ∈ T) (hy : y ∈ T)
      (hxy : angle x < angle y) :
      ∀ theta ∈ Icc (alpha + angle x) (alpha + angle y),
        circleMap 0 1 theta ∈ T := by
    intro theta htheta
    let tau : ℝ := theta - alpha
    have htau : tau ∈ Icc (angle x) (angle y) := by
      dsimp [tau]
      constructor <;> linarith [htheta.1, htheta.2]
    obtain ⟨v, hvT, hvangle⟩ :=
      hTpre.intermediate_value hx hy hangleCont htau
    have hcircleRot : circleMap 0 1 tau = u * v := by
      have hpolar := Complex.norm_mul_exp_arg_mul_I (u * v)
      rw [hrotNorm hvT] at hpolar
      norm_num at hpolar
      change Complex.arg (u * v) = tau at hvangle
      rw [hvangle] at hpolar
      rw [circleMap_zero]
      norm_num
      exact hpolar
    have hthetaEq : theta = alpha + tau := by simp [tau]
    rw [hthetaEq]
    have hmulCircle : circleMap 0 1 (alpha + tau) =
        circleMap 0 1 alpha * circleMap 0 1 tau := by
      simpa using (circleMap_zero_mul 1 1 alpha tau).symm
    rw [hmulCircle, ← huInvCircle, hcircleRot]
    simpa [huNe] using hvT
  rcases lt_or_gt_of_ne hangleNe with hlt | hgt
  · refine ⟨alpha + angle z, alpha + angle w, by linarith,
      ?_, harc z w hzT hwT hlt⟩
    rw [add_sub_add_left_eq_sub]
    rw [abs_of_neg (sub_neg.mpr hlt)] at hwidth
    linarith
  · refine ⟨alpha + angle w, alpha + angle z, by linarith,
      ?_, harc w z hwT hzT hgt⟩
    rw [add_sub_add_left_eq_sub]
    rw [abs_of_pos (sub_pos.mpr hgt)] at hwidth
    exact hwidth

/-- The inverse Riemann map is uniformly Cauchy in every sufficiently small
disc cap at a boundary point of the unit disc.  This is the central convex
crosscut lemma. -/
theorem inverseRiemannMap_boundary_cauchy
    {U : Set ℂ} {phi : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hUb : IsBounded U)
    (hphi : DifferentiableOn ℂ phi U)
    (hbij : BijOn phi U (ball 0 1))
    {zeta : ℂ} (hzeta : zeta ∈ sphere (0 : ℂ) 1) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta : ℝ, 0 < delta ∧
        ∀ z ∈ ball (0 : ℂ) 1, dist z zeta < delta →
          ∀ w ∈ ball (0 : ℂ) 1, dist w zeta < delta →
            dist (inverseRiemannMap U phi z)
              (inverseRiemannMap U phi w) < epsilon := by
  intro epsilon hepsilon
  let g := inverseRiemannMap U phi
  have hgdiff : DifferentiableOn ℂ g (ball 0 1) :=
    differentiableOn_inverseRiemannMap hUo hphi hbij
  have hginj : InjOn g (ball 0 1) := injOn_inverseRiemannMap hbij
  have hgbound : IsBounded (g '' ball (0 : ℂ) 1) := by
    apply hUb.subset
    exact hbij.surjOn.mapsTo_invFunOn.image_subset
  by_contra hdelta
  push Not at hdelta
  let eta : ℕ → ℝ := fun n ↦ 1 / (n + 1 : ℝ)
  let R : ℕ → ℝ := fun n ↦ min (1 / 2 : ℝ) (eta n)
  have heta (n : ℕ) : 0 < eta n := by
    dsimp [eta]
    positivity
  have hR (n : ℕ) : 0 < R n := by
    dsimp [R]
    positivity
  have hcross : ∀ n : ℕ, ∃ rho : ℝ,
      rho ∈ Ioo 0 (R n) ∧
      diam (g '' (ball (0 : ℂ) 1 ∩ sphere zeta rho)) ≤ eta n := by
    intro n
    exact exists_diam_image_ball_inter_sphere_le hgdiff hginj hgbound
      (heta n) (hR n)
  choose rho hrho hdiam using hcross
  have hrhoPos (n : ℕ) : 0 < rho n := (hrho n).1
  have hrhoEta (n : ℕ) : rho n ≤ eta n :=
    (hrho n).2.le.trans (min_le_right (1 / 2 : ℝ) (eta n))
  have hrhoOne (n : ℕ) : rho n < 1 :=
    (hrho n).2.trans_le ((min_le_left (1 / 2 : ℝ) (eta n)).trans (by norm_num))
  have hrhoZero : Tendsto rho atTop (nhds 0) := by
    exact squeeze_zero (fun n ↦ (hrhoPos n).le) hrhoEta
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hbad : ∀ n : ℕ, ∃ z ∈ ball (0 : ℂ) 1,
      dist z zeta < rho n ∧ ∃ w ∈ ball (0 : ℂ) 1,
        dist w zeta < rho n ∧ epsilon ≤ dist (g z) (g w) := by
    intro n
    obtain ⟨z, hz, hzd, w, hw, hwd, hsep⟩ :=
      hdelta (rho n) (hrhoPos n)
    exact ⟨z, hz, hzd, w, hw, hwd, hsep⟩
  choose z hz hzd w hw hwd hsep using hbad
  let v : ℕ → ℂ := fun n ↦ inwardCrosscutPoint zeta (rho n)
  have hv (n : ℕ) : v n ∈ ball (0 : ℂ) 1 ∩ sphere zeta (rho n) :=
    inwardCrosscutPoint_mem hzeta (hrhoPos n) (hrhoOne n)
  have hvlim : Tendsto v atTop (nhds zeta) :=
    tendsto_inwardCrosscutPoint hrhoZero
  let X : ℕ → (ℂ × ℂ) × ℂ := fun n ↦ ((g (z n), g (w n)), g (v n))
  let K : Set ((ℂ × ℂ) × ℂ) :=
    (closure U ×ˢ closure U) ×ˢ closure U
  have hKcompact : IsCompact K :=
    (hUb.isCompact_closure.prod hUb.isCompact_closure).prod hUb.isCompact_closure
  have hXK (n : ℕ) : X n ∈ K := by
    refine ⟨⟨subset_closure (inverseRiemannMap_mem hbij (hz n)),
      subset_closure (inverseRiemannMap_mem hbij (hw n))⟩,
      subset_closure (inverseRiemannMap_mem hbij (hv n).1)⟩
  obtain ⟨L, hLK, sigma, hsigmaMono, hsigmaLim⟩ :=
    hKcompact.tendsto_subseq hXK
  let x : ℂ := L.1.1
  let y : ℂ := L.1.2
  let p : ℂ := L.2
  have hxU : x ∈ closure U := hLK.1.1
  have hyU : y ∈ closure U := hLK.1.2
  have hpU : p ∈ closure U := hLK.2
  have hxlim : Tendsto (fun k ↦ g (z (sigma k))) atTop (nhds x) := by
    exact ((continuous_fst.comp continuous_fst).tendsto L).comp hsigmaLim
  have hylim : Tendsto (fun k ↦ g (w (sigma k))) atTop (nhds y) := by
    exact ((continuous_snd.comp continuous_fst).tendsto L).comp hsigmaLim
  have hplim : Tendsto (fun k ↦ g (v (sigma k))) atTop (nhds p) := by
    exact (continuous_snd.tendsto L).comp hsigmaLim
  have hxy : epsilon ≤ dist x y := by
    exact ge_of_tendsto' (hxlim.dist hylim) fun k ↦ hsep (sigma k)
  have hxyne : x ≠ y := by
    exact dist_pos.mp (hepsilon.trans_le hxy)
  have hsigTop : Tendsto sigma atTop atTop := hsigmaMono.tendsto_atTop
  have hvsub : Tendsto (fun k ↦ v (sigma k)) atTop (nhds zeta) :=
    hvlim.comp hsigTop
  have hpNot : p ∉ U := by
    intro hp
    have hphiAt : ContinuousAt phi p :=
      ((hphi p hp).differentiableAt (hUo.mem_nhds hp)).continuousAt
    have hphiLimit : Tendsto (fun k ↦ phi (g (v (sigma k))))
        atTop (nhds (phi p)) := hphiAt.tendsto.comp hplim
    have heq : (fun k ↦ phi (g (v (sigma k)))) =
        fun k ↦ v (sigma k) := by
      funext k
      exact riemannMap_inverseRiemannMap hbij (hv (sigma k)).1
    rw [heq] at hphiLimit
    have hphizeta : phi p = zeta := tendsto_nhds_unique hphiLimit hvsub
    have hphiMem := hbij.mapsTo hp
    rw [hphizeta, mem_ball, dist_zero_right,
      norm_eq_one_of_mem_unitSphere hzeta] at hphiMem
    exact (lt_irrefl 1) hphiMem
  have himpossible (q : ℂ) (hqU : q ∈ closure U) (qdom : ℕ → ℂ)
      (hqdom : ∀ n, qdom n ∈ ball (0 : ℂ) 1)
      (hqclose : ∀ n, dist (qdom n) zeta < rho n)
      (hqlim : Tendsto (fun k ↦ g (qdom (sigma k))) atTop (nhds q))
      (hqp : q ≠ p) : False := by
    have hzeroD : (0 : ℂ) ∈ ball 0 1 := by simp
    let a : ℂ := g 0
    have haU : a ∈ U := inverseRiemannMap_mem hbij hzeroD
    let line : ℕ → ℝ → ℂ := fun k t ↦
      (1 - t) • a + t • g (qdom (sigma k))
    have hlineU (k : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        line k t ∈ U := by
      exact hUc haU (inverseRiemannMap_mem hbij (hqdom (sigma k)))
        (sub_nonneg.mpr ht.2) ht.1 (by ring)
    have htauExists : ∀ k : ℕ, ∃ t ∈ Icc (0 : ℝ) 1,
        phi (line k t) ∈ sphere zeta (rho (sigma k)) := by
      intro k
      let F : ℝ → ℝ := fun t ↦ dist (phi (line k t)) zeta
      have hlineCont : Continuous (line k) := by
        dsimp [line]
        fun_prop
      have hFcont : ContinuousOn F (Icc (0 : ℝ) 1) := by
        have hc : ContinuousOn (phi ∘ line k) (Icc (0 : ℝ) 1) :=
          hphi.continuousOn.comp hlineCont.continuousOn
            (fun t ht ↦ hlineU k t ht)
        intro t ht
        exact (hc t ht).dist continuousWithinAt_const
      have hFa : F 0 = 1 := by
        dsimp [F]
        rw [show line k 0 = a by simp [line]]
        rw [show phi a = 0 by
          exact riemannMap_inverseRiemannMap hbij hzeroD]
        rw [dist_zero_left, norm_eq_one_of_mem_unitSphere hzeta]
      have hFb : F 1 = dist (qdom (sigma k)) zeta := by
        dsimp [F]
        rw [show line k 1 = g (qdom (sigma k)) by simp [line]]
        exact congrArg (fun z ↦ dist z zeta)
          (riemannMap_inverseRiemannMap hbij (hqdom (sigma k)))
      have hrange := intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num) hFcont
      have hrhomem : rho (sigma k) ∈ Icc (F 1) (F 0) := by
        rw [hFa, hFb]
        exact ⟨(hqclose (sigma k)).le,
          (hrhoOne (sigma k)).le⟩
      obtain ⟨t, ht, hFt⟩ := hrange hrhomem
      refine ⟨t, ht, ?_⟩
      rw [mem_sphere]
      exact hFt
    choose tau htau htausphere using htauExists
    let Y : ℕ → ℂ := fun k ↦ line k (tau k)
    have hYU (k : ℕ) : Y k ∈ U := hlineU k (tau k) (htau k)
    have hYimage (k : ℕ) : Y k ∈
        g '' (ball (0 : ℂ) 1 ∩ sphere zeta (rho (sigma k))) := by
      refine ⟨phi (Y k), ⟨hbij.mapsTo (hYU k), htausphere k⟩, ?_⟩
      exact inverseRiemannMap_riemannMap hbij (hYU k)
    have hvImage (k : ℕ) : g (v (sigma k)) ∈
        g '' (ball (0 : ℂ) 1 ∩ sphere zeta (rho (sigma k))) :=
      ⟨v (sigma k), hv (sigma k), rfl⟩
    have himageBound (k : ℕ) : IsBounded
        (g '' (ball (0 : ℂ) 1 ∩ sphere zeta (rho (sigma k)))) := by
      apply hUb.subset
      rintro _ ⟨s, hs, rfl⟩
      exact inverseRiemannMap_mem hbij hs.1
    have hYdist (k : ℕ) :
        dist (Y k) (g (v (sigma k))) ≤ eta (sigma k) := by
      exact (Metric.dist_le_diam_of_mem (himageBound k)
        (hYimage k) (hvImage k)).trans (hdiam (sigma k))
    obtain ⟨t, ht, psi, hpsiMono, hpsiLim⟩ :=
      isCompact_Icc.tendsto_subseq htau
    have hpsiTop : Tendsto psi atTop atTop := hpsiMono.tendsto_atTop
    have hsigpsiTop : Tendsto (sigma ∘ psi) atTop atTop :=
      (hsigmaMono.comp hpsiMono).tendsto_atTop
    have hqsub : Tendsto (fun k ↦ g (qdom (sigma (psi k))))
        atTop (nhds q) := hqlim.comp hpsiTop
    let qstar : ℂ := (1 - t) • a + t • q
    have hYline : Tendsto (fun k ↦ Y (psi k)) atTop (nhds qstar) := by
      have hleft : Tendsto (fun k ↦ (1 - tau (psi k) : ℝ))
          atTop (nhds (1 - t)) := tendsto_const_nhds.sub hpsiLim
      have hleft' : Tendsto (fun k ↦ (1 - tau (psi k)) • a)
          atTop (nhds ((1 - t) • a)) := hleft.smul_const a
      have hright : Tendsto
          (fun k ↦ tau (psi k) • g (qdom (sigma (psi k))))
          atTop (nhds (t • q)) := hpsiLim.smul hqsub
      simpa only [Y, line, qstar] using hleft'.add hright
    have hpsub : Tendsto (fun k ↦ g (v (sigma (psi k))))
        atTop (nhds p) := hplim.comp hpsiTop
    have hetaSub : Tendsto (fun k ↦ eta (sigma (psi k)))
        atTop (nhds 0) := by
      exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hsigpsiTop
    have hdistZero : Tendsto
        (fun k ↦ dist (Y (psi k)) (g (v (sigma (psi k)))))
        atTop (nhds 0) := by
      exact squeeze_zero (fun _ ↦ dist_nonneg)
        (fun k ↦ hYdist (psi k)) hetaSub
    have hYp : Tendsto (fun k ↦ Y (psi k)) atTop (nhds p) := by
      apply hpsub.congr_dist
      simpa only [dist_comm] using hdistZero
    have hqstarP : qstar = p := tendsto_nhds_unique hYline hYp
    have hqstarNe : qstar ≠ p := by
      rcases eq_or_lt_of_le ht.2 with htOne | htOne
      · subst t
        simpa only [qstar, sub_self, zero_smul, one_smul, zero_add] using hqp
      · intro heq
        have haInt : a ∈ interior U := by
          rwa [hUo.interior_eq]
        have hstarInt : qstar ∈ interior U := by
          exact hUc.combo_interior_closure_mem_interior haInt hqU
            (sub_pos.mpr htOne) ht.1 (by ring)
        apply hpNot
        rw [← heq]
        exact interior_subset hstarInt
    exact hqstarNe hqstarP
  rcases eq_or_ne x p with hxp | hxp
  · apply himpossible y hyU w hw hwd hylim
    intro hyp
    apply hxyne
    exact hxp.trans hyp.symm
  · exact himpossible x hxU z hz hzd hxlim hxp

/-- The canonical inclusion of the open unit disc into the closed unit disc. -/
def openDiscInClosedDisc :
    ball (0 : ℂ) 1 → closedBall (0 : ℂ) 1 :=
  Set.inclusion ball_subset_closedBall

private theorem isDenseInducing_openDiscInClosedDisc :
    IsDenseInducing openDiscInClosedDisc := by
  refine ⟨(Topology.IsEmbedding.inclusion ball_subset_closedBall).isInducing, ?_⟩
  change DenseRange (Set.inclusion ball_subset_closedBall)
  rw [denseRange_inclusion_iff]
  rw [closure_ball (0 : ℂ) one_ne_zero]

private theorem exists_inverseRiemannMap_limit_closedDisc
    {U : Set ℂ} {phi : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hUb : IsBounded U)
    (hphi : DifferentiableOn ℂ phi U)
    (hbij : BijOn phi U (ball 0 1))
    (b : closedBall (0 : ℂ) 1) :
    ∃ c ∈ closure U, Tendsto
      (fun z : ball (0 : ℂ) 1 ↦ inverseRiemannMap U phi z)
      (comap openDiscInClosedDisc (nhds b)) (nhds c) := by
  let g := inverseRiemannMap U phi
  let f : ball (0 : ℂ) 1 → ℂ := fun z ↦ g z
  let i := openDiscInClosedDisc
  have hdi : IsDenseInducing i := isDenseInducing_openDiscInClosedDisc
  by_cases hb : (b : ℂ) ∈ ball (0 : ℂ) 1
  · let a : ball (0 : ℂ) 1 := ⟨b, hb⟩
    have hfAt : ContinuousAt f a := by
      have hgWithin :=
        (differentiableOn_inverseRiemannMap hUo hphi hbij) b hb
      have hgAt : ContinuousAt g b :=
        (hgWithin.differentiableAt (isOpen_ball.mem_nhds hb)).continuousAt
      exact hgAt.comp_of_eq continuousAt_subtype_val rfl
    have hlim : Tendsto f (comap i (nhds b)) (nhds (f a)) := by
      have hi : i a = b := rfl
      rw [← hi, ← hdi.nhds_eq_comap]
      exact hfAt.tendsto
    refine ⟨f a, subset_closure ?_, hlim⟩
    exact inverseRiemannMap_mem hbij a.2
  · have hbSphere : (b : ℂ) ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere, dist_zero_right]
      apply le_antisymm
      · simpa only [mem_closedBall, dist_zero_right] using b.2
      · exact not_lt.mp (by simpa only [mem_ball, dist_zero_right] using hb)
    let l : Filter (ball (0 : ℂ) 1) := comap i (nhds b)
    let hl : NeBot l := hdi.comap_nhds_neBot b
    have hcauchy : Cauchy (map f l) := by
      rw [Metric.cauchy_iff]
      refine ⟨hl.map f, ?_⟩
      intro epsilon hepsilon
      obtain ⟨delta, hdelta, hclose⟩ :=
        inverseRiemannMap_boundary_cauchy hUo hUc hUb hphi hbij
          hbSphere epsilon hepsilon
      let s : Set (ball (0 : ℂ) 1) :=
        {z | dist (z : ℂ) (b : ℂ) < delta}
      have hs : s ∈ l := by
        exact preimage_mem_comap (ball_mem_nhds b hdelta)
      refine ⟨f '' s, image_mem_map hs, ?_⟩
      rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
      exact hclose z z.2 hz w w.2 hw
    obtain ⟨c, hc⟩ := CompleteSpace.complete hcauchy
    have hcU : c ∈ closure U := by
      rw [mem_closure_iff_nhds]
      intro V hV
      have hVmap : V ∈ map f l := hc hV
      have hUmap : U ∈ map f l := by
        change f ⁻¹' U ∈ l
        exact univ_mem' fun z ↦ inverseRiemannMap_mem hbij z.2
      exact hcauchy.1.nonempty_of_mem (inter_mem hVmap hUmap)
    exact ⟨c, hcU, hc⟩

/-- The inverse Riemann map has a continuous extension from the closed unit
disc into the closure of the convex domain. -/
theorem exists_continuous_extension_inverseRiemannMap
    {U : Set ℂ} {phi : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hUb : IsBounded U)
    (hphi : DifferentiableOn ℂ phi U)
    (hbij : BijOn phi U (ball 0 1)) :
    ∃ F : closedBall (0 : ℂ) 1 → closure U,
      Continuous F ∧
      ∀ z : ball (0 : ℂ) 1,
        F (openDiscInClosedDisc z) =
          ⟨inverseRiemannMap U phi z,
            subset_closure (inverseRiemannMap_mem hbij z.2)⟩ := by
  let i := openDiscInClosedDisc
  let f : ball (0 : ℂ) 1 → ℂ := fun z ↦ inverseRiemannMap U phi z
  let di : IsDenseInducing i := isDenseInducing_openDiscInClosedDisc
  have hlim : ∀ b : closedBall (0 : ℂ) 1, ∃ c,
      Tendsto f (comap i (nhds b)) (nhds c) := by
    intro b
    obtain ⟨c, _, hc⟩ :=
      exists_inverseRiemannMap_limit_closedDisc hUo hUc hUb hphi hbij b
    exact ⟨c, hc⟩
  let ext : closedBall (0 : ℂ) 1 → ℂ := di.extend f
  have hextCont : Continuous ext := di.continuous_extend hlim
  have hextClosure (b : closedBall (0 : ℂ) 1) : ext b ∈ closure U := by
    obtain ⟨c, hcU, hc⟩ :=
      exists_inverseRiemannMap_limit_closedDisc hUo hUc hUb hphi hbij b
    have heq : ext b = c := di.extend_eq_of_tendsto hc
    rwa [heq]
  let F : closedBall (0 : ℂ) 1 → closure U :=
    fun b ↦ ⟨ext b, hextClosure b⟩
  refine ⟨F, hextCont.subtype_mk _, ?_⟩
  intro z
  apply Subtype.ext
  exact di.extend_eq' hlim z

/-- Any continuous extension of the inverse Riemann map takes the unit circle
to the frontier of the convex domain. -/
theorem continuous_extension_inverseRiemannMap_maps_sphere_to_frontier
    {U : Set ℂ} {phi : ℂ → ℂ}
    (hUo : IsOpen U)
    (hphi : DifferentiableOn ℂ phi U)
    (hbij : BijOn phi U (ball 0 1))
    {F : closedBall (0 : ℂ) 1 → closure U}
    (hFcont : Continuous F)
    (hFext : ∀ z : ball (0 : ℂ) 1,
      F (openDiscInClosedDisc z) =
        ⟨inverseRiemannMap U phi z,
          subset_closure (inverseRiemannMap_mem hbij z.2)⟩)
    {b : closedBall (0 : ℂ) 1}
    (hb : (b : ℂ) ∈ sphere (0 : ℂ) 1) :
    (F b : ℂ) ∈ frontier U := by
  rw [frontier, hUo.interior_eq]
  refine ⟨(F b).2, ?_⟩
  intro hFbU
  let rho : ℕ → ℝ := fun n ↦ 1 / (n + 2 : ℝ)
  have hrhoPos (n : ℕ) : 0 < rho n := by
    dsimp [rho]
    positivity
  have hrhoOne (n : ℕ) : rho n < 1 := by
    dsimp [rho]
    rw [div_lt_one (by positivity : (0 : ℝ) < n + 2)]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hrhoZero : Tendsto rho atTop (nhds 0) := by
    exact squeeze_zero (fun n ↦ (hrhoPos n).le) (fun n ↦ by
      dsimp [rho]
      gcongr
      norm_num) tendsto_one_div_add_atTop_nhds_zero_nat
  let z : ℕ → ball (0 : ℂ) 1 := fun n ↦
    ⟨inwardCrosscutPoint b (rho n),
      (inwardCrosscutPoint_mem hb (hrhoPos n) (hrhoOne n)).1⟩
  let zbar : ℕ → closedBall (0 : ℂ) 1 := fun n ↦
    openDiscInClosedDisc (z n)
  have hzlim : Tendsto zbar atTop (nhds b) := by
    rw [tendsto_subtype_rng]
    exact tendsto_inwardCrosscutPoint hrhoZero
  have hFlim : Tendsto (fun n ↦ (F (zbar n) : ℂ)) atTop
      (nhds (F b : ℂ)) := by
    exact (continuous_subtype_val.tendsto (F b)).comp
      ((hFcont.tendsto b).comp hzlim)
  have hphiAt : ContinuousAt phi (F b : ℂ) :=
    ((hphi (F b) hFbU).differentiableAt
      (hUo.mem_nhds hFbU)).continuousAt
  have hphiLim : Tendsto (fun n ↦ phi (F (zbar n) : ℂ)) atTop
      (nhds (phi (F b : ℂ))) := hphiAt.tendsto.comp hFlim
  have hphiEq : (fun n ↦ phi (F (zbar n) : ℂ)) =
      fun n ↦ (z n : ℂ) := by
    funext n
    rw [hFext]
    exact riemannMap_inverseRiemannMap hbij (z n).2
  rw [hphiEq] at hphiLim
  have hzlim' : Tendsto (fun n ↦ (z n : ℂ)) atTop (nhds (b : ℂ)) :=
    tendsto_inwardCrosscutPoint hrhoZero
  have hphiB : phi (F b : ℂ) = (b : ℂ) :=
    tendsto_nhds_unique hphiLim hzlim'
  have hphiMem : phi (F b : ℂ) ∈ ball (0 : ℂ) 1 :=
    hbij.mapsTo hFbU
  rw [hphiB, mem_ball, dist_zero_right,
    norm_eq_one_of_mem_unitSphere hb] at hphiMem
  exact (lt_irrefl 1) hphiMem

/-- Any continuous extension of the inverse Riemann map is onto the closure of
the domain. -/
theorem continuous_extension_inverseRiemannMap_surjective
    {U : Set ℂ} {phi : ℂ → ℂ}
    (hbij : BijOn phi U (ball 0 1))
    {F : closedBall (0 : ℂ) 1 → closure U}
    (hFcont : Continuous F)
    (hFext : ∀ z : ball (0 : ℂ) 1,
      F (openDiscInClosedDisc z) =
        ⟨inverseRiemannMap U phi z,
          subset_closure (inverseRiemannMap_mem hbij z.2)⟩) :
    Surjective F := by
  intro y
  obtain ⟨x, hxU, hxlim⟩ := mem_closure_iff_seq_limit.mp y.2
  let z : ℕ → ball (0 : ℂ) 1 := fun n ↦
    ⟨phi (x n), hbij.mapsTo (hxU n)⟩
  let zbar : ℕ → closedBall (0 : ℂ) 1 := fun n ↦
    openDiscInClosedDisc (z n)
  obtain ⟨b, sigma, hsigmaMono, hsigmaLim⟩ :=
    CompactSpace.tendsto_subseq zbar
  have hFsub : Tendsto (fun k ↦ F (zbar (sigma k))) atTop (nhds (F b)) :=
    (hFcont.tendsto b).comp hsigmaLim
  let xbar : ℕ → closure U := fun n ↦
    ⟨x n, subset_closure (hxU n)⟩
  have hxbarLim : Tendsto xbar atTop (nhds y) := by
    rw [tendsto_subtype_rng]
    exact hxlim
  have hsigmaTop : Tendsto sigma atTop atTop := hsigmaMono.tendsto_atTop
  have hxbarSub : Tendsto (fun k ↦ xbar (sigma k)) atTop (nhds y) :=
    hxbarLim.comp hsigmaTop
  have hF_eq_xbar : (fun k ↦ F (zbar (sigma k))) =
      fun k ↦ xbar (sigma k) := by
    funext k
    rw [hFext]
    apply Subtype.ext
    exact inverseRiemannMap_riemannMap hbij (hxU (sigma k))
  rw [hF_eq_xbar] at hFsub
  exact ⟨b, tendsto_nhds_unique hFsub hxbarSub⟩

/-- Every fiber of a continuous inverse-Riemann-map extension is
preconnected.  The proof realizes the fiber as the decreasing intersection of
closures of inverse images of convex metric caps. -/
theorem continuous_extension_inverseRiemannMap_fiber_preconnected
    {U : Set ℂ} {phi : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : Convex ℝ U)
    (hphi : DifferentiableOn ℂ phi U)
    (hbij : BijOn phi U (ball 0 1))
    {F : closedBall (0 : ℂ) 1 → closure U}
    (hFcont : Continuous F)
    (hFext : ∀ z : ball (0 : ℂ) 1,
      F (openDiscInClosedDisc z) =
        ⟨inverseRiemannMap U phi z,
          subset_closure (inverseRiemannMap_mem hbij z.2)⟩)
    (p : closure U) :
    IsPreconnected (F ⁻¹' {p}) := by
  let H : ball (0 : ℂ) 1 ≃ₜ U :=
    inverseRiemannMapHomeomorph hUo hphi hbij
  let i := openDiscInClosedDisc
  have hdi : IsDenseInducing i := isDenseInducing_openDiscInClosedDisc
  let radius : ℕ → ℝ := fun n ↦ 1 / (n + 1 : ℝ)
  have hradiusPos (n : ℕ) : 0 < radius n := by
    dsimp [radius]
    positivity
  have hradiusZero : Tendsto radius atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let cap : ℕ → Set U := fun n ↦
    {x | dist (x : ℂ) (p : ℂ) < radius n}
  let S : ℕ → Set (ball (0 : ℂ) 1) := fun n ↦ H ⁻¹' cap n
  let C : ℕ → Set (closedBall (0 : ℂ) 1) := fun n ↦
    closure (i '' S n)
  have hcapImage (n : ℕ) :
      ((↑) : U → ℂ) '' cap n = U ∩ ball (p : ℂ) (radius n) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hzU, hzball⟩
      exact ⟨⟨z, hzU⟩, hzball, rfl⟩
  have hcapPreconnected (n : ℕ) : IsPreconnected (cap n) := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [hcapImage]
    exact (hUc.inter (convex_ball (p : ℂ) (radius n))).isPreconnected
  have hSPreconnected (n : ℕ) : IsPreconnected (S n) := by
    exact H.isPreconnected_preimage.mpr (hcapPreconnected n)
  have hCPreconnected (n : ℕ) : IsPreconnected (C n) := by
    exact ((hSPreconnected n).image i
      hdi.continuous.continuousOn).closure
  have hCCompact (n : ℕ) : IsCompact (C n) := by
    exact isClosed_closure.isCompact
  have hradiusAnti : Antitone radius := by
    intro a b hab
    dsimp [radius]
    gcongr
  have hcapAnti : Antitone cap := by
    intro a b hab x hx
    exact hx.trans_le (hradiusAnti hab)
  have hSAnti : Antitone S := by
    intro a b hab
    exact preimage_mono (hcapAnti hab)
  have hCAnti : Antitone C := by
    intro a b hab
    exact closure_mono (image_mono (hSAnti hab))
  have hbaseSubset (n : ℕ) : i '' S n ⊆
      F ⁻¹' closedBall p (radius n) := by
    rintro _ ⟨z, hzS, rfl⟩
    change dist (F (i z)) p ≤ radius n
    rw [hFext]
    change dist (inverseRiemannMap U phi z) (p : ℂ) ≤ radius n
    exact hzS.le
  have hCClosedBall (n : ℕ) : C n ⊆
      F ⁻¹' closedBall p (radius n) := by
    exact closure_minimal (hbaseSubset n)
      (isClosed_closedBall.preimage hFcont)
  have hfiberEq : F ⁻¹' {p} = ⋂ n, C n := by
    ext z
    constructor
    · intro hzFiber
      have hFz : F z = p := hzFiber
      apply mem_iInter.mpr
      intro n
      rw [Metric.mem_closure_iff]
      intro epsilon hepsilon
      let O : Set (closedBall (0 : ℂ) 1) :=
        ball z epsilon ∩ F ⁻¹' ball p (radius n)
      have hOopen : IsOpen O :=
        isOpen_ball.inter (isOpen_ball.preimage hFcont)
      have hzO : z ∈ O := by
        refine ⟨mem_ball_self hepsilon, ?_⟩
        change dist (F z) p < radius n
        rw [hFz, dist_self]
        exact hradiusPos n
      obtain ⟨w, hwO, hwRange⟩ :=
        mem_closure_iff_nhds.mp (hdi.dense z) O
          (hOopen.mem_nhds hzO)
      obtain ⟨a, rfl⟩ := hwRange
      refine ⟨i a, ?_, ?_⟩
      · refine ⟨a, ?_, rfl⟩
        change dist (inverseRiemannMap U phi a) (p : ℂ) < radius n
        have hdistF : dist (F (i a)) p < radius n := by
          have hmem : F (i a) ∈ ball p (radius n) := hwO.2
          simpa only [mem_ball] using hmem
        rw [hFext] at hdistF
        exact hdistF
      · simpa only [mem_ball, dist_comm] using hwO.1
    · intro hzAll
      have hdist (n : ℕ) : dist (F z) p ≤ radius n := by
        exact hCClosedBall n ((mem_iInter.mp hzAll) n)
      have hdistZero : dist (F z) p ≤ 0 :=
        ge_of_tendsto' hradiusZero hdist
      have hEq : F z = p :=
        dist_eq_zero.mp (le_antisymm hdistZero dist_nonneg)
      exact hEq
  rw [hfiberEq]
  exact isPreconnected_iInter_of_antitone_compact C
    hCCompact hCPreconnected hCAnti

/-- A continuous inverse-Riemann-map extension for a convex domain is
injective.  Connectedness of boundary fibers turns a hypothetical
non-singleton fiber into a boundary arc, while Jensen boundary uniqueness
rules out that arc. -/
theorem continuous_extension_inverseRiemannMap_injective
    {U : Set ℂ} {phi : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : Convex ℝ U)
    (hphi : DifferentiableOn ℂ phi U)
    (hbij : BijOn phi U (ball 0 1))
    {F : closedBall (0 : ℂ) 1 → closure U}
    (hFcont : Continuous F)
    (hFext : ∀ z : ball (0 : ℂ) 1,
      F (openDiscInClosedDisc z) =
        ⟨inverseRiemannMap U phi z,
          subset_closure (inverseRiemannMap_mem hbij z.2)⟩) :
    Injective F := by
  classical
  intro x y hFxy
  have hsphere_of_not_ball (z : closedBall (0 : ℂ) 1)
      (hz : (z : ℂ) ∉ ball (0 : ℂ) 1) :
      (z : ℂ) ∈ sphere (0 : ℂ) 1 := by
    rw [mem_sphere, dist_zero_right]
    apply le_antisymm
    · simpa only [mem_closedBall, dist_zero_right] using z.2
    · exact not_lt.mp (by simpa only [mem_ball, dist_zero_right] using hz)
  have hinterior_value {z : closedBall (0 : ℂ) 1}
      (hz : (z : ℂ) ∈ ball (0 : ℂ) 1) :
      (F z : ℂ) ∈ U := by
    let zo : ball (0 : ℂ) 1 := ⟨z, hz⟩
    have hzo : openDiscInClosedDisc zo = z := by rfl
    rw [← hzo, hFext]
    exact inverseRiemannMap_mem hbij zo.2
  by_cases hx : (x : ℂ) ∈ ball (0 : ℂ) 1
  · have hy : (y : ℂ) ∈ ball (0 : ℂ) 1 := by
      by_contra hy
      have hySphere := hsphere_of_not_ball y hy
      have hyFront :=
        continuous_extension_inverseRiemannMap_maps_sphere_to_frontier
          hUo hphi hbij hFcont hFext hySphere
      rw [frontier, hUo.interior_eq] at hyFront
      exact hyFront.2 (hFxy ▸ hinterior_value hx)
    let xo : ball (0 : ℂ) 1 := ⟨x, hx⟩
    let yo : ball (0 : ℂ) 1 := ⟨y, hy⟩
    have hxo : openDiscInClosedDisc xo = x := by rfl
    have hyo : openDiscInClosedDisc yo = y := by rfl
    apply Subtype.ext
    apply injOn_inverseRiemannMap hbij xo.2 yo.2
    calc
      inverseRiemannMap U phi xo = (F x : ℂ) := by
        rw [← hxo, hFext]
      _ = (F y : ℂ) := congrArg Subtype.val hFxy
      _ = inverseRiemannMap U phi yo := by
        rw [← hyo, hFext]
  · have hy : (y : ℂ) ∉ ball (0 : ℂ) 1 := by
      intro hy
      have hxSphere := hsphere_of_not_ball x hx
      have hxFront :=
        continuous_extension_inverseRiemannMap_maps_sphere_to_frontier
          hUo hphi hbij hFcont hFext hxSphere
      rw [frontier, hUo.interior_eq] at hxFront
      exact hxFront.2 (hFxy.symm ▸ hinterior_value hy)
    have hxSphere := hsphere_of_not_ball x hx
    have hySphere := hsphere_of_not_ball y hy
    by_contra hxy
    let p : closure U := F x
    have hpFront : (p : ℂ) ∈ frontier U :=
      continuous_extension_inverseRiemannMap_maps_sphere_to_frontier
        hUo hphi hbij hFcont hFext hxSphere
    have hpNotU : (p : ℂ) ∉ U := by
      rw [frontier, hUo.interior_eq] at hpFront
      exact hpFront.2
    let T : Set ℂ := ((↑) : closedBall (0 : ℂ) 1 → ℂ) ''
      (F ⁻¹' {p})
    have hTpre : IsPreconnected T := by
      exact (continuous_extension_inverseRiemannMap_fiber_preconnected
        hUo hUc hphi hbij hFcont hFext p).image _
          continuous_subtype_val.continuousOn
    have hTsphere : T ⊆ sphere (0 : ℂ) 1 := by
      rintro z ⟨b, hb, rfl⟩
      apply hsphere_of_not_ball
      intro hbBall
      have hbU : (F b : ℂ) ∈ U := hinterior_value hbBall
      have hFbp : F b = p := hb
      exact hpNotU (hFbp ▸ hbU)
    have hxT : (x : ℂ) ∈ T := by
      exact ⟨x, rfl, rfl⟩
    have hyT : (y : ℂ) ∈ T := by
      exact ⟨y, hFxy.symm, rfl⟩
    have hxyVal : (x : ℂ) ≠ (y : ℂ) := by
      intro h
      exact hxy (Subtype.ext h)
    let f : ℂ → ℂ := fun z ↦
      if hz : z ∈ closedBall (0 : ℂ) 1 then
        (F ⟨z, hz⟩ : ℂ) - (p : ℂ)
      else 0
    have hfcont : ContinuousOn f (closedBall (0 : ℂ) 1) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hc : Continuous (fun z : closedBall (0 : ℂ) 1 ↦
          (F z : ℂ) - (p : ℂ)) :=
        (continuous_subtype_val.comp hFcont).sub continuous_const
      convert hc using 1
      funext z
      simp only [Set.domRestrict_apply, f, dif_pos z.2]
    have hfEq (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
        f z = inverseRiemannMap U phi z - (p : ℂ) := by
      have hzClosed : z ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hz
      let zo : ball (0 : ℂ) 1 := ⟨z, hz⟩
      have hzo : (⟨z, hzClosed⟩ : closedBall (0 : ℂ) 1) =
          openDiscInClosedDisc zo := by rfl
      dsimp [f]
      rw [dif_pos hzClosed]
      rw [hzo, hFext]
    have hfdiff : DifferentiableOn ℂ f (ball 0 1) := by
      exact ((differentiableOn_inverseRiemannMap hUo hphi hbij).sub
        (differentiable_const (p : ℂ)).differentiableOn).congr hfEq
    have hfne : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0 := by
      intro z hz hfz
      have heq : inverseRiemannMap U phi z = (p : ℂ) := by
        rw [hfEq z hz, sub_eq_zero] at hfz
        exact hfz
      exact hpNotU (heq ▸ inverseRiemannMap_mem hbij hz)
    have hfzeroT : ∀ z ∈ T, f z = 0 := by
      rintro z ⟨b, hb, rfl⟩
      have hbp : F b = p := hb
      dsimp [f]
      rw [dif_pos b.2, hbp, sub_self]
    by_cases hTproper : T ≠ sphere (0 : ℂ) 1
    · obtain ⟨a, b, hab, hwidth, harc⟩ :=
        exists_circleMap_interval_subset_of_preconnected
          hTpre hTsphere hxT hyT hxyVal hTproper
      exact (not_boundary_interval_zero_of_differentiableOn_unitDisc
        hfdiff hfcont hfne hab hwidth) fun theta htheta ↦
          hfzeroT _ (harc theta htheta)
    · have hTsphereEq : T = sphere (0 : ℂ) 1 := not_ne_iff.mp hTproper
      exact (not_boundary_arc_zero_of_differentiableOn_unitDisc
        hfdiff hfcont hfne Real.pi_pos (by linarith [Real.pi_pos]))
          fun theta _ ↦ hfzeroT _ (by
            rw [hTsphereEq]
            simpa only [abs_one] using
              circleMap_mem_sphere' (0 : ℂ) 1 theta)

/-- Carathéodory's theorem for a bounded convex domain, in the direction
from the closed unit disc to the closure of the domain.  The homeomorphism
agrees with the inverse Riemann map on the open disc. -/
theorem exists_homeomorph_closedDisc_closure_extends_inverseRiemannMap
    {U : Set ℂ} {phi : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hUb : IsBounded U)
    (hphi : DifferentiableOn ℂ phi U)
    (hbij : BijOn phi U (ball 0 1)) :
    ∃ H : closedBall (0 : ℂ) 1 ≃ₜ closure U,
      ∀ z : ball (0 : ℂ) 1,
        H (openDiscInClosedDisc z) =
          ⟨inverseRiemannMap U phi z,
            subset_closure (inverseRiemannMap_mem hbij z.2)⟩ := by
  obtain ⟨F, hFcont, hFext⟩ :=
    exists_continuous_extension_inverseRiemannMap hUo hUc hUb hphi hbij
  have hFinj : Injective F :=
    continuous_extension_inverseRiemannMap_injective
      hUo hUc hphi hbij hFcont hFext
  have hFsurj : Surjective F :=
    continuous_extension_inverseRiemannMap_surjective hbij hFcont hFext
  have hFhome : IsHomeomorph F :=
    isHomeomorph_iff_continuous_bijective.mpr
      ⟨hFcont, hFinj, hFsurj⟩
  let H : closedBall (0 : ℂ) 1 ≃ₜ closure U :=
    hFhome.homeomorph F
  refine ⟨H, ?_⟩
  intro z
  change F (openDiscInClosedDisc z) = _
  exact hFext z

/-- Carathéodory's theorem for a bounded convex domain, in the direction
used for boundary values: the Riemann map extends to a homeomorphism from the
closure of the domain onto the closed unit disc. -/
theorem exists_homeomorph_closure_closedDisc_extends_riemannMap
    {U : Set ℂ} {phi : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hUb : IsBounded U)
    (hphi : DifferentiableOn ℂ phi U)
    (hbij : BijOn phi U (ball 0 1)) :
    ∃ Phi : closure U ≃ₜ closedBall (0 : ℂ) 1,
      ∀ z : U,
        Phi ⟨z, subset_closure z.2⟩ =
          ⟨phi z, ball_subset_closedBall (hbij.mapsTo z.2)⟩ := by
  obtain ⟨H, hHext⟩ :=
    exists_homeomorph_closedDisc_closure_extends_inverseRiemannMap
      hUo hUc hUb hphi hbij
  refine ⟨H.symm, ?_⟩
  intro z
  let w : ball (0 : ℂ) 1 := ⟨phi z, hbij.mapsTo z.2⟩
  have hinv : inverseRiemannMap U phi w = z :=
    inverseRiemannMap_riemannMap hbij z.2
  have hHz : H (openDiscInClosedDisc w) =
      ⟨z, subset_closure z.2⟩ := by
    rw [hHext]
    apply Subtype.ext
    exact hinv
  apply H.injective
  rw [H.apply_symm_apply]
  symm
  convert hHz using 1
  apply Subtype.ext
  rfl

/-- A Carathéodory extension of a Riemann map sends the frontier of the
domain to the unit circle. -/
theorem homeomorph_closure_closedDisc_maps_frontier_to_sphere
    {U : Set ℂ} {phi : ℂ → ℂ}
    (hUo : IsOpen U) (hbij : BijOn phi U (ball 0 1))
    (Phi : closure U ≃ₜ closedBall (0 : ℂ) 1)
    (hPhiExt : ∀ z : U,
      Phi ⟨z, subset_closure z.2⟩ =
        ⟨phi z, ball_subset_closedBall (hbij.mapsTo z.2)⟩)
    {z : closure U} (hz : (z : ℂ) ∈ frontier U) :
    (Phi z : ℂ) ∈ sphere (0 : ℂ) 1 := by
  have hnotBall : (Phi z : ℂ) ∉ ball (0 : ℂ) 1 := by
    intro hball
    let w : ball (0 : ℂ) 1 := ⟨Phi z, hball⟩
    let u : U := ⟨inverseRiemannMap U phi w,
      inverseRiemannMap_mem hbij w.2⟩
    have hphiU : phi u = (Phi z : ℂ) :=
      riemannMap_inverseRiemannMap hbij w.2
    have hPhiEq : Phi ⟨u, subset_closure u.2⟩ = Phi z := by
      rw [hPhiExt]
      apply Subtype.ext
      exact hphiU
    have huz : (⟨u, subset_closure u.2⟩ : closure U) = z :=
      Phi.injective hPhiEq
    rw [frontier, hUo.interior_eq] at hz
    exact hz.2 (huz ▸ u.2)
  rw [mem_sphere, dist_zero_right]
  apply le_antisymm
  · simpa only [mem_closedBall, dist_zero_right] using (Phi z).2
  · exact not_lt.mp (by
      simpa only [mem_ball, dist_zero_right] using hnotBall)

end

end DiskRigidity.Complex
