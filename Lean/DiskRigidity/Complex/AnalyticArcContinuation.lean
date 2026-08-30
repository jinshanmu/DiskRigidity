/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.BiholomorphicBasics
public import DiskRigidity.Complex.MoreraGlue
public import DiskRigidity.Complex.RealAnalyticComplexification
public import DiskRigidity.Complex.RelativelyOpenAnalyticArc
public import DiskRigidity.Operator.ConvexBoundaryAEEq
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Analytic continuation across a regular analytic convex-boundary arc

We complexify and locally invert the real-analytic boundary parametrization,
extend the boundary-zero function by zero outside the convex body, and apply
Morera's theorem across the flattened real diameter.  This is the local
analytic-continuation argument used in the manuscript.
-/

noncomputable section

open Filter Function MeasureTheory Metric Set Topology
open scoped Real

namespace DiskRigidity.Complex

@[expose] public section

namespace NumericalRangeArc

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Faithful local flattening/Morera continuation across a regular injective
real-analytic arc in the frontier of a compact convex body. -/
theorem eqOn_zero_of_diffContOnCl_of_regularAnalytic_frontier_arc
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    {gamma : ℝ → ℂ} {t r : ℝ} (hr : 0 < r)
    (hana : AnalyticOnNhd ℝ gamma (ball t r))
    (hinj : Set.InjOn gamma (ball t r))
    (hfront : ∀ u ∈ ball t r, gamma u ∈ frontier K)
    (hregular : deriv gamma t ≠ 0)
    {h : ℂ → ℂ} (hh : DiffContOnCl ℂ h (interior K))
    (hzero : ∀ u ∈ ball t r, h (gamma u) = 0) :
    EqOn h 0 (interior K) := by
  classical
  have hKclosed : IsClosed K := hcompact.isClosed
  have hKint : (interior K).Nonempty := ⟨c, hc⟩
  have hclosure : closure (interior K) = K := by
    calc
      closure (interior K) = closure K :=
        hconv.closure_interior_eq_closure_of_nonempty_interior hKint
      _ = K := hKclosed.closure_eq
  have hhK : ContinuousOn h K := by
    rw [← hclosure]
    exact hh.continuousOn
  have hgammaAt : AnalyticAt ℝ gamma t := hana t (mem_ball_self hr)
  obtain ⟨G, hGana, hGagree⟩ :=
    exists_complexification_of_analyticAt hgammaAt
  have hGrestrict : HasDerivAt (fun u : ℝ ↦ G (u : ℂ))
      (deriv G (t : ℂ)) t :=
    hGana.hasStrictDerivAt.hasDerivAt.comp_ofReal
  have hGderiv : deriv G (t : ℂ) = deriv gamma t := by
    have hsame : HasDerivAt gamma (deriv G (t : ℂ)) t :=
      hGrestrict.congr_of_eventuallyEq (Filter.EventuallyEq.symm hGagree)
    exact hsame.deriv.symm
  have hGregular : deriv G (t : ℂ) ≠ 0 := by
    rw [hGderiv]
    exact hregular
  obtain ⟨V, hV, hGinj⟩ :=
    (exists_injOn_nhds_iff_deriv_ne_zero hGana).mpr hGregular
  have hVreal : ∀ᶠ u : ℝ in nhds t, (u : ℂ) ∈ V :=
    Complex.continuous_ofReal.continuousAt hV
  have hrealLocal : ∀ᶠ u : ℝ in nhds t,
      (u : ℂ) ∈ V ∧ G (u : ℂ) = gamma u ∧ u ∈ ball t r :=
    hVreal.and <| hGagree.and <| isOpen_ball.mem_nhds (mem_ball_self hr)
  obtain ⟨rho, hrho, hrhoLocal⟩ := Metric.eventually_nhds_iff.mp hrealLocal
  have hanaRho : AnalyticOnNhd ℝ gamma (ball t rho) := by
    intro u hu
    exact hana u (hrhoLocal hu).2.2
  have hinjRho : Set.InjOn gamma (ball t rho) := by
    intro u hu v hv huv
    exact hinj (hrhoLocal hu).2.2 (hrhoLocal hv).2.2 huv
  have hfrontRho : ∀ u ∈ ball t rho, gamma u ∈ frontier K := by
    intro u hu
    exact hfront u (hrhoLocal hu).2.2
  obtain ⟨a, b, O, hat, htb, hIcc, hOopen, hOfront⟩ :=
    exists_open_inter_frontier_eq_image_Ioo hconv hc hcompact hrho
      hanaRho.continuousOn hinjRho hfrontRho
  have htIoo : t ∈ Ioo a b := ⟨hat, htb⟩
  have hgammaT : gamma t ∈ O ∩ frontier K := by
    rw [hOfront]
    exact ⟨t, htIoo, rfl⟩
  have hGt : G (t : ℂ) = gamma t := hGagree.self_of_nhds
  have hGO : G (t : ℂ) ∈ O := hGt ▸ hgammaT.1
  have hGanalyticNear : ∀ᶠ z : ℂ in nhds (t : ℂ), AnalyticAt ℂ G z :=
    hGana.eventually_analyticAt
  have hGmapsNear : ∀ᶠ z : ℂ in nhds (t : ℂ), G z ∈ O :=
    hGana.continuousAt <| hOopen.mem_nhds hGO
  have hcomplexLocal : ∀ᶠ z : ℂ in nhds (t : ℂ),
      z ∈ V ∧ AnalyticAt ℂ G z ∧ G z ∈ O :=
    by
      filter_upwards [hV, hGanalyticNear, hGmapsNear] with z hzV hzana hzO
      exact ⟨hzV, hzana, hzO⟩
  obtain ⟨eps, heps, hepsLocal⟩ := Metric.eventually_nhds_iff.mp hcomplexLocal
  let delta : ℝ := eps / 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hdeltaEps : delta < eps := by
    dsimp [delta]
    linarith
  have hlocal {z : ℂ} (hz : z ∈ ball (t : ℂ) delta) :
      z ∈ V ∧ AnalyticAt ℂ G z ∧ G z ∈ O := by
    apply hepsLocal
    exact lt_trans hz hdeltaEps
  have hzeroO : ∀ z ∈ O ∩ frontier K, h z = 0 := by
    intro z hz
    rw [hOfront] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    have huRho : u ∈ ball t rho := hIcc (Ioo_subset_Icc_self hu)
    exact hzero u (hrhoLocal huRho).2.2
  let hExt : ℂ → ℂ := fun z ↦ if z ∈ K then h z else 0
  have hExtCont : ContinuousOn hExt O := by
    apply ContinuousOn.if (p := fun z : ℂ ↦ z ∈ K)
    · intro z hz
      have hz' : z ∈ O ∩ frontier K := by simpa using hz
      simpa [hExt] using hzeroO z hz'
    · apply hhK.mono
      intro z hz
      simpa [hKclosed.closure_eq] using hz.2
    · exact continuousOn_const
  let H : ℂ → ℂ := fun z ↦ hExt (G z)
  have hGdiff : DifferentiableOn ℂ G (ball (t : ℂ) delta) := by
    intro z hz
    exact (hlocal hz).2.1.differentiableAt.differentiableWithinAt
  have hGmaps : MapsTo G (ball (t : ℂ) delta) O := by
    intro z hz
    exact (hlocal hz).2.2
  have hHcont : ContinuousOn H (ball (t : ℂ) delta) := by
    simpa [H, Function.comp_def] using
      hExtCont.comp hGdiff.continuousOn hGmaps
  have hGnotFrontier {z : ℂ} (hz : z ∈ ball (t : ℂ) delta)
      (hzim : z.im ≠ 0) : G z ∉ frontier K := by
    intro hGfront
    have hGOz : G z ∈ O := (hlocal hz).2.2
    have hpair : G z ∈ O ∩ frontier K := ⟨hGOz, hGfront⟩
    rw [hOfront] at hpair
    obtain ⟨u, hu, huG⟩ := hpair
    have huRho : u ∈ ball t rho := hIcc (Ioo_subset_Icc_self hu)
    have huLocal := hrhoLocal huRho
    have hzu : z = (u : ℂ) := by
      apply hGinj (hlocal hz).1 huLocal.1
      exact huG.symm.trans huLocal.2.1.symm
    apply hzim
    rw [hzu]
    simp
  have hHdiff : ∀ z ∈ ball (t : ℂ) delta, z.im ≠ 0 →
      DifferentiableAt ℂ H z := by
    intro z hz hzim
    have hGzDiff : DifferentiableAt ℂ G z := (hlocal hz).2.1.differentiableAt
    have hnotFront := hGnotFrontier hz hzim
    have hExtDiff : DifferentiableAt ℂ hExt (G z) := by
      by_cases hGzK : G z ∈ K
      · have hGzInt : G z ∈ interior K :=
          (mem_interior_iff_notMem_frontier hGzK).2 hnotFront
        apply (hh.differentiableAt isOpen_interior hGzInt).congr_of_eventuallyEq
        filter_upwards [isOpen_interior.mem_nhds hGzInt] with w hw
        simp [hExt, interior_subset hw]
      · apply (differentiableAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
        filter_upwards [hKclosed.isOpen_compl.mem_nhds hGzK] with w hw
        change w ∉ K at hw
        simp [hExt, hw]
    simpa [H, Function.comp_def] using hExtDiff.comp z hGzDiff
  have hHdiffOn : DifferentiableOn ℂ H (ball (t : ℂ) delta) :=
    differentiableOn_ball_of_continuousOn_of_differentiableAt_off_real
      hHcont hHdiff
  have hGinjBall : Set.InjOn G (ball (t : ℂ) delta) := by
    apply hGinj.mono
    intro z hz
    exact (hlocal hz).1
  have hGimageOpen : IsOpen (G '' ball (t : ℂ) delta) :=
    isOpen_image_of_differentiableOn_of_injOn isOpen_ball hGdiff hGinjBall
  have hGtImage : G (t : ℂ) ∈ G '' ball (t : ℂ) delta :=
    ⟨(t : ℂ), mem_ball_self hdelta, rfl⟩
  obtain ⟨eta, heta, hetaImage⟩ :=
    Metric.isOpen_iff.mp hGimageOpen (G (t : ℂ)) hGtImage
  have hGtFrontier : G (t : ℂ) ∈ frontier K := hGt ▸ hgammaT.2
  have hGtClosureCompl : G (t : ℂ) ∈ closure Kᶜ := by
    rw [frontier_eq_closure_inter_closure] at hGtFrontier
    exact hGtFrontier.2
  obtain ⟨zout, hzoutK, hzoutDist⟩ :=
    Metric.mem_closure_iff.mp hGtClosureCompl eta heta
  have hzoutImage : zout ∈ G '' ball (t : ℂ) delta := by
    apply hetaImage
    simpa [mem_ball, dist_comm] using hzoutDist
  obtain ⟨wout, hwout, rfl⟩ := hzoutImage
  have hHeventZero : H =ᶠ[nhds wout] (0 : ℂ → ℂ) := by
    have hGcontAt : ContinuousAt G wout := (hlocal hwout).2.1.continuousAt
    filter_upwards [hGcontAt (hKclosed.isOpen_compl.mem_nhds hzoutK)] with w hw
    change G w ∉ K at hw
    simp [H, hExt, hw]
  have hHzero : EqOn H 0 (ball (t : ℂ) delta) := by
    exact (hHdiffOn.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const (convex_ball (t : ℂ) delta).isPreconnected
      hwout hHeventZero
  have hGtClosureInterior : G (t : ℂ) ∈ closure (interior K) := by
    rw [hclosure]
    exact hKclosed.frontier_subset hGtFrontier
  obtain ⟨zin, hzinInt, hzinDist⟩ :=
    Metric.mem_closure_iff.mp hGtClosureInterior eta heta
  have hzinImage : zin ∈ G '' ball (t : ℂ) delta := by
    apply hetaImage
    simpa [mem_ball, dist_comm] using hzinDist
  have hzeroNearZin : h =ᶠ[nhds zin] (0 : ℂ → ℂ) := by
    have hopen : IsOpen (interior K ∩ G '' ball (t : ℂ) delta) :=
      isOpen_interior.inter hGimageOpen
    filter_upwards [hopen.mem_nhds ⟨hzinInt, hzinImage⟩] with z hz
    obtain ⟨w, hw, rfl⟩ := hz.2
    have hzeroHw := hHzero hw
    simpa [H, hExt, interior_subset hz.1] using hzeroHw
  exact (hh.differentiableOn.analyticOnNhd isOpen_interior).eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const hconv.interior.isPreconnected hzinInt hzeroNearZin

/-- The parameterized endpoint used by the numerical-range rigidity proof.
An arclength-a.e. boundary identity on the strictly curved affine arc is
first upgraded by continuity on a smaller seam-free subarc, and the faithful
local flattening/Morera theorem then propagates it through the numerical-range
interior. -/
theorem eqOn_zero_of_diffContOnCl_of_ae_radial_strictlyCurved_affineArc
    (A : Operator.SquareMatrix n)
    {c : ℂ} (hc : c ∈ interior (Operator.numericalRange A))
    {t r : ℝ} (hr : 0 < r)
    (hana : AnalyticOnNhd ℝ (affineBoundaryPoint A) (ball t r))
    (hinj : Set.InjOn (affineBoundaryPoint A) (ball t r))
    (harc : ∀ u ∈ ball t r,
      affineBoundaryPoint A u ∈ frontier (Operator.numericalRange A) ∧
      0 < deriv (deriv (affineNumericalRangeSupport A)) u ∧
      (∀ z ∈ Operator.numericalRange A,
        affineSupportValue u z ≤
          affineSupportValue u (affineBoundaryPoint A u)) ∧
      ∀ z ∈ Operator.numericalRange A,
        affineSupportValue u z =
          affineSupportValue u (affineBoundaryPoint A u) →
        z = affineBoundaryPoint A u)
    {h : ℂ → ℂ}
    (hh : DiffContOnCl ℂ h (interior (Operator.numericalRange A)))
    (hzeroAE : ∀ᵐ s : ℝ
        ∂Operator.radialBoundaryArcLengthMeasure (Operator.numericalRange A) c,
      Operator.radialBoundaryParametrization
          (Operator.numericalRange A) c s ∈
        affineBoundaryPoint A '' ball t r →
      h (Operator.radialBoundaryParametrization
          (Operator.numericalRange A) c s) = 0) :
    EqOn h 0 (interior (Operator.numericalRange A)) := by
  classical
  let K := Operator.numericalRange A
  let gamma := affineBoundaryPoint A
  let sigma := Operator.radialBoundaryParametrization K c
  have hconv : Convex ℝ K := Operator.numericalRange_convex A
  have hcompact : IsCompact K := Operator.isCompact_numericalRange A
  have hKclosed : IsClosed K := hcompact.isClosed
  have hfrontArc : ∀ u ∈ ball t r, gamma u ∈ frontier K := by
    intro u hu
    exact (harc u hu).1
  obtain ⟨a, b, O, hat, htb, hIcc, hOopen, hOfront⟩ :=
    exists_open_inter_frontier_eq_image_Ioo hconv hc hcompact hr
      hana.continuousOn hinj hfrontArc
  let uleft : ℝ := (a + t) / 2
  let uright : ℝ := (t + b) / 2
  have huleft : uleft ∈ Ioo a b := by
    dsimp [uleft]
    constructor <;> linarith
  have huright : uright ∈ Ioo a b := by
    dsimp [uright]
    constructor <;> linarith
  have hleftRight : uleft ≠ uright := by
    dsimp [uleft, uright]
    linarith
  have hgammaLeftRight : gamma uleft ≠ gamma uright := by
    intro heq
    apply hleftRight
    exact hinj
      (hIcc (Ioo_subset_Icc_self huleft))
      (hIcc (Ioo_subset_Icc_self huright)) heq
  have hseam : ∃ u ∈ Ioo a b,
      gamma u ≠ sigma 0 := by
    by_cases hleft : gamma uleft ≠ sigma 0
    · exact ⟨uleft, huleft, hleft⟩
    · refine ⟨uright, huright, ?_⟩
      intro hright
      apply hgammaLeftRight
      exact (not_ne_iff.mp hleft).trans hright.symm
  obtain ⟨u₀, hu₀, hu₀Seam⟩ := hseam
  have hu₀R : u₀ ∈ ball t r := hIcc (Ioo_subset_Icc_self hu₀)
  have hgammaCont : ContinuousAt gamma u₀ :=
    (hana u₀ hu₀R).continuousAt
  have hav         : ∀ᶠ u : ℝ in nhds u₀, gamma u ≠ sigma 0 := by
    have hopen : IsOpen ({sigma 0}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
    exact hgammaCont (hopen.mem_nhds hu₀Seam)
  have hsmallLocal : ∀ᶠ u : ℝ in nhds u₀,
      u ∈ Ioo a b ∧ gamma u ≠ sigma 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hu₀, hav] with u huIoo huAvoid
    exact ⟨huIoo, huAvoid⟩
  obtain ⟨rho, hrho, hrhoLocal⟩ := Metric.eventually_nhds_iff.mp hsmallLocal
  have hclosure : closure (interior K) = K := by
    calc
      closure (interior K) = closure K :=
        hconv.closure_interior_eq_closure_of_nonempty_interior ⟨c, hc⟩
      _ = K := hKclosed.closure_eq
  have hhFrontier : ContinuousOn h (frontier K) := by
    apply hh.continuousOn.mono
    rw [hclosure]
    exact hKclosed.frontier_subset
  have hzeroAEO : ∀ᵐ s : ℝ
      ∂Operator.radialBoundaryArcLengthMeasure K c,
      sigma s ∈ O → h (sigma s) = 0 := by
    filter_upwards [hzeroAE] with s hs
    intro hsO
    apply hs
    have hsFront : sigma s ∈ frontier K :=
      Operator.radialBoundaryParametrization_mem_frontier
        hconv hc hcompact s
    have hsArc : sigma s ∈ gamma '' Ioo a b := by
      rw [← hOfront]
      exact ⟨hsO, hsFront⟩
    obtain ⟨u, hu, huEq⟩ := hsArc
    exact ⟨u, hIcc (Ioo_subset_Icc_self hu), huEq⟩
  have hzeroSmall : ∀ u ∈ ball u₀ rho, h (gamma u) = 0 := by
    intro u hu
    have huLocal := hrhoLocal hu
    have huFront : gamma u ∈ frontier K := by
      exact hfrontArc u (hIcc (Ioo_subset_Icc_self huLocal.1))
    obtain ⟨s, hs⟩ := Set.ext_iff.mp
      (Operator.range_radialBoundaryParametrization hconv hc hcompact)
        (gamma u) |>.mpr huFront
    obtain ⟨v, hv, hsv⟩ :=
      (Operator.radialBoundaryParametrization_periodic K c).exists_mem_Ico₀
        Real.two_pi_pos s
    have hsigmaV : sigma v = gamma u := by
      exact hsv.symm.trans hs
    have hvne : v ≠ 0 := by
      intro hvzero
      apply huLocal.2
      rw [← hsigmaV, hvzero]
    have hvIoo : v ∈ Ioo (0 : ℝ) (2 * Real.pi) := by
      exact ⟨lt_of_le_of_ne hv.1 hvne.symm, hv.2⟩
    have hsigmaVO : sigma v ∈ O := by
      have hpair : gamma u ∈ O ∩ frontier K := by
        rw [hOfront]
        exact ⟨u, huLocal.1, rfl⟩
      simpa only [hsigmaV] using hpair.1
    have heq := Operator.eq_of_ae_eq_on_open_radialBoundaryNeighborhood
      (K := K) (c := c) (E := ℂ) (f := h) (g := fun _ : ℂ ↦ (0 : ℂ))
      (O := O) hconv hc hcompact hOopen hzeroAEO hhFrontier
      (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (0 : ℂ)) (frontier K))
      (t := v) hvIoo hsigmaVO
    rw [← hsigmaV]
    exact heq
  have hanaSmall : AnalyticOnNhd ℝ gamma (ball u₀ rho) := by
    intro u hu
    exact hana u (hIcc (Ioo_subset_Icc_self (hrhoLocal hu).1))
  have hinjSmall : Set.InjOn gamma (ball u₀ rho) := by
    intro u hu v hv huv
    exact hinj
      (hIcc (Ioo_subset_Icc_self (hrhoLocal hu).1))
      (hIcc (Ioo_subset_Icc_self (hrhoLocal hv).1)) huv
  have hfrontSmall : ∀ u ∈ ball u₀ rho, gamma u ∈ frontier K := by
    intro u hu
    exact hfrontArc u (hIcc (Ioo_subset_Icc_self (hrhoLocal hu).1))
  have hregular : deriv gamma u₀ ≠ 0 := by
    have hana₀ : AnalyticAt ℝ gamma u₀ := hana u₀ hu₀R
    have hderiv := hasDerivAt_affineBoundaryPoint_of_analyticAt A hana₀
    rw [hderiv.deriv]
    intro heq
    have him := congrArg Complex.im heq
    have hcurv := (harc u₀ hu₀R).2.1
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul,
      zero_sub, Complex.zero_im] at him
    linarith
  exact eqOn_zero_of_diffContOnCl_of_regularAnalytic_frontier_arc
    hconv hc hcompact hrho hanaSmall hinjSmall hfrontSmall hregular hh hzeroSmall

end NumericalRangeArc

end

end DiskRigidity.Complex
