/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib.Analysis.Complex.JensenFormula

/-!
# Boundary uniqueness on a circular arc

This file isolates the elementary Jensen-formula argument used in the convex
Carathéodory theorem.  A zero-free holomorphic function in the unit disc that
is continuous on the closed disc cannot vanish on a nontrivial boundary arc.
-/

noncomputable section

open Bornology Filter Function MeasureTheory Metric Set Topology
open scoped ComplexConjugate Real

namespace DiskRigidity.Complex

@[expose] public section

/-- A zero-free holomorphic function in the open unit disc, continuous on the
closed unit disc, cannot vanish on a boundary arc of positive angular length.
The arc is parametrized as `0 ≤ theta ≤ ell`; arbitrary arcs reduce to this
one by rotating the source. -/
theorem not_boundary_arc_zero_of_differentiableOn_unitDisc
    {f : ℂ → ℂ}
    (hfdiff : DifferentiableOn ℂ f (ball 0 1))
    (hfcont : ContinuousOn f (closedBall 0 1))
    (hfne : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0)
    {ell : ℝ} (hellPos : 0 < ell) (hellTwoPi : ell < 2 * Real.pi) :
    ¬(∀ theta ∈ Icc (0 : ℝ) ell,
      f (circleMap 0 1 theta) = 0) := by
  intro hzero
  have hcompact : IsCompact (closedBall (0 : ℂ) 1) := isCompact_closedBall 0 1
  have hfimageBounded : IsBounded (f '' closedBall (0 : ℂ) 1) :=
    (hcompact.image_of_continuousOn hfcont).isBounded
  obtain ⟨M, hMPos, hM⟩ := hfimageBounded.exists_pos_norm_le
  have hzeroMem : (0 : ℂ) ∈ ball 0 1 := by simp
  have hfzeroPos : 0 < ‖f 0‖ := norm_pos_iff.mpr (hfne 0 hzeroMem)
  let q : ℝ :=
    ((2 * Real.pi) * Real.log ‖f 0‖ -
      ((2 * Real.pi) - ell) * Real.log M - 1) / ell
  let epsilon : ℝ := Real.exp q
  have hepsilon : 0 < epsilon := Real.exp_pos q
  have hfunif : UniformContinuousOn f (closedBall (0 : ℂ) 1) :=
    hcompact.uniformContinuousOn_of_continuous hfcont
  obtain ⟨delta, hdeltaPos, hdelta⟩ :=
    (Metric.uniformContinuousOn_iff.mp hfunif) epsilon hepsilon
  let d : ℝ := min (delta / 2) (1 / 2)
  let r : ℝ := 1 - d
  have hdPos : 0 < d := by
    dsimp [d]
    positivity
  have hdHalf : d ≤ 1 / 2 := min_le_right _ _
  have hdDelta : d < delta := by
    exact (min_le_left (delta / 2) (1 / 2)).trans_lt
      (half_lt_self hdeltaPos)
  have hrPos : 0 < r := by
    dsimp [r]
    linarith
  have hrOne : r < 1 := by
    dsimp [r]
    linarith
  have hrAbs : |r| = r := abs_of_pos hrPos
  have hcircleBall (theta : ℝ) :
      circleMap 0 r theta ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_zero_right, norm_circleMap_zero, hrAbs]
    exact hrOne
  have hcircleClosedOne (theta : ℝ) :
      circleMap 0 1 theta ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_circleMap_zero]
    norm_num
  have hcircleClosedR (theta : ℝ) :
      circleMap 0 r theta ∈ closedBall (0 : ℂ) 1 :=
    ball_subset_closedBall (hcircleBall theta)
  have hcircleDist (theta : ℝ) :
      dist (circleMap 0 r theta) (circleMap 0 1 theta) = d := by
    rw [Complex.dist_eq]
    simp only [circleMap, zero_add]
    rw [← sub_mul, norm_mul, Complex.norm_exp]
    have hexp : Real.exp (((theta : ℂ) * Complex.I).re) = 1 := by simp
    rw [hexp, mul_one]
    have hrd : r - 1 = -d := by simp [r]
    change ‖(r : ℂ) - ((1 : ℝ) : ℂ)‖ = d
    have hcast : (r : ℂ) - ((1 : ℝ) : ℂ) =
        ((r - 1 : ℝ) : ℂ) := by norm_num
    rw [hcast, hrd, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos hdPos]
  have hsmall (theta : ℝ) (htheta : theta ∈ Icc (0 : ℝ) ell) :
      ‖f (circleMap 0 r theta)‖ < epsilon := by
    have hdist := hdelta (circleMap 0 r theta) (hcircleClosedR theta)
      (circleMap 0 1 theta) (hcircleClosedOne theta)
      (by simpa only [hcircleDist] using hdDelta)
    rw [hzero theta htheta, dist_zero_right] at hdist
    exact hdist
  have hbound (theta : ℝ) : ‖f (circleMap 0 r theta)‖ ≤ M := by
    exact hM _ ⟨circleMap 0 r theta, hcircleClosedR theta, rfl⟩
  let integrand : ℝ → ℝ := fun theta ↦
    Real.log ‖f (circleMap 0 r theta)‖
  have hcompCont : Continuous (fun theta ↦ f (circleMap 0 r theta)) := by
    exact hfdiff.continuousOn.comp_continuous
      (differentiable_circleMap 0 r).continuous hcircleBall
  have hcompNe (theta : ℝ) : f (circleMap 0 r theta) ≠ 0 :=
    hfne _ (hcircleBall theta)
  have hintegrandCont : Continuous integrand := by
    rw [continuous_iff_continuousAt]
    intro theta
    change ContinuousAt (fun x ↦ Real.log ‖f (circleMap 0 r x)‖) theta
    have hnormCont : ContinuousAt
        (fun x : ℝ ↦ ‖f (circleMap 0 r x)‖) theta :=
      hcompCont.continuousAt.norm
    exact ContinuousAt.comp' (f := fun x : ℝ ↦ ‖f (circleMap 0 r x)‖)
      (Real.continuousAt_log (norm_ne_zero_iff.mpr (hcompNe theta))) hnormCont
  have hIntZeroEll : IntervalIntegrable integrand volume 0 ell :=
    hintegrandCont.intervalIntegrable 0 ell
  have hIntEllTwoPi : IntervalIntegrable integrand volume ell (2 * Real.pi) :=
    hintegrandCont.intervalIntegrable ell (2 * Real.pi)
  have hlogSmall (theta : ℝ) (htheta : theta ∈ Icc (0 : ℝ) ell) :
      integrand theta ≤ Real.log epsilon := by
    dsimp [integrand]
    exact Real.log_le_log (norm_pos_iff.mpr (hcompNe theta)) (hsmall theta htheta).le
  have hlogBound (theta : ℝ) : integrand theta ≤ Real.log M := by
    dsimp [integrand]
    exact Real.log_le_log (norm_pos_iff.mpr (hcompNe theta)) (hbound theta)
  have hIntSmall :
      (∫ theta in (0 : ℝ)..ell, integrand theta) ≤ ell * Real.log epsilon := by
    calc
      (∫ theta in (0 : ℝ)..ell, integrand theta)
          ≤ ∫ _theta in (0 : ℝ)..ell, Real.log epsilon := by
            exact intervalIntegral.integral_mono_on hellPos.le hIntZeroEll
              intervalIntegrable_const hlogSmall
      _ = ell * Real.log epsilon := by simp
  have hIntBound :
      (∫ theta in ell..(2 * Real.pi), integrand theta) ≤
        ((2 * Real.pi) - ell) * Real.log M := by
    calc
      (∫ theta in ell..(2 * Real.pi), integrand theta)
          ≤ ∫ _theta in ell..(2 * Real.pi), Real.log M := by
            exact intervalIntegral.integral_mono_on hellTwoPi.le hIntEllTwoPi
              intervalIntegrable_const (fun theta _ ↦ hlogBound theta)
      _ = ((2 * Real.pi) - ell) * Real.log M := by simp
  have hIntegralBound :
      (∫ theta in (0 : ℝ)..(2 * Real.pi), integrand theta) ≤
        ell * Real.log epsilon +
          ((2 * Real.pi) - ell) * Real.log M := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      hIntZeroEll hIntEllTwoPi]
    exact add_le_add hIntSmall hIntBound
  have hanalytic : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |r|) := by
    exact (hfdiff.analyticOnNhd isOpen_ball).mono fun z hz ↦ by
      rw [mem_closedBall, dist_zero_right, hrAbs] at hz
      rw [mem_ball, dist_zero_right]
      exact hz.trans_lt hrOne
  have hJensen :
      Real.circleAverage (Real.log ‖f ·‖) 0 r = Real.log ‖f 0‖ := by
    rw [hanalytic.circleAverage_log_norm_of_ne_zero]
    intro z hz
    apply hfne z
    rw [mem_closedBall, dist_zero_right, hrAbs] at hz
    rw [mem_ball, dist_zero_right]
    exact hz.trans_lt hrOne
  have hAverageBound :
      Real.circleAverage (Real.log ‖f ·‖) 0 r ≤
        ((2 * Real.pi) * Real.log ‖f 0‖ - 1) / (2 * Real.pi) := by
    rw [Real.circleAverage, smul_eq_mul]
    change (2 * Real.pi)⁻¹ *
      (∫ theta in (0 : ℝ)..(2 * Real.pi), integrand theta) ≤ _
    calc
      _ ≤ (2 * Real.pi)⁻¹ *
          (ell * Real.log epsilon +
            ((2 * Real.pi) - ell) * Real.log M) := by
              gcongr
      _ = ((2 * Real.pi) * Real.log ‖f 0‖ - 1) /
          (2 * Real.pi) := by
            rw [Real.log_exp]
            dsimp [epsilon, q]
            field_simp [hellPos.ne', Real.two_pi_pos.ne']
            ring
  rw [hJensen] at hAverageBound
  have htwoPiPos : 0 < 2 * Real.pi := Real.two_pi_pos
  have := (le_div_iff₀ htwoPiPos).mp hAverageBound
  linarith

/-- The rotation-invariant form of
`not_boundary_arc_zero_of_differentiableOn_unitDisc`. -/
theorem not_boundary_interval_zero_of_differentiableOn_unitDisc
    {f : ℂ → ℂ}
    (hfdiff : DifferentiableOn ℂ f (ball 0 1))
    (hfcont : ContinuousOn f (closedBall 0 1))
    (hfne : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0)
    {a b : ℝ} (hab : a < b) (hwidth : b - a < 2 * Real.pi) :
    ¬(∀ theta ∈ Icc a b, f (circleMap 0 1 theta) = 0) := by
  intro hzero
  let u : ℂ := circleMap 0 1 a
  let g : ℂ → ℂ := fun z ↦ f (u * z)
  have huNorm : ‖u‖ = 1 := by simp [u, norm_circleMap_zero]
  have hmulBall {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
      u * z ∈ ball (0 : ℂ) 1 := by
    simpa only [mem_ball, dist_zero_right, norm_mul, huNorm, one_mul] using hz
  have hmulClosed {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
      u * z ∈ closedBall (0 : ℂ) 1 := by
    simpa only [mem_closedBall, dist_zero_right, norm_mul, huNorm, one_mul] using hz
  have hmulDiff : Differentiable ℂ (fun z : ℂ ↦ u * z) :=
    (differentiable_const u).mul differentiable_id
  have hgdiff : DifferentiableOn ℂ g (ball 0 1) := by
    intro z hz
    have hfAt : DifferentiableAt ℂ f (u * z) :=
      (hfdiff _ (hmulBall hz)).differentiableAt
        (isOpen_ball.mem_nhds (hmulBall hz))
    exact (hfAt.comp z (hmulDiff z)).differentiableWithinAt
  have hgcont : ContinuousOn g (closedBall 0 1) := by
    exact hfcont.comp hmulDiff.continuous.continuousOn fun _ hz ↦ hmulClosed hz
  have hgne : ∀ z ∈ ball (0 : ℂ) 1, g z ≠ 0 := by
    intro z hz
    exact hfne _ (hmulBall hz)
  apply not_boundary_arc_zero_of_differentiableOn_unitDisc
    hgdiff hgcont hgne (sub_pos.mpr hab) hwidth
  intro theta htheta
  have htheta' : a + theta ∈ Icc a b := by
    constructor
    · linarith [htheta.1]
    · linarith [htheta.2]
  dsimp [g, u]
  rw [circleMap_zero_mul]
  norm_num
  exact hzero (a + theta) htheta'

/-- A nonzero holomorphic function on the unit disc has a uniform lower
bound for its logarithmic circle averages on radii between `1 / 2` and `1`.
This is Jensen's formula with all zero-divisor terms retained. -/
private theorem exists_lowerBound_circleAverage_log_norm
    {f : ℂ → ℂ}
    (hfdiff : DifferentiableOn ℂ f (ball 0 1))
    (hfnonzero : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0) :
    ∃ L : ℝ, ∀ r : ℝ, (1 / 2 : ℝ) ≤ r → r < 1 →
      L ≤ Real.circleAverage (Real.log ‖f ·‖) 0 r := by
  have hanalyticUnit : AnalyticOnNhd ℂ f (ball (0 : ℂ) 1) :=
    hfdiff.analyticOnNhd isOpen_ball
  obtain ⟨x, hx, hfx⟩ := hfnonzero
  have hxOrder : analyticOrderAt f x ≠ ⊤ := by
    rw [(hanalyticUnit x hx).analyticOrderAt_eq_zero.mpr hfx]
    exact ENat.natCast_ne_top 0
  have horderFinite : ∀ u ∈ ball (0 : ℂ) 1,
      analyticOrderAt f u ≠ ⊤ := by
    intro u hu
    exact hanalyticUnit.analyticOrderAt_ne_top_of_isPreconnected
      (convex_ball (0 : ℂ) 1).isPreconnected hx hu hxOrder
  have hzeroMem : (0 : ℂ) ∈ ball 0 1 := by simp
  have horderZero : analyticOrderAt f 0 ≠ ⊤ :=
    horderFinite 0 hzeroMem
  let m : ℝ := ((MeromorphicOn.divisor f (ball (0 : ℂ) 1)) 0 : ℤ)
  have hmNonneg : 0 ≤ m := by
    dsimp [m]
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
      hanalyticUnit hzeroMem]
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp horderZero
    rw [← hk]
    simp only [ENat.map_natCast, WithTop.untop₀_coe]
    exact_mod_cast Nat.zero_le k
  let L : ℝ := m * Real.log (1 / 2 : ℝ) +
    Real.log ‖meromorphicTrailingCoeffAt f 0‖
  refine ⟨L, ?_⟩
  intro r hrHalf hrOne
  have hrPos : 0 < r := lt_of_lt_of_le (by norm_num) hrHalf
  have hrAbs : |r| = r := abs_of_pos hrPos
  have hclosedSubset : closedBall (0 : ℂ) |r| ⊆ ball 0 1 := by
    intro z hz
    rw [mem_closedBall, dist_zero_right, hrAbs] at hz
    rw [mem_ball, dist_zero_right]
    exact hz.trans_lt hrOne
  have hanalyticR : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |r|) :=
    hanalyticUnit.mono hclosedSubset
  have hanalyticR' : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r) := by
    rwa [hrAbs] at hanalyticR
  have hcenterDiv :
      ((MeromorphicOn.divisor f (closedBall (0 : ℂ) r)) 0 : ℝ) = m := by
    dsimp [m]
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
        hanalyticR' (mem_closedBall_self hrPos.le),
      MeromorphicOn.AnalyticOnNhd.divisor_apply
        hanalyticUnit hzeroMem]
  have hsumNonneg : 0 ≤ ∑ᶠ u,
      (MeromorphicOn.divisor f (closedBall (0 : ℂ) r) u : ℝ) *
        Real.log (r * ‖(0 : ℂ) - u‖⁻¹) := by
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ closedBall (0 : ℂ) r
    · have hdiv : 0 ≤
          (MeromorphicOn.divisor f (closedBall (0 : ℂ) r) u : ℝ) := by
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hanalyticR' hu]
        obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp
          (horderFinite u (hclosedSubset (by rwa [hrAbs])))
        rw [← hk]
        simp only [ENat.map_natCast, WithTop.untop₀_coe]
        exact_mod_cast Nat.zero_le k
      have hlog : 0 ≤ Real.log (r * ‖(0 : ℂ) - u‖⁻¹) := by
        by_cases hu0 : u = 0
        · subst u
          simp
        · apply Real.log_nonneg
          rw [zero_sub, norm_neg]
          have huNormPos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
          have huNormLe : ‖u‖ ≤ r := by
            simpa only [mem_closedBall, dist_zero_right] using hu
          rw [le_mul_inv_iff₀ huNormPos]
          simpa using huNormLe
      exact mul_nonneg hdiv hlog
    · rw [MeromorphicOn.divisor_def]
      simp [hu]
  have hlogHalf : Real.log (1 / 2 : ℝ) ≤ Real.log r :=
    Real.log_le_log (by norm_num) hrHalf
  have hmLog : m * Real.log (1 / 2 : ℝ) ≤ m * Real.log r :=
    mul_le_mul_of_nonneg_left hlogHalf hmNonneg
  have hformula :=
    hanalyticR.meromorphicOn.circleAverage_log_norm hrPos.ne'
  rw [hrAbs] at hformula
  rw [hformula, hcenterDiv]
  dsimp [L]
  linarith

/-- The zero set of a nonzero holomorphic function in a compact subdisc of
the unit disc is finite. -/
private theorem finite_zeroSet_closedBall_of_differentiableOn_unitDisc
    {f : ℂ → ℂ}
    (hfdiff : DifferentiableOn ℂ f (ball 0 1))
    (hfnonzero : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0)
    {r : ℝ} (hr : |r| < 1) :
    {z : ℂ | z ∈ closedBall 0 |r| ∧ f z = 0}.Finite := by
  have hanalyticUnit : AnalyticOnNhd ℂ f (ball (0 : ℂ) 1) :=
    hfdiff.analyticOnNhd isOpen_ball
  obtain ⟨x, hx, hfx⟩ := hfnonzero
  have hxOrder : analyticOrderAt f x ≠ ⊤ := by
    rw [(hanalyticUnit x hx).analyticOrderAt_eq_zero.mpr hfx]
    exact ENat.natCast_ne_top 0
  have hclosedSubset : closedBall (0 : ℂ) |r| ⊆ ball 0 1 := by
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    rw [mem_ball, dist_zero_right]
    exact hz.trans_lt hr
  have hanalyticR : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |r|) :=
    hanalyticUnit.mono hclosedSubset
  have horderFinite : ∀ u ∈ closedBall (0 : ℂ) |r|,
      analyticOrderAt f u ≠ ⊤ := by
    intro u hu
    exact hanalyticUnit.analyticOrderAt_ne_top_of_isPreconnected
      (convex_ball (0 : ℂ) 1).isPreconnected hx
        (hclosedSubset hu) hxOrder
  apply (MeromorphicOn.divisor f (closedBall (0 : ℂ) |r|)).finiteSupport
    (isCompact_closedBall 0 |r|) |>.subset
  intro u hu
  rw [Function.mem_support]
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hanalyticR hu.1]
  have horderNe : analyticOrderAt f u ≠ 0 := by
    intro hzero
    exact ((hanalyticR u hu.1).analyticOrderAt_eq_zero.mp hzero) hu.2
  simpa [horderFinite u hu.1] using horderNe

/-- A nonzero holomorphic function in the open unit disc, continuous on the
closed disc, cannot vanish on a boundary arc of positive angular length.
Unlike `not_boundary_arc_zero_of_differentiableOn_unitDisc`, interior zeros
are allowed. -/
theorem not_boundary_arc_zero_of_nonzero_differentiableOn_unitDisc
    {f : ℂ → ℂ}
    (hfdiff : DifferentiableOn ℂ f (ball 0 1))
    (hfcont : ContinuousOn f (closedBall 0 1))
    (hfnonzero : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0)
    {ell : ℝ} (hellPos : 0 < ell) (hellTwoPi : ell < 2 * Real.pi) :
    ¬(∀ theta ∈ Icc (0 : ℝ) ell,
      f (circleMap 0 1 theta) = 0) := by
  intro hzero
  obtain ⟨L, haverageLower⟩ :=
    exists_lowerBound_circleAverage_log_norm hfdiff hfnonzero
  have hcompact : IsCompact (closedBall (0 : ℂ) 1) :=
    isCompact_closedBall 0 1
  have hfimageBounded : IsBounded (f '' closedBall (0 : ℂ) 1) :=
    (hcompact.image_of_continuousOn hfcont).isBounded
  obtain ⟨M, hMPos, hM⟩ := hfimageBounded.exists_pos_norm_le
  let q : ℝ :=
    ((2 * Real.pi) * L -
      ((2 * Real.pi) - ell) * Real.log M - 1) / ell
  let epsilon : ℝ := Real.exp q
  have hepsilon : 0 < epsilon := Real.exp_pos q
  have hfunif : UniformContinuousOn f (closedBall (0 : ℂ) 1) :=
    hcompact.uniformContinuousOn_of_continuous hfcont
  obtain ⟨delta, hdeltaPos, hdelta⟩ :=
    (Metric.uniformContinuousOn_iff.mp hfunif) epsilon hepsilon
  let d : ℝ := min (delta / 2) (1 / 2)
  let r : ℝ := 1 - d
  have hdPos : 0 < d := by
    dsimp [d]
    positivity
  have hdHalf : d ≤ 1 / 2 := min_le_right _ _
  have hdDelta : d < delta :=
    (min_le_left (delta / 2) (1 / 2)).trans_lt
      (half_lt_self hdeltaPos)
  have hrPos : 0 < r := by
    dsimp [r]
    linarith
  have hrHalf : (1 / 2 : ℝ) ≤ r := by
    dsimp [r]
    linarith
  have hrOne : r < 1 := by
    dsimp [r]
    linarith
  have hrAbs : |r| = r := abs_of_pos hrPos
  have hcircleBall (theta : ℝ) :
      circleMap 0 r theta ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_zero_right, norm_circleMap_zero, hrAbs]
    exact hrOne
  have hcircleClosedOne (theta : ℝ) :
      circleMap 0 1 theta ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_circleMap_zero]
    norm_num
  have hcircleClosedR (theta : ℝ) :
      circleMap 0 r theta ∈ closedBall (0 : ℂ) 1 :=
    ball_subset_closedBall (hcircleBall theta)
  have hcircleOwnClosed (theta : ℝ) :
      circleMap 0 r theta ∈ closedBall (0 : ℂ) |r| := by
    rw [mem_closedBall, dist_zero_right, norm_circleMap_zero]
  have hcircleDist (theta : ℝ) :
      dist (circleMap 0 r theta) (circleMap 0 1 theta) = d := by
    rw [Complex.dist_eq]
    simp only [circleMap, zero_add]
    rw [← sub_mul, norm_mul, Complex.norm_exp]
    have hexp : Real.exp (((theta : ℂ) * Complex.I).re) = 1 := by simp
    rw [hexp, mul_one]
    have hrd : r - 1 = -d := by simp [r]
    change ‖(r : ℂ) - ((1 : ℝ) : ℂ)‖ = d
    have hcast : (r : ℂ) - ((1 : ℝ) : ℂ) =
        ((r - 1 : ℝ) : ℂ) := by norm_num
    rw [hcast, hrd, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos hdPos]
  have hsmall (theta : ℝ) (htheta : theta ∈ Icc (0 : ℝ) ell) :
      ‖f (circleMap 0 r theta)‖ < epsilon := by
    have hdist := hdelta (circleMap 0 r theta) (hcircleClosedR theta)
      (circleMap 0 1 theta) (hcircleClosedOne theta)
      (by simpa only [hcircleDist] using hdDelta)
    rw [hzero theta htheta, dist_zero_right] at hdist
    exact hdist
  have hbound (theta : ℝ) : ‖f (circleMap 0 r theta)‖ ≤ M :=
    hM _ ⟨circleMap 0 r theta, hcircleClosedR theta, rfl⟩
  let integrand : ℝ → ℝ := fun theta ↦
    Real.log ‖f (circleMap 0 r theta)‖
  let modifiedIntegrand : ℝ → ℝ := fun theta ↦
    if f (circleMap 0 r theta) = 0 then
      min (Real.log epsilon) (Real.log M)
    else integrand theta
  have hzeroThetaCountable :
      {theta : ℝ | f (circleMap 0 r theta) = 0}.Countable := by
    let Z : Set ℂ :=
      {z | z ∈ closedBall 0 |r| ∧ f z = 0}
    have hZfinite : Z.Finite :=
      finite_zeroSet_closedBall_of_differentiableOn_unitDisc
        hfdiff hfnonzero (by simpa [hrAbs] using hrOne)
    apply ((hZfinite.countable.preimage_circleMap 0 hrPos.ne')).mono
    intro theta htheta
    exact ⟨hcircleOwnClosed theta, htheta⟩
  have hmodifiedEq : integrand =ᶠ[ae volume] modifiedIntegrand := by
    filter_upwards [hzeroThetaCountable.ae_notMem volume] with theta htheta
    have hne : f (circleMap 0 r theta) ≠ 0 := by
      exact htheta
    simp only [modifiedIntegrand, hne, if_false]
  have hanalytic : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |r|) := by
    exact (hfdiff.analyticOnNhd isOpen_ball).mono fun z hz ↦ by
      rw [mem_closedBall, dist_zero_right, hrAbs] at hz
      rw [mem_ball, dist_zero_right]
      exact hz.trans_lt hrOne
  have hIntFull : IntervalIntegrable integrand volume 0 (2 * Real.pi) := by
    exact (hanalytic.mono sphere_subset_closedBall).meromorphicOn
      |>.circleIntegrable_log_norm
  have hIntZeroEll : IntervalIntegrable integrand volume 0 ell := by
    apply hIntFull.mono_set
    rw [uIcc_of_le hellPos.le, uIcc_of_le Real.two_pi_pos.le]
    exact Icc_subset_Icc le_rfl hellTwoPi.le
  have hIntEllTwoPi :
      IntervalIntegrable integrand volume ell (2 * Real.pi) := by
    apply hIntFull.mono_set
    rw [uIcc_of_le hellTwoPi.le, uIcc_of_le Real.two_pi_pos.le]
    exact Icc_subset_Icc hellPos.le le_rfl
  have hIntZeroEllModified :
      IntervalIntegrable modifiedIntegrand volume 0 ell :=
    hIntZeroEll.congr_ae (hmodifiedEq.filter_mono ae_restrict_le)
  have hIntEllTwoPiModified :
      IntervalIntegrable modifiedIntegrand volume ell (2 * Real.pi) :=
    hIntEllTwoPi.congr_ae (hmodifiedEq.filter_mono ae_restrict_le)
  have hlogSmall (theta : ℝ) (htheta : theta ∈ Icc (0 : ℝ) ell) :
      modifiedIntegrand theta ≤ Real.log epsilon := by
    by_cases hthetaZero : f (circleMap 0 r theta) = 0
    · simp [modifiedIntegrand, hthetaZero]
    · simp only [modifiedIntegrand, hthetaZero, if_false, integrand]
      exact Real.log_le_log (norm_pos_iff.mpr hthetaZero)
        (hsmall theta htheta).le
  have hlogBound (theta : ℝ) :
      modifiedIntegrand theta ≤ Real.log M := by
    by_cases hthetaZero : f (circleMap 0 r theta) = 0
    · simp [modifiedIntegrand, hthetaZero]
    · simp only [modifiedIntegrand, hthetaZero, if_false, integrand]
      exact Real.log_le_log (norm_pos_iff.mpr hthetaZero) (hbound theta)
  have hIntSmallModified :
      (∫ theta in (0 : ℝ)..ell, modifiedIntegrand theta) ≤
        ell * Real.log epsilon := by
    calc
      (∫ theta in (0 : ℝ)..ell, modifiedIntegrand theta)
          ≤ ∫ _theta in (0 : ℝ)..ell, Real.log epsilon := by
            exact intervalIntegral.integral_mono_on hellPos.le
              hIntZeroEllModified intervalIntegrable_const hlogSmall
      _ = ell * Real.log epsilon := by simp
  have hIntBoundModified :
      (∫ theta in ell..(2 * Real.pi), modifiedIntegrand theta) ≤
        ((2 * Real.pi) - ell) * Real.log M := by
    calc
      (∫ theta in ell..(2 * Real.pi), modifiedIntegrand theta)
          ≤ ∫ _theta in ell..(2 * Real.pi), Real.log M := by
            exact intervalIntegral.integral_mono_on hellTwoPi.le
              hIntEllTwoPiModified intervalIntegrable_const
                (fun theta _ ↦ hlogBound theta)
      _ = ((2 * Real.pi) - ell) * Real.log M := by simp
  have hIntSmall :
      (∫ theta in (0 : ℝ)..ell, integrand theta) ≤
        ell * Real.log epsilon := by
    rw [intervalIntegral.integral_congr_ae
      (hmodifiedEq.mono fun _ h _ ↦ h)]
    exact hIntSmallModified
  have hIntBound :
      (∫ theta in ell..(2 * Real.pi), integrand theta) ≤
        ((2 * Real.pi) - ell) * Real.log M := by
    rw [intervalIntegral.integral_congr_ae
      (hmodifiedEq.mono fun _ h _ ↦ h)]
    exact hIntBoundModified
  have hIntegralBound :
      (∫ theta in (0 : ℝ)..(2 * Real.pi), integrand theta) ≤
        ell * Real.log epsilon +
          ((2 * Real.pi) - ell) * Real.log M := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      hIntZeroEll hIntEllTwoPi]
    exact add_le_add hIntSmall hIntBound
  have hAverageBound :
      Real.circleAverage (Real.log ‖f ·‖) 0 r ≤
        ((2 * Real.pi) * L - 1) / (2 * Real.pi) := by
    rw [Real.circleAverage, smul_eq_mul]
    change (2 * Real.pi)⁻¹ *
      (∫ theta in (0 : ℝ)..(2 * Real.pi), integrand theta) ≤ _
    calc
      _ ≤ (2 * Real.pi)⁻¹ *
          (ell * Real.log epsilon +
            ((2 * Real.pi) - ell) * Real.log M) := by
              gcongr
      _ = ((2 * Real.pi) * L - 1) / (2 * Real.pi) := by
            rw [Real.log_exp]
            dsimp [epsilon, q]
            field_simp [hellPos.ne', Real.two_pi_pos.ne']
            ring
  have hLower := haverageLower r hrHalf hrOne
  have hcontr := hLower.trans hAverageBound
  have htwoPiPos : 0 < 2 * Real.pi := Real.two_pi_pos
  have := (le_div_iff₀ htwoPiPos).mp hcontr
  linarith

/-- Rotation-invariant boundary-arc uniqueness for an arbitrary nonzero
holomorphic function; interior zeros are allowed. -/
theorem not_boundary_interval_zero_of_nonzero_differentiableOn_unitDisc
    {f : ℂ → ℂ}
    (hfdiff : DifferentiableOn ℂ f (ball 0 1))
    (hfcont : ContinuousOn f (closedBall 0 1))
    (hfnonzero : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0)
    {a b : ℝ} (hab : a < b) (hwidth : b - a < 2 * Real.pi) :
    ¬(∀ theta ∈ Icc a b, f (circleMap 0 1 theta) = 0) := by
  intro hzero
  let u : ℂ := circleMap 0 1 a
  let g : ℂ → ℂ := fun z ↦ f (u * z)
  have huNorm : ‖u‖ = 1 := by simp [u, norm_circleMap_zero]
  have huNe : u ≠ 0 := norm_ne_zero_iff.mp (by rw [huNorm]; norm_num)
  have hmulBall {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
      u * z ∈ ball (0 : ℂ) 1 := by
    simpa only [mem_ball, dist_zero_right, norm_mul, huNorm, one_mul]
      using hz
  have hmulClosed {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
      u * z ∈ closedBall (0 : ℂ) 1 := by
    simpa only [mem_closedBall, dist_zero_right, norm_mul, huNorm, one_mul]
      using hz
  have hmulDiff : Differentiable ℂ (fun z : ℂ ↦ u * z) :=
    (differentiable_const u).mul differentiable_id
  have hgdiff : DifferentiableOn ℂ g (ball 0 1) := by
    intro z hz
    have hfAt : DifferentiableAt ℂ f (u * z) :=
      (hfdiff _ (hmulBall hz)).differentiableAt
        (isOpen_ball.mem_nhds (hmulBall hz))
    exact (hfAt.comp z (hmulDiff z)).differentiableWithinAt
  have hgcont : ContinuousOn g (closedBall 0 1) :=
    hfcont.comp hmulDiff.continuous.continuousOn
      fun _ hz ↦ hmulClosed hz
  have hgnonzero : ∃ z ∈ ball (0 : ℂ) 1, g z ≠ 0 := by
    obtain ⟨z, hz, hfz⟩ := hfnonzero
    refine ⟨u⁻¹ * z, ?_, ?_⟩
    · simpa only [mem_ball, dist_zero_right, norm_mul, norm_inv,
        huNorm, inv_one, one_mul] using hz
    · dsimp [g]
      rwa [← mul_assoc, mul_inv_cancel₀ huNe, one_mul]
  apply not_boundary_arc_zero_of_nonzero_differentiableOn_unitDisc
    hgdiff hgcont hgnonzero (sub_pos.mpr hab) hwidth
  intro theta htheta
  have htheta' : a + theta ∈ Icc a b := by
    constructor
    · linarith [htheta.1]
    · linarith [htheta.2]
  dsimp [g, u]
  rw [circleMap_zero_mul]
  norm_num
  exact hzero (a + theta) htheta'

end

end DiskRigidity.Complex
