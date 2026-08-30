/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.ConvexBoundaryMoments
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Winding one of the radial convex boundary

The positive radial representation computes the winding integral directly.
The only nonsmooth term is the logarithmic derivative of the Lipschitz
radius; the Lipschitz fundamental theorem makes its integral vanish.
-/

@[expose] public section

noncomputable section

open Bornology Filter MeasureTheory Metric Set Topology
open scoped NNReal Pointwise

namespace DiskRigidity.Operator

/-- The radial radius is bounded uniformly above and away from zero. -/
theorem exists_uniform_bounds_radialBoundaryRadius
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K) :
    ∃ r R : ℝ, 0 < r ∧ r ≤ R ∧ ∀ t,
      r ≤ radialBoundaryRadius K c t ∧
        radialBoundaryRadius K c t ≤ R := by
  have hKnhds : K ∈ 𝓝 c := mem_interior_iff_mem_nhds.mp hc
  obtain ⟨r, hr, hrK⟩ := Metric.mem_nhds_iff.mp hKnhds
  obtain ⟨R, hKR⟩ := hcompact.isBounded.subset_closedBall c
  have hradiusLower (t : ℝ) : r ≤ radialBoundaryRadius K c t := by
    by_contra hnot
    have hlt : radialBoundaryRadius K c t < r := lt_of_not_ge hnot
    let z := radialBoundaryParametrization K c t
    have hzball : z ∈ ball c r := by
      simpa [z, radialBoundaryRadius, mem_ball, dist_eq_norm, norm_sub_rev] using hlt
    have hzint : z ∈ interior K :=
      mem_interior_iff_mem_nhds.mpr <|
        Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hzball) hrK
    exact (radialBoundaryParametrization_mem_frontier
      hconv hc hcompact t).2 hzint
  have hradiusUpper (t : ℝ) : radialBoundaryRadius K c t ≤ R := by
    have hzK : radialBoundaryParametrization K c t ∈ K := by
      have hz' := (frontier_subset_closure : frontier K ⊆ closure K)
        (radialBoundaryParametrization_mem_frontier hconv hc hcompact t)
      simpa only [hcompact.isClosed.closure_eq] using hz'
    have hz := hKR hzK
    simpa [radialBoundaryRadius, mem_closedBall, dist_eq_norm, norm_sub_rev] using hz
  refine ⟨r, R, hr, hradiusLower 0 |>.trans (hradiusUpper 0), ?_⟩
  exact fun t ↦ ⟨hradiusLower t, hradiusUpper t⟩

/-- The logarithm of the positive periodic radial radius is globally
Lipschitz. -/
theorem exists_lipschitzWith_log_radialBoundaryRadius
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K) :
    ∃ C : ℝ≥0, LipschitzWith C
      (fun t ↦ Real.log (radialBoundaryRadius K c t)) := by
  obtain ⟨r, R, hr, hrR, hradius⟩ :=
    exists_uniform_bounds_radialBoundaryRadius hconv hc hcompact
  obtain ⟨Crho, hrho⟩ :=
    exists_lipschitzWith_radialBoundaryRadius hconv hc hcompact
  have hlogdiff : ContDiffOn ℝ 1 Real.log (Set.Icc r R) :=
    Real.contDiffOn_log.mono fun x hx ↦ by
      have : 0 < x := hr.trans_le hx.1
      simpa only [mem_compl_iff, mem_singleton_iff] using this.ne'
  obtain ⟨Clog, hlog⟩ := hlogdiff.exists_lipschitzOnWith
    (by norm_num) (convex_Icc r R) isCompact_Icc
  refine ⟨Clog * Crho, lipschitzOnWith_univ.mp ?_⟩
  exact hlog.comp hrho.lipschitzOnWith fun t _ ↦ hradius t

/-- The logarithmic derivative of the radial radius integrates to zero
over one period. -/
theorem intervalIntegral_deriv_radius_div_radius_eq_zero
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K) :
    ∫ t in (0 : ℝ)..(2 * Real.pi),
        deriv (radialBoundaryRadius K c) t /
          radialBoundaryRadius K c t = 0 := by
  obtain ⟨C, hlogLip⟩ :=
    exists_lipschitzWith_log_radialBoundaryRadius hconv hc hcompact
  have hFTC := intervalIntegral_deriv_eq_sub_of_lipschitzWith
    hlogLip 0 (2 * Real.pi)
  have hradiusClose : radialBoundaryRadius K c (2 * Real.pi) =
      radialBoundaryRadius K c 0 := by
    simp only [radialBoundaryRadius]
    exact congrArg (fun z : ℂ ↦ ‖z - c‖) <| by
      simpa only [zero_add] using radialBoundaryParametrization_periodic K c 0
  rw [hradiusClose, sub_self] at hFTC
  calc
    _ = ∫ t in (0 : ℝ)..(2 * Real.pi),
        deriv (fun s ↦ Real.log (radialBoundaryRadius K c s)) t := by
      apply intervalIntegral.integral_congr_ae
      obtain ⟨Crho, hrho⟩ :=
        exists_lipschitzWith_radialBoundaryRadius hconv hc hcompact
      filter_upwards [hrho.ae_differentiableAt_real] with t ht _
      have hpos := radialBoundaryRadius_pos hconv hc hcompact t
      change deriv (radialBoundaryRadius K c) t /
        radialBoundaryRadius K c t =
          deriv (Real.log ∘ radialBoundaryRadius K c) t
      simpa only [div_eq_mul_inv, mul_comm] using
        ((Real.hasDerivAt_log hpos.ne').comp t ht.hasDerivAt).deriv.symm
    _ = 0 := hFTC

/-- Polar differentiation gives the pointwise winding-density identity
almost everywhere. -/
theorem ae_neg_I_mul_deriv_div_sub_center_eq
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K) :
    ∀ᵐ t : ℝ,
      -Complex.I * deriv (radialBoundaryParametrization K c) t /
          (radialBoundaryParametrization K c t - c) =
        1 - Complex.I *
          (deriv (radialBoundaryRadius K c) t /
            radialBoundaryRadius K c t : ℝ) := by
  obtain ⟨C, hrho⟩ :=
    exists_lipschitzWith_radialBoundaryRadius hconv hc hcompact
  filter_upwards [hrho.ae_differentiableAt_real] with t ht
  let rho := radialBoundaryRadius K c t
  let rho' := deriv (radialBoundaryRadius K c) t
  let u := circleMap 0 1 t
  have hsigma := hasDerivAt_radialBoundaryParametrization
    hconv hc hcompact ht.hasDerivAt
  have hpolar := radialBoundaryParametrization_eq_radius_mul_circleMap
    hconv hc hcompact t
  have hrho : (rho : ℂ) ≠ 0 := by
    exact_mod_cast (radialBoundaryRadius_pos hconv hc hcompact t).ne'
  dsimp only [rho] at hrho
  rw [hsigma.deriv, hpolar]
  simp only [add_sub_cancel_left, Complex.real_smul]
  push_cast
  field_simp [hrho]
  rw [mul_add, ← mul_assoc Complex.I Complex.I, Complex.I_mul_I]
  ring

/-- The scalar winding density is Bochner integrable for the concrete
arclength measure. -/
theorem integrable_normal_div_sub_center_radialBoundary
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K) :
    Integrable
      (fun t ↦ radialOutwardUnitNormal K c t /
        (radialBoundaryParametrization K c t - c))
      (radialBoundaryArcLengthMeasure K c) := by
  let _ : IsFiniteMeasure (radialBoundaryArcLengthMeasure K c) :=
    isFiniteMeasure_radialBoundaryArcLengthMeasure hconv hc hcompact
  obtain ⟨r, R, hr, hrR, hradius⟩ :=
    exists_uniform_bounds_radialBoundaryRadius hconv hc hcompact
  obtain ⟨Cσ, hσ⟩ :=
    exists_lipschitzWith_radialBoundaryParametrization hconv hc hcompact
  have hmeas : Measurable
      (fun t ↦ radialOutwardUnitNormal K c t /
        (radialBoundaryParametrization K c t - c)) :=
    (measurable_radialOutwardUnitNormal K c).div
      (hσ.continuous.sub continuous_const).measurable
  apply Integrable.of_bound hmeas.aestronglyMeasurable (1 / r)
  filter_upwards with t
  rw [norm_div]
  apply div_le_div₀ zero_le_one
    (norm_radialOutwardUnitNormal_le_one K c t) hr
  simpa only [radialBoundaryRadius] using (hradius t).1

/-- One positive radial turn has winding number one around its center. -/
theorem integral_normal_div_sub_center_radialBoundary
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K) :
    ∫ t, radialOutwardUnitNormal K c t /
        (radialBoundaryParametrization K c t - c)
      ∂radialBoundaryArcLengthMeasure K c = (2 * Real.pi : ℝ) := by
  rw [integral_radialBoundaryArcLengthMeasure_eq]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  have hlog := intervalIntegral_deriv_radius_div_radius_eq_zero
    hconv hc hcompact
  have hrhoLip := (exists_lipschitzWith_radialBoundaryRadius
    hconv hc hcompact).choose_spec
  have hratioInt : IntervalIntegrable
      (fun t ↦ deriv (radialBoundaryRadius K c) t /
        radialBoundaryRadius K c t) volume 0 (2 * Real.pi) := by
    exact (intervalIntegrable_deriv_of_lipschitzWith
      hrhoLip 0 (2 * Real.pi)).mul_continuousOn <|
        (hrhoLip.continuous.inv₀ fun t ↦
          (radialBoundaryRadius_pos hconv hc hcompact t).ne').continuousOn
  have hlogC :
      ∫ t in (0 : ℝ)..(2 * Real.pi),
        ((deriv (radialBoundaryRadius K c) t /
          radialBoundaryRadius K c t : ℝ) : ℂ) = 0 := by
    change ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.ofRealCLM
      (deriv (radialBoundaryRadius K c) t /
        radialBoundaryRadius K c t) = 0
    rw [Complex.ofRealCLM.intervalIntegral_comp_comm hratioInt, hlog, map_zero]
  calc
    ∫ t in (0 : ℝ)..(2 * Real.pi),
        radialBoundarySpeed K c t •
          (radialOutwardUnitNormal K c t /
            (radialBoundaryParametrization K c t - c)) =
        ∫ t in (0 : ℝ)..(2 * Real.pi),
          (-Complex.I * deriv (radialBoundaryParametrization K c) t /
            (radialBoundaryParametrization K c t - c)) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards
        [ae_deriv_eq_I_mul_normal_mul_speed hconv hc hcompact]
        with t ht _
      rw [ht]
      simp only [Complex.real_smul]
      field_simp
      simp only [pow_two, Complex.I_mul_I]
      ring
    _ = ∫ t in (0 : ℝ)..(2 * Real.pi),
          (1 - Complex.I *
            ((deriv (radialBoundaryRadius K c) t /
              radialBoundaryRadius K c t : ℝ) : ℂ)) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards
        [ae_neg_I_mul_deriv_div_sub_center_eq hconv hc hcompact]
        with t ht _
      exact ht
    _ = (2 * Real.pi : ℝ) := by
      rw [intervalIntegral.integral_sub]
      · rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
          hlogC, mul_zero, sub_zero]
        norm_num
      · exact intervalIntegrable_const
      · have hcomplexInt : IntervalIntegrable
            (fun t ↦ ((deriv (radialBoundaryRadius K c) t /
              radialBoundaryRadius K c t : ℝ) : ℂ)) volume 0 (2 * Real.pi) :=
          ⟨Complex.ofRealCLM.integrable_comp hratioInt.1,
            Complex.ofRealCLM.integrable_comp hratioInt.2⟩
        exact hcomplexInt.const_mul Complex.I

end DiskRigidity.Operator
