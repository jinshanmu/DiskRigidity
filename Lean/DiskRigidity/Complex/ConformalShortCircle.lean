/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.ConformalArea
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Short images of circles for conformal maps

The length--area method says that a holomorphic injection with bounded image
has circles of arbitrarily small image length at every sufficiently small
scale.  This file contains the precise specialization needed for the direct
convex-domain boundary argument.

The polar-Fubini and length--area calculations follow Tau Ceti's
`MeasureTheory.Integral.CircleLIntegral` and
`Analysis.Complex.Conformal.LengthArea` modules (Apache-2.0), specialized to
the results used here.
-/

open MeasureTheory Metric Set Topology
open scoped ENNReal Real

namespace DiskRigidity.Complex

public section

private theorem rpow_lintegral_le_measure_univ_rpow_mul
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {u : α → ℝ≥0∞}
    (hu : AEMeasurable u μ) {r : ℝ} (hr : 1 ≤ r) :
    (∫⁻ x, u x ∂μ) ^ r ≤ μ univ ^ (r - 1) * ∫⁻ x, u x ^ r ∂μ := by
  have hf : AEStronglyMeasurable u μ := hu.aestronglyMeasurable
  have hr0 : (0 : ℝ) < r := one_pos.trans_le hr
  have hCr : eLpNorm u (ENNReal.ofReal r) μ = (∫⁻ x, u x ^ r ∂μ) ^ (1 / r) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr0) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hr0.le]
    simp only [enorm_eq_self]
  have holder : ∫⁻ x, u x ∂μ ≤
      (∫⁻ x, u x ^ r ∂μ) ^ (1 / r) * μ univ ^ (1 - 1 / r) := by
    have hle : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (f := u) (μ := μ) hle hf
    rw [eLpNorm_one_eq_lintegral_enorm, hCr, ENNReal.toReal_one,
      ENNReal.toReal_ofReal hr0.le, div_one] at h
    simpa only [enorm_eq_self] using h
  have hinv : 1 / r * r = 1 := by field_simp
  have hexp : (1 - 1 / r) * r = r - 1 := by field_simp
  calc
    (∫⁻ x, u x ∂μ) ^ r ≤
        ((∫⁻ x, u x ^ r ∂μ) ^ (1 / r) * μ univ ^ (1 - 1 / r)) ^ r :=
      ENNReal.rpow_le_rpow holder hr0.le
    _ = ((∫⁻ x, u x ^ r ∂μ) ^ (1 / r)) ^ r *
        (μ univ ^ (1 - 1 / r)) ^ r := ENNReal.mul_rpow_of_nonneg _ _ hr0.le
    _ = (∫⁻ x, u x ^ r ∂μ) * μ univ ^ (r - 1) := by
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hinv, hexp, ENNReal.rpow_one]
    _ = μ univ ^ (r - 1) * ∫⁻ x, u x ^ r ∂μ := mul_comm _ _

/-- Arc-length integral of a nonnegative weight over a circle. -/
noncomputable def circleWeightIntegral (g : ℂ → ℝ≥0∞) (ζ : ℂ) (ρ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ρ * ∫⁻ θ in Ioo (-π) π, g (circleMap ζ ρ θ)

private theorem periodic_comp_circleMap (g : ℂ → ℝ≥0∞) (ζ : ℂ) (ρ : ℝ) :
    Function.Periodic (fun θ ↦ g (circleMap ζ ρ θ)) (2 * π) := fun θ ↦
  congrArg g (periodic_circleMap ζ ρ θ)

private theorem lintegral_Ioc_comp_circleMap (g : ℂ → ℝ≥0∞) (ζ : ℂ) (ρ t u : ℝ) :
    ∫⁻ θ in Ioc t (t + 2 * π), g (circleMap ζ ρ θ) =
      ∫⁻ θ in Ioc u (u + 2 * π), g (circleMap ζ ρ θ) :=
  (isAddFundamentalDomain_Ioc Real.two_pi_pos t).setLIntegral_eq
    (isAddFundamentalDomain_Ioc Real.two_pi_pos u) _
    fun v θ ↦ (periodic_comp_circleMap g ζ ρ).map_vadd_zmultiples v θ

/-- The angular interval in `circleWeightIntegral` may be shifted by a full period. -/
theorem circleWeightIntegral_eq_lintegral_Ioc (g : ℂ → ℝ≥0∞) (ζ : ℂ) (ρ t : ℝ) :
    circleWeightIntegral g ζ ρ =
      ENNReal.ofReal ρ * ∫⁻ θ in Ioc t (t + 2 * π), g (circleMap ζ ρ θ) := by
  have hπ : -π + 2 * π = π := by ring
  rw [circleWeightIntegral, ← lintegral_Ioc_comp_circleMap g ζ ρ (-π) t, hπ]
  exact congrArg _ (setLIntegral_congr Ioo_ae_eq_Ioc)

private theorem add_polarCoord_symm_eq_circleMap (ζ : ℂ) (p : ℝ × ℝ) :
    ζ + _root_.Complex.polarCoord.symm p = circleMap ζ p.1 p.2 := by
  simp [circleMap, _root_.Complex.exp_mul_I, ← _root_.Complex.ofReal_cos,
    ← _root_.Complex.ofReal_sin]

private theorem continuous_circleMap_uncurry (ζ : ℂ) :
    Continuous fun p : ℝ × ℝ ↦ circleMap ζ p.1 p.2 := by
  simp only [circleMap]
  fun_prop

private theorem lintegral_circleWeightIntegral_eq_lintegral
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) (ζ : ℂ) :
    ∫⁻ ρ in Ioi (0 : ℝ), circleWeightIntegral g ζ ρ = ∫⁻ z, g z := by
  have hjoint : Measurable fun p : ℝ × ℝ ↦
      ENNReal.ofReal p.1 * g (circleMap ζ p.1 p.2) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul
      (hg.comp (continuous_circleMap_uncurry ζ).measurable)
  calc
    ∫⁻ ρ in Ioi (0 : ℝ), circleWeightIntegral g ζ ρ =
        ∫⁻ ρ in Ioi (0 : ℝ),
          ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal ρ * g (circleMap ζ ρ θ) := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun ρ _ ↦ ?_
      rw [circleWeightIntegral, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
        ENNReal.ofReal p.1 * g (circleMap ζ p.1 p.2) := by
      rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ hjoint.aemeasurable]
    _ = ∫⁻ z, g (ζ + z) := by
      rw [← _root_.Complex.lintegral_comp_polarCoord_symm (fun z ↦ g (ζ + z)),
        _root_.polarCoord_target]
      simp_rw [smul_eq_mul, add_polarCoord_symm_eq_circleMap]
    _ = ∫⁻ z, g z := lintegral_add_left_eq_self g ζ

private theorem sq_lintegral_angle_le {g : ℂ → ℝ≥0∞} {ζ : ℂ} {ρ : ℝ}
    (hg : AEMeasurable (fun θ ↦ g (circleMap ζ ρ θ))
      (volume.restrict (Ioo (-π) π))) :
    (∫⁻ θ in Ioo (-π) π, g (circleMap ζ ρ θ)) ^ 2 ≤
      ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π, g (circleMap ζ ρ θ) ^ 2 := by
  have hvol : (volume.restrict (Ioo (-π) π)) univ = ENNReal.ofReal (2 * π) := by
    rw [Measure.restrict_apply_univ, Real.volume_Ioo]
    ring_nf
  have hpow : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x ^ 2 := fun x ↦ by
    rw [← ENNReal.rpow_natCast x 2]
    norm_num
  have hexp : (2 : ℝ) - 1 = 1 := by norm_num
  have h := rpow_lintegral_le_measure_univ_rpow_mul
    (μ := volume.restrict (Ioo (-π) π))
    (u := fun θ ↦ g (circleMap ζ ρ θ)) hg (r := 2) one_le_two
  rw [hvol, hexp, ENNReal.rpow_one] at h
  simpa only [hpow] using h

private theorem circleWeightIntegral_sq_le {g : ℂ → ℝ≥0∞} (ζ : ℂ) (ρ : ℝ)
    (hg : AEMeasurable (fun θ ↦ g (circleMap ζ ρ θ))
      (volume.restrict (Ioo (-π) π))) :
    circleWeightIntegral g ζ ρ ^ 2 ≤
      ENNReal.ofReal (2 * π * ρ) * circleWeightIntegral (fun z ↦ g z ^ 2) ζ ρ := by
  rcases le_or_gt ρ 0 with hρ | hρ
  · simp [circleWeightIntegral, ENNReal.ofReal_of_nonpos hρ]
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  rw [circleWeightIntegral, circleWeightIntegral, mul_pow, ENNReal.ofReal_mul h2π]
  calc
    ENNReal.ofReal ρ ^ 2 * (∫⁻ θ in Ioo (-π) π, g (circleMap ζ ρ θ)) ^ 2 ≤
        ENNReal.ofReal ρ ^ 2 *
          (ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π, g (circleMap ζ ρ θ) ^ 2) := by
      gcongr
      exact sq_lintegral_angle_le hg
    _ = ENNReal.ofReal (2 * π) * ENNReal.ofReal ρ *
        (ENNReal.ofReal ρ * ∫⁻ θ in Ioo (-π) π, g (circleMap ζ ρ θ) ^ 2) := by
      ring

private theorem lintegral_circleWeightIntegral_sq_div_le_lintegral_sq
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) (ζ : ℂ) :
    ∫⁻ ρ in Ioi (0 : ℝ), circleWeightIntegral g ζ ρ ^ 2 / ENNReal.ofReal ρ ≤
      ENNReal.ofReal (2 * π) * ∫⁻ z, g z ^ 2 := by
  have hstep : ∀ ρ ∈ Ioi (0 : ℝ),
      circleWeightIntegral g ζ ρ ^ 2 / ENNReal.ofReal ρ ≤
        ENNReal.ofReal (2 * π) * circleWeightIntegral (fun z ↦ g z ^ 2) ζ ρ := by
    intro ρ hρ
    have hρ0 : ENNReal.ofReal ρ ≠ 0 := (ENNReal.ofReal_pos.mpr hρ).ne'
    rw [ENNReal.div_le_iff hρ0 ENNReal.ofReal_ne_top]
    refine (circleWeightIntegral_sq_le ζ ρ
      (hg.comp (measurable_circleMap ζ ρ)).aemeasurable).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * π)]
    ring
  calc
    ∫⁻ ρ in Ioi (0 : ℝ), circleWeightIntegral g ζ ρ ^ 2 / ENNReal.ofReal ρ ≤
        ∫⁻ ρ in Ioi (0 : ℝ),
          ENNReal.ofReal (2 * π) * circleWeightIntegral (fun z ↦ g z ^ 2) ζ ρ :=
      setLIntegral_mono' measurableSet_Ioi hstep
    _ = ENNReal.ofReal (2 * π) * ∫⁻ z, g z ^ 2 := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_circleWeightIntegral_eq_lintegral (hg.pow_const 2) ζ]

private theorem lintegral_inv_ofReal_Ioo {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∫⁻ ρ in Ioo r R, (ENNReal.ofReal ρ)⁻¹ = ENNReal.ofReal (Real.log (R / r)) := by
  have hR : 0 < R := hr.trans hrR
  have hcont : ContinuousOn (fun x : ℝ ↦ x⁻¹) (uIcc r R) := by
    refine ContinuousOn.inv₀ continuousOn_id fun x hx ↦ ?_
    rw [uIcc_of_le hrR.le] at hx
    exact ne_of_gt (hr.trans_le hx.1)
  have hint : IntegrableOn (fun x : ℝ ↦ x⁻¹) (Ioo r R) :=
    (hcont.intervalIntegrable).1.mono_set Ioo_subset_Ioc_self
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioo r R)] fun x : ℝ ↦ x⁻¹ := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    exact le_of_lt (inv_pos.mpr (hr.trans hx.1))
  have hval : ∫ x in Ioo r R, x⁻¹ = Real.log (R / r) := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hrR.le]
    exact integral_inv_of_pos hr hR
  rw [← hval, MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn]
  refine setLIntegral_congr_fun measurableSet_Ioo fun x hx ↦ ?_
  rw [ENNReal.ofReal_inv_of_pos (hr.trans hx.1)]

private theorem exists_circleWeightIntegral_sq_lt {g : ℂ → ℝ≥0∞}
    (hg : Measurable g) (ζ : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) {c : ℝ≥0∞}
    (hc : ENNReal.ofReal (2 * π) * (∫⁻ z, g z ^ 2) <
      c * ENNReal.ofReal (Real.log (R / r))) :
    ∃ ρ ∈ Ioo r R, circleWeightIntegral g ζ ρ ^ 2 < c := by
  by_contra hcon
  have hle : ∀ ρ ∈ Ioo r R, c ≤ circleWeightIntegral g ζ ρ ^ 2 := fun ρ hρ ↦
    not_lt.mp fun h ↦ hcon ⟨ρ, hρ, h⟩
  have hconst : ∫⁻ ρ in Ioo r R, c * (ENNReal.ofReal ρ)⁻¹ =
      c * ENNReal.ofReal (Real.log (R / r)) := by
    rw [lintegral_const_mul'' (f := fun ρ : ℝ ↦ (ENNReal.ofReal ρ)⁻¹) c
      ENNReal.measurable_ofReal.inv.aemeasurable, lintegral_inv_ofReal_Ioo hr hrR]
  have hmono : ∫⁻ ρ in Ioo r R, c * (ENNReal.ofReal ρ)⁻¹ ≤
      ∫⁻ ρ in Ioo r R,
        circleWeightIntegral g ζ ρ ^ 2 / ENNReal.ofReal ρ := by
    refine setLIntegral_mono' measurableSet_Ioo fun ρ hρ ↦ ?_
    rw [div_eq_mul_inv]
    gcongr
    exact hle ρ hρ
  have hsub : ∫⁻ ρ in Ioo r R,
      circleWeightIntegral g ζ ρ ^ 2 / ENNReal.ofReal ρ ≤
      ∫⁻ ρ in Ioi (0 : ℝ),
        circleWeightIntegral g ζ ρ ^ 2 / ENNReal.ofReal ρ :=
    lintegral_mono_set fun x hx ↦ hr.trans hx.1
  refine absurd (hc.trans_le ?_) (lt_irrefl _)
  calc
    c * ENNReal.ofReal (Real.log (R / r)) =
        ∫⁻ ρ in Ioo r R, c * (ENNReal.ofReal ρ)⁻¹ := hconst.symm
    _ ≤ ENNReal.ofReal (2 * π) * ∫⁻ z, g z ^ 2 :=
      (hmono.trans hsub).trans (lintegral_circleWeightIntegral_sq_div_le_lintegral_sq hg ζ)

private theorem log_div_mul_exp_neg {R : ℝ} (hR : 0 < R) (L : ℝ) :
    Real.log (R / (R * Real.exp (-L))) = L := by
  have h : R / (R * Real.exp (-L)) = Real.exp L := by
    rw [Real.exp_neg]
    field_simp
  rw [h, Real.log_exp]

private theorem exists_circleWeightIntegral_lt_of_lintegral_sq_ne_top
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) (hfin : (∫⁻ z, g z ^ 2) ≠ ∞)
    (ζ : ℂ) {c : ℝ≥0∞} (hc : c ≠ 0) {R : ℝ} (hR : 0 < R) :
    ∃ ρ ∈ Ioo 0 R, circleWeightIntegral g ζ ρ < c := by
  suffices h : ∀ b : ℝ≥0∞, b ≠ 0 → b ≠ ∞ →
      ∃ ρ ∈ Ioo 0 R, circleWeightIntegral g ζ ρ < b by
    obtain ⟨ρ, hρ, hlt⟩ := h (min c 1) (by simp [hc]) (by simp)
    exact ⟨ρ, hρ, hlt.trans_le (min_le_left c 1)⟩
  intro b hb0 hbtop
  have hAtop : ENNReal.ofReal (2 * π) * ∫⁻ z, g z ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  set A : ℝ := (ENNReal.ofReal (2 * π) * ∫⁻ z, g z ^ 2).toReal
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  set br : ℝ := b.toReal
  have hbr0 : 0 < br := ENNReal.toReal_pos hb0 hbtop
  set L : ℝ := (A + 1) / br ^ 2 with hL
  have hLpos : 0 < L := div_pos (by linarith) (by positivity)
  have hbrL : br ^ 2 * L = A + 1 := by rw [hL]; field_simp
  set r : ℝ := R * Real.exp (-L) with hr
  have hrpos : 0 < r := mul_pos hR (Real.exp_pos _)
  have hrR : r < R := by
    have hexp : Real.exp (-L) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    nlinarith
  have hlog : Real.log (R / r) = L := by rw [hr, log_div_mul_exp_neg hR]
  have hlt : ENNReal.ofReal (2 * π) * ∫⁻ z, g z ^ 2 <
      b ^ 2 * ENNReal.ofReal (Real.log (R / r)) := by
    have hAeq : ENNReal.ofReal (2 * π) * ∫⁻ z, g z ^ 2 = ENNReal.ofReal A :=
      (ENNReal.ofReal_toReal hAtop).symm
    have hbeq : b = ENNReal.ofReal br := (ENNReal.ofReal_toReal hbtop).symm
    rw [hAeq, hbeq, hlog, ← ENNReal.ofReal_pow hbr0.le,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ br ^ 2), hbrL]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  obtain ⟨ρ, hρmem, hρlt⟩ := exists_circleWeightIntegral_sq_lt hg ζ hrpos hrR hlt
  refine ⟨ρ, ⟨hrpos.trans hρmem.1, hρmem.2⟩, ?_⟩
  by_contra hcon
  exact absurd (pow_le_pow_left' (not_lt.mp hcon) 2) (not_le.mpr hρlt)

/-- The derivative-weighted length of the part of a circle selected by `s`. -/
noncomputable def conformalCircleLength
    (f : ℂ → ℂ) (s : Set ℂ) (ζ : ℂ) (ρ : ℝ) : ℝ≥0∞ :=
  circleWeightIntegral (s.indicator fun z ↦ ‖deriv f z‖ₑ) ζ ρ

/-- The defining circle integral for `conformalCircleLength`. -/
theorem conformalCircleLength_def (f : ℂ → ℂ) (s : Set ℂ) (ζ : ℂ) (ρ : ℝ) :
    conformalCircleLength f s ζ ρ =
      circleWeightIntegral (s.indicator fun z ↦ ‖deriv f z‖ₑ) ζ ρ := by
  rw [conformalCircleLength]

private theorem measurable_indicator_enorm_deriv (f : ℂ → ℂ)
    {s : Set ℂ} (hs : MeasurableSet s) :
    Measurable (s.indicator fun z ↦ ‖deriv f z‖ₑ) :=
  (measurable_deriv f).enorm.indicator hs

private theorem lintegral_indicator_enorm_deriv_sq (f : ℂ → ℂ)
    {s : Set ℂ} (hs : MeasurableSet s) :
    ∫⁻ z, s.indicator (fun z ↦ ‖deriv f z‖ₑ) z ^ 2 =
      ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2 := by
  rw [← lintegral_indicator hs]
  refine lintegral_congr fun z ↦ ?_
  by_cases hz : z ∈ s <;> simp [hz]

/-- A conformal injection with bounded image has arbitrarily short selected circles near every
point. -/
theorem exists_conformalCircleLength_lt_of_isBounded {U s : Set ℂ} {f : ℂ → ℂ}
    (hUo : IsOpen U) (hf : DifferentiableOn ℂ f U) (hs : MeasurableSet s) (hsU : s ⊆ U)
    (hinj : InjOn f s) (hb : Bornology.IsBounded (f '' s)) (ζ : ℂ)
    {c : ℝ≥0∞} (hc : c ≠ 0) {R : ℝ} (hR : 0 < R) :
    ∃ ρ ∈ Ioo 0 R, conformalCircleLength f s ζ ρ < c := by
  have hfin : (∫⁻ z, s.indicator (fun z ↦ ‖deriv f z‖ₑ) z ^ 2) ≠ ∞ := by
    rw [lintegral_indicator_enorm_deriv_sq f hs]
    exact lintegral_enorm_deriv_sq_ne_top_of_isBounded hUo hf hs.nullMeasurableSet hsU hinj hb
  obtain ⟨ρ, hρ, hlt⟩ := exists_circleWeightIntegral_lt_of_lintegral_sq_ne_top
    (measurable_indicator_enorm_deriv f hs) hfin ζ hc hR
  exact ⟨ρ, hρ, by rwa [conformalCircleLength_def]⟩

private theorem ofReal_dist_le_mul_lintegral_Ioc {U : Set ℂ} {f : ℂ → ℂ}
    (hUo : IsOpen U) (hf : DifferentiableOn ℂ f U) (ζ : ℂ) {ρ a b : ℝ}
    (hab : a ≤ b) (hmemU : ∀ θ ∈ Icc a b, circleMap ζ ρ θ ∈ U) :
    ENNReal.ofReal (dist (f (circleMap ζ ρ a)) (f (circleMap ζ ρ b))) ≤
      ENNReal.ofReal |ρ| * ∫⁻ θ in Ioc a b, ‖deriv f (circleMap ζ ρ θ)‖ₑ := by
  have hcd : ContDiffOn ℝ 1 (fun θ ↦ f (circleMap ζ ρ θ)) (Icc a b) := fun θ hθ ↦
    (((hf.analyticAt (hUo.mem_nhds (hmemU θ hθ))).contDiffAt.restrict_scalars ℝ).comp θ
      (contDiff_circleMap ζ ρ).contDiffAt).contDiffWithinAt
  have hderiv : ∀ θ ∈ Ioc a b,
      ‖deriv (fun t ↦ f (circleMap ζ ρ t)) θ‖ₑ =
        ENNReal.ofReal |ρ| * ‖deriv f (circleMap ζ ρ θ)‖ₑ := by
    intro θ hθ
    have hmem := hmemU θ (Ioc_subset_Icc_self hθ)
    have h : HasDerivAt (fun t ↦ f (circleMap ζ ρ t))
        ((circleMap 0 ρ θ * Complex.I) • deriv f (circleMap ζ ρ θ)) θ :=
      ((hf _ hmem).differentiableAt (hUo.mem_nhds hmem)).hasDerivAt.scomp θ
        (hasDerivAt_circleMap ζ ρ θ)
    rw [h.deriv, smul_eq_mul, enorm_mul]
    congr 1
    rw [← ofReal_norm, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one]
  calc
    ENNReal.ofReal (dist (f (circleMap ζ ρ a)) (f (circleMap ζ ρ b))) =
        ‖f (circleMap ζ ρ b) - f (circleMap ζ ρ a)‖ₑ := by
      rw [dist_comm, dist_eq_norm, ofReal_norm]
    _ ≤ ∫⁻ θ in Icc a b,
        ‖deriv (fun t ↦ f (circleMap ζ ρ t)) θ‖ₑ :=
      enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hcd hab
    _ = ∫⁻ θ in Ioc a b,
        ‖deriv (fun t ↦ f (circleMap ζ ρ t)) θ‖ₑ := by
      rw [← restrict_Ioc_eq_restrict_Icc]
    _ = ∫⁻ θ in Ioc a b,
        ENNReal.ofReal |ρ| * ‖deriv f (circleMap ζ ρ θ)‖ₑ :=
      setLIntegral_congr_fun measurableSet_Ioc hderiv
    _ = ENNReal.ofReal |ρ| * ∫⁻ θ in Ioc a b,
        ‖deriv f (circleMap ζ ρ θ)‖ₑ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The chord across a selected circular arc is at most its conformal image length. -/
theorem ofReal_dist_le_conformalCircleLength {U s : Set ℂ} {f : ℂ → ℂ}
    (hUo : IsOpen U) (hf : DifferentiableOn ℂ f U) (ζ : ℂ) {ρ a b : ℝ}
    (hρ : 0 < ρ) (hab : a ≤ b) (hb : b ≤ a + 2 * π)
    (hmem : ∀ θ ∈ Icc a b, circleMap ζ ρ θ ∈ s)
    (hmemU : ∀ θ ∈ Icc a b, circleMap ζ ρ θ ∈ U) :
    ENNReal.ofReal (dist (f (circleMap ζ ρ a)) (f (circleMap ζ ρ b))) ≤
      conformalCircleLength f s ζ ρ := by
  rw [conformalCircleLength_def,
    circleWeightIntegral_eq_lintegral_Ioc (s.indicator fun z ↦ ‖deriv f z‖ₑ) ζ ρ a]
  have hchord := ofReal_dist_le_mul_lintegral_Ioc hUo hf ζ hab hmemU
  rw [abs_of_pos hρ] at hchord
  refine hchord.trans ?_
  have hInt : ∫⁻ θ in Ioc a b, ‖deriv f (circleMap ζ ρ θ)‖ₑ ≤
      ∫⁻ θ in Ioc a (a + 2 * π),
        s.indicator (fun z ↦ ‖deriv f z‖ₑ) (circleMap ζ ρ θ) := by
    rw [← lintegral_indicator measurableSet_Ioc,
      ← lintegral_indicator measurableSet_Ioc]
    refine lintegral_mono fun θ ↦ ?_
    by_cases hθ : θ ∈ Ioc a b
    · have hθbig : θ ∈ Ioc a (a + 2 * π) := ⟨hθ.1, hθ.2.trans hb⟩
      simp [hθ, hθbig, hmem θ (Ioc_subset_Icc_self hθ)]
    · simp [hθ]
  simpa only [mul_comm] using (mul_le_mul_left hInt (ENNReal.ofReal ρ))

private theorem exists_mem_Icc_circleMap_eq_local {c : ℂ} {ρ : ℝ} (α : ℝ) {z : ℂ}
    (hz : z ∈ sphere c ρ) :
    ∃ t ∈ Icc (-π) π, circleMap c ρ (α + t) = z := by
  have hρ : 0 ≤ ρ := nonneg_of_mem_sphere hz
  have hmem : z ∈ circleMap c ρ '' Icc (α - π) (α - π + 2 * π) := by
    rw [(periodic_circleMap c ρ).image_Icc Real.two_pi_pos, range_circleMap,
      abs_of_nonneg hρ]
    exact hz
  obtain ⟨θ, hθ, rfl⟩ := hmem
  refine ⟨θ - α, ?_, by congr 1; ring⟩
  constructor <;> linarith [hθ.1, hθ.2]

private theorem dist_circleMap_sq_local (c d : ℂ) (ρ θ : ℝ) :
    dist (circleMap c ρ θ) d ^ 2 =
      ρ ^ 2 + dist c d ^ 2 - 2 * ρ * dist c d * Real.cos (θ - (d - c).arg) := by
  have hdist : dist c d = ‖d - c‖ := by rw [dist_eq_norm, norm_sub_rev]
  have hsub : circleMap c ρ θ - d =
      (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - (d - c) := by
    simp only [circleMap]
    ring
  have hconj : (starRingEnd ℂ) (d - c) =
      ((‖d - c‖ : ℝ) : ℂ) * Complex.exp (((-(d - c).arg : ℝ) : ℂ) * Complex.I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (d - c)]
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    push_cast
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hre : ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) *
      (starRingEnd ℂ) (d - c)).re =
      ρ * ‖d - c‖ * Real.cos (θ - (d - c).arg) := by
    have hmul : (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) *
        (starRingEnd ℂ) (d - c) =
        ((ρ * ‖d - c‖ : ℝ) : ℂ) *
          Complex.exp (((θ - (d - c).arg : ℝ) : ℂ) * Complex.I) := by
      rw [hconj, mul_mul_mul_comm, ← Complex.exp_add]
      push_cast
      ring_nf
    rw [hmul, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hunit : Complex.normSq ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = ρ ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I]
    ring
  rw [dist_eq_norm, Complex.sq_norm, hsub, Complex.normSq_sub, hunit, hre,
    Complex.normSq_eq_norm_sq, hdist]
  ring

private theorem circleMap_mem_ball_iff_sq_local {c ζ : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (ρ θ : ℝ) :
    circleMap ζ ρ θ ∈ ball c r ↔
      ρ ^ 2 + dist ζ c ^ 2 - r ^ 2 <
        2 * ρ * dist ζ c * Real.cos (θ - (c - ζ).arg) := by
  rw [mem_ball, ← sq_lt_sq₀ dist_nonneg hr, dist_circleMap_sq_local]
  constructor <;> intro h <;> linarith

private theorem lt_cos_of_mem_Icc_local {k a b θ : ℝ}
    (ha : -π ≤ a) (hb : b ≤ π) (hθ : θ ∈ Icc a b)
    (hka : k < Real.cos a) (hkb : k < Real.cos b) : k < Real.cos θ := by
  rcases le_total θ 0 with hθ0 | h0θ
  · have hcos : Real.cos a ≤ Real.cos θ := by
      rw [← Real.cos_neg a, ← Real.cos_neg θ]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith [hθ.1])
    exact hka.trans_le hcos
  · have hcos : Real.cos b ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi h0θ hb hθ.2
    exact hkb.trans_le hcos

private theorem circleMap_mem_ball_of_mem_Icc_local {c ζ : ℂ} {r ρ : ℝ}
    (hρ : 0 ≤ ρ) {a b θ : ℝ}
    (ha : -π ≤ a - (c - ζ).arg) (hb : b - (c - ζ).arg ≤ π)
    (hθ : θ ∈ Icc a b) (hain : circleMap ζ ρ a ∈ ball c r)
    (hbin : circleMap ζ ρ b ∈ ball c r) : circleMap ζ ρ θ ∈ ball c r := by
  have hr : 0 < r := dist_nonneg.trans_lt (mem_ball.mp hain)
  rw [circleMap_mem_ball_iff_sq_local hr.le] at hain hbin ⊢
  have hnn : (0 : ℝ) ≤ 2 * ρ * dist ζ c := mul_nonneg (by positivity) dist_nonneg
  rcases hnn.eq_or_lt with hd | hpos
  · rw [← hd] at hain ⊢
    linarith
  · have hkey : ∀ x : ℝ,
        (ρ ^ 2 + dist ζ c ^ 2 - r ^ 2 <
          2 * ρ * dist ζ c * Real.cos (x - (c - ζ).arg)) ↔
        (ρ ^ 2 + dist ζ c ^ 2 - r ^ 2) / (2 * ρ * dist ζ c) <
          Real.cos (x - (c - ζ).arg) := fun x ↦ by
      rw [div_lt_iff₀ hpos, mul_comm]
    rw [hkey] at hain hbin ⊢
    exact lt_cos_of_mem_Icc_local ha hb
      ⟨by linarith [hθ.1], by linarith [hθ.2]⟩ hain hbin

/-- Any two values on the intersection of a disc with a circle are separated by at most the
derivative-weighted length of the selected circle. -/
theorem ofReal_dist_le_conformalCircleLength_of_mem_ball_inter_sphere
    {f : ℂ → ℂ} {c ζ : ℂ} {r ρ : ℝ}
    (hf : DifferentiableOn ℂ f (ball c r)) {z w : ℂ}
    (hz : z ∈ ball c r ∩ sphere ζ ρ) (hw : w ∈ ball c r ∩ sphere ζ ρ) :
    ENNReal.ofReal (dist (f z) (f w)) ≤
      conformalCircleLength f (ball c r) ζ ρ := by
  rcases (nonneg_of_mem_sphere hz.2).eq_or_lt with hρ | hρ
  · have hzζ : z = ζ := by simpa [← hρ] using hz.2
    have hwζ : w = ζ := by simpa [← hρ] using hw.2
    simp [hzζ, hwζ]
  suffices h : ∀ z' w' : ℂ,
      z' ∈ ball c r ∩ sphere ζ ρ → w' ∈ ball c r ∩ sphere ζ ρ →
      ∀ t₁ ∈ Icc (-π) π, ∀ t₂ ∈ Icc (-π) π, t₁ ≤ t₂ →
      circleMap ζ ρ ((c - ζ).arg + t₁) = z' →
      circleMap ζ ρ ((c - ζ).arg + t₂) = w' →
      ENNReal.ofReal (dist (f z') (f w')) ≤
        conformalCircleLength f (ball c r) ζ ρ by
    obtain ⟨t₁, ht₁, hz'⟩ := exists_mem_Icc_circleMap_eq_local (c - ζ).arg hz.2
    obtain ⟨t₂, ht₂, hw'⟩ := exists_mem_Icc_circleMap_eq_local (c - ζ).arg hw.2
    rcases le_total t₁ t₂ with hle | hle
    · exact h z w hz hw t₁ ht₁ t₂ ht₂ hle hz' hw'
    · rw [dist_comm]
      exact h w z hw hz t₂ ht₂ t₁ ht₁ hle hw' hz'
  rintro z' w' hz' hw' t₁ ht₁ t₂ ht₂ hle rfl rfl
  have harc : ∀ θ ∈ Icc ((c - ζ).arg + t₁) ((c - ζ).arg + t₂),
      circleMap ζ ρ θ ∈ ball c r := fun θ hθ ↦
    circleMap_mem_ball_of_mem_Icc_local hρ.le
      (by rw [add_sub_cancel_left]; exact ht₁.1)
      (by rw [add_sub_cancel_left]; exact ht₂.2) hθ hz'.1 hw'.1
  exact ofReal_dist_le_conformalCircleLength isOpen_ball hf ζ hρ (by linarith)
    (by linarith [ht₁.1, ht₂.2, Real.pi_pos]) harc harc

/-- A bound on conformal circle length bounds the diameter of the corresponding disc crosscut. -/
theorem diam_image_ball_inter_sphere_le
    {f : ℂ → ℂ} {c ζ : ℂ} {r ρ ε : ℝ}
    (hf : DifferentiableOn ℂ f (ball c r)) (hε : 0 ≤ ε)
    (hlen : conformalCircleLength f (ball c r) ζ ρ ≤ ENNReal.ofReal ε) :
    diam (f '' (ball c r ∩ sphere ζ ρ)) ≤ ε := by
  refine diam_le_of_forall_dist_le hε ?_
  rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
  exact (ENNReal.ofReal_le_ofReal_iff hε).mp
    ((ofReal_dist_le_conformalCircleLength_of_mem_ball_inter_sphere hf hz hw).trans hlen)

/-- A conformal map of a disc onto a bounded set has crosscuts of arbitrarily small image
diameter at every boundary scale. -/
theorem exists_diam_image_ball_inter_sphere_le
    {f : ℂ → ℂ} {c ζ : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : Bornology.IsBounded (f '' ball c r)) {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    ∃ ρ ∈ Ioo 0 R, diam (f '' (ball c r ∩ sphere ζ ρ)) ≤ ε := by
  obtain ⟨ρ, hρ, hlen⟩ := exists_conformalCircleLength_lt_of_isBounded isOpen_ball hf
    measurableSet_ball subset_rfl hinj hb ζ (ENNReal.ofReal_pos.mpr hε).ne' hR
  exact ⟨ρ, hρ, diam_image_ball_inter_sphere_le hf hε.le hlen.le⟩

end

end DiskRigidity.Complex
