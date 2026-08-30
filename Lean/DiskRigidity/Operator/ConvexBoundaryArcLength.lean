/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.ConvexBoundarySupport
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Arclength measure for the radial convex-boundary parametrization

The arclength measure is the speed-weighted Lebesgue measure on one period
`[0, 2π]`.  It is finite, and all almost-everywhere geometric identities
for the radial curve transfer to it.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set Topology
open scoped ENNReal InnerProductSpace NNReal Pointwise

namespace DiskRigidity.Operator

/-- Lebesgue measure on one closed parameter period. -/
def radialBoundaryParameterMeasure : Measure ℝ :=
  volume.restrict (Set.Icc 0 (2 * Real.pi))

/-- Speed-weighted parameter measure, i.e. arclength along one turn of the
convex boundary. -/
def radialBoundaryArcLengthMeasure (K : Set ℂ) (c : ℂ) : Measure ℝ :=
  radialBoundaryParameterMeasure.withDensity
    (fun t ↦ ENNReal.ofReal (radialBoundarySpeed K c t))

/-- The boundary speed has finite integral on one parameter period. -/
theorem hasFiniteIntegral_radialBoundarySpeed
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K) :
    HasFiniteIntegral (radialBoundarySpeed K c)
      radialBoundaryParameterMeasure := by
  let _ : IsFiniteMeasure radialBoundaryParameterMeasure := by
    rw [radialBoundaryParameterMeasure]
    infer_instance
  obtain ⟨C, hC⟩ :=
    exists_lipschitzWith_radialBoundaryParametrization hconv hc hcompact
  apply HasFiniteIntegral.of_bounded (C := (C : ℝ))
  exact Filter.Eventually.of_forall fun t ↦ by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ radialBoundarySpeed K c t from norm_nonneg _)]
    exact norm_deriv_le_of_lipschitz hC

/-- Arclength of the rectifiable convex boundary is finite. -/
theorem isFiniteMeasure_radialBoundaryArcLengthMeasure
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K) :
    IsFiniteMeasure (radialBoundaryArcLengthMeasure K c) := by
  apply isFiniteMeasure_withDensity_ofReal
  exact hasFiniteIntegral_radialBoundarySpeed hconv hc hcompact

/-- Any Lebesgue-a.e. identity transfers to the speed-weighted measure on
one period. -/
theorem ae_radialBoundaryArcLengthMeasure_of_ae_volume
    {K : Set ℂ} {c : ℂ} {P : ℝ → Prop}
    (hP : ∀ᵐ t ∂volume, P t) :
    ∀ᵐ t ∂radialBoundaryArcLengthMeasure K c, P t := by
  apply (withDensity_absolutelyContinuous radialBoundaryParameterMeasure
    (fun t ↦ ENNReal.ofReal (radialBoundarySpeed K c t))).ae_le
  exact ae_restrict_of_ae hP

/-- The arclength measure is supported on the chosen parameter period. -/
theorem ae_mem_Icc_radialBoundaryArcLengthMeasure (K : Set ℂ) (c : ℂ) :
    ∀ᵐ t ∂radialBoundaryArcLengthMeasure K c,
      t ∈ Set.Icc 0 (2 * Real.pi) := by
  apply (withDensity_absolutelyContinuous radialBoundaryParameterMeasure
    (fun t ↦ ENNReal.ofReal (radialBoundarySpeed K c t))).ae_le
  exact ae_restrict_mem measurableSet_Icc

/-- The constructed outward normal is unit arclength-almost everywhere. -/
theorem ae_norm_radialOutwardUnitNormal_eq_one_arcLength
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K) :
    ∀ᵐ t ∂radialBoundaryArcLengthMeasure K c,
      ‖radialOutwardUnitNormal K c t‖ = 1 :=
  ae_radialBoundaryArcLengthMeasure_of_ae_volume
    (ae_norm_radialOutwardUnitNormal_eq_one hconv hc hcompact)

/-- The supporting-half-plane property holds arclength-almost everywhere. -/
theorem ae_radialOutwardUnitNormal_supports_arcLength
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K) :
    ∀ᵐ t ∂radialBoundaryArcLengthMeasure K c, ∀ w ∈ K,
      (star (radialOutwardUnitNormal K c t) * w).re ≤
        (star (radialOutwardUnitNormal K c t) *
          radialBoundaryParametrization K c t).re :=
  ae_radialBoundaryArcLengthMeasure_of_ae_volume
    (ae_radialOutwardUnitNormal_supports hconv hc hcompact)

/-- The exact differential relation `dσ = i ν ds` holds
arclength-almost everywhere in the parameter. -/
theorem ae_deriv_eq_I_mul_normal_mul_speed_arcLength
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K) :
    ∀ᵐ t ∂radialBoundaryArcLengthMeasure K c,
      deriv (radialBoundaryParametrization K c) t =
        Complex.I * radialOutwardUnitNormal K c t *
          radialBoundarySpeed K c t :=
  ae_radialBoundaryArcLengthMeasure_of_ae_volume
    (ae_deriv_eq_I_mul_normal_mul_speed hconv hc hcompact)

/-- Integration against arclength is speed-weighted integration over one
closed parameter period. -/
theorem integral_radialBoundaryArcLengthMeasure_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set ℂ) (c : ℂ) (F : ℝ → E) :
    ∫ t, F t ∂radialBoundaryArcLengthMeasure K c =
      ∫ t in Set.Icc 0 (2 * Real.pi),
        radialBoundarySpeed K c t • F t := by
  rw [radialBoundaryArcLengthMeasure,
    integral_withDensity_eq_integral_toReal_smul]
  · apply integral_congr_ae
    filter_upwards with t
    rw [ENNReal.toReal_ofReal (show 0 ≤ radialBoundarySpeed K c t from norm_nonneg _)]
  · exact (measurable_radialBoundarySpeed K c).ennreal_ofReal
  · exact Filter.Eventually.of_forall fun t ↦ ENNReal.ofReal_lt_top

end DiskRigidity.Operator
