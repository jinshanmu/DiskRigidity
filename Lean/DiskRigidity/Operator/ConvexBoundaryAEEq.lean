/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.ConvexBoundaryArcLength
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# From arclength-almost-everywhere to pointwise boundary identities

The radial convex-boundary parametrization has nonzero speed almost
everywhere.  Consequently its speed-weighted arclength measure has exactly
the same null sets as Lebesgue measure on one parameter period.  Continuous
boundary identities that hold arclength-almost everywhere therefore hold at
every parameter value in that period.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Topology
open scoped ENNReal

namespace DiskRigidity.Operator

/-- Speed-weighted radial arclength and Lebesgue measure restricted to one
full parameter period have the same almost-everywhere equalities. -/
theorem ae_eq_radialBoundaryArcLength_iff_ae_eq_parameterMeasure
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    {E : Type*} {f g : ℝ → E} :
    f =ᵐ[radialBoundaryArcLengthMeasure K c] g ↔
      f =ᵐ[radialBoundaryParameterMeasure] g := by
  have hspeed : ∀ᵐ t ∂radialBoundaryParameterMeasure,
      ENNReal.ofReal (radialBoundarySpeed K c t) ≠ 0 := by
    apply ae_restrict_of_ae
    filter_upwards
      [ae_differentiableAt_radialBoundaryParametrization_and_deriv_ne_zero
        hconv hc hcompact] with t ht
    rw [ENNReal.ofReal_ne_zero_iff]
    simpa only [radialBoundarySpeed] using norm_pos_iff.mpr ht.2
  exact withDensity_ae_eq
    (measurable_radialBoundarySpeed K c).ennreal_ofReal.aemeasurable hspeed

/-- A continuous identity which holds radial-arclength-almost everywhere
holds pointwise throughout the chosen closed parameter period. -/
theorem eqOn_Icc_of_ae_eq_radialBoundaryArcLength
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    {E : Type*} [TopologicalSpace E] [T2Space E] {f g : ℝ → E}
    (hfg : f =ᵐ[radialBoundaryArcLengthMeasure K c] g)
    (hf : ContinuousOn f (Icc (0 : ℝ) (2 * Real.pi)))
    (hg : ContinuousOn g (Icc (0 : ℝ) (2 * Real.pi))) :
    EqOn f g (Icc (0 : ℝ) (2 * Real.pi)) := by
  have hparameter : f =ᵐ[radialBoundaryParameterMeasure] g :=
    (ae_eq_radialBoundaryArcLength_iff_ae_eq_parameterMeasure
      hconv hc hcompact).mp hfg
  have hvolume : f =ᵐ[volume.restrict (Icc (0 : ℝ) (2 * Real.pi))] g := by
    simpa only [radialBoundaryParameterMeasure] using hparameter
  exact Measure.eqOn_Icc_of_ae_eq volume Real.two_pi_pos.ne hvolume hf hg

/-- A continuous identity on the convex boundary that holds after radial
parametrization almost everywhere holds at every boundary point. -/
theorem eqOn_frontier_of_ae_eq_radialBoundaryParametrization
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    {E : Type*} [TopologicalSpace E] [T2Space E] {f g : ℂ → E}
    (hfg :
      (fun t ↦ f (radialBoundaryParametrization K c t))
        =ᵐ[radialBoundaryArcLengthMeasure K c]
          fun t ↦ g (radialBoundaryParametrization K c t))
    (hf : ContinuousOn f (frontier K))
    (hg : ContinuousOn g (frontier K)) :
    EqOn f g (frontier K) := by
  let sigma : ℝ → ℂ := radialBoundaryParametrization K c
  have hsigma : Continuous sigma := by
    exact (exists_lipschitzWith_radialBoundaryParametrization
      hconv hc hcompact).choose_spec.continuous
  have hcompF : ContinuousOn (f ∘ sigma) (Icc (0 : ℝ) (2 * Real.pi)) := by
    exact hf.comp hsigma.continuousOn fun t _ ↦
      radialBoundaryParametrization_mem_frontier hconv hc hcompact t
  have hcompG : ContinuousOn (g ∘ sigma) (Icc (0 : ℝ) (2 * Real.pi)) := by
    exact hg.comp hsigma.continuousOn fun t _ ↦
      radialBoundaryParametrization_mem_frontier hconv hc hcompact t
  have hall := eqOn_Icc_of_ae_eq_radialBoundaryArcLength
    hconv hc hcompact hfg hcompF hcompG
  intro z hz
  obtain ⟨t, ht⟩ := Set.ext_iff.mp
    (range_radialBoundaryParametrization hconv hc hcompact) z |>.mpr hz
  obtain ⟨u, hu, hut⟩ :=
    (radialBoundaryParametrization_periodic K c).exists_mem_Ico₀
      Real.two_pi_pos t
  have huIcc : u ∈ Icc (0 : ℝ) (2 * Real.pi) := ⟨hu.1, hu.2.le⟩
  have hsigmaU : sigma u = z := by
    change radialBoundaryParametrization K c u = z
    exact hut.symm.trans ht
  have heq := hall huIcc
  change f (sigma u) = g (sigma u) at heq
  exact hsigmaU ▸ heq

/-- Local form of the preceding continuity upgrade.  An almost-everywhere
identity needed only above an open boundary neighborhood holds at every
interior parameter value above that neighborhood. -/
theorem eq_of_ae_eq_on_open_radialBoundaryNeighborhood
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    {E : Type*} [TopologicalSpace E] [T2Space E] {f g : ℂ → E}
    {O : Set ℂ} (hO : IsOpen O)
    (hfg : ∀ᵐ t ∂radialBoundaryArcLengthMeasure K c,
      radialBoundaryParametrization K c t ∈ O →
        f (radialBoundaryParametrization K c t) =
          g (radialBoundaryParametrization K c t))
    (hf : ContinuousOn f (frontier K))
    (hg : ContinuousOn g (frontier K))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (2 * Real.pi))
    (htO : radialBoundaryParametrization K c t ∈ O) :
    f (radialBoundaryParametrization K c t) =
      g (radialBoundaryParametrization K c t) := by
  let sigma : ℝ → ℂ := radialBoundaryParametrization K c
  have hsigma : Continuous sigma :=
    (exists_lipschitzWith_radialBoundaryParametrization
      hconv hc hcompact).choose_spec.continuous
  have hspeed : ∀ᵐ u ∂radialBoundaryParameterMeasure,
      ENNReal.ofReal (radialBoundarySpeed K c u) ≠ 0 := by
    apply ae_restrict_of_ae
    filter_upwards
      [ae_differentiableAt_radialBoundaryParametrization_and_deriv_ne_zero
        hconv hc hcompact] with u hu
    rw [ENNReal.ofReal_ne_zero_iff]
    simpa only [radialBoundarySpeed] using norm_pos_iff.mpr hu.2
  have hparameter : ∀ᵐ u ∂radialBoundaryParameterMeasure,
      sigma u ∈ O → f (sigma u) = g (sigma u) := by
    exact Measure.AbsolutelyContinuous.ae_le
      (withDensity_absolutelyContinuous'
        (measurable_radialBoundarySpeed K c).ennreal_ofReal.aemeasurable
        hspeed) hfg
  have hvolume : ∀ᵐ u ∂volume,
      u ∈ Icc (0 : ℝ) (2 * Real.pi) →
      sigma u ∈ O → f (sigma u) = g (sigma u) := by
    rw [radialBoundaryParameterMeasure,
      ae_restrict_iff' measurableSet_Icc] at hparameter
    exact hparameter
  let U : Set ℝ := Ioo (0 : ℝ) (2 * Real.pi) ∩ sigma ⁻¹' O
  have hUopen : IsOpen U := isOpen_Ioo.inter (hO.preimage hsigma)
  have hrestricted :
      (f ∘ sigma) =ᵐ[volume.restrict U] (g ∘ sigma) := by
    change ∀ᵐ u ∂volume.restrict U,
      (f ∘ sigma) u = (g ∘ sigma) u
    rw [ae_restrict_iff' hUopen.measurableSet]
    filter_upwards [hvolume] with u hu
    intro huU
    exact hu ⟨huU.1.1.le, huU.1.2.le⟩ huU.2
  have heq : EqOn (f ∘ sigma) (g ∘ sigma) U :=
    Measure.eqOn_open_of_ae_eq hrestricted hUopen
      (hf.comp hsigma.continuousOn fun u _ ↦
        radialBoundaryParametrization_mem_frontier hconv hc hcompact u)
      (hg.comp hsigma.continuousOn fun u _ ↦
        radialBoundaryParametrization_mem_frontier hconv hc hcompact u)
  exact heq ⟨ht, htO⟩

end DiskRigidity.Operator
