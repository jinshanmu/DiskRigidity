/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.NumericalRangeAnalyticArc
public import DiskRigidity.Operator.ConvexBoundaryArcLength
public import DiskRigidity.Operator.NumericalRangeConvexity
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Unique exposure by radial normals on a curved numerical-range arc

On the strictly curved affine arc, the radial arclength normal agrees with
the unique affine supporting direction.  Consequently the radial normal
also exposes exactly one point there.
-/

noncomputable section

open Filter Function MeasureTheory Metric Set Topology
open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator Real

namespace DiskRigidity.Complex

@[expose] public section

namespace NumericalRangeArc

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The radial boundary construction is a homeomorphism from the unit
circle to the frontier of a compact convex body with an interior basepoint.
This is the topological form of the gauge-rescaling construction behind the
angular parametrization. -/
def radialBoundaryHomeomorph
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K) :
    sphere (0 : ℂ) 1 ≃ₜ frontier K := by
  let S := Operator.centeredConvexBody K c
  let e₀ : ℂ ≃ₜ ℂ := gaugeRescaleHomeomorph (ball (0 : ℂ) 1) S
    (convex_ball 0 1) (ball_mem_nhds 0 zero_lt_one)
    (NormedSpace.isVonNBounded_ball ℝ ℂ 1)
    (Operator.convex_centeredConvexBody hconv)
    (Operator.centeredConvexBody_mem_nhds_zero hc)
    (Operator.centeredConvexBody_isVonNBounded hcompact)
  let e : ℂ ≃ₜ ℂ := e₀.trans (Homeomorph.addLeft c)
  have himage : e '' sphere (0 : ℂ) 1 = frontier K := by
    calc
      e '' sphere (0 : ℂ) 1 =
          Operator.radialBoundaryPoint K c '' sphere (0 : ℂ) 1 := by
        apply image_congr
        intro u _
        rfl
      _ = frontier K :=
        Operator.image_radialBoundaryPoint_sphere hconv hc hcompact
  exact (e.image (sphere (0 : ℂ) 1)).trans (Homeomorph.setCongr himage)

/-- The metric unit sphere in `ℂ` and the bundled multiplicative circle are
the same topological subspace. -/
def unitSphereCircleHomeomorph : sphere (0 : ℂ) 1 ≃ₜ Circle :=
  Homeomorph.setCongr (by rfl)

/-- The derivative of the affine boundary parametrization.  Analyticity of
the parametrization itself recovers the needed differentiability of the
support function and its first derivative. -/
theorem hasDerivAt_affineBoundaryPoint_of_analyticAt
    (A : Operator.SquareMatrix n) {u : ℝ}
    (hana : AnalyticAt ℝ (affineBoundaryPoint A) u) :
    HasDerivAt (affineBoundaryPoint A)
      (((-u * deriv (deriv (affineNumericalRangeSupport A)) u : ℝ) : ℂ) -
        Complex.I *
          ((deriv (deriv (affineNumericalRangeSupport A)) u : ℝ) : ℂ)) u := by
  let h := affineNumericalRangeSupport A
  let gamma := affineBoundaryPoint A
  have hgre : AnalyticAt ℝ (fun v ↦ (gamma v).re) u :=
    (Complex.reCLM.analyticAt (gamma u)).comp hana
  have hgim : AnalyticAt ℝ (fun v ↦ (gamma v).im) u :=
    (Complex.imCLM.analyticAt (gamma u)).comp hana
  have hhEq : (fun v ↦ (gamma v).re - v * (gamma v).im) = h := by
    funext v
    simp [gamma, affineBoundaryPoint, h]
  have hh : AnalyticAt ℝ h u := by
    rw [← hhEq]
    exact hgre.sub (analyticAt_id.mul hgim)
  have hdEq : (fun v ↦ -(gamma v).im) = deriv h := by
    funext v
    simp [gamma, affineBoundaryPoint, h]
  have hd : AnalyticAt ℝ (deriv h) u := by
    rw [← hdEq]
    exact hgim.neg
  have hhDeriv : HasDerivAt h (deriv h u) u :=
    hh.differentiableAt.hasDerivAt
  have hdDeriv : HasDerivAt (deriv h) (deriv (deriv h) u) u :=
    hd.differentiableAt.hasDerivAt
  change HasDerivAt (fun v ↦
    (((h v - v * deriv h v : ℝ) : ℂ) -
      Complex.I * ((deriv h v : ℝ) : ℂ)))
        (((-u * deriv (deriv h) u : ℝ) : ℂ) -
          Complex.I * ((deriv (deriv h) u : ℝ) : ℂ)) u
  convert (hhDeriv.sub ((hasDerivAt_id (𝕜 := ℝ) u).mul hdDeriv)).ofReal_comp.sub
    ((hasDerivAt_const u Complex.I).mul hdDeriv.ofReal_comp) using 1
  · rfl
  · funext v
    rfl
  · simp [id]

/-- If the affine support graph has positive curvature at `u`, then every
nonzero supporting normal at its boundary point is a positive multiple of
the affine normal `(1, -u)`.  Hence a radial supporting normal inherits the
unique-exposure property of that affine normal. -/
theorem radial_normal_uniquely_exposes_affineBoundaryPoint
    (A : Operator.SquareMatrix n) {c : ℂ} {s u : ℝ}
    (hc : c ∈ interior (Operator.numericalRange A))
    (hana : AnalyticAt ℝ (affineBoundaryPoint A) u)
    (hcurv : 0 < deriv (deriv (affineNumericalRangeSupport A)) u)
    (hmem : ∀ᶠ v in 𝓝 u,
      affineBoundaryPoint A v ∈ Operator.numericalRange A)
    (hfront : affineBoundaryPoint A u ∈
      frontier (Operator.numericalRange A))
    (hunique : ∀ z ∈ Operator.numericalRange A,
      affineSupportValue u z =
        affineSupportValue u (affineBoundaryPoint A u) →
      z = affineBoundaryPoint A u)
    (hsupport : ∀ w ∈ Operator.numericalRange A,
      (star (Operator.radialOutwardUnitNormal
        (Operator.numericalRange A) c s) * w).re ≤
      (star (Operator.radialOutwardUnitNormal
        (Operator.numericalRange A) c s) *
          Operator.radialBoundaryParametrization
            (Operator.numericalRange A) c s).re)
    (hnorm : ‖Operator.radialOutwardUnitNormal
      (Operator.numericalRange A) c s‖ = 1)
    (hpoint : Operator.radialBoundaryParametrization
      (Operator.numericalRange A) c s = affineBoundaryPoint A u) :
    ∀ z ∈ Operator.numericalRange A,
      (star (Operator.radialOutwardUnitNormal
        (Operator.numericalRange A) c s) * z).re =
        (star (Operator.radialOutwardUnitNormal
          (Operator.numericalRange A) c s) *
            Operator.radialBoundaryParametrization
              (Operator.numericalRange A) c s).re →
      z = Operator.radialBoundaryParametrization
        (Operator.numericalRange A) c s := by
  let K := Operator.numericalRange A
  let gamma := affineBoundaryPoint A
  let nu := Operator.radialOutwardUnitNormal K c s
  let p := gamma u
  let h₂ := deriv (deriv (affineNumericalRangeSupport A)) u
  have hgamma : HasDerivAt gamma
      (((-u * h₂ : ℝ) : ℂ) - Complex.I * ((h₂ : ℝ) : ℂ)) u := by
    exact hasDerivAt_affineBoundaryPoint_of_analyticAt A hana
  have hgre : HasDerivAt (fun v ↦ (gamma v).re) (-u * h₂) u := by
    simpa only [Function.comp_apply, Complex.reCLM_apply, Complex.sub_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero] using!
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hgamma
  have hgim : HasDerivAt (fun v ↦ (gamma v).im) (-h₂) u := by
    simpa only [Function.comp_apply, Complex.imCLM_apply, Complex.sub_im,
      Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, one_mul, zero_sub, zero_add] using!
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt u hgamma
  let q : ℝ → ℝ := fun v ↦
    nu.re * (gamma v).re + nu.im * (gamma v).im
  have hnuGamma : HasDerivAt q
      (nu.re * (-u * h₂) + nu.im * (-h₂)) u := by
    apply ((hgre.const_mul nu.re).add (hgim.const_mul nu.im)).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun v ↦ by rfl
  have hlocal : IsLocalMax q u := by
    filter_upwards [hmem] with v hv
    simpa [q, nu, gamma, K, hpoint, Complex.star_def,
      Complex.mul_re] using hsupport (gamma v) hv
  have hzero := hlocal.hasDerivAt_eq_zero hnuGamma
  have hrelation : nu.im = -u * nu.re := by
    change 0 < h₂ at hcurv
    nlinarith
  have hnure : nu.re ≠ 0 := by
    intro hre
    have him : nu.im = 0 := by simp [hrelation, hre]
    have hnu : nu = 0 := by
      apply Complex.ext
      · simpa using hre
      · simpa using him
    simp [nu, K, hnu] at hnorm
  have hcK : c ∈ K := interior_subset hc
  have hcp : affineSupportValue u c < affineSupportValue u p := by
    have hle : affineSupportValue u c ≤ affineSupportValue u p := by
      calc
        affineSupportValue u c ≤ affineNumericalRangeSupport A u :=
          affineNumericalRangeSupport_le A u hcK
        _ = affineSupportValue u p := by simp [p, gamma]
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hcpEq : c = p := hunique c hcK heq
    have hpInt : p ∈ interior K := hcpEq ▸ hc
    exact hfront.2 hpInt
  have hsupportc : (star nu * c).re ≤ (star nu * p).re := by
    simpa [nu, K, p, hpoint] using hsupport c hcK
  have hpair (z w : ℂ) :
      (star nu * z).re - (star nu * w).re =
        nu.re * (affineSupportValue u z - affineSupportValue u w) := by
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, affineSupportValue_apply]
    rw [hrelation]
    ring
  have hnurepos : 0 < nu.re := by
    have hdiffnonneg :
        0 ≤ (star nu * p).re - (star nu * c).re := sub_nonneg.mpr hsupportc
    rw [hpair p c] at hdiffnonneg
    by_contra hnot
    have hnule : nu.re ≤ 0 := le_of_not_gt hnot
    have hnult : nu.re < 0 := lt_of_le_of_ne hnule hnure
    have hdiffpos :
        0 < affineSupportValue u p - affineSupportValue u c := sub_pos.mpr hcp
    have := mul_neg_of_neg_of_pos hnult hdiffpos
    linarith
  intro z hz heq
  have heq' : (star nu * z).re = (star nu * p).re := by
    simpa [nu, K, p, hpoint] using heq
  have haff : affineSupportValue u z = affineSupportValue u p := by
    have hdiff :
        nu.re * (affineSupportValue u z - affineSupportValue u p) = 0 := by
      rw [← hpair z p, heq']
      ring
    exact sub_eq_zero.mp (mul_eq_zero.mp hdiff |>.resolve_left hnure)
  have hzEq := hunique z hz haff
  simpa [K, p, gamma, hpoint] using hzEq

/-- High-level curved-arc endpoint in the exact radial-arclength coordinates
used by the Cauchy boundary package.  The analytic affine arc is retained in
the conclusion, and at almost every radial parameter whose boundary point
lies on that arc, the displayed radial normal exposes that point uniquely. -/
theorem exists_strictlyCurved_radial_uniquelyExposed_numericalRangeArc
    [Nonempty n] (A : Operator.SquareMatrix n)
    (hspec : spectrum ℂ A ⊆ interior (Operator.numericalRange A))
    {c : ℂ} (hc : c ∈ interior (Operator.numericalRange A)) :
    ∃ t r : ℝ, 0 < r ∧
      AnalyticOnNhd ℝ (affineBoundaryPoint A) (ball t r) ∧
      Set.InjOn (affineBoundaryPoint A) (ball t r) ∧
      (∀ u ∈ ball t r,
        affineBoundaryPoint A u ∈ frontier (Operator.numericalRange A) ∧
        0 < deriv (deriv (affineNumericalRangeSupport A)) u ∧
        (∀ z ∈ Operator.numericalRange A,
          affineSupportValue u z ≤
            affineSupportValue u (affineBoundaryPoint A u)) ∧
        ∀ z ∈ Operator.numericalRange A,
          affineSupportValue u z =
            affineSupportValue u (affineBoundaryPoint A u) →
          z = affineBoundaryPoint A u) ∧
      ∀ᵐ s : ℝ ∂Operator.radialBoundaryArcLengthMeasure
          (Operator.numericalRange A) c,
        Operator.radialBoundaryParametrization
            (Operator.numericalRange A) c s ∈
          affineBoundaryPoint A '' ball t r →
        ∀ z ∈ Operator.numericalRange A,
          (star (Operator.radialOutwardUnitNormal
            (Operator.numericalRange A) c s) * z).re =
            (star (Operator.radialOutwardUnitNormal
              (Operator.numericalRange A) c s) *
                Operator.radialBoundaryParametrization
                  (Operator.numericalRange A) c s).re →
          z = Operator.radialBoundaryParametrization
            (Operator.numericalRange A) c s := by
  obtain ⟨t, r, hr, hana, hinj, harc⟩ :=
    exists_strictlyCurved_exposed_numericalRangeArc A hspec
  refine ⟨t, r, hr, hana, hinj, harc, ?_⟩
  let K := Operator.numericalRange A
  have hconv : Convex ℝ K := Operator.numericalRange_convex A
  have hcompact : IsCompact K := Operator.isCompact_numericalRange A
  have hfrontK : frontier K ⊆ K := by
    simpa only [hcompact.isClosed.closure_eq] using
      (frontier_subset_closure : frontier K ⊆ closure K)
  filter_upwards
    [Operator.ae_radialOutwardUnitNormal_supports_arcLength
      hconv hc hcompact,
     Operator.ae_norm_radialOutwardUnitNormal_eq_one_arcLength
      hconv hc hcompact] with s hsupport hnorm
  rintro ⟨u, hu, hpoint⟩
  have hmem : ∀ᶠ v in 𝓝 u, affineBoundaryPoint A v ∈ K := by
    filter_upwards [isOpen_ball.mem_nhds hu] with v hv
    exact hfrontK (harc v hv).1
  apply radial_normal_uniquely_exposes_affineBoundaryPoint
    A hc (hana u hu) (harc u hu).2.1 hmem (harc u hu).1
      (harc u hu).2.2.2 hsupport hnorm
  exact hpoint.symm

end NumericalRangeArc

end

end DiskRigidity.Complex
