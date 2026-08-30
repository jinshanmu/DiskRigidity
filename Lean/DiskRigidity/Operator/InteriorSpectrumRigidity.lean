/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.AnalyticArcContinuation
public import DiskRigidity.Complex.BoundaryFiniteBlaschkeExtremizer
public import DiskRigidity.Operator.ConcreteBoundaryFiniteBlaschkeEquality
public import DiskRigidity.Operator.HolomorphicBoundaryTransfer
public import DiskRigidity.Operator.RationalCollapseEndgame

/-!
# Rigidity in the interior-spectrum case

This module assembles the boundary-continuous finite-Blaschke extremizer,
the concrete radial double-layer equality data, the curved uniquely exposed
arc, faithful boundary continuation, and the rational-lemniscate endgame.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Metric Set Topology
open DiskRigidity.Complex
open scoped BoundedContinuousFunction InnerProductSpace Matrix
  Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

/-- The complete interior-spectrum branch of disk rigidity for the standard
positive finite index type.  Every boundary, Cauchy, dilation, arc,
continuation, and rational-level input is constructed internally. -/
theorem interiorSpectrum_diskRigidity_finSucc
    {N : ℕ} (A : SquareMatrix (Fin (N + 1)))
    (hInt : (interior (numericalRange A)).Nonempty)
    (hspec : spectrum ℂ A ⊆ interior (numericalRange A))
    (hpsi : crouzeixConstant A = 2) :
    ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ numericalRange A = closedBall c r := by
  obtain ⟨g, phi, Bl, hgcl, _hgSchur, _hphi, hbij, hBl, hgeq,
      hnorm, hnonconst, hgFrontier, hgOne⟩ :=
    DiskRigidity.Complex.exists_boundaryContinuous_finiteBlaschke_extremizer_direct
      A hInt hspec hpsi
  let c : ℂ := hInt.choose
  have hc : c ∈ interior (numericalRange A) := hInt.choose_spec
  let B := neighborhoodHolomorphicCauchyBoundaryOfConvexBody A
    (numericalRange_convex A) hc (isCompact_numericalRange A)
    Set.Subset.rfl hspec
  have hclosure : closure (interior (numericalRange A)) = numericalRange A := by
    rw [(numericalRange_convex A).closure_interior_eq_closure_of_nonempty_interior
      hInt, (isCompact_numericalRange A).isClosed.closure_eq]
  have hgK : ContinuousOn g (numericalRange A) := by
    rw [← hclosure]
    exact hgcl.continuousOn
  let P := convexDiskAlgebraDilationData B
    (numericalRange_convex A) hc (isCompact_numericalRange A)
    g hgK hgcl.differentiableOn
    (DiskRigidity.Complex.charpoly_roots_subset_of_spectrum_subset A hspec)
    hgOne
  let _ : IsFiniteMeasure
      (radialBoundaryArcLengthMeasure (numericalRange A) c) :=
    isFiniteMeasure_radialBoundaryArcLengthMeasure
      (numericalRange_convex A) hc (isCompact_numericalRange A)
  have hequality :=
    exists_sharpEqualityData_and_concreteFiniteBlaschkeBoundaryKernel
      A hc hspec g phi Bl hgcl hbij hBl hgeq hnonconst
      hgFrontier hgOne hnorm
  obtain ⟨x, y, hxy, hkernel, hboundaryNorm⟩ := by
    simpa only [B, P] using hequality
  obtain ⟨t, r, hr, hana, hinj, harc, hunique⟩ :=
    NumericalRangeArc.exists_strictlyCurved_radial_uniquelyExposed_numericalRangeArc
      A hspec hc
  let C : Polynomial ℂ := adjugateScalarNumerator A y x
  let D : Polynomial ℂ := adjugateScalarNumerator A x x
  let h : ℂ → ℂ := fun z ↦ C.eval z * g z - (2 : ℂ) • D.eval z
  have hresolventPoint : ∀ᵐ s : ℝ ∂radialBoundaryArcLengthMeasure
      (numericalRange A) c,
      radialBoundaryParametrization (numericalRange A) c s ∈
          NumericalRangeArc.affineBoundaryPoint A '' ball t r →
        B.toCauchyResolventBoundary.boundaryPoint s ∉ spectrum ℂ A := by
    filter_upwards with s
    intro _hsArc hsSpec
    have hsFront := radialBoundaryParametrization_mem_frontier
      (numericalRange_convex A) hc (isCompact_numericalRange A) s
    exact hsFront.2 (hspec hsSpec)
  have hAdjugate := P.adjugate_transfer_identity_ae_on
    (fun s ↦ radialBoundaryParametrization (numericalRange A) c s ∈
      NumericalRangeArc.affineBoundaryPoint A '' ball t r)
    hxy hkernel hboundaryNorm hunique hresolventPoint
  have hzeroAE : ∀ᵐ s : ℝ ∂radialBoundaryArcLengthMeasure
      (numericalRange A) c,
      radialBoundaryParametrization (numericalRange A) c s ∈
          NumericalRangeArc.affineBoundaryPoint A '' ball t r →
        h (radialBoundaryParametrization (numericalRange A) c s) = 0 := by
    filter_upwards [hAdjugate] with s hs
    intro hsArc
    have hs' := hs hsArc
    change C.eval (radialBoundaryParametrization (numericalRange A) c s) *
        g (radialBoundaryParametrization (numericalRange A) c s) =
      2 * D.eval (radialBoundaryParametrization (numericalRange A) c s) at hs'
    exact sub_eq_zero.mpr (by simpa only [smul_eq_mul] using hs')
  have hhdiff : DiffContOnCl ℂ h (interior (numericalRange A)) := by
    constructor
    · exact (C.differentiable.differentiableOn.mul hgcl.differentiableOn).sub
        ((differentiableOn_const (c := (2 : ℂ))).mul
          D.differentiable.differentiableOn)
    · exact (C.continuous.continuousOn.mul hgcl.continuousOn).sub
        (continuousOn_const.mul D.continuous.continuousOn)
  have hzero : EqOn h 0 (interior (numericalRange A)) :=
    NumericalRangeArc.eqOn_zero_of_diffContOnCl_of_ae_radial_strictlyCurved_affineArc
        A hc hr hana hinj harc hhdiff hzeroAE
  have hidentity : ∀ z ∈ interior (numericalRange A),
      (adjugateScalarNumerator A y x).eval z * g z =
        2 * (adjugateScalarNumerator A x x).eval z := by
    intro z hz
    simpa only [h, smul_eq_mul] using sub_eq_zero.mp (hzero hz)
  have hgInterior : ∀ z ∈ interior (numericalRange A), ‖g z‖ < 1 :=
    norm_lt_one_of_eqOn_finiteBlaschke_comp_of_nonconstant
      hbij hBl hgeq hnonconst
  have hyx : ⟪y, x⟫_ℂ = 0 := by
    exact inner_eq_zero_symm.mp hxy.inner_xy
  exact numericalRange_eq_closedBall_of_adjugate_transfer_identity
    A hInt x y hxy.norm_x hyx g hgcl.differentiableOn hgK
    hgInterior hgFrontier hidentity

end DiskRigidity.Operator
