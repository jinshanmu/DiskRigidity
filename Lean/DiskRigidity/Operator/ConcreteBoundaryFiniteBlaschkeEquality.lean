/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.BoundaryFiniteBlaschkeEquality
public import DiskRigidity.Operator.ConvexHolomorphicCauchy

/-!
# Concrete equality data for the boundary finite-Blaschke extremizer

The neighborhood Cauchy boundary is now the canonical radial boundary of the
numerical range of `A`.  Consequently the theorem below has no boundary,
Cauchy, square-root, dilation, or spectral-radius hypothesis.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Metric Set Topology
open scoped BoundedContinuousFunction InnerProductSpace Matrix
  Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Proposition 3.3 with every analytic input concrete.  For an arbitrary
nonconstant disk-algebra extremizer, the canonical numerical-range Cauchy
boundaries produce the equality vectors, the radial boundary kernel, and the
unimodular boundary multiplier. -/
theorem exists_sharpEqualityData_and_concreteBoundaryKernel_of_nonconstant
    [Nonempty n] (A : SquareMatrix n)
    {c : ℂ} (hc : c ∈ interior (numericalRange A))
    (hspectrum : spectrum ℂ A ⊆ interior (numericalRange A))
    (g : ℂ → ℂ)
    (hgcl : DiffContOnCl ℂ g (interior (numericalRange A)))
    (hnonconst : DiskRigidity.Complex.IsNonconstantOn
      (interior (numericalRange A)) g)
    (hgFrontier : ∀ z ∈ frontier (numericalRange A), ‖g z‖ = 1)
    (hgOne : ∀ z ∈ numericalRange A, ‖g z‖ ≤ 1)
    (hnorm : ‖DiskRigidity.Complex.spectralJetEval A g‖ = 2) :
    let B := neighborhoodHolomorphicCauchyBoundaryOfConvexBody A
      (numericalRange_convex A) hc (isCompact_numericalRange A)
      Set.Subset.rfl hspectrum
    let P := convexDiskAlgebraDilationData B
      (numericalRange_convex A) hc (isCompact_numericalRange A)
      g (by
        rw [← (isCompact_numericalRange A).isClosed.closure_eq,
          ← (numericalRange_convex A).closure_interior_eq_closure_of_nonempty_interior
            ⟨c, hc⟩]
        exact hgcl.continuousOn)
      hgcl.differentiableOn
      (DiskRigidity.Complex.charpoly_roots_subset_of_spectrum_subset
        A hspectrum) hgOne
    ∃ x y : EuclideanVector n,
      SharpEqualityData
        (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g)) x y ∧
      (∀ᵐ t ∂radialBoundaryArcLengthMeasure (numericalRange A) c,
        P.squareRoot.factor t (y - P.boundaryFunction t • x) = 0) ∧
      ∀ᵐ t ∂radialBoundaryArcLengthMeasure (numericalRange A) c,
        ‖P.boundaryFunction t‖ = 1 := by
  have hclosure : closure (interior (numericalRange A)) = numericalRange A := by
    rw [(numericalRange_convex A).closure_interior_eq_closure_of_nonempty_interior
      ⟨c, hc⟩, (isCompact_numericalRange A).isClosed.closure_eq]
  have hgK : ContinuousOn g (numericalRange A) := by
    rw [← hclosure]
    exact hgcl.continuousOn
  let B := neighborhoodHolomorphicCauchyBoundaryOfConvexBody A
    (numericalRange_convex A) hc (isCompact_numericalRange A)
      Set.Subset.rfl hspectrum
  let _ : IsFiniteMeasure
      (radialBoundaryArcLengthMeasure (numericalRange A) c) :=
    isFiniteMeasure_radialBoundaryArcLengthMeasure
      (numericalRange_convex A) hc (isCompact_numericalRange A)
  let P := convexDiskAlgebraDilationData B
    (numericalRange_convex A) hc (isCompact_numericalRange A)
      g hgK hgcl.differentiableOn
      (DiskRigidity.Complex.charpoly_roots_subset_of_spectrum_subset
        A hspectrum) hgOne
  obtain ⟨x, y, hxy, hkernel⟩ :=
    exists_sharpEqualityData_and_convexDiskAlgebraBoundaryKernel_of_nonconstant
      A B hc hspectrum g hgK hgcl.differentiableOn hgOne
        hnonconst hnorm
  refine ⟨x, y, hxy, hkernel, ?_⟩
  filter_upwards [P.boundaryFunction_eq] with t ht
  rw [ht]
  apply hgFrontier
  exact radialBoundaryParametrization_mem_frontier
    (numericalRange_convex A) hc (isCompact_numericalRange A) t

/-- A boundary-continuous finite-Blaschke extremizer produces concrete sharp
equality vectors, the almost-everywhere square-root kernel, and the
unimodularity of the actual radial boundary multiplier. -/
theorem exists_sharpEqualityData_and_concreteFiniteBlaschkeBoundaryKernel
    [Nonempty n] (A : SquareMatrix n)
    {c : ℂ} (hc : c ∈ interior (numericalRange A))
    (hspectrum : spectrum ℂ A ⊆ interior (numericalRange A))
    (g phi Bl : ℂ → ℂ)
    (hgcl : DiffContOnCl ℂ g (interior (numericalRange A)))
    (hbij : BijOn phi (interior (numericalRange A)) (ball 0 1))
    (hBl : DiskRigidity.Complex.IsSchurFiniteBlaschke Bl)
    (hgeq : EqOn g (Bl ∘ phi) (interior (numericalRange A)))
    (hnonconst : DiskRigidity.Complex.IsNonconstantOn
      (interior (numericalRange A)) g)
    (hgFrontier : ∀ z ∈ frontier (numericalRange A), ‖g z‖ = 1)
    (hgOne : ∀ z ∈ numericalRange A, ‖g z‖ ≤ 1)
    (hnorm : ‖DiskRigidity.Complex.spectralJetEval A g‖ = 2) :
    let B := neighborhoodHolomorphicCauchyBoundaryOfConvexBody A
      (numericalRange_convex A) hc (isCompact_numericalRange A)
      Set.Subset.rfl hspectrum
    let P := convexDiskAlgebraDilationData B
      (numericalRange_convex A) hc (isCompact_numericalRange A)
      g (by
        rw [← (isCompact_numericalRange A).isClosed.closure_eq,
          ← (numericalRange_convex A).closure_interior_eq_closure_of_nonempty_interior
            ⟨c, hc⟩]
        exact hgcl.continuousOn)
      hgcl.differentiableOn
      (DiskRigidity.Complex.charpoly_roots_subset_of_spectrum_subset
        A hspectrum) hgOne
    ∃ x y : EuclideanVector n,
      SharpEqualityData
        (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g)) x y ∧
      (∀ᵐ t ∂radialBoundaryArcLengthMeasure (numericalRange A) c,
        P.squareRoot.factor t (y - P.boundaryFunction t • x) = 0) ∧
      ∀ᵐ t ∂radialBoundaryArcLengthMeasure (numericalRange A) c,
        ‖P.boundaryFunction t‖ = 1 := by
  have hclosure : closure (interior (numericalRange A)) = numericalRange A := by
    rw [(numericalRange_convex A).closure_interior_eq_closure_of_nonempty_interior
      ⟨c, hc⟩, (isCompact_numericalRange A).isClosed.closure_eq]
  have hgK : ContinuousOn g (numericalRange A) := by
    rw [← hclosure]
    exact hgcl.continuousOn
  let B := neighborhoodHolomorphicCauchyBoundaryOfConvexBody A
    (numericalRange_convex A) hc (isCompact_numericalRange A)
      Set.Subset.rfl hspectrum
  let _ : IsFiniteMeasure
      (radialBoundaryArcLengthMeasure (numericalRange A) c) :=
    isFiniteMeasure_radialBoundaryArcLengthMeasure
      (numericalRange_convex A) hc (isCompact_numericalRange A)
  let P := convexDiskAlgebraDilationData B
    (numericalRange_convex A) hc (isCompact_numericalRange A)
      g hgK hgcl.differentiableOn
      (DiskRigidity.Complex.charpoly_roots_subset_of_spectrum_subset
        A hspectrum) hgOne
  obtain ⟨x, y, hxy, hkernel⟩ :=
    exists_sharpEqualityData_and_finiteBlaschkeBoundaryKernel
      A B hc hspectrum g phi Bl hgK hgcl.differentiableOn
        hbij hBl hgeq hnonconst hgOne hnorm
  refine ⟨x, y, hxy, hkernel, ?_⟩
  filter_upwards [P.boundaryFunction_eq] with t ht
  rw [ht]
  apply hgFrontier
  exact radialBoundaryParametrization_mem_frontier
    (numericalRange_convex A) hc (isCompact_numericalRange A) t

end DiskRigidity.Operator
