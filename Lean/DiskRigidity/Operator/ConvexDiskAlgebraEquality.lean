/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.ConvexDiskAlgebraDilation
public import DiskRigidity.Operator.HolomorphicSpectralRadius

/-!
# Equality data for a convex disk-algebra extremizer

This file runs the concrete radial-contraction dilation on a numerical range
and extracts the equality vectors and forward boundary kernel.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Metric Set Topology
open scoped BoundedContinuousFunction InnerProductSpace Matrix
  Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {i : Type*} [TopologicalSpace i] [MeasurableSpace i]
  [OpensMeasurableSpace i] {mu : Measure i}
  [BorelSpace i] [IsFiniteMeasure mu]

/-- A forward neighborhood Cauchy boundary produces the sharp equality
vectors and almost-everywhere boundary kernel for any disk-algebra extremizer
that is strictly Schur on the spectrum. -/
theorem exists_sharpEqualityData_and_convexDiskAlgebraBoundaryKernel
    [Nonempty n] (A : SquareMatrix n)
    (B : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary
      A (numericalRange A) mu)
    {c : ℂ} (hc : c ∈ interior (numericalRange A))
    (hspectrum : spectrum ℂ A ⊆ interior (numericalRange A))
    (g : ℂ → ℂ) (hgK : ContinuousOn g (numericalRange A))
    (hg : DifferentiableOn ℂ g (interior (numericalRange A)))
    (hgOne : ∀ z ∈ numericalRange A, ‖g z‖ ≤ 1)
    (hgStrict : ∀ z ∈ spectrum ℂ A, ‖g z‖ < 1)
    (hnorm : ‖DiskRigidity.Complex.spectralJetEval A g‖ = 2) :
    let P := convexDiskAlgebraDilationData B
      (numericalRange_convex A) hc (isCompact_numericalRange A)
      g hgK hg
      (DiskRigidity.Complex.charpoly_roots_subset_of_spectrum_subset
        A hspectrum) hgOne
    ∃ x y : EuclideanVector n,
      SharpEqualityData
        (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g)) x y ∧
      ∀ᵐ t ∂mu,
        P.squareRoot.factor t (y - P.boundaryFunction t • x) = 0 := by
  let hroots :=
    DiskRigidity.Complex.charpoly_roots_subset_of_spectrum_subset A hspectrum
  let P := convexDiskAlgebraDilationData B
    (numericalRange_convex A) hc (isCompact_numericalRange A)
      g hgK hg hroots hgOne
  have hradius : spectralRadius ℂ
      (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g)) < 1 :=
    spectralRadius_spectralJetEval_lt_one A g hgStrict
  simpa only [P] using
    exists_sharpEqualityData_and_holomorphicBoundaryKernel P hnorm hradius

/-- A nonconstant function bounded by one on a numerical range has modulus
strictly below one throughout its interior.  This is the maximum-modulus step
in Proposition 3.3 of the manuscript. -/
theorem norm_lt_one_on_interior_numericalRange_of_nonconstant
    (A : SquareMatrix n)
    (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (interior (numericalRange A)))
    (hgOne : ∀ z ∈ numericalRange A, ‖g z‖ ≤ 1)
    (hnonconst : DiskRigidity.Complex.IsNonconstantOn
      (interior (numericalRange A)) g) :
    ∀ z ∈ interior (numericalRange A), ‖g z‖ < 1 := by
  intro z hz
  have hle : ‖g z‖ ≤ 1 := hgOne z (interior_subset hz)
  apply lt_of_le_of_ne hle
  intro heq
  have hmax : IsMaxOn (norm ∘ g) (interior (numericalRange A)) z := by
    intro w hw
    change ‖g w‖ ≤ ‖g z‖
    rw [heq]
    exact hgOne w (interior_subset hw)
  have hconst : EqOn g (Function.const ℂ (g z))
      (interior (numericalRange A)) :=
    _root_.Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
      (numericalRange_convex A).interior.isPreconnected isOpen_interior
      hg hz hmax
  exact hnonconst ⟨g z, hconst⟩

/-- Proposition 3.3 in its manuscript generality: nonconstancy and the unit
bound imply the strict spectral modulus internally, so no finite-Blaschke or
spectral-radius hypothesis is exposed. -/
theorem exists_sharpEqualityData_and_convexDiskAlgebraBoundaryKernel_of_nonconstant
    [Nonempty n] (A : SquareMatrix n)
    (B : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary
      A (numericalRange A) mu)
    {c : ℂ} (hc : c ∈ interior (numericalRange A))
    (hspectrum : spectrum ℂ A ⊆ interior (numericalRange A))
    (g : ℂ → ℂ) (hgK : ContinuousOn g (numericalRange A))
    (hg : DifferentiableOn ℂ g (interior (numericalRange A)))
    (hgOne : ∀ z ∈ numericalRange A, ‖g z‖ ≤ 1)
    (hnonconst : DiskRigidity.Complex.IsNonconstantOn
      (interior (numericalRange A)) g)
    (hnorm : ‖DiskRigidity.Complex.spectralJetEval A g‖ = 2) :
    let P := convexDiskAlgebraDilationData B
      (numericalRange_convex A) hc (isCompact_numericalRange A)
      g hgK hg
      (DiskRigidity.Complex.charpoly_roots_subset_of_spectrum_subset
        A hspectrum) hgOne
    ∃ x y : EuclideanVector n,
      SharpEqualityData
        (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g)) x y ∧
      ∀ᵐ t ∂mu,
        P.squareRoot.factor t (y - P.boundaryFunction t • x) = 0 := by
  have hgStrict : ∀ z ∈ spectrum ℂ A, ‖g z‖ < 1 := fun z hz ↦
    norm_lt_one_on_interior_numericalRange_of_nonconstant
      A g hg hgOne hnonconst z (hspectrum hz)
  exact exists_sharpEqualityData_and_convexDiskAlgebraBoundaryKernel
    A B hc hspectrum g hgK hg hgOne hgStrict hnorm

end DiskRigidity.Operator
