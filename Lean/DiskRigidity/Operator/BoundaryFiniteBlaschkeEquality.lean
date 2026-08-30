/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.BoundaryFiniteBlaschkeExtremizer
public import DiskRigidity.Operator.ConvexDiskAlgebraEquality

/-!
# Equality data for a boundary-continuous finite Blaschke extremizer

The nonconstancy of the extremizer rules out the unimodular constant branch
of the Schur dichotomy.  Its values are therefore strictly inside the unit
disc throughout the numerical-range interior, which supplies the strict
spectral-radius hypothesis automatically.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Metric Set Topology
open scoped BoundedContinuousFunction InnerProductSpace Matrix
  Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A nonconstant finite-Blaschke composition has modulus strictly below one
at every interior point of its source domain. -/
theorem norm_lt_one_of_eqOn_finiteBlaschke_comp_of_nonconstant
    {U : Set ℂ} {g phi Bl : ℂ → ℂ}
    (hbij : BijOn phi U (ball 0 1))
    (hBl : DiskRigidity.Complex.IsSchurFiniteBlaschke Bl)
    (hgeq : EqOn g (Bl ∘ phi) U)
    (hnonconst : DiskRigidity.Complex.IsNonconstantOn U g) :
    ∀ z ∈ U, ‖g z‖ < 1 := by
  rcases hBl.isSchur.eqOn_unimodular_const_or_mapsTo_ball with
    ⟨a, _ha, hconst⟩ | hmaps
  · exfalso
    apply hnonconst
    refine ⟨a, ?_⟩
    intro z hz
    rw [hgeq hz]
    change Bl (phi z) = a
    simpa using hconst (hbij.mapsTo hz)
  · intro z hz
    rw [hgeq hz]
    simpa [mem_ball_zero_iff] using hmaps (hbij.mapsTo hz)

variable {i : Type*} [TopologicalSpace i] [MeasurableSpace i]
  [OpensMeasurableSpace i] {mu : Measure i}
  [BorelSpace i] [IsFiniteMeasure mu]
variable {j : Type*} [TopologicalSpace j] [MeasurableSpace j]
  [OpensMeasurableSpace j] {nu : Measure j}
  [BorelSpace j] [IsFiniteMeasure nu]

/-- Exact sharp equality and forward boundary-kernel data for a
boundary-continuous finite-Blaschke extremizer.  Strict spectral radius and
the complete forward/adjoint dilations are conclusions, not hypotheses. -/
theorem exists_sharpEqualityData_and_finiteBlaschkeBoundaryKernel
    [Nonempty n] (A : SquareMatrix n)
    (B : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary
      A (numericalRange A) mu)
    (Badj : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary
      Aᴴ (numericalRange Aᴴ) nu)
    {c : ℂ} (hc : c ∈ interior (numericalRange A))
    (hspectrum : spectrum ℂ A ⊆ interior (numericalRange A))
    (g phi Bl : ℂ → ℂ)
    (hgK : ContinuousOn g (numericalRange A))
    (hg : DifferentiableOn ℂ g (interior (numericalRange A)))
    (hbij : BijOn phi (interior (numericalRange A)) (ball 0 1))
    (hBl : DiskRigidity.Complex.IsSchurFiniteBlaschke Bl)
    (hgeq : EqOn g (Bl ∘ phi) (interior (numericalRange A)))
    (hnonconst : DiskRigidity.Complex.IsNonconstantOn
      (interior (numericalRange A)) g)
    (hgOne : ∀ z ∈ numericalRange A, ‖g z‖ ≤ 1)
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
  have hgInterior : ∀ z ∈ interior (numericalRange A), ‖g z‖ < 1 :=
    norm_lt_one_of_eqOn_finiteBlaschke_comp_of_nonconstant
      hbij hBl hgeq hnonconst
  have hgStrict : ∀ z ∈ spectrum ℂ A, ‖g z‖ < 1 := fun z hz ↦
    hgInterior z (hspectrum hz)
  exact exists_sharpEqualityData_and_convexDiskAlgebraBoundaryKernel
    A B Badj hc hspectrum g hgK hg hgOne hgStrict hnorm

end DiskRigidity.Operator
