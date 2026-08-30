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

This file runs the concrete radial-contraction dilation simultaneously on a
numerical range and on its reflected adjoint numerical range.  Reflection of
continuity, holomorphy, bounds, and finite spectral jets is discharged
internally.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Metric Set Topology
open scoped BoundedContinuousFunction InnerProductSpace Matrix
  Matrix.Norms.L2Operator ComplexConjugate

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Conjugation maps the adjoint numerical range back to the original
numerical range. -/
theorem star_mem_numericalRange_of_mem_conjTranspose
    (A : SquareMatrix n) {z : ℂ} (hz : z ∈ numericalRange Aᴴ) :
    starRingEnd ℂ z ∈ numericalRange A := by
  rw [numericalRange_conjTranspose] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  simpa using hw

/-- Reflection preserves continuity on the corresponding numerical range. -/
theorem continuousOn_reflectedHolomorphicFunction_numericalRange
    (A : SquareMatrix n) (g : ℂ → ℂ)
    (hg : ContinuousOn g (numericalRange A)) :
    ContinuousOn (reflectedHolomorphicFunction g) (numericalRange Aᴴ) := by
  have hcomp : ContinuousOn (g ∘ starRingEnd ℂ) (numericalRange Aᴴ) :=
    hg.comp Complex.continuous_conj.continuousOn fun z hz ↦
      star_mem_numericalRange_of_mem_conjTranspose A hz
  simpa [reflectedHolomorphicFunction, Function.comp_def] using hcomp.star

/-- Reflection preserves holomorphy in the corresponding numerical-range
interior. -/
theorem differentiableOn_reflectedHolomorphicFunction_numericalRange
    (A : SquareMatrix n) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (interior (numericalRange A))) :
    DifferentiableOn ℂ (reflectedHolomorphicFunction g)
      (interior (numericalRange Aᴴ)) := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  change DifferentiableAt ℂ (star ∘ g ∘ conj) z
  rw [differentiableAt_star_conj_iff]
  apply hg.differentiableAt
  apply isOpen_interior.mem_nhds
  simpa using star_mem_interior_numericalRange_conjTranspose Aᴴ hz

/-- Reflection preserves a scalar norm bound on the corresponding numerical
range. -/
theorem norm_reflectedHolomorphicFunction_le_numericalRange
    (A : SquareMatrix n) (g : ℂ → ℂ) {r : ℝ}
    (hg : ∀ z ∈ numericalRange A, ‖g z‖ ≤ r) :
    ∀ z ∈ numericalRange Aᴴ, ‖reflectedHolomorphicFunction g z‖ ≤ r := by
  intro z hz
  simpa only [reflectedHolomorphicFunction, Function.comp_apply, norm_star]
    using hg (starRingEnd ℂ z)
      (star_mem_numericalRange_of_mem_conjTranspose A hz)

variable {i : Type*} [TopologicalSpace i] [MeasurableSpace i]
  [OpensMeasurableSpace i] {mu : Measure i}
  [BorelSpace i] [IsFiniteMeasure mu]
variable {j : Type*} [TopologicalSpace j] [MeasurableSpace j]
  [OpensMeasurableSpace j] {nu : Measure j}
  [BorelSpace j] [IsFiniteMeasure nu]

/-- Forward and reflected neighborhood Cauchy boundaries produce the sharp
equality vectors and the almost-everywhere forward boundary kernel for any
disk-algebra extremizer that is strictly Schur on the spectrum. -/
theorem exists_sharpEqualityData_and_convexDiskAlgebraBoundaryKernel
    [Nonempty n] (A : SquareMatrix n)
    (B : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary
      A (numericalRange A) mu)
    (Badj : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary
      Aᴴ (numericalRange Aᴴ) nu)
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
  let hspectrumAdj :=
    spectrum_conjTranspose_subset_interior_numericalRange A hspectrum
  let hrootsAdj :=
    DiskRigidity.Complex.charpoly_roots_subset_of_spectrum_subset
      Aᴴ hspectrumAdj
  let hgKAdj :=
    continuousOn_reflectedHolomorphicFunction_numericalRange A g hgK
  let hgAdj :=
    differentiableOn_reflectedHolomorphicFunction_numericalRange A g hg
  let hgOneAdj :=
    norm_reflectedHolomorphicFunction_le_numericalRange A g hgOne
  let P := convexDiskAlgebraDilationData B
    (numericalRange_convex A) hc (isCompact_numericalRange A)
      g hgK hg hroots hgOne
  let Padj := convexDiskAlgebraDilationData Badj
    (numericalRange_convex Aᴴ)
      (star_mem_interior_numericalRange_conjTranspose A hc)
      (isCompact_numericalRange Aᴴ)
      (reflectedHolomorphicFunction g) hgKAdj hgAdj hrootsAdj hgOneAdj
  have hradius : spectralRadius ℂ
      (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g)) < 1 :=
    spectralRadius_spectralJetEval_lt_one A g hgStrict
  simpa only [P] using
    exists_sharpEqualityData_and_reflectedHolomorphicBoundaryKernel
      P Padj hnorm hradius

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
    (Badj : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary
      Aᴴ (numericalRange Aᴴ) nu)
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
    A B Badj hc hspectrum g hgK hg hgOne hgStrict hnorm

end DiskRigidity.Operator
