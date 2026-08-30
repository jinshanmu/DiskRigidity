/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.HolomorphicEqualityData

/-!
# Double-layer dilations from uniform polynomial approximation

This module promotes a neighborhood Cauchy boundary to the exact
disk-algebra dilation needed for a boundary-continuous extremizer.  It also
shows that uniform polynomial approximation on a numerical range is
automatically inherited by the reflected function on the adjoint numerical
range.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Metric Set Topology
open scoped BoundedContinuousFunction InnerProductSpace Matrix
  Matrix.Norms.L2Operator ComplexConjugate

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {i : Type*} [TopologicalSpace i] [MeasurableSpace i]
  [OpensMeasurableSpace i] {mu : Measure i}
  [BorelSpace i] [IsFiniteMeasure mu]

/-- A function continuous on the boundary set and uniformly approximable
there by polynomials has the complete holomorphic double-layer dilation. -/
def _root_.DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary.diskAlgebraDilationData
    {A : SquareMatrix n} {K : Set ℂ}
    (B : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary A K mu)
    (g : ℂ → ℂ) (hgK : ContinuousOn g K)
    (hg : DifferentiableOn ℂ g (interior K))
    (hroots : ∀ z ∈ A.charpoly.roots, z ∈ interior K)
    (hgOne : ∀ z ∈ K, ‖g z‖ ≤ 1)
    (happroxPow : ∀ k : ℕ,
      HasUniformPolynomialApproximationOn K (fun z ↦ g z ^ k)) :
    HolomorphicResolventDilationData B.toCauchyResolventBoundary g := by
  refine
    { analyticAt_roots := fun a ↦ hg.analyticAt
        (isOpen_interior.mem_nhds
          (hroots (a : ℂ) (Multiset.mem_toFinset.mp a.2)))
      boundaryFunction := B.boundaryTrace g
      boundaryFunction_eq := B.boundaryTrace_eq g hgK
      boundaryFunction_norm_le_one :=
        B.boundaryTrace_norm_le g 1 hgK hgOne
      cauchy_pow := ?_ }
  intro k _hk
  let P := Classical.choose (happroxPow k)
  have hP := Classical.choose_spec (happroxPow k)
  exact holomorphic_cauchy_of_tendstoUniformlyOn_polynomial
    B (fun z ↦ g z ^ k) (hgK.pow k) (hg.pow k) hroots
      P hP

/-- The corresponding normalized factor-two bound for a disk-algebra
function. -/
theorem norm_spectralJetEval_le_two_of_uniformApproximation
    [Nonempty n] {A : SquareMatrix n} {K : Set ℂ}
    (B : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary A K mu)
    (g : ℂ → ℂ) (hgK : ContinuousOn g K)
    (hg : DifferentiableOn ℂ g (interior K))
    (hroots : ∀ z ∈ A.charpoly.roots, z ∈ interior K)
    (hgOne : ∀ z ∈ K, ‖g z‖ ≤ 1)
    (happroxPow : ∀ k : ℕ,
      HasUniformPolynomialApproximationOn K (fun z ↦ g z ^ k)) :
    ‖DiskRigidity.Complex.spectralJetEval A g‖ ≤ 2 := by
  let P := B.diskAlgebraDilationData g hgK hg hroots hgOne happroxPow
  rw [matrix_norm_eq_operator_norm]
  exact P.witness.norm_le_two

omit [TopologicalSpace i] [MeasurableSpace i] [OpensMeasurableSpace i]
  [BorelSpace i] [IsFiniteMeasure mu] in
/-- Uniform polynomial approximation is preserved by reflection from a
matrix numerical range to the numerical range of its adjoint. -/
theorem hasUniformPolynomialApproximationOn_reflected_numericalRange
    (A : SquareMatrix n) (g : ℂ → ℂ)
    (happrox : HasUniformPolynomialApproximationOn (numericalRange A) g) :
    HasUniformPolynomialApproximationOn (numericalRange Aᴴ)
      (reflectedHolomorphicFunction g) := by
  obtain ⟨P, hP⟩ := happrox
  refine ⟨fun m ↦ conjugatePolynomial (P m), ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hP) ε hε] with m hm
  intro z hz
  rw [numericalRange_conjTranspose] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  simpa only [reflectedHolomorphicFunction, Function.comp_apply,
    map_star, star_star, conjugatePolynomial_eval, starRingEnd_apply,
    dist_star_star] using hm w hw

end DiskRigidity.Operator
