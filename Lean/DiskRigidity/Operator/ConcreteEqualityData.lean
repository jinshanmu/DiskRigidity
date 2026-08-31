/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.ConvexPolynomialCauchy
public import DiskRigidity.Operator.EqualityData

/-!
# Concrete equality data on the numerical-range boundary

This file instantiates the boundary dilation in Proposition 3.3 with the
concrete radial arclength boundary of the numerical range.  In particular,
the almost-everywhere kernel identity is obtained without asking the caller
for a boundary parametrization, a Cauchy formula, a positive square root, or
a dilation witness.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BoundedContinuousFunction InnerProductSpace Matrix
  Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The concrete polynomial dilation attached to a compact convex body.
All boundary and Cauchy data, including the positive square root, are
constructed canonically. -/
def convexBodyPolynomialDilationData
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K)
    (p : Polynomial ℂ) (hp : ∀ z ∈ K, ‖p.eval z‖ ≤ 1) :
    PolynomialResolventDilationData
      (polynomialCauchyResolventBoundaryOfConvexBodyConcrete
        A hconv hc hcompact hWA hspectrum).toCauchyResolventBoundary p :=
  let B := polynomialCauchyResolventBoundaryOfConvexBodyConcrete
    A hconv hc hcompact hWA hspectrum
  let f := radialPolynomialBoundaryFunction hconv hc hcompact p
  B.polynomialDilationData p f
    (Filter.Eventually.of_forall fun _ ↦ rfl)
    (norm_radialPolynomialBoundaryFunction_le
      hconv hc hcompact p zero_le_one hp)

/-- The preceding dilation specialized to the numerical range itself. -/
def numericalRangePolynomialDilationData
    [Nonempty n] (A : SquareMatrix n) {c : ℂ}
    (hc : c ∈ interior (numericalRange A))
    (hspectrum : spectrum ℂ A ⊆ interior (numericalRange A))
    (p : Polynomial ℂ) (hp : maxPolynomialModulus A p ≤ 1) :
    PolynomialResolventDilationData
      (polynomialCauchyResolventBoundaryOfConvexBodyConcrete A
        (numericalRange_convex A) hc (isCompact_numericalRange A)
        Set.Subset.rfl hspectrum).toCauchyResolventBoundary p :=
  convexBodyPolynomialDilationData A (numericalRange_convex A) hc
    (isCompact_numericalRange A) Set.Subset.rfl hspectrum p
      (fun _z hz ↦ (norm_eval_le_maxPolynomialModulus A p hz).trans hp)

/-- Proposition 3.3 for a polynomial extremizer, with the concrete
numerical-range boundary supplied internally. -/
theorem exists_sharpEqualityData_and_concreteBoundaryKernel
    [Nonempty n] (A : SquareMatrix n) (p : Polynomial ℂ)
    {c : ℂ}
    (hc : c ∈ interior (numericalRange A))
    (hspectrum : spectrum ℂ A ⊆ interior (numericalRange A))
    (hp : maxPolynomialModulus A p ≤ 1)
    (hnorm : ‖polynomialEval p A‖ = 2)
    (hradius : spectralRadius ℂ
      (euclideanOperator (polynomialEval p A)) < 1) :
    let P := numericalRangePolynomialDilationData A hc hspectrum p hp
    ∃ x y : EuclideanVector n,
      SharpEqualityData (euclideanOperator (polynomialEval p A)) x y ∧
        ∀ᵐ t ∂radialBoundaryArcLengthMeasure (numericalRange A) c,
      P.squareRoot.factor t
            (y - P.boundaryFunction t • x) = 0 := by
  let _ : IsFiniteMeasure
      (radialBoundaryArcLengthMeasure (numericalRange A) c) :=
    isFiniteMeasure_radialBoundaryArcLengthMeasure
      (numericalRange_convex A) hc (isCompact_numericalRange A)
  let P := numericalRangePolynomialDilationData A hc hspectrum p hp
  let D := P.witness
  let realization : BoundaryMultiplicationRealization D
      (radialBoundaryArcLengthMeasure (numericalRange A) c) :=
    BoundaryMultiplicationRealization.ofLp D P.boundaryFunction
      P.squareRoot.factor rfl P.squareRoot.boundaryIsometry_coe_ae
  have hoperatorNorm :
      ‖euclideanOperator (polynomialEval p A)‖ = 2 := by
    simpa only [← matrix_norm_eq_operator_norm] using hnorm
  simpa only [P, realization, BoundaryMultiplicationRealization.ofLp] using
    (exists_sharpEqualityData_and_boundaryKernel
      (euclideanOperator (polynomialEval p A)) D realization
      hoperatorNorm hradius)

/-- One-matrix form of the concrete polynomial equality theorem. -/
theorem exists_sharpEqualityData_and_numericalRangeBoundaryKernel
    [Nonempty n] (A : SquareMatrix n) (p : Polynomial ℂ) {c : ℂ}
    (hc : c ∈ interior (numericalRange A))
    (hspectrum : spectrum ℂ A ⊆ interior (numericalRange A))
    (hp : maxPolynomialModulus A p ≤ 1)
    (hnorm : ‖polynomialEval p A‖ = 2)
    (hradius : spectralRadius ℂ
      (euclideanOperator (polynomialEval p A)) < 1) :
    let P := numericalRangePolynomialDilationData A hc hspectrum p hp
    ∃ x y : EuclideanVector n,
      SharpEqualityData (euclideanOperator (polynomialEval p A)) x y ∧
        ∀ᵐ t ∂radialBoundaryArcLengthMeasure (numericalRange A) c,
          P.squareRoot.factor t
            (y - P.boundaryFunction t • x) = 0 := by
  exact exists_sharpEqualityData_and_concreteBoundaryKernel A p hc hspectrum
    hp hnorm hradius

end DiskRigidity.Operator
