/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.ConvexPolynomialCauchy
public import DiskRigidity.Operator.FoundationSymmetries
public import DiskRigidity.Operator.EqualityData

/-!
# Concrete equality data on the numerical-range boundary

This file instantiates both boundary dilations in Proposition 3.3 with the
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

/-- The spectrum of the adjoint matrix is the complex conjugate of the
original spectrum. -/
theorem spectrum_conjTranspose (A : SquareMatrix n) :
    spectrum ℂ Aᴴ = starRingEnd ℂ '' spectrum ℂ A := by
  ext z
  constructor
  · intro hz
    refine ⟨starRingEnd ℂ z, ?_, by simp⟩
    rw [spectrum.mem_iff] at hz ⊢
    intro hu
    apply hz
    have hs := hu.star
    simpa [Matrix.star_eq_conjTranspose,
      Algebra.algebraMap_eq_smul_one] using hs
  · rintro ⟨w, hw, rfl⟩
    rw [spectrum.mem_iff] at hw ⊢
    intro hu
    apply hw
    have hs := hu.star
    simpa [Matrix.star_eq_conjTranspose,
      Algebra.algebraMap_eq_smul_one] using hs

/-- Strict inclusion of the spectrum in the numerical-range interior is
preserved by adjoints. -/
theorem spectrum_conjTranspose_subset_interior_numericalRange
    (A : SquareMatrix n)
    (hspectrum : spectrum ℂ A ⊆ interior (numericalRange A)) :
    spectrum ℂ Aᴴ ⊆ interior (numericalRange Aᴴ) := by
  rw [spectrum_conjTranspose, numericalRange_conjTranspose]
  change Complex.conjCLE '' spectrum ℂ A ⊆
    interior (Complex.conjCLE '' numericalRange A)
  rw [← Complex.conjCLE.isHomeomorph.image_interior]
  exact Set.image_mono hspectrum

/-- Conjugating an interior point gives an interior point of the adjoint
numerical range. -/
theorem star_mem_interior_numericalRange_conjTranspose
    (A : SquareMatrix n) {c : ℂ}
    (hc : c ∈ interior (numericalRange A)) :
    starRingEnd ℂ c ∈ interior (numericalRange Aᴴ) := by
  rw [numericalRange_conjTranspose]
  change Complex.conjCLE c ∈
    interior (Complex.conjCLE '' numericalRange A)
  rw [← Complex.conjCLE.isHomeomorph.image_interior]
  exact ⟨c, hc, rfl⟩

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

/-- Proposition 3.3 for a polynomial extremizer, with both concrete
numerical-range boundaries supplied internally.  The two centers and the
strict spectral inclusions are ordinary geometric hypotheses; no analytic
boundary package is assumed. -/
theorem exists_sharpEqualityData_and_concreteBoundaryKernel
    [Nonempty n] (A : SquareMatrix n) (p : Polynomial ℂ)
    {c cadj : ℂ}
    (hc : c ∈ interior (numericalRange A))
    (hcadj : cadj ∈ interior (numericalRange Aᴴ))
    (hspectrum : spectrum ℂ A ⊆ interior (numericalRange A))
    (hspectrumAdj : spectrum ℂ Aᴴ ⊆ interior (numericalRange Aᴴ))
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
  let _ : IsFiniteMeasure
      (radialBoundaryArcLengthMeasure (numericalRange Aᴴ) cadj) :=
    isFiniteMeasure_radialBoundaryArcLengthMeasure
      (numericalRange_convex Aᴴ) hcadj (isCompact_numericalRange Aᴴ)
  let q := conjugatePolynomial p
  have hq : maxPolynomialModulus Aᴴ q ≤ 1 := by
    simpa only [q, maxPolynomialModulus_conjTranspose_conjugate] using hp
  let P := numericalRangePolynomialDilationData A hc hspectrum p hp
  let Padj := numericalRangePolynomialDilationData Aᴴ hcadj
    hspectrumAdj q hq
  let D := P.witness
  let DadjRaw := Padj.witness
  have hadj : euclideanOperator (polynomialEval q Aᴴ) =
      ContinuousLinearMap.adjoint
        (euclideanOperator (polynomialEval p A)) := by
    rw [polynomialEval_conjugate_conjTranspose,
      euclideanOperator_conjTranspose]
  let Dadj : DilationWitness
      (K := Lp (EuclideanVector n) 2
        (radialBoundaryArcLengthMeasure (numericalRange Aᴴ) cadj))
      (ContinuousLinearMap.adjoint
        (euclideanOperator (polynomialEval p A))) := by
    rw [← hadj]
    exact DadjRaw
  let realization : BoundaryMultiplicationRealization D
      (radialBoundaryArcLengthMeasure (numericalRange A) c) :=
    BoundaryMultiplicationRealization.ofLp D P.boundaryFunction
      P.squareRoot.factor rfl P.squareRoot.boundaryIsometry_coe_ae
  have hoperatorNorm :
      ‖euclideanOperator (polynomialEval p A)‖ = 2 := by
    simpa only [← matrix_norm_eq_operator_norm] using hnorm
  simpa only [P, realization, BoundaryMultiplicationRealization.ofLp] using
    (exists_sharpEqualityData_and_boundaryKernel
      (euclideanOperator (polynomialEval p A)) D Dadj realization
      hoperatorNorm hradius)

/-- Strongest one-matrix form of the concrete polynomial equality theorem.
The reflected center and the adjoint spectral inclusion are derived rather
than supplied by the caller. -/
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
  exact exists_sharpEqualityData_and_concreteBoundaryKernel A p hc
    (star_mem_interior_numericalRange_conjTranspose A hc) hspectrum
    (spectrum_conjTranspose_subset_interior_numericalRange A hspectrum)
    hp hnorm hradius

end DiskRigidity.Operator
