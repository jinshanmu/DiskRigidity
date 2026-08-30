/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.ConvexBoundaryArcLength
public import DiskRigidity.Operator.ResolventDilation
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.MeasureTheory.Measure.ResolventTransform

/-!
# The concrete resolvent package on a convex boundary

For a compact convex body whose interior contains the spectrum, this file
constructs the boundary resolvent and discharges its inverse identity,
continuity, integrability, unit-normal, and supporting-half-plane fields.
The sole remaining analytic input is the ordinary holomorphic polynomial
Cauchy formula.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set Topology
open scoped BoundedContinuousFunction InnerProductSpace Matrix
  Matrix.Norms.L2Operator NNReal Pointwise

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The algebraic resolvent evaluated on the concrete radial boundary. -/
def convexBoundaryResolvent
    (A : SquareMatrix n) (K : Set ℂ) (c : ℂ) (t : ℝ) :
    SquareMatrix n :=
  resolvent A (radialBoundaryParametrization K c t)

/-- Every boundary parameter lies in the resolvent set when the spectrum is
strictly inside the convex body. -/
theorem radialBoundaryParametrization_mem_resolventSet
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hspectrum : spectrum ℂ A ⊆ interior K) (t : ℝ) :
    radialBoundaryParametrization K c t ∈ resolventSet ℂ A := by
  have hfront :=
    radialBoundaryParametrization_mem_frontier hconv hc hcompact t
  have hnot : radialBoundaryParametrization K c t ∉ spectrum ℂ A := by
    intro hs
    exact hfront.2 (hspectrum hs)
  simpa [spectrum] using hnot

/-- The concrete boundary resolvent is a genuine two-sided inverse (the
left-inverse form is the one used by the double layer). -/
theorem convexBoundaryResolvent_mul
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hspectrum : spectrum ℂ A ⊆ interior K) (t : ℝ) :
    (radialBoundaryParametrization K c t • (1 : SquareMatrix n) - A) *
        convexBoundaryResolvent A K c t = 1 := by
  let hR := radialBoundaryParametrization_mem_resolventSet
    A hconv hc hcompact hspectrum t
  rw [convexBoundaryResolvent, spectrum.resolvent_eq hR]
  simpa [Algebra.algebraMap_eq_smul_one, hR.unit_spec] using hR.unit.mul_inv

/-- Applying the Euclidean-operator equivalence to the matrix resolvent
gives the Banach-algebra resolvent of the associated operator. -/
theorem euclideanOperator_convexBoundaryResolvent_eq_resolvent
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hspectrum : spectrum ℂ A ⊆ interior K) (t : ℝ) :
    euclideanOperator (convexBoundaryResolvent A K c t) =
      resolvent (euclideanOperator A)
        (radialBoundaryParametrization K c t) := by
  have hR := radialBoundaryParametrization_mem_resolventSet
    A hconv hc hcompact hspectrum t
  have hRop := AlgHom.mem_resolventSet_apply
    (euclideanOperator (n := n)) hR
  have hleft :
      (radialBoundaryParametrization K c t •
          (1 : EuclideanEndomorphism n) - euclideanOperator A) *
        euclideanOperator (convexBoundaryResolvent A K c t) = 1 := by
    simpa using congrArg (euclideanOperator (n := n))
      (convexBoundaryResolvent_mul A hconv hc hcompact hspectrum t)
  have hright :
      resolvent (euclideanOperator A)
          (radialBoundaryParametrization K c t) *
        (radialBoundaryParametrization K c t •
          (1 : EuclideanEndomorphism n) - euclideanOperator A) = 1 := by
    rw [spectrum.resolvent_eq hRop]
    simpa only [Algebra.algebraMap_eq_smul_one, hRop.unit_spec] using
      hRop.unit.inv_mul
  exact (left_inv_eq_right_inv hright hleft).symm

/-- The holomorphic half of the double-layer density is integrable on the
finite arclength measure. -/
theorem integrable_rightResolventBoundaryTerm_convexBoundary
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hspectrum : spectrum ℂ A ⊆ interior K) :
    Integrable
      (fun t ↦ rightResolventBoundaryTerm
        (convexBoundaryResolvent A K c t)
        (radialOutwardUnitNormal K c t))
      (radialBoundaryArcLengthMeasure K c) := by
  let _ : IsFiniteMeasure (radialBoundaryArcLengthMeasure K c) :=
    isFiniteMeasure_radialBoundaryArcLengthMeasure hconv hc hcompact
  let G : ℝ → EuclideanEndomorphism n := fun t ↦
    euclideanOperator (convexBoundaryResolvent A K c t)
  obtain ⟨C, hsigma⟩ :=
    exists_lipschitzWith_radialBoundaryParametrization hconv hc hcompact
  have hG : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro t
    have hR := radialBoundaryParametrization_mem_resolventSet
      A hconv hc hcompact hspectrum t
    have hRop := AlgHom.mem_resolventSet_apply
      (euclideanOperator (n := n)) hR
    rw [show G = fun s ↦ resolvent (euclideanOperator A)
        (radialBoundaryParametrization K c s) by
      funext s
      exact euclideanOperator_convexBoundaryResolvent_eq_resolvent
        A hconv hc hcompact hspectrum s]
    exact (spectrum.hasDerivAt_resolvent_const_left hRop).continuousAt.comp
      hsigma.continuous.continuousAt
  have hmeas : Measurable
      (fun t ↦ rightResolventBoundaryTerm
        (convexBoundaryResolvent A K c t)
        (radialOutwardUnitNormal K c t)) := by
    exact (measurable_radialOutwardUnitNormal K c).smul hG.measurable
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hG.norm.continuousOn
  have hIcc0 : (0 : ℝ) ∈ Set.Icc 0 (2 * Real.pi) := by
    exact ⟨le_rfl, by positivity⟩
  have hM0 : 0 ≤ M :=
    (norm_nonneg (G 0)).trans (hM ⟨0, hIcc0, rfl⟩)
  apply Integrable.of_bound hmeas.aestronglyMeasurable M
  filter_upwards [ae_mem_Icc_radialBoundaryArcLengthMeasure K c] with t ht
  rw [rightResolventBoundaryTerm, norm_smul]
  calc
    ‖radialOutwardUnitNormal K c t‖ * ‖G t‖ ≤ 1 * M := by
      gcongr
      · exact norm_radialOutwardUnitNormal_le_one K c t
      · exact hM ⟨t, ht, rfl⟩
    _ = M := one_mul M

/-- Polynomial trace on the periodic radial boundary, bundled as a bounded
continuous scalar multiplier. -/
def radialPolynomialBoundaryFunction
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (q : Polynomial ℂ) : ℝ →ᵇ ℂ where
  toFun t := q.eval (radialBoundaryParametrization K c t)
  continuous_toFun := by
    obtain ⟨C, hC⟩ :=
      exists_lipschitzWith_radialBoundaryParametrization hconv hc hcompact
    exact q.continuous.comp hC.continuous
  map_bounded' := by
    rw [← isBounded_range_iff]
    apply (hcompact.image q.continuous).isBounded.subset
    rintro _ ⟨t, rfl⟩
    refine ⟨radialBoundaryParametrization K c t, ?_, rfl⟩
    have hmem : radialBoundaryParametrization K c t ∈ closure K :=
      frontier_subset_closure
        (radialBoundaryParametrization_mem_frontier hconv hc hcompact t)
    simpa [hcompact.isClosed.closure_eq] using hmem

@[simp]
theorem radialPolynomialBoundaryFunction_apply
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (q : Polynomial ℂ) (t : ℝ) :
    radialPolynomialBoundaryFunction hconv hc hcompact q t =
      q.eval (radialBoundaryParametrization K c t) :=
  rfl

/-- A pointwise bound on the convex body controls the multiplier norm of
its periodic boundary trace. -/
theorem norm_radialPolynomialBoundaryFunction_le
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (q : Polynomial ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hq : ∀ z ∈ K, ‖q.eval z‖ ≤ r) :
    ‖radialPolynomialBoundaryFunction hconv hc hcompact q‖ ≤ r := by
  rw [BoundedContinuousFunction.norm_le hr]
  intro t
  apply hq
  have hmem : radialBoundaryParametrization K c t ∈ closure K :=
    frontier_subset_closure
      (radialBoundaryParametrization_mem_frontier hconv hc hcompact t)
  simpa [hcompact.isClosed.closure_eq] using hmem

/-- The concrete polynomial Cauchy-resolvent package for a compact convex
body.  Only the ordinary polynomial Cauchy formula is supplied; every other
field is constructed above. -/
def polynomialCauchyResolventBoundaryOfConvexBody
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K)
    (hcauchy : ∀ q : Polynomial ℂ,
      polynomialRightResolventIntegral
          (mu := radialBoundaryArcLengthMeasure K c)
          (radialBoundaryParametrization K c)
          (radialOutwardUnitNormal K c)
          (convexBoundaryResolvent A K c) q =
        ((2 * Real.pi : ℝ) : ℂ) •
          euclideanOperator (polynomialEval q A)) :
    PolynomialCauchyResolventBoundary A
      (radialBoundaryArcLengthMeasure K c) where
  boundaryPoint := radialBoundaryParametrization K c
  outwardNormal := radialOutwardUnitNormal K c
  resolvent := convexBoundaryResolvent A K c
  normal_unit_ae :=
    ae_norm_radialOutwardUnitNormal_eq_one_arcLength hconv hc hcompact
  resolvent_ae := Filter.Eventually.of_forall fun t ↦
    convexBoundaryResolvent_mul A hconv hc hcompact hspectrum t
  support_ae := by
    filter_upwards
      [ae_radialOutwardUnitNormal_supports_arcLength hconv hc hcompact]
      with t ht
    exact fun w hw ↦ ht w (hWA hw)
  integrable_right :=
    integrable_rightResolventBoundaryTerm_convexBoundary
      A hconv hc hcompact hspectrum
  polynomial_cauchy := hcauchy

/-- End-to-end normalized sharp estimate on one compact convex body.  The
ordinary polynomial Cauchy formula is the only analytic hypothesis. -/
theorem norm_polynomialEval_le_two_of_convexBodyCauchy
    [Nonempty n]
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K)
    (hcauchy : ∀ q : Polynomial ℂ,
      polynomialRightResolventIntegral
          (mu := radialBoundaryArcLengthMeasure K c)
          (radialBoundaryParametrization K c)
          (radialOutwardUnitNormal K c)
          (convexBoundaryResolvent A K c) q =
        ((2 * Real.pi : ℝ) : ℂ) •
          euclideanOperator (polynomialEval q A))
    (q : Polynomial ℂ)
    (hq : ∀ z ∈ K, ‖q.eval z‖ ≤ 1) :
    ‖polynomialEval q A‖ ≤ 2 := by
  let _ : IsFiniteMeasure (radialBoundaryArcLengthMeasure K c) :=
    isFiniteMeasure_radialBoundaryArcLengthMeasure hconv hc hcompact
  let B := polynomialCauchyResolventBoundaryOfConvexBody
    A hconv hc hcompact hWA hspectrum hcauchy
  let f := radialPolynomialBoundaryFunction hconv hc hcompact q
  exact (B.polynomialDilationData q f
    (Filter.Eventually.of_forall fun t ↦ rfl)
    (norm_radialPolynomialBoundaryFunction_le
      hconv hc hcompact q zero_le_one hq)).norm_polynomialEval_le_two

end DiskRigidity.Operator
