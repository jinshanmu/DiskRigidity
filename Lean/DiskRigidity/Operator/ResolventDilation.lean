/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.BoundaryCompression
public import DiskRigidity.Operator.CanonicalBoundarySquareRoot
public import DiskRigidity.Operator.EqualityData
public import DiskRigidity.Operator.ResolventBoundary
public import Mathlib.Algebra.Polynomial.Smeval
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The resolvent error in the double-layer dilation

This file derives the uniform boundedness and commutation required by the
abstract dilation lemma from the concrete right-resolvent integral in (3.7).
It also reduces the exact error formula to the weighted adjoint Cauchy
identity, using the actual `L²` compression theorem.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped BoundedContinuousFunction InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A finite-dimensional resolvent commutes with its matrix. -/
theorem matrix_resolvent_commutes
    (A R : SquareMatrix n) (sigma : ℂ)
    (hR : (sigma • (1 : SquareMatrix n) - A) * R = 1) :
    Commute R A := by
  rw [commute_iff_eq]
  have hright : R * (sigma • (1 : SquareMatrix n) - A) = 1 :=
    mul_eq_one_comm.mp hR
  have hdefect :
      (sigma • (1 : SquareMatrix n) - A) * R =
        R * (sigma • (1 : SquareMatrix n) - A) :=
    hR.trans hright.symm
  have hsub : sigma • R - A * R = sigma • R - R * A := by
    simpa only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      using hdefect
  exact (sub_right_inj.mp hsub).symm

/-- Consequently a resolvent commutes with every polynomial in the matrix. -/
theorem matrix_resolvent_commutes_polynomialEval
    (A R : SquareMatrix n) (sigma : ℂ) (p : Polynomial ℂ)
    (hR : (sigma • (1 : SquareMatrix n) - A) * R = 1) :
    Commute R (polynomialEval p A) := by
  rw [polynomialEval, Polynomial.aeval_eq_smeval]
  exact (Polynomial.smeval_commute_left ℂ p
    (matrix_resolvent_commutes A R sigma hR).symm).symm

/-- The associated Euclidean operators retain the same polynomial
commutation relation. -/
theorem euclidean_resolvent_commutes_polynomialEval
    (A R : SquareMatrix n) (sigma : ℂ) (p : Polynomial ℂ)
    (hR : (sigma • (1 : SquareMatrix n) - A) * R = 1) :
    Commute (euclideanOperator R)
      (euclideanOperator (polynomialEval p A)) := by
  rw [commute_iff_eq] at *
  simpa using congrArg (euclideanOperator (n := n))
    (matrix_resolvent_commutes_polynomialEval A R sigma p hR)

variable {i : Type*} [TopologicalSpace i] [MeasurableSpace i]
  [OpensMeasurableSpace i] {mu : Measure i}

/-- The right side of (3.7), written against arclength measure using
`dσ = i ν ds`. -/
def normalizedRightResolventIntegral
    (nu : i → ℂ) (R : i → SquareMatrix n) (f : i →ᵇ ℂ) (k : ℕ) :
    EuclideanEndomorphism n :=
  ((((2 * Real.pi)⁻¹ : ℝ) : ℂ)) •
    ∫ t, ((star (f ^ k) : i →ᵇ ℂ) t) •
      rightResolventBoundaryTerm (R t) (nu t) ∂mu

/-- The weighted adjoint half which Cauchy's formula identifies with the
adjoint functional-calculus power. -/
def weightedAdjointResolventIntegral
    (nu : i → ℂ) (R : i → SquareMatrix n) (f : i →ᵇ ℂ) (k : ℕ) :
    EuclideanEndomorphism n :=
  ∫ t, ((star (f ^ k) : i →ᵇ ℂ) t) •
    adjointResolventBoundaryTerm (R t) (nu t) ∂mu

/-- The polynomial Cauchy integral on the holomorphic resolvent half.  With
`dσ = i ν ds`, the usual Cauchy formula says that this is
`2π q(A)`. -/
def polynomialRightResolventIntegral
    (sigma nu : i → ℂ) (R : i → SquareMatrix n) (q : Polynomial ℂ) :
    EuclideanEndomorphism n :=
  ∫ t, q.eval (sigma t) • rightResolventBoundaryTerm (R t) (nu t) ∂mu

omit [OpensMeasurableSpace i] in
/-- Taking the Hilbert-space adjoint of a polynomial right-resolvent
integral gives the conjugate-weighted adjoint-resolvent integral.  This is
the algebraic bridge which turns the ordinary Cauchy formula into the
weighted formula used in (3.7). -/
theorem integral_conjugateBoundary_adjointResolvent_eq_star
    (nu : i → ℂ) (R : i → SquareMatrix n) (f : i →ᵇ ℂ) (k : ℕ) :
    ∫ t, ((star (f ^ k) : i →ᵇ ℂ) t) •
        adjointResolventBoundaryTerm (R t) (nu t) ∂mu =
      star (∫ t, ((f ^ k : i →ᵇ ℂ) t) •
        rightResolventBoundaryTerm (R t) (nu t) ∂mu) := by
  calc
    _ = ∫ t, star (((f ^ k : i →ᵇ ℂ) t) •
        rightResolventBoundaryTerm (R t) (nu t)) ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp [rightResolventBoundaryTerm, adjointResolventBoundaryTerm,
        ContinuousLinearMap.star_eq_adjoint, ← euclideanOperator_conjTranspose]
    _ = star (∫ t, ((f ^ k : i →ᵇ ℂ) t) •
        rightResolventBoundaryTerm (R t) (nu t) ∂mu) :=
      by
        simpa only [starL'_apply] using
          (starL' ℝ : EuclideanEndomorphism n ≃L[ℝ]
            EuclideanEndomorphism n).integral_comp_comm
              (fun t ↦ ((f ^ k : i →ᵇ ℂ) t) •
                rightResolventBoundaryTerm (R t) (nu t))

omit [OpensMeasurableSpace i] in
/-- The weighted adjoint Cauchy formula needed in (3.7) is not an
independent analytic hypothesis: it follows by taking adjoints of the
ordinary polynomial Cauchy formula on the holomorphic resolvent half. -/
theorem weightedAdjointResolventIntegral_eq_of_polynomialCauchy
    (A : SquareMatrix n) (sigma nu : i → ℂ) (R : i → SquareMatrix n)
    (p : Polynomial ℂ) (f : i →ᵇ ℂ) (k : ℕ)
    (hboundary : ∀ᵐ t ∂mu, f t = p.eval (sigma t))
    (hcauchy : polynomialRightResolventIntegral (mu := mu) sigma nu R (p ^ k) =
      ((2 * Real.pi : ℝ) : ℂ) •
        euclideanOperator (polynomialEval (p ^ k) A)) :
    weightedAdjointResolventIntegral (mu := mu) nu R f k =
      ((2 * Real.pi : ℝ) : ℂ) •
        (ContinuousLinearMap.adjoint
          (euclideanOperator (polynomialEval p A))) ^ k := by
  have hright :
      ∫ t, ((f ^ k : i →ᵇ ℂ) t) •
          rightResolventBoundaryTerm (R t) (nu t) ∂mu =
        polynomialRightResolventIntegral (mu := mu) sigma nu R (p ^ k) := by
    rw [polynomialRightResolventIntegral]
    apply integral_congr_ae
    filter_upwards [hboundary] with t ht
    simp [ht]
  rw [weightedAdjointResolventIntegral,
    integral_conjugateBoundary_adjointResolvent_eq_star, hright, hcauchy]
  simp [ContinuousLinearMap.star_eq_adjoint, polynomialEval]

/-- Its integrand is integrable whenever the unweighted right-resolvent
boundary term is integrable. -/
theorem integrable_weightedRightResolvent
    (nu : i → ℂ) (R : i → SquareMatrix n) (f : i →ᵇ ℂ) (k : ℕ)
    (hright : Integrable
      (fun t ↦ rightResolventBoundaryTerm (R t) (nu t)) mu) :
    Integrable (fun t ↦ ((star (f ^ k) : i →ᵇ ℂ) t) •
      rightResolventBoundaryTerm (R t) (nu t)) mu :=
  integrable_boundedContinuous_smul _ hright (star (f ^ k))

/-- Integrability of the weighted adjoint half. -/
theorem integrable_weightedAdjointResolvent
    (nu : i → ℂ) (R : i → SquareMatrix n) (f : i →ᵇ ℂ) (k : ℕ)
    (hadjoint : Integrable
      (fun t ↦ adjointResolventBoundaryTerm (R t) (nu t)) mu) :
    Integrable (fun t ↦ ((star (f ^ k) : i →ᵇ ℂ) t) •
      adjointResolventBoundaryTerm (R t) (nu t)) mu :=
  integrable_boundedContinuous_smul _ hadjoint (star (f ^ k))

/-- Splitting the density under a weighted integral leaves exactly the two
weighted Cauchy halves. -/
theorem integral_weighted_normalizedDoubleLayerDensity_eq_split
    (nu : i → ℂ) (R : i → SquareMatrix n) (f : i →ᵇ ℂ) (k : ℕ)
    (hright : Integrable
      (fun t ↦ rightResolventBoundaryTerm (R t) (nu t)) mu)
    (hadjoint : Integrable
      (fun t ↦ adjointResolventBoundaryTerm (R t) (nu t)) mu) :
    ∫ t, ((star (f ^ k) : i →ᵇ ℂ) t) •
        normalizedDoubleLayerDensity (R t) (nu t) ∂mu =
      ((((2 * Real.pi)⁻¹ : ℝ) : ℂ)) •
        ((∫ t, ((star (f ^ k) : i →ᵇ ℂ) t) •
            rightResolventBoundaryTerm (R t) (nu t) ∂mu) +
          ∫ t, ((star (f ^ k) : i →ᵇ ℂ) t) •
            adjointResolventBoundaryTerm (R t) (nu t) ∂mu) := by
  let c : ℂ := (((2 * Real.pi)⁻¹ : ℝ) : ℂ)
  have heq :
      (fun t ↦ ((star (f ^ k) : i →ᵇ ℂ) t) •
        normalizedDoubleLayerDensity (R t) (nu t)) =
      fun t ↦ c •
        (((star (f ^ k) : i →ᵇ ℂ) t) •
            rightResolventBoundaryTerm (R t) (nu t) +
          ((star (f ^ k) : i →ᵇ ℂ) t) •
            adjointResolventBoundaryTerm (R t) (nu t)) := by
    funext t
    rw [normalizedDoubleLayerDensity_eq_cauchy_terms]
    dsimp [c]
    module
  rw [heq, integral_smul,
    integral_add (integrable_weightedRightResolvent nu R f k hright)
      (integrable_weightedAdjointResolvent nu R f k hadjoint)]

/-- The exact double-layer error identity (3.7) follows from the concrete
compression theorem and the weighted adjoint Cauchy formula. -/
theorem dilationError_eq_normalizedRightResolventIntegral
    [BorelSpace i] [IsFiniteMeasure mu]
    {D : PositiveBoundaryDensity (n := n) mu}
    (S : PositiveBoundarySquareRoot D)
    (T : EuclideanEndomorphism n) (nu : i → ℂ)
    (R : i → SquareMatrix n) (f : i →ᵇ ℂ) (k : ℕ)
    (hdensity : ∀ᵐ t ∂mu,
      D.density t = normalizedDoubleLayerDensity (R t) (nu t))
    (hright : Integrable
      (fun t ↦ rightResolventBoundaryTerm (R t) (nu t)) mu)
    (hadjoint : Integrable
      (fun t ↦ adjointResolventBoundaryTerm (R t) (nu t)) mu)
    (hcauchyAdjoint : weightedAdjointResolventIntegral (mu := mu) nu R f k =
      ((2 * Real.pi : ℝ) : ℂ) • (ContinuousLinearMap.adjoint T) ^ k) :
    dilationError T
        (boundaryMultiplier (E := EuclideanVector n) (mu := mu) f)
        S.boundaryIsometry k =
      normalizedRightResolventIntegral (mu := mu) nu R f k := by
  have hdensityIntegral :
      ∫ t, ((star (f ^ k) : i →ᵇ ℂ) t) • D.density t ∂mu =
        ∫ t, ((star (f ^ k) : i →ᵇ ℂ) t) •
          normalizedDoubleLayerDensity (R t) (nu t) ∂mu := by
    apply integral_congr_ae
    filter_upwards [hdensity] with t ht
    rw [ht]
  rw [dilationError, boundaryCompression_eq_boundaryPhi, boundaryPhi,
    hdensityIntegral,
    integral_weighted_normalizedDoubleLayerDensity_eq_split nu R f k hright hadjoint,
    ← weightedAdjointResolventIntegral, hcauchyAdjoint,
    normalizedRightResolventIntegral]
  have hpi : (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
      (((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    push_cast
    field_simp [ne_of_gt Real.pi_pos]
  simp only [smul_add, smul_smul]
  rw [hpi]
  norm_num
  congr 1
  ring

omit [OpensMeasurableSpace i] in
/-- The resolvent integral in (3.7) has a bound independent of the power. -/
theorem norm_normalizedRightResolventIntegral_le
    (nu : i → ℂ) (R : i → SquareMatrix n) (f : i →ᵇ ℂ)
    (hf : ‖f‖ ≤ 1)
    (hright : Integrable
      (fun t ↦ rightResolventBoundaryTerm (R t) (nu t)) mu)
    (k : ℕ) :
    ‖normalizedRightResolventIntegral (mu := mu) nu R f k‖ ≤
      (2 * Real.pi)⁻¹ *
        ∫ t, ‖rightResolventBoundaryTerm (R t) (nu t)‖ ∂mu := by
  rw [normalizedRightResolventIntegral, norm_smul]
  have hcoef :
      ‖((((2 * Real.pi)⁻¹ : ℝ) : ℂ))‖ = (2 * Real.pi)⁻¹ := by
    rw [Complex.norm_real]
    exact Real.norm_of_nonneg (by positivity)
  rw [hcoef]
  gcongr
  apply norm_integral_le_of_norm_le hright.norm
  filter_upwards [] with t
  rw [norm_smul, BoundedContinuousFunction.star_apply, norm_star,
    BoundedContinuousFunction.pow_apply, norm_pow]
  have hft : ‖f t‖ ≤ 1 := (f.norm_coe_le_norm t).trans hf
  exact (mul_le_mul_of_nonneg_right
    (pow_le_one₀ (norm_nonneg (f t)) hft) (norm_nonneg _)).trans_eq
      (one_mul _)

omit [DecidableEq n] [TopologicalSpace i] [OpensMeasurableSpace i] in
/-- Bochner integration preserves a common commutation relation. -/
theorem commute_integral
    (T : EuclideanEndomorphism n) (F : i → EuclideanEndomorphism n)
    (hF : Integrable F mu) (hcomm : ∀ᵐ t ∂mu, Commute (F t) T) :
    Commute (∫ t, F t ∂mu) T := by
  rw [commute_iff_eq]
  let mulRightT : EuclideanEndomorphism n →L[ℂ] EuclideanEndomorphism n :=
    (ContinuousLinearMap.mul ℂ (EuclideanEndomorphism n)).flip T
  let mulLeftT : EuclideanEndomorphism n →L[ℂ] EuclideanEndomorphism n :=
    ContinuousLinearMap.mul ℂ (EuclideanEndomorphism n) T
  calc
    (∫ t, F t ∂mu) * T = ∫ t, F t * T ∂mu := by
      exact (mulRightT.integral_comp_comm hF).symm
    _ = ∫ t, T * F t ∂mu := integral_congr_ae (hcomm.mono fun _ ht ↦ ht.eq)
    _ = T * ∫ t, F t ∂mu := mulLeftT.integral_comp_comm hF

/-- The normalized right-resolvent integral commutes with a polynomial
functional-calculus value. -/
theorem normalizedRightResolventIntegral_commutes_polynomialEval
    (A : SquareMatrix n) (sigma nu : i → ℂ) (R : i → SquareMatrix n)
    (f : i →ᵇ ℂ) (p : Polynomial ℂ) (k : ℕ)
    (hresolvent : ∀ᵐ t ∂mu,
      (sigma t • (1 : SquareMatrix n) - A) * R t = 1)
    (hright : Integrable
      (fun t ↦ rightResolventBoundaryTerm (R t) (nu t)) mu) :
    Commute (normalizedRightResolventIntegral (mu := mu) nu R f k)
      (euclideanOperator (polynomialEval p A)) := by
  let F : i → EuclideanEndomorphism n := fun t ↦
    ((star (f ^ k) : i →ᵇ ℂ) t) •
      rightResolventBoundaryTerm (R t) (nu t)
  have hF : Integrable F mu := integrable_weightedRightResolvent nu R f k hright
  have hcommF : ∀ᵐ t ∂mu,
      Commute (F t) (euclideanOperator (polynomialEval p A)) := by
    filter_upwards [hresolvent] with t hR
    exact (euclidean_resolvent_commutes_polynomialEval A (R t) (sigma t) p hR).smul_left
      (nu t) |>.smul_left ((star (f ^ k) : i →ᵇ ℂ) t)
  exact (commute_integral _ F hF hcommF).smul_left
    ((((2 * Real.pi)⁻¹ : ℝ) : ℂ))

/-- Concrete convex-boundary/resolvent data used in Proposition 3.2.  Its
fields are geometric support and resolvent identities plus the two ordinary
Cauchy formulas; positivity, mass two, and all dilation estimates are not
stored here. -/
structure CauchyResolventBoundary (A : SquareMatrix n) (mu : Measure i) where
  /-- Boundary point at a parameter value. -/
  boundaryPoint : i → ℂ
  /-- Outward unit normal at a parameter value. -/
  outwardNormal : i → ℂ
  /-- Resolvent matrix at the boundary point. -/
  resolvent : i → SquareMatrix n
  normal_unit_ae : ∀ᵐ t ∂mu, ‖outwardNormal t‖ = 1
  resolvent_ae : ∀ᵐ t ∂mu,
    (boundaryPoint t • (1 : SquareMatrix n) - A) * resolvent t = 1
  support_ae : ∀ᵐ t ∂mu, ∀ w ∈ numericalRange A,
    (star (outwardNormal t) * w).re ≤
      (star (outwardNormal t) * boundaryPoint t).re
  integrable_right : Integrable
    (fun t ↦ rightResolventBoundaryTerm (resolvent t) (outwardNormal t)) mu
  integrable_adjoint : Integrable
    (fun t ↦ adjointResolventBoundaryTerm (resolvent t) (outwardNormal t)) mu
  cauchy_right :
    ∫ t, rightResolventBoundaryTerm (resolvent t) (outwardNormal t) ∂mu =
      ((2 * Real.pi : ℝ) : ℂ) • (1 : EuclideanEndomorphism n)
  cauchy_adjoint :
    ∫ t, adjointResolventBoundaryTerm (resolvent t) (outwardNormal t) ∂mu =
      ((2 * Real.pi : ℝ) : ℂ) • (1 : EuclideanEndomorphism n)

/-- The positive density of mass `2 I` constructed from concrete boundary
resolvent data. -/
def CauchyResolventBoundary.positiveDensity
    {A : SquareMatrix n} (B : CauchyResolventBoundary A mu) :
    PositiveBoundaryDensity (n := n) mu :=
  positiveBoundaryDensityOfCauchyResolvent A B.boundaryPoint B.outwardNormal
    B.resolvent B.resolvent_ae B.support_ae B.integrable_right
    B.integrable_adjoint B.cauchy_right B.cauchy_adjoint

/-- The constructed density is definitionally the normalized double-layer
density. -/
@[simp]
theorem CauchyResolventBoundary.positiveDensity_apply
    {A : SquareMatrix n} (B : CauchyResolventBoundary A mu) (t : i) :
    B.positiveDensity.density t =
      normalizedDoubleLayerDensity (B.resolvent t) (B.outwardNormal t) :=
  rfl

/-- A boundary package carrying just the holomorphic polynomial Cauchy
formula.  Its adjoint Cauchy identity and all conjugate-weighted identities
are consequences, rather than separate assumptions. -/
structure PolynomialCauchyResolventBoundary
    (A : SquareMatrix n) (mu : Measure i) where
  /-- Boundary point at a parameter value. -/
  boundaryPoint : i → ℂ
  /-- Outward unit normal at a parameter value. -/
  outwardNormal : i → ℂ
  /-- Resolvent matrix at the boundary point. -/
  resolvent : i → SquareMatrix n
  normal_unit_ae : ∀ᵐ t ∂mu, ‖outwardNormal t‖ = 1
  resolvent_ae : ∀ᵐ t ∂mu,
    (boundaryPoint t • (1 : SquareMatrix n) - A) * resolvent t = 1
  support_ae : ∀ᵐ t ∂mu, ∀ w ∈ numericalRange A,
    (star (outwardNormal t) * w).re ≤
      (star (outwardNormal t) * boundaryPoint t).re
  integrable_right : Integrable
    (fun t ↦ rightResolventBoundaryTerm (resolvent t) (outwardNormal t)) mu
  polynomial_cauchy : ∀ q : Polynomial ℂ,
    polynomialRightResolventIntegral (mu := mu) boundaryPoint outwardNormal
        resolvent q =
      ((2 * Real.pi : ℝ) : ℂ) •
        euclideanOperator (polynomialEval q A)

omit [TopologicalSpace i] [OpensMeasurableSpace i] in
/-- The adjoint resolvent half is integrable because it is pointwise the
adjoint of the integrable holomorphic half. -/
theorem PolynomialCauchyResolventBoundary.integrable_adjoint
    {A : SquareMatrix n} (B : PolynomialCauchyResolventBoundary A mu) :
    Integrable
      (fun t ↦ adjointResolventBoundaryTerm
        (B.resolvent t) (B.outwardNormal t)) mu := by
  have hstar : Integrable
      (fun t ↦ star (rightResolventBoundaryTerm
        (B.resolvent t) (B.outwardNormal t))) mu :=
    (starL' ℝ : EuclideanEndomorphism n ≃L[ℝ]
      EuclideanEndomorphism n).integrable_comp_iff.mpr B.integrable_right
  exact hstar.congr (Filter.Eventually.of_forall fun t ↦ by
    simp [rightResolventBoundaryTerm, adjointResolventBoundaryTerm,
      ContinuousLinearMap.star_eq_adjoint, ← euclideanOperator_conjTranspose])

omit [TopologicalSpace i] [OpensMeasurableSpace i] in
/-- The polynomial Cauchy formula at the constant polynomial is the ordinary
right-resolvent mass identity. -/
theorem PolynomialCauchyResolventBoundary.cauchy_right
    {A : SquareMatrix n} (B : PolynomialCauchyResolventBoundary A mu) :
    ∫ t, rightResolventBoundaryTerm
          (B.resolvent t) (B.outwardNormal t) ∂mu =
      ((2 * Real.pi : ℝ) : ℂ) • (1 : EuclideanEndomorphism n) := by
  simpa [polynomialRightResolventIntegral, polynomialEval] using
    B.polynomial_cauchy 1

omit [OpensMeasurableSpace i] in
/-- Taking adjoints of the preceding identity gives the ordinary adjoint
resolvent mass identity. -/
theorem PolynomialCauchyResolventBoundary.cauchy_adjoint
    {A : SquareMatrix n} (B : PolynomialCauchyResolventBoundary A mu) :
    ∫ t, adjointResolventBoundaryTerm
          (B.resolvent t) (B.outwardNormal t) ∂mu =
      ((2 * Real.pi : ℝ) : ℂ) • (1 : EuclideanEndomorphism n) := by
  have hstar := integral_conjugateBoundary_adjointResolvent_eq_star
    (mu := mu) B.outwardNormal B.resolvent (1 : i →ᵇ ℂ) 0
  have hstar' :
      ∫ t, adjointResolventBoundaryTerm
          (B.resolvent t) (B.outwardNormal t) ∂mu =
        star (∫ t, rightResolventBoundaryTerm
          (B.resolvent t) (B.outwardNormal t) ∂mu) := by
    simpa using hstar
  rw [hstar', B.cauchy_right]
  simp

/-- Forgetting the polynomial enhancement produces exactly the concrete
Cauchy-resolvent boundary package used by the positive double layer. -/
def PolynomialCauchyResolventBoundary.toCauchyResolventBoundary
    {A : SquareMatrix n} (B : PolynomialCauchyResolventBoundary A mu) :
    CauchyResolventBoundary A mu where
  boundaryPoint := B.boundaryPoint
  outwardNormal := B.outwardNormal
  resolvent := B.resolvent
  normal_unit_ae := B.normal_unit_ae
  resolvent_ae := B.resolvent_ae
  support_ae := B.support_ae
  integrable_right := B.integrable_right
  integrable_adjoint := B.integrable_adjoint
  cauchy_right := B.cauchy_right
  cauchy_adjoint := B.cauchy_adjoint

/-- For one polynomial, this is the remaining analytic data after the
positive double-layer density has been constructed.  The boundary function
is explicitly the trace of the polynomial.  The sole Cauchy assumption is
the weighted adjoint formula; (3.7), its bound, and its commutation relation
are derived below. -/
structure PolynomialResolventDilationData
    {A : SquareMatrix n} (B : CauchyResolventBoundary A mu)
    (p : Polynomial ℂ) where
  /-- Bounded boundary trace of the polynomial. -/
  boundaryFunction : i →ᵇ ℂ
  boundaryFunction_eq_eval_ae : ∀ᵐ t ∂mu,
    boundaryFunction t = p.eval (B.boundaryPoint t)
  boundaryFunction_norm_le_one : ‖boundaryFunction‖ ≤ 1
  weighted_adjoint_cauchy : ∀ k : ℕ, 1 ≤ k →
    weightedAdjointResolventIntegral (mu := mu) B.outwardNormal B.resolvent
        boundaryFunction k =
      ((2 * Real.pi : ℝ) : ℂ) •
        (ContinuousLinearMap.adjoint
          (euclideanOperator (polynomialEval p A))) ^ k

/-- The square root in the polynomial dilation data is constructed
canonically from its positive resolvent density. -/
noncomputable def PolynomialResolventDilationData.squareRoot
    {A : SquareMatrix n} {B : CauchyResolventBoundary A mu}
    {p : Polynomial ℂ} (_P : PolynomialResolventDilationData B p) :
    PositiveBoundarySquareRoot B.positiveDensity :=
  B.positiveDensity.canonicalSquareRoot

/-- Ordinary holomorphic polynomial Cauchy formulas automatically supply
the conjugate-weighted adjoint formula required by one polynomial dilation.
Thus no separate weighted Cauchy hypothesis remains. -/
def PolynomialCauchyResolventBoundary.polynomialDilationData
    {A : SquareMatrix n} (B : PolynomialCauchyResolventBoundary A mu)
    (p : Polynomial ℂ) (f : i →ᵇ ℂ)
    (hboundary : ∀ᵐ t ∂mu, f t = p.eval (B.boundaryPoint t))
    (hfnorm : ‖f‖ ≤ 1) :
    PolynomialResolventDilationData B.toCauchyResolventBoundary p where
  boundaryFunction := f
  boundaryFunction_eq_eval_ae := hboundary
  boundaryFunction_norm_le_one := hfnorm
  weighted_adjoint_cauchy := by
    intro k _hk
    exact weightedAdjointResolventIntegral_eq_of_polynomialCauchy
      A B.boundaryPoint B.outwardNormal B.resolvent p f k hboundary
      (B.polynomial_cauchy (p ^ k))

variable [BorelSpace i] [IsFiniteMeasure mu]

/-- Formula (3.7), now a theorem of the concrete polynomial boundary data. -/
theorem PolynomialResolventDilationData.error_eq
    {A : SquareMatrix n} {B : CauchyResolventBoundary A mu}
    {p : Polynomial ℂ} (P : PolynomialResolventDilationData B p)
    (k : ℕ) (hk : 1 ≤ k) :
    dilationError (euclideanOperator (polynomialEval p A))
        (boundaryMultiplier (E := EuclideanVector n) (mu := mu)
          P.boundaryFunction)
        P.squareRoot.boundaryIsometry k =
      normalizedRightResolventIntegral (mu := mu) B.outwardNormal B.resolvent
        P.boundaryFunction k := by
  exact dilationError_eq_normalizedRightResolventIntegral P.squareRoot
    (euclideanOperator (polynomialEval p A)) B.outwardNormal B.resolvent
    P.boundaryFunction k (Filter.Eventually.of_forall fun t ↦ by simp)
    B.integrable_right B.integrable_adjoint (P.weighted_adjoint_cauchy k hk)

/-- The errors in the concrete polynomial dilation are uniformly bounded. -/
theorem PolynomialResolventDilationData.errors_bounded
    {A : SquareMatrix n} {B : CauchyResolventBoundary A mu}
    {p : Polynomial ℂ} (P : PolynomialResolventDilationData B p) :
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k →
      ‖dilationError (euclideanOperator (polynomialEval p A))
        (boundaryMultiplier (E := EuclideanVector n) (mu := mu)
          P.boundaryFunction)
        P.squareRoot.boundaryIsometry k‖ ≤ C := by
  refine ⟨(2 * Real.pi)⁻¹ *
    ∫ t, ‖rightResolventBoundaryTerm (B.resolvent t) (B.outwardNormal t)‖ ∂mu,
    ?_⟩
  intro k hk
  rw [P.error_eq k hk]
  exact norm_normalizedRightResolventIntegral_le B.outwardNormal B.resolvent
    P.boundaryFunction P.boundaryFunction_norm_le_one B.integrable_right k

/-- The errors in the concrete polynomial dilation commute with the
polynomial matrix value. -/
theorem PolynomialResolventDilationData.errors_commute
    {A : SquareMatrix n} {B : CauchyResolventBoundary A mu}
    {p : Polynomial ℂ} (P : PolynomialResolventDilationData B p) :
    ∀ k : ℕ, 1 ≤ k →
      Commute
        (dilationError (euclideanOperator (polynomialEval p A))
          (boundaryMultiplier (E := EuclideanVector n) (mu := mu)
            P.boundaryFunction)
          P.squareRoot.boundaryIsometry k)
        (euclideanOperator (polynomialEval p A)) := by
  intro k hk
  rw [P.error_eq k hk]
  exact normalizedRightResolventIntegral_commutes_polynomialEval A
    B.boundaryPoint B.outwardNormal B.resolvent P.boundaryFunction p k
    B.resolvent_ae B.integrable_right

/-- The concrete boundary/resolvent construction supplies the exact
`DilationWitness` consumed by the sharp abstract lemma. -/
def PolynomialResolventDilationData.witness
    {A : SquareMatrix n} {B : CauchyResolventBoundary A mu}
    {p : Polynomial ℂ} (P : PolynomialResolventDilationData B p) :
    DilationWitness (K := Lp (EuclideanVector n) 2 mu)
      (euclideanOperator (polynomialEval p A)) :=
  boundaryDilationWitness (euclideanOperator (polynomialEval p A))
    P.squareRoot P.boundaryFunction P.boundaryFunction_norm_le_one
    P.errors_bounded P.errors_commute

/-- The normalized sharp bound obtained from the concrete double-layer
construction, with no norm or error conclusion assumed in its data. -/
theorem PolynomialResolventDilationData.norm_polynomialEval_le_two
    [Nonempty n]
    {A : SquareMatrix n} {B : CauchyResolventBoundary A mu}
    {p : Polynomial ℂ} (P : PolynomialResolventDilationData B p) :
    ‖polynomialEval p A‖ ≤ 2 := by
  rw [matrix_norm_eq_operator_norm]
  exact P.witness.norm_le_two

/-- The exact homogeneous polynomial estimate (3.3), when the concrete
boundary/resolvent construction is available for every normalized
polynomial. -/
theorem sharp_polynomial_bound_of_resolvent_dilations
    [Nonempty n]
    (A : SquareMatrix n) (B : CauchyResolventBoundary A mu)
    (hdata : ∀ q : Polynomial ℂ, maxPolynomialModulus A q ≤ 1 →
      PolynomialResolventDilationData B q)
    (p : Polynomial ℂ) :
    ‖polynomialEval p A‖ ≤ 2 * maxPolynomialModulus A p := by
  apply polynomial_bound_of_normalized_bound A
  intro q hq
  exact (hdata q hq).norm_polynomialEval_le_two

/-- A direct end-to-end form of the normalized estimate from raw
parametrized convex-boundary data.  Every hypothesis is geometric or an
ordinary Cauchy/integrability assertion; the square root, `L²` isometry,
dilation error, boundedness, and commutation are all constructed. -/
theorem norm_polynomialEval_le_two_of_parametrizedBoundary
    [Nonempty n]
    (A : SquareMatrix n) (p : Polynomial ℂ)
    (sigma nu : i → ℂ) (R : i → SquareMatrix n) (f : i →ᵇ ℂ)
    (hunit : ∀ᵐ t ∂mu, ‖nu t‖ = 1)
    (hresolvent : ∀ᵐ t ∂mu,
      (sigma t • (1 : SquareMatrix n) - A) * R t = 1)
    (hsupport : ∀ᵐ t ∂mu, ∀ w ∈ numericalRange A,
      (star (nu t) * w).re ≤ (star (nu t) * sigma t).re)
    (hright : Integrable
      (fun t ↦ rightResolventBoundaryTerm (R t) (nu t)) mu)
    (hadjoint : Integrable
      (fun t ↦ adjointResolventBoundaryTerm (R t) (nu t)) mu)
    (hcauchyRight :
      ∫ t, rightResolventBoundaryTerm (R t) (nu t) ∂mu =
        ((2 * Real.pi : ℝ) : ℂ) • (1 : EuclideanEndomorphism n))
    (hcauchyAdjoint :
      ∫ t, adjointResolventBoundaryTerm (R t) (nu t) ∂mu =
        ((2 * Real.pi : ℝ) : ℂ) • (1 : EuclideanEndomorphism n))
    (hboundaryValue : ∀ᵐ t ∂mu, f t = p.eval (sigma t))
    (hf : ‖f‖ ≤ 1)
    (hweightedAdjoint : ∀ k : ℕ, 1 ≤ k →
      weightedAdjointResolventIntegral (mu := mu) nu R f k =
        ((2 * Real.pi : ℝ) : ℂ) •
          (ContinuousLinearMap.adjoint
            (euclideanOperator (polynomialEval p A))) ^ k) :
    ‖polynomialEval p A‖ ≤ 2 := by
  let B : CauchyResolventBoundary A mu :=
    { boundaryPoint := sigma
      outwardNormal := nu
      resolvent := R
      normal_unit_ae := hunit
      resolvent_ae := hresolvent
      support_ae := hsupport
      integrable_right := hright
      integrable_adjoint := hadjoint
      cauchy_right := hcauchyRight
      cauchy_adjoint := hcauchyAdjoint }
  let P : PolynomialResolventDilationData B p :=
    { boundaryFunction := f
      boundaryFunction_eq_eval_ae := hboundaryValue
      boundaryFunction_norm_le_one := hf
      weighted_adjoint_cauchy := hweightedAdjoint }
  exact P.norm_polynomialEval_le_two

/-- The exact homogeneous bound (3.3) from one raw parametrized boundary and
a boundary functional calculus for every normalized polynomial. -/
theorem sharp_polynomial_bound_of_parametrizedBoundary
    [Nonempty n]
    (A : SquareMatrix n)
    (sigma nu : i → ℂ) (R : i → SquareMatrix n)
    (hunit : ∀ᵐ t ∂mu, ‖nu t‖ = 1)
    (hresolvent : ∀ᵐ t ∂mu,
      (sigma t • (1 : SquareMatrix n) - A) * R t = 1)
    (hsupport : ∀ᵐ t ∂mu, ∀ w ∈ numericalRange A,
      (star (nu t) * w).re ≤ (star (nu t) * sigma t).re)
    (hright : Integrable
      (fun t ↦ rightResolventBoundaryTerm (R t) (nu t)) mu)
    (hadjoint : Integrable
      (fun t ↦ adjointResolventBoundaryTerm (R t) (nu t)) mu)
    (hcauchyRight :
      ∫ t, rightResolventBoundaryTerm (R t) (nu t) ∂mu =
        ((2 * Real.pi : ℝ) : ℂ) • (1 : EuclideanEndomorphism n))
    (hcauchyAdjoint :
      ∫ t, adjointResolventBoundaryTerm (R t) (nu t) ∂mu =
        ((2 * Real.pi : ℝ) : ℂ) • (1 : EuclideanEndomorphism n))
    (boundaryFunction : Polynomial ℂ → i →ᵇ ℂ)
    (hboundaryValue : ∀ q : Polynomial ℂ, ∀ᵐ t ∂mu,
      boundaryFunction q t = q.eval (sigma t))
    (hboundaryNorm : ∀ q : Polynomial ℂ,
      maxPolynomialModulus A q ≤ 1 → ‖boundaryFunction q‖ ≤ 1)
    (hweightedAdjoint : ∀ q : Polynomial ℂ,
      maxPolynomialModulus A q ≤ 1 → ∀ k : ℕ, 1 ≤ k →
        weightedAdjointResolventIntegral (mu := mu) nu R
            (boundaryFunction q) k =
          ((2 * Real.pi : ℝ) : ℂ) •
            (ContinuousLinearMap.adjoint
              (euclideanOperator (polynomialEval q A))) ^ k)
    (p : Polynomial ℂ) :
    ‖polynomialEval p A‖ ≤ 2 * maxPolynomialModulus A p := by
  let B : CauchyResolventBoundary A mu :=
    { boundaryPoint := sigma
      outwardNormal := nu
      resolvent := R
      normal_unit_ae := hunit
      resolvent_ae := hresolvent
      support_ae := hsupport
      integrable_right := hright
      integrable_adjoint := hadjoint
      cauchy_right := hcauchyRight
      cauchy_adjoint := hcauchyAdjoint }
  apply sharp_polynomial_bound_of_resolvent_dilations A B
  intro q hq
  exact
    { boundaryFunction := boundaryFunction q
      boundaryFunction_eq_eval_ae := hboundaryValue q
      boundaryFunction_norm_le_one := hboundaryNorm q hq
      weighted_adjoint_cauchy := hweightedAdjoint q hq }

/-- The normalized estimate from a parametrized supporting boundary and the
single, ordinary holomorphic polynomial Cauchy formula.  Both the adjoint
mass identity and every conjugate-weighted formula in (3.7) are derived. -/
theorem norm_polynomialEval_le_two_of_polynomialCauchyBoundary
    [Nonempty n]
    (A : SquareMatrix n) (p : Polynomial ℂ)
    (sigma nu : i → ℂ) (R : i → SquareMatrix n) (f : i →ᵇ ℂ)
    (hunit : ∀ᵐ t ∂mu, ‖nu t‖ = 1)
    (hresolvent : ∀ᵐ t ∂mu,
      (sigma t • (1 : SquareMatrix n) - A) * R t = 1)
    (hsupport : ∀ᵐ t ∂mu, ∀ w ∈ numericalRange A,
      (star (nu t) * w).re ≤ (star (nu t) * sigma t).re)
    (hright : Integrable
      (fun t ↦ rightResolventBoundaryTerm (R t) (nu t)) mu)
    (hcauchy : ∀ q : Polynomial ℂ,
      polynomialRightResolventIntegral (mu := mu) sigma nu R q =
        ((2 * Real.pi : ℝ) : ℂ) •
          euclideanOperator (polynomialEval q A))
    (hboundaryValue : ∀ᵐ t ∂mu, f t = p.eval (sigma t))
    (hf : ‖f‖ ≤ 1) :
    ‖polynomialEval p A‖ ≤ 2 := by
  let B : PolynomialCauchyResolventBoundary A mu :=
    { boundaryPoint := sigma
      outwardNormal := nu
      resolvent := R
      normal_unit_ae := hunit
      resolvent_ae := hresolvent
      support_ae := hsupport
      integrable_right := hright
      polynomial_cauchy := hcauchy }
  exact (B.polynomialDilationData p f hboundaryValue hf).norm_polynomialEval_le_two

/-- The exact homogeneous sharp polynomial estimate from one parametrized
supporting boundary and the ordinary holomorphic polynomial Cauchy formula.
No positive density, square root, dilation, adjoint Cauchy formula, or
weighted Cauchy formula is supplied as a hypothesis. -/
theorem sharp_polynomial_bound_of_polynomialCauchyBoundary
    [Nonempty n]
    (A : SquareMatrix n)
    (sigma nu : i → ℂ) (R : i → SquareMatrix n)
    (hunit : ∀ᵐ t ∂mu, ‖nu t‖ = 1)
    (hresolvent : ∀ᵐ t ∂mu,
      (sigma t • (1 : SquareMatrix n) - A) * R t = 1)
    (hsupport : ∀ᵐ t ∂mu, ∀ w ∈ numericalRange A,
      (star (nu t) * w).re ≤ (star (nu t) * sigma t).re)
    (hright : Integrable
      (fun t ↦ rightResolventBoundaryTerm (R t) (nu t)) mu)
    (hcauchy : ∀ q : Polynomial ℂ,
      polynomialRightResolventIntegral (mu := mu) sigma nu R q =
        ((2 * Real.pi : ℝ) : ℂ) •
          euclideanOperator (polynomialEval q A))
    (boundaryFunction : Polynomial ℂ → i →ᵇ ℂ)
    (hboundaryValue : ∀ q : Polynomial ℂ, ∀ᵐ t ∂mu,
      boundaryFunction q t = q.eval (sigma t))
    (hboundaryNorm : ∀ q : Polynomial ℂ,
      maxPolynomialModulus A q ≤ 1 → ‖boundaryFunction q‖ ≤ 1)
    (p : Polynomial ℂ) :
    ‖polynomialEval p A‖ ≤ 2 * maxPolynomialModulus A p := by
  let B : PolynomialCauchyResolventBoundary A mu :=
    { boundaryPoint := sigma
      outwardNormal := nu
      resolvent := R
      normal_unit_ae := hunit
      resolvent_ae := hresolvent
      support_ae := hsupport
      integrable_right := hright
      polynomial_cauchy := hcauchy }
  apply sharp_polynomial_bound_of_resolvent_dilations A
    B.toCauchyResolventBoundary
  intro q hq
  exact B.polynomialDilationData q (boundaryFunction q)
    (hboundaryValue q) (hboundaryNorm q hq)

/-- The full equality and boundary-kernel data of Proposition 3.3 extracted
from concrete forward and reflected-boundary resolvent constructions.  The
matrix equality identifies the reflected polynomial value with the adjoint;
none of the four vector identities or the boundary kernel is assumed. -/
theorem exists_sharpEqualityData_and_resolventBoundaryKernel
    [Nonempty n]
    {A Aadj : SquareMatrix n}
    {B : CauchyResolventBoundary A mu}
    {Badj : CauchyResolventBoundary Aadj mu}
    {p q : Polynomial ℂ}
    (P : PolynomialResolventDilationData B p)
    (Padj : PolynomialResolventDilationData Badj q)
    (hadj : euclideanOperator (polynomialEval q Aadj) =
      ContinuousLinearMap.adjoint
        (euclideanOperator (polynomialEval p A)))
    (hnorm : ‖euclideanOperator (polynomialEval p A)‖ = 2)
    (hradius : spectralRadius ℂ
      (euclideanOperator (polynomialEval p A)) < 1) :
    ∃ x y : EuclideanVector n,
      SharpEqualityData (euclideanOperator (polynomialEval p A)) x y ∧
        ∀ᵐ t ∂mu,
          P.squareRoot.factor t
            (y - P.boundaryFunction t • x) = 0 := by
  let T := euclideanOperator (polynomialEval p A)
  let D := P.witness
  let Dadj : DilationWitness (K := Lp (EuclideanVector n) 2 mu)
      (ContinuousLinearMap.adjoint T) := by
    rw [← hadj]
    exact Padj.witness
  let realization : BoundaryMultiplicationRealization D mu :=
    BoundaryMultiplicationRealization.ofLp D P.boundaryFunction
      P.squareRoot.factor rfl P.squareRoot.boundaryIsometry_coe_ae
  simpa only [T, realization, BoundaryMultiplicationRealization.ofLp] using
    (exists_sharpEqualityData_and_boundaryKernel T D Dadj realization
      hnorm hradius)

end DiskRigidity.Operator
