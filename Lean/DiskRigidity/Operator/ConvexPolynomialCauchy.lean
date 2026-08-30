/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.ConvexResolventMass
public import DiskRigidity.Operator.FoundationUnitary
public import DiskRigidity.Operator.OuterParallelSharpBound

/-!
# The concrete polynomial Cauchy formula on a convex boundary

The constant-resolvent mass computed by the convex homotopy is promoted,
by the elementary resolvent recurrence and the vanishing polynomial normal
moments, to the full polynomial Cauchy formula.  No contour formula is an
input to this file.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set Topology
open scoped BoundedContinuousFunction InnerProductSpace Matrix
  Matrix.Norms.L2Operator NNReal Pointwise

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The boundary integral of the `k`th scalar power times the resolvent. -/
def powerBoundaryResolventIntegral
    (A : SquareMatrix n) (K : Set ℂ) (c : ℂ) (k : ℕ) :
    EuclideanEndomorphism n :=
  ∫ t, (radialBoundaryParametrization K c t) ^ k •
      (radialOutwardUnitNormal K c t •
        homotopyBoundaryOperatorResolvent A K c 1 t)
    ∂radialBoundaryArcLengthMeasure K c

/-- Every power-weighted boundary resolvent integrand is integrable. -/
theorem integrable_powerBoundaryResolventIntegral
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K) (k : ℕ) :
    Integrable
      (fun t ↦ (radialBoundaryParametrization K c t) ^ k •
        (radialOutwardUnitNormal K c t •
          homotopyBoundaryOperatorResolvent A K c 1 t))
      (radialBoundaryArcLengthMeasure K c) := by
  let f := radialPolynomialBoundaryFunction hconv hc hcompact
    (Polynomial.X ^ k)
  have hbase := integrable_homotopyResolventMass_Icc
    A hconv hc hcompact hWA hspectrum
      (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
  have hbounded : ∀ᵐ t ∂radialBoundaryArcLengthMeasure K c,
      ‖f t‖ ≤ ‖f‖ := Filter.Eventually.of_forall f.norm_coe_le_norm
  have h := hbase.bdd_smul ‖f‖
    f.continuous.aestronglyMeasurable hbounded
  change Integrable
    (fun t ↦ f t • (radialOutwardUnitNormal K c t •
      homotopyBoundaryOperatorResolvent A K c 1 t))
    (radialBoundaryArcLengthMeasure K c) at h
  simpa only [f, radialPolynomialBoundaryFunction_apply,
    Polynomial.eval_pow, Polynomial.eval_X] using h

/-- Multiplying a resolvent by its scalar parameter yields the identity
plus the matrix times the resolvent. -/
theorem smul_homotopyBoundaryOperatorResolvent_one_eq
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K) (t : ℝ) :
    radialBoundaryParametrization K c t •
        homotopyBoundaryOperatorResolvent A K c 1 t =
      1 + euclideanOperator A *
        homotopyBoundaryOperatorResolvent A K c 1 t := by
  let σ := radialBoundaryParametrization K c t
  let R := homotopyBoundaryOperatorResolvent A K c 1 t
  have hRmatrix := radialBoundary_mem_resolventSet_convexMatrixHomotopy_Icc
    A hconv hc hcompact hWA hspectrum
      (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1) t
  have hR := AlgHom.mem_resolventSet_apply
    (euclideanOperator (n := n)) hRmatrix
  rw [← convexOperatorHomotopy_eq_euclideanOperator] at hR
  have hinv :
      (σ • (1 : EuclideanEndomorphism n) - euclideanOperator A) * R = 1 := by
    rw [show euclideanOperator A = convexOperatorHomotopy A c 1 by
      rw [convexOperatorHomotopy_eq_euclideanOperator,
        convexMatrixHomotopy_one]]
    dsimp only [R, σ, homotopyBoundaryOperatorResolvent]
    rw [spectrum.resolvent_eq hR]
    simpa only [Algebra.algebraMap_eq_smul_one, hR.unit_spec] using
      hR.unit.mul_inv
  have hexpand :
      (σ • (1 : EuclideanEndomorphism n) - euclideanOperator A) * R =
        σ • R - euclideanOperator A * R := by
    simp only [sub_mul, smul_mul_assoc, one_mul]
  rw [hexpand] at hinv
  dsimp only [σ, R] at hinv ⊢
  exact eq_add_of_sub_eq hinv

/-- Pointwise resolvent recurrence for the power-weighted boundary
integrands. -/
theorem powerBoundaryResolventIntegrand_succ
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K) (k : ℕ) (t : ℝ) :
    radialBoundaryParametrization K c t ^ (k + 1) •
        (radialOutwardUnitNormal K c t •
          homotopyBoundaryOperatorResolvent A K c 1 t) =
      radialBoundaryParametrization K c t ^ k •
          (radialOutwardUnitNormal K c t •
            (1 : EuclideanEndomorphism n)) +
        euclideanOperator A *
          (radialBoundaryParametrization K c t ^ k •
            (radialOutwardUnitNormal K c t •
              homotopyBoundaryOperatorResolvent A K c 1 t)) := by
  have hσR := smul_homotopyBoundaryOperatorResolvent_one_eq
    A hconv hc hcompact hWA hspectrum t
  calc
    radialBoundaryParametrization K c t ^ (k + 1) •
        (radialOutwardUnitNormal K c t •
          homotopyBoundaryOperatorResolvent A K c 1 t) =
      radialBoundaryParametrization K c t ^ k •
        (radialOutwardUnitNormal K c t •
          (radialBoundaryParametrization K c t •
            homotopyBoundaryOperatorResolvent A K c 1 t)) := by
              rw [pow_succ]
              module
    _ = radialBoundaryParametrization K c t ^ k •
        (radialOutwardUnitNormal K c t •
          (1 + euclideanOperator A *
            homotopyBoundaryOperatorResolvent A K c 1 t)) := by
              rw [hσR]
    _ = radialBoundaryParametrization K c t ^ k •
          (radialOutwardUnitNormal K c t •
            (1 : EuclideanEndomorphism n)) +
        euclideanOperator A *
          (radialBoundaryParametrization K c t ^ k •
            (radialOutwardUnitNormal K c t •
              homotopyBoundaryOperatorResolvent A K c 1 t)) := by
              simp only [smul_add, mul_smul_comm, smul_smul]

/-- The `k+1` power integral is the matrix times the `k`th power integral;
the scalar normal moment is the vanishing correction term. -/
theorem powerBoundaryResolventIntegral_succ
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K) (k : ℕ) :
    powerBoundaryResolventIntegral A K c (k + 1) =
      euclideanOperator A * powerBoundaryResolventIntegral A K c k := by
  let μ := radialBoundaryArcLengthMeasure K c
  let F : ℕ → ℝ → EuclideanEndomorphism n := fun j t ↦
    radialBoundaryParametrization K c t ^ j •
      (radialOutwardUnitNormal K c t •
        homotopyBoundaryOperatorResolvent A K c 1 t)
  let M : ℝ → EuclideanEndomorphism n := fun t ↦
    radialBoundaryParametrization K c t ^ k •
      (radialOutwardUnitNormal K c t • (1 : EuclideanEndomorphism n))
  let T := euclideanOperator A
  have hpoint (t : ℝ) : F (k + 1) t = M t + T * F k t := by
    exact powerBoundaryResolventIntegrand_succ
      A hconv hc hcompact hWA hspectrum k t
  have hk : Integrable (F k) μ :=
    integrable_powerBoundaryResolventIntegral
      A hconv hc hcompact hWA hspectrum k
  have hsucc : Integrable (F (k + 1)) μ :=
    integrable_powerBoundaryResolventIntegral
      A hconv hc hcompact hWA hspectrum (k + 1)
  have hT : Integrable (fun t ↦ T * F k t) μ := hk.const_mul T
  have hM : Integrable M μ := by
    apply (hsucc.sub hT).congr
    filter_upwards with t
    exact (eq_sub_iff_add_eq.mpr (hpoint t).symm).symm
  have hmoment : ∫ t, M t ∂μ = 0 := by
    have hscalar := integral_polynomial_mul_normal_radialBoundary_eq_zero
      hconv hc hcompact (Polynomial.X ^ k)
    have hspan := integral_smul_const
      (fun t ↦ radialBoundaryParametrization K c t ^ k *
        radialOutwardUnitNormal K c t)
      (1 : EuclideanEndomorphism n)
      (μ := μ)
    dsimp only [M]
    rw [show (∫ t, radialBoundaryParametrization K c t ^ k •
          (radialOutwardUnitNormal K c t •
            (1 : EuclideanEndomorphism n)) ∂μ) =
        (∫ t, radialBoundaryParametrization K c t ^ k *
          radialOutwardUnitNormal K c t ∂μ) •
            (1 : EuclideanEndomorphism n) by
          simpa only [smul_smul] using hspan]
    have hscalar' : ∫ t, radialBoundaryParametrization K c t ^ k *
        radialOutwardUnitNormal K c t ∂μ = 0 := by
      simpa only [Polynomial.eval_pow, Polynomial.eval_X, μ] using hscalar
    rw [hscalar']
    module
  rw [powerBoundaryResolventIntegral]
  change ∫ t, F (k + 1) t ∂μ = T * ∫ t, F k t ∂μ
  calc
    ∫ t, F (k + 1) t ∂μ = ∫ t, (M t + T * F k t) ∂μ := by
      apply integral_congr_ae
      filter_upwards with t
      exact hpoint t
    _ = (∫ t, M t ∂μ) + (∫ t, T * F k t ∂μ) :=
      integral_add hM hT
    _ = 0 + T * (∫ t, F k t ∂μ) := by
      rw [hmoment, integral_const_mul_of_integrable hk]
    _ = T * (∫ t, F k t ∂μ) := zero_add _

/-- The zeroth power integral is the concrete resolvent mass. -/
theorem powerBoundaryResolventIntegral_zero_eq_two_pi_one
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K) :
    powerBoundaryResolventIntegral A K c 0 =
      (((2 * Real.pi : ℝ) : ℂ) • (1 : EuclideanEndomorphism n)) := by
  simpa only [powerBoundaryResolventIntegral, pow_zero, one_smul,
    homotopyResolventMass] using
      homotopyResolventMass_one_eq_two_pi_one
        A hconv hc hcompact hWA hspectrum

/-- Exact evaluation of every power-weighted boundary resolvent integral. -/
theorem powerBoundaryResolventIntegral_eq
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K) (k : ℕ) :
    powerBoundaryResolventIntegral A K c k =
      (((2 * Real.pi : ℝ) : ℂ) • (euclideanOperator A) ^ k) := by
  induction k with
  | zero =>
      simpa only [pow_zero] using
        powerBoundaryResolventIntegral_zero_eq_two_pi_one
          A hconv hc hcompact hWA hspectrum
  | succ k ih =>
      rw [powerBoundaryResolventIntegral_succ
        A hconv hc hcompact hWA hspectrum k, ih]
      rw [pow_succ']
      exact mul_smul_comm (((2 * Real.pi : ℝ) : ℂ))
        (euclideanOperator A) ((euclideanOperator A) ^ k)

/-- The polynomial-weighted version of the concrete boundary-resolvent
integral, expressed using the operator homotopy at time one. -/
def polynomialBoundaryOperatorResolventIntegral
    (A : SquareMatrix n) (K : Set ℂ) (c : ℂ) (q : Polynomial ℂ) :
    EuclideanEndomorphism n :=
  ∫ t, q.eval (radialBoundaryParametrization K c t) •
      (radialOutwardUnitNormal K c t •
        homotopyBoundaryOperatorResolvent A K c 1 t)
    ∂radialBoundaryArcLengthMeasure K c

/-- Every polynomial-weighted boundary-resolvent integrand is integrable. -/
theorem integrable_polynomialBoundaryOperatorResolventIntegral
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K) (q : Polynomial ℂ) :
    Integrable
      (fun t ↦ q.eval (radialBoundaryParametrization K c t) •
        (radialOutwardUnitNormal K c t •
          homotopyBoundaryOperatorResolvent A K c 1 t))
      (radialBoundaryArcLengthMeasure K c) := by
  let f := radialPolynomialBoundaryFunction hconv hc hcompact q
  have hbase := integrable_homotopyResolventMass_Icc
    A hconv hc hcompact hWA hspectrum
      (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
  have hbounded : ∀ᵐ t ∂radialBoundaryArcLengthMeasure K c,
      ‖f t‖ ≤ ‖f‖ := Filter.Eventually.of_forall f.norm_coe_le_norm
  have h := hbase.bdd_smul ‖f‖
    f.continuous.aestronglyMeasurable hbounded
  change Integrable
    (fun t ↦ f t • (radialOutwardUnitNormal K c t •
      homotopyBoundaryOperatorResolvent A K c 1 t))
    (radialBoundaryArcLengthMeasure K c) at h
  simpa only [f, radialPolynomialBoundaryFunction_apply] using h

/-- The full ordinary polynomial Cauchy formula, derived from the concrete
convex boundary and the resolvent recurrence. -/
theorem polynomialBoundaryOperatorResolventIntegral_eq
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K) (q : Polynomial ℂ) :
    polynomialBoundaryOperatorResolventIntegral A K c q =
      (((2 * Real.pi : ℝ) : ℂ) • Polynomial.aeval (euclideanOperator A) q) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [polynomialBoundaryOperatorResolventIntegral]
      change (∫ t, (p + q).eval (radialBoundaryParametrization K c t) •
        (radialOutwardUnitNormal K c t •
          homotopyBoundaryOperatorResolvent A K c 1 t)
          ∂radialBoundaryArcLengthMeasure K c) = _
      rw [show (∫ t, (p + q).eval (radialBoundaryParametrization K c t) •
            (radialOutwardUnitNormal K c t •
              homotopyBoundaryOperatorResolvent A K c 1 t)
              ∂radialBoundaryArcLengthMeasure K c) =
          (∫ t, p.eval (radialBoundaryParametrization K c t) •
            (radialOutwardUnitNormal K c t •
              homotopyBoundaryOperatorResolvent A K c 1 t)
              ∂radialBoundaryArcLengthMeasure K c) +
          (∫ t, q.eval (radialBoundaryParametrization K c t) •
            (radialOutwardUnitNormal K c t •
              homotopyBoundaryOperatorResolvent A K c 1 t)
              ∂radialBoundaryArcLengthMeasure K c) by
        rw [← integral_add
          (integrable_polynomialBoundaryOperatorResolventIntegral
            A hconv hc hcompact hWA hspectrum p)
          (integrable_polynomialBoundaryOperatorResolventIntegral
            A hconv hc hcompact hWA hspectrum q)]
        apply integral_congr_ae
        filter_upwards with t
        simp only [Polynomial.eval_add]
        module]
      change polynomialBoundaryOperatorResolventIntegral A K c p +
          polynomialBoundaryOperatorResolventIntegral A K c q = _
      rw [hp, hq, map_add, smul_add]
  | monomial k a =>
      rw [polynomialBoundaryOperatorResolventIntegral]
      calc
        ∫ t, (Polynomial.monomial k a).eval
              (radialBoundaryParametrization K c t) •
            (radialOutwardUnitNormal K c t •
              homotopyBoundaryOperatorResolvent A K c 1 t)
              ∂radialBoundaryArcLengthMeasure K c =
          ∫ t, a • (radialBoundaryParametrization K c t ^ k •
            (radialOutwardUnitNormal K c t •
              homotopyBoundaryOperatorResolvent A K c 1 t))
              ∂radialBoundaryArcLengthMeasure K c := by
            apply integral_congr_ae
            filter_upwards with t
            simp only [Polynomial.eval_monomial]
            module
        _ =
          a • powerBoundaryResolventIntegral A K c k := by
            rw [powerBoundaryResolventIntegral]
            exact integral_smul a _
        _ = a • ((((2 * Real.pi : ℝ) : ℂ) •
              (euclideanOperator A) ^ k)) := by
            rw [powerBoundaryResolventIntegral_eq
              A hconv hc hcompact hWA hspectrum k]
        _ = (((2 * Real.pi : ℝ) : ℂ) •
              Polynomial.aeval (euclideanOperator A)
                (Polynomial.monomial k a)) := by
            simp only [Polynomial.aeval_monomial,
              Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
            module

/-- At time one, the homotopy boundary resolvent is the Euclidean image
of the concrete matrix boundary resolvent. -/
theorem homotopyBoundaryOperatorResolvent_one_eq_convexBoundaryResolvent
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hspectrum : spectrum ℂ A ⊆ interior K) (t : ℝ) :
    homotopyBoundaryOperatorResolvent A K c 1 t =
      euclideanOperator (convexBoundaryResolvent A K c t) := by
  calc
    homotopyBoundaryOperatorResolvent A K c 1 t =
        resolvent (euclideanOperator A)
          (radialBoundaryParametrization K c t) := by
            rw [homotopyBoundaryOperatorResolvent,
              convexOperatorHomotopy_eq_euclideanOperator,
              convexMatrixHomotopy_one]
    _ = euclideanOperator (convexBoundaryResolvent A K c t) :=
      (euclideanOperator_convexBoundaryResolvent_eq_resolvent
        A hconv hc hcompact hspectrum t).symm

/-- The concrete `polynomialRightResolventIntegral` is the ordinary Cauchy
integral, with no analytic formula supplied by the caller. -/
theorem polynomialRightResolventIntegral_convexBoundary_eq
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K) (q : Polynomial ℂ) :
    polynomialRightResolventIntegral
        (mu := radialBoundaryArcLengthMeasure K c)
        (radialBoundaryParametrization K c)
        (radialOutwardUnitNormal K c)
        (convexBoundaryResolvent A K c) q =
      (((2 * Real.pi : ℝ) : ℂ) •
        euclideanOperator (polynomialEval q A)) := by
  rw [polynomialRightResolventIntegral]
  change (∫ t, q.eval (radialBoundaryParametrization K c t) •
    (radialOutwardUnitNormal K c t •
      euclideanOperator (convexBoundaryResolvent A K c t))
      ∂radialBoundaryArcLengthMeasure K c) = _
  rw [show (∫ t, q.eval (radialBoundaryParametrization K c t) •
      (radialOutwardUnitNormal K c t •
        euclideanOperator (convexBoundaryResolvent A K c t))
        ∂radialBoundaryArcLengthMeasure K c) =
      polynomialBoundaryOperatorResolventIntegral A K c q by
    rw [polynomialBoundaryOperatorResolventIntegral]
    apply integral_congr_ae
    filter_upwards with t
    rw [homotopyBoundaryOperatorResolvent_one_eq_convexBoundaryResolvent
      A hconv hc hcompact hspectrum]]
  rw [polynomialBoundaryOperatorResolventIntegral_eq
    A hconv hc hcompact hWA hspectrum q,
    euclideanOperator_polynomialEval]

/-- The fully concrete polynomial Cauchy-resolvent boundary attached to a
compact convex body containing the numerical range. -/
def polynomialCauchyResolventBoundaryOfConvexBodyConcrete
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K) :
    PolynomialCauchyResolventBoundary A
      (radialBoundaryArcLengthMeasure K c) :=
  polynomialCauchyResolventBoundaryOfConvexBody
    A hconv hc hcompact hWA hspectrum
      (polynomialRightResolventIntegral_convexBoundary_eq
        A hconv hc hcompact hWA hspectrum)

/-- End-to-end normalized factor-two estimate on one compact convex body,
with no Cauchy formula supplied by the caller. -/
theorem norm_polynomialEval_le_two_of_convexBody
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K)
    (q : Polynomial ℂ) (hq : ∀ z ∈ K, ‖q.eval z‖ ≤ 1) :
    ‖polynomialEval q A‖ ≤ 2 := by
  exact norm_polynomialEval_le_two_of_convexBodyCauchy
    A hconv hc hcompact hWA hspectrum
      (polynomialRightResolventIntegral_convexBoundary_eq
        A hconv hc hcompact hWA hspectrum) q hq

/-- The unconditional sharp polynomial numerical-range bound. -/
theorem sharp_polynomial_bound
    [Nonempty n] (A : SquareMatrix n) (p : Polynomial ℂ) :
    ‖polynomialEval p A‖ ≤ 2 * maxPolynomialModulus A p := by
  let m := maxPolynomialModulus A p
  have hm : 0 ≤ m := maxPolynomialModulus_nonneg A p
  have happrox : ∀ δ : ℝ, 0 < δ →
      ‖polynomialEval p A‖ ≤ 2 * (m + δ) := by
    intro δ hδ
    let U : Set ℂ := {z | ‖p.eval z‖ < m + δ}
    have hUopen : IsOpen U :=
      isOpen_lt p.continuous.norm continuous_const
    have hWU : numericalRange A ⊆ U := by
      intro z hz
      exact (norm_eval_le_maxPolynomialModulus A p hz).trans_lt
        (lt_add_of_pos_right m hδ)
    obtain ⟨ε, hε, hthick⟩ :=
      (isCompact_numericalRange A).exists_cthickening_subset_open
        hUopen hWU
    let K := Metric.cthickening ε (numericalRange A)
    have hKcompact : IsCompact K := (isCompact_numericalRange A).cthickening
    have hKconv : Convex ℝ K := (numericalRange_convex A).cthickening ε
    have hWint : numericalRange A ⊆ interior K :=
      (self_subset_thickening hε (numericalRange A)).trans
        (thickening_subset_interior_cthickening ε (numericalRange A))
    obtain ⟨c, hcW⟩ := numericalRange_nonempty A
    have hc : c ∈ interior K := hWint hcW
    have hWA : numericalRange A ⊆ K := hWint.trans interior_subset
    have hspectrum : spectrum ℂ A ⊆ interior K :=
      (spectrum_subset_numericalRange A).trans hWint
    have hmδ : 0 < m + δ := lt_of_le_of_lt hm (lt_add_of_pos_right m hδ)
    let a : ℂ := (((m + δ)⁻¹ : ℝ) : ℂ)
    let q : Polynomial ℂ := a • p
    have ha : ‖a‖ = (m + δ)⁻¹ := by
      simp only [a, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hmδ)]
    have hq : ∀ z ∈ K, ‖q.eval z‖ ≤ 1 := by
      intro z hz
      have hpz : ‖p.eval z‖ ≤ m + δ := (hthick hz).le
      simp only [q, Polynomial.eval_smul, norm_smul, ha]
      calc
        (m + δ)⁻¹ * ‖p.eval z‖ ≤ (m + δ)⁻¹ * (m + δ) := by
          exact mul_le_mul_of_nonneg_left hpz (inv_nonneg.mpr hmδ.le)
        _ = 1 := inv_mul_cancel₀ hmδ.ne'
    have hqbound := norm_polynomialEval_le_two_of_convexBody
      A hKconv hc hKcompact hWA hspectrum q hq
    simp only [q, polynomialEval_smul, norm_smul, ha] at hqbound
    calc
      ‖polynomialEval p A‖ =
          (m + δ) * ((m + δ)⁻¹ * ‖polynomialEval p A‖) := by
        field_simp
      _ ≤ (m + δ) * 2 :=
        mul_le_mul_of_nonneg_left hqbound hmδ.le
      _ = 2 * (m + δ) := mul_comm _ _
  apply le_of_forall_pos_le_add
  intro ε hε
  have h := happrox (ε / 2) (half_pos hε)
  change ‖polynomialEval p A‖ ≤ 2 * m + ε
  nlinarith

end DiskRigidity.Operator
