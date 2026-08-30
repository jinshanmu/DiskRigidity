/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.NumericalRange
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Topology.ContinuousMap.Bounded.Star

/-!
# Positive double-layer operators

This module develops the support defect, positive boundary density, and
normalized mass used by the sharp numerical-range estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction ComplexOrder Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

/-- Twice the Hermitian support-line matrix
`Re (conj ν (σI - A))` occurring in the double-layer construction. -/
def doubleLayerSupportMatrix {n : Type*} [DecidableEq n]
    (A : SquareMatrix n) (σ ν : ℂ) : SquareMatrix n :=
  ν • (star σ • (1 : SquareMatrix n) - Aᴴ) +
    star ν • (σ • (1 : SquareMatrix n) - A)

/-- The support-line matrix is twice the matrix real part. -/
theorem doubleLayerSupportMatrix_eq_two_smul_rePart
    {n : Type*} [DecidableEq n] (A : SquareMatrix n) (σ ν : ℂ) :
    doubleLayerSupportMatrix A σ ν =
      (2 : ℂ) • rePart (star ν • (σ • (1 : SquareMatrix n) - A)) := by
  simp only [doubleLayerSupportMatrix, rePart, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, star_star, smul_add, smul_smul]
  module

/-- The support-line matrix is Hermitian. -/
theorem doubleLayerSupportMatrix_isHermitian
    {n : Type*} [DecidableEq n] (A : SquareMatrix n) (σ ν : ℂ) :
    (doubleLayerSupportMatrix A σ ν).IsHermitian := by
  simp [doubleLayerSupportMatrix, Matrix.IsHermitian, add_comm]

/-- The unnormalised double-layer density `νR + conj(ν)R⁺`. -/
def doubleLayerDensity {n : Type*} (R : SquareMatrix n) (ν : ℂ) :
    SquareMatrix n :=
  ν • R + star ν • Rᴴ

/-- Every double-layer density is Hermitian. -/
theorem doubleLayerDensity_isHermitian
    {n : Type*} (R : SquareMatrix n) (ν : ℂ) :
    (doubleLayerDensity R ν).IsHermitian := by
  simp [doubleLayerDensity, Matrix.IsHermitian, add_comm]

/-- Taking adjoints turns the right resolvent identity into the left one. -/
theorem resolvent_conjTranspose_leftInverse
    {n : Type*} [Fintype n] [DecidableEq n]
    (A R : SquareMatrix n) (σ : ℂ)
    (hR : (σ • (1 : SquareMatrix n) - A) * R = 1) :
    Rᴴ * (star σ • (1 : SquareMatrix n) - Aᴴ) = 1 := by
  have h := congrArg Matrix.conjTranspose hR
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, starRingEnd_apply,
    star_star] using h

/-- Exact resolvent congruence identity behind positivity of the double layer. -/
theorem doubleLayer_congruence_density_identity
    {n : Type*} [Fintype n] [DecidableEq n]
    (A R : SquareMatrix n) (σ ν : ℂ)
    (hR : (σ • (1 : SquareMatrix n) - A) * R = 1) :
    Rᴴ * doubleLayerSupportMatrix A σ ν * R = doubleLayerDensity R ν := by
  have hRstar := resolvent_conjTranspose_leftInverse A R σ hR
  simp only [doubleLayerSupportMatrix, doubleLayerDensity, mul_add, add_mul,
    mul_smul_comm, smul_mul_assoc, mul_assoc, hR, hRstar, one_mul, mul_one]

/-- Positivity of the supporting half-plane transfers to the density by congruence. -/
theorem doubleLayerDensity_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    (A R : SquareMatrix n) (σ ν : ℂ)
    (hR : (σ • (1 : SquareMatrix n) - A) * R = 1)
    (hSupport : (doubleLayerSupportMatrix A σ ν).PosSemidef) :
    (doubleLayerDensity R ν).PosSemidef := by
  rw [← doubleLayer_congruence_density_identity A R σ ν hR]
  exact hSupport.conjTranspose_mul_mul_same R

/-- Matrix positive semidefiniteness is exactly positivity of the associated
Euclidean continuous operator. -/
theorem isPositive_euclideanOperator_iff
    {n : Type*} [Fintype n] [DecidableEq n] (A : SquareMatrix n) :
    (euclideanOperator A).IsPositive ↔ A.PosSemidef := by
  rw [← ContinuousLinearMap.isPositive_toLinearMap_iff]
  change A.toEuclideanLin.IsPositive ↔ A.PosSemidef
  exact Matrix.isPositive_toEuclideanLin_iff

/-- The positive double-layer density is positive as a Hilbert-space operator. -/
theorem doubleLayerDensity_operator_isPositive
    {n : Type*} [Fintype n] [DecidableEq n]
    (A R : SquareMatrix n) (σ ν : ℂ)
    (hR : (σ • (1 : SquareMatrix n) - A) * R = 1)
    (hSupport : (doubleLayerSupportMatrix A σ ν).PosSemidef) :
    (euclideanOperator (doubleLayerDensity R ν)).IsPositive := by
  rw [isPositive_euclideanOperator_iff]
  exact doubleLayerDensity_posSemidef A R σ ν hR hSupport

/-- Continuous endomorphisms of the manuscript's Euclidean column space. -/
abbrev EuclideanEndomorphism (n : Type*) :=
  EuclideanVector n →L[ℂ] EuclideanVector n

/-- The exact measure-theoretic data of a positive double-layer density of mass `2I`.
The density is stored as an operator, avoiding any dependence on a choice of coordinates. -/
structure PositiveBoundaryDensity
    {i n : Type*} [TopologicalSpace i] [MeasurableSpace i]
    [Fintype n] [DecidableEq n]
    (mu : Measure i) where
  /-- Boundary operator density. -/
  density : i → EuclideanEndomorphism n
  integrable_density : Integrable density mu
  integrable_smul' : ∀ h : i →ᵇ ℂ, Integrable (fun x ↦ h x • density x) mu
  isPositive_ae : ∀ᵐ x ∂mu, (density x).IsPositive
  mass_eq_two_one : ∫ x, density x ∂mu =
    (2 : ℂ) • (1 : EuclideanEndomorphism n)

variable {i n : Type*} [TopologicalSpace i] [MeasurableSpace i]
  [OpensMeasurableSpace i] [Fintype n] [DecidableEq n]
  {mu : Measure i}

omit [OpensMeasurableSpace i] in
/-- Multiplication by a bounded continuous scalar preserves integrability. -/
theorem PositiveBoundaryDensity.integrable_smul
    (D : PositiveBoundaryDensity (n := n) mu) (h : i →ᵇ ℂ) :
    Integrable (fun x ↦ h x • D.density x) mu :=
  D.integrable_smul' h

/-- The normalized positive boundary map `Φ(h) = (1/2) ∫ h P`. -/
def boundaryPhi (D : PositiveBoundaryDensity (n := n) mu) (h : i →ᵇ ℂ) :
    EuclideanEndomorphism n :=
  (2 : ℂ)⁻¹ • ∫ x, h x • D.density x ∂mu

/-- Complex-linearity of the positive boundary map. -/
def boundaryPhiLinear (D : PositiveBoundaryDensity (n := n) mu) :
    (i →ᵇ ℂ) →ₗ[ℂ] EuclideanEndomorphism n where
  toFun := boundaryPhi D
  map_add' h g := by
    unfold boundaryPhi
    rw [← smul_add,
      ← integral_add (D.integrable_smul h) (D.integrable_smul g)]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    exact add_smul (h x) (g x) (D.density x)
  map_smul' c h := by
    simp only [boundaryPhi, BoundedContinuousFunction.smul_apply]
    have hfun :
        (fun x ↦ (c • h x) • D.density x) =
          fun x ↦ c • (h x • D.density x) := by
      funext x
      change (c * h x) • D.density x = c • (h x • D.density x)
      rw [smul_smul]
    rw [hfun, integral_smul]
    simp only [smul_smul, RingHom.id_apply]
    ring_nf

omit [OpensMeasurableSpace i] in
/-- The mass identity makes the boundary map unital. -/
@[simp]
theorem boundaryPhi_one (D : PositiveBoundaryDensity (n := n) mu) :
    boundaryPhi D (1 : i →ᵇ ℂ) = 1 := by
  rw [boundaryPhi]
  change (2 : ℂ)⁻¹ • ∫ x, (1 : ℂ) • D.density x ∂mu = 1
  simp only [one_smul, D.mass_eq_two_one]
  rw [smul_smul]
  norm_num

omit [OpensMeasurableSpace i] in
/-- Positive boundary densities are self-adjoint almost everywhere. -/
theorem PositiveBoundaryDensity.isSelfAdjoint_ae
    (D : PositiveBoundaryDensity (n := n) mu) :
    ∀ᵐ x ∂mu, IsSelfAdjoint (D.density x) :=
  D.isPositive_ae.mono fun _ hx ↦ hx.isSelfAdjoint

/-- For a positive operator, a vector with zero quadratic form lies in its kernel. -/
theorem ContinuousLinearMap.IsPositive.apply_eq_zero_of_re_inner_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P : E →L[ℂ] E) (hP : P.IsPositive) (v : E)
    (hqre : (inner ℂ v (P v)).re = 0) :
    P v = 0 := by
  let w : E := P v
  let c : ℝ := ‖P‖
  let r : ℝ := (c + 1)⁻¹
  have hc : 0 ≤ c := norm_nonneg P
  have hr : 0 < r := by
    exact inv_pos.mpr (by dsimp [c]; linarith)
  have hq : inner ℂ v (P v) = 0 := by
    have hsym := hP.inner_left_eq_inner_right v v
    have hreal := (ContinuousLinearMap.isPositive_iff_complex P).mp hP v |>.1
    change ((inner ℂ (P v) v).re : ℂ) = inner ℂ (P v) v at hreal
    rw [hsym] at hreal
    calc
      inner ℂ v (P v) = ((inner ℂ v (P v)).re : ℂ) := hreal.symm
      _ = 0 := by rw [hqre]; norm_num
  have hvPw : inner ℂ v (P w) = inner ℂ w w := by
    rw [← hP.inner_left_eq_inner_right v w]
  have hwPv : inner ℂ w (P v) = inner ℂ w w := by
    rfl
  have hqw : (inner ℂ w (P w)).re ≤ c * ‖w‖ ^ 2 := by
    calc
      (inner ℂ w (P w)).re ≤ ‖inner ℂ w (P w)‖ := Complex.re_le_norm _
      _ ≤ ‖w‖ * ‖P w‖ := norm_inner_le_norm w (P w)
      _ ≤ ‖w‖ * (c * ‖w‖) := by
        gcongr
        exact P.le_opNorm w
      _ = c * ‖w‖ ^ 2 := by ring
  have hpos := hP.re_inner_nonneg_right (v - (r : ℂ) • w)
  have hexpand :
      (inner ℂ (v - (r : ℂ) • w)
        (P (v - (r : ℂ) • w))).re =
        -2 * r * ‖w‖ ^ 2 + r ^ 2 * (inner ℂ w (P w)).re := by
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, map_sub, Complex.conj_ofReal,
      hq, hvPw, hwPv, inner_self_eq_norm_sq_to_K]
    simp only [Complex.coe_algebraMap, zero_sub, Complex.sub_re, Complex.neg_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.sub_im, Complex.mul_im, add_zero, neg_mul]
    have hcastre : ((↑‖w‖ : ℂ) ^ 2).re = ‖w‖ ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    rw [hcastre]
    ring
  change 0 ≤ (inner ℂ (v - (r : ℂ) • w)
    (P (v - (r : ℂ) • w))).re at hpos
  rw [hexpand] at hpos
  have hrbound : r * c < 1 := by
    dsimp [r]
    rw [inv_mul_eq_div, div_lt_one (by dsimp [c]; linarith)]
    linarith
  have hwsq : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg _
  have hupper :
      -2 * r * ‖w‖ ^ 2 + r ^ 2 * (inner ℂ w (P w)).re ≤
        r * ‖w‖ ^ 2 * (-2 + r * c) := by
    calc
      _ ≤ -2 * r * ‖w‖ ^ 2 + r ^ 2 * (c * ‖w‖ ^ 2) := by
        gcongr
      _ = r * ‖w‖ ^ 2 * (-2 + r * c) := by ring
  have hwzero : ‖w‖ ^ 2 = 0 := by
    by_contra hn
    have hwpos : 0 < ‖w‖ ^ 2 := lt_of_le_of_ne hwsq (Ne.symm hn)
    have hcoef : -2 + r * c < 0 := by linarith
    have : r * ‖w‖ ^ 2 * (-2 + r * c) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hr hwpos) hcoef
    linarith
  have hw : w = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg w]
  exact hw

omit [OpensMeasurableSpace i] in
/-- If a positive density annihilates a vector in its integrated quadratic form,
then it annihilates that vector almost everywhere. -/
theorem density_mul_eq_zero_ae_of_integral_inner_eq_zero
    (D : PositiveBoundaryDensity (n := n) mu) (v : EuclideanVector n)
    (hzero : MeasureTheory.integral mu
      (fun x ↦ (inner ℂ v (D.density x v)).re) = 0) :
    ∀ᵐ x ∂mu, D.density x v = 0 := by
  have hnonneg : ∀ᵐ x ∂mu,
      0 ≤ (inner ℂ v (D.density x v)).re := by
    filter_upwards [D.isPositive_ae] with x hx
    exact hx.re_inner_nonneg_right v
  have hint : Integrable
      (fun x ↦ (inner ℂ v (D.density x v)).re) mu := by
    have happly := (ContinuousLinearMap.apply ℂ (EuclideanVector n) v).integrable_comp
      D.integrable_density
    have hinner := (innerSL ℂ v).integrable_comp happly
    exact hinner.re
  have hreZero : ∀ᵐ x ∂mu,
      (inner ℂ v (D.density x v)).re = 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg
      hint).mp hzero
  filter_upwards [D.isPositive_ae, hreZero] with x hx hzeroAt
  exact ContinuousLinearMap.IsPositive.apply_eq_zero_of_re_inner_eq_zero
    (D.density x) hx v hzeroAt

omit [TopologicalSpace i] [OpensMeasurableSpace i] in
/-- Pointwise form of the equality `M_f Vx = Vy`: for a boundary square-root
factor `S`, multiplication equality is exactly the kernel identity
`S(σ)(y-f(σ)x)=0`. -/
theorem boundary_kernel_identity_of_multiplication_equality
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (factor : i → E →L[ℂ] E) (f : i → ℂ) (x y : E)
    (hmul : ∀ᵐ σ ∂mu, f σ • factor σ x = factor σ y) :
    ∀ᵐ σ ∂mu, factor σ (y - f σ • x) = 0 := by
  filter_upwards [hmul] with σ hσ
  rw [map_sub, map_smul, ← hσ, sub_self]

end DiskRigidity.Operator
