/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.BoundarySpectrum
public import DiskRigidity.Operator.DoubleLayer
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Convex support lines and the resolvent boundary density

This file supplies the concrete pointwise bridge in (3.5).  An outward
supporting normal to the numerical range makes the support defect positive;
resolvent congruence then makes the normalized double-layer density positive.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction ComplexOrder Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A scalar supporting-line inequality for the outward normal is exactly
positivity of the support matrix used in (3.5). -/
theorem doubleLayerSupportMatrix_posSemidef_of_support
    (A : SquareMatrix n) (sigma nu : ℂ)
    (hsupport : ∀ w ∈ numericalRange A,
      (star nu * w).re ≤ (star nu * sigma).re) :
    (doubleLayerSupportMatrix A sigma nu).PosSemidef := by
  let alpha : ℝ := (star nu * sigma).re
  have hP := supportDefect_posSemidef A (star nu) alpha hsupport
  have heq :
      doubleLayerSupportMatrix A sigma nu =
        (2 : ℝ) •
          (((alpha : ℂ) • (1 : SquareMatrix n)) - rePart (star nu • A)) := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [doubleLayerSupportMatrix, rePart, alpha,
        Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply, if_pos, Matrix.conjTranspose_apply, smul_eq_mul]
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
    · simp only [doubleLayerSupportMatrix, rePart, Matrix.add_apply,
        Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hij, if_false,
        Matrix.conjTranspose_apply, smul_eq_mul, zero_sub, mul_zero,
        Complex.real_smul]
      rw [star_mul, star_star]
      norm_num
      ring
  rw [heq]
  exact hP.smul (by norm_num)

/-- The matrix-valued density `P(σ) = Re (nu R) / pi`. -/
def normalizedDoubleLayerDensityMatrix
    (R : SquareMatrix n) (nu : ℂ) : SquareMatrix n :=
  (((2 * Real.pi)⁻¹ : ℝ) : ℂ) • doubleLayerDensity R nu

/-- The same normalized density acting on Euclidean column space. -/
def normalizedDoubleLayerDensity
    (R : SquareMatrix n) (nu : ℂ) : EuclideanEndomorphism n :=
  euclideanOperator (normalizedDoubleLayerDensityMatrix R nu)

/-- The holomorphic half of the double-layer density. -/
def rightResolventBoundaryTerm
    (R : SquareMatrix n) (nu : ℂ) : EuclideanEndomorphism n :=
  nu • euclideanOperator R

/-- The adjoint half of the double-layer density. -/
def adjointResolventBoundaryTerm
    (R : SquareMatrix n) (nu : ℂ) : EuclideanEndomorphism n :=
  star nu • euclideanOperator Rᴴ

/-- Splitting the normalized density into the two Cauchy boundary terms. -/
theorem normalizedDoubleLayerDensity_eq_cauchy_terms
    (R : SquareMatrix n) (nu : ℂ) :
    normalizedDoubleLayerDensity R nu =
      ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) •
        (rightResolventBoundaryTerm R nu +
          adjointResolventBoundaryTerm R nu)) := by
  have hmap (c : ℂ) (B : SquareMatrix n) :
      euclideanOperator (c • B) = c • euclideanOperator B := by
    exact map_smul (euclideanOperator (n := n)) c B
  simp only [normalizedDoubleLayerDensity, normalizedDoubleLayerDensityMatrix,
    doubleLayerDensity, rightResolventBoundaryTerm,
    adjointResolventBoundaryTerm, smul_add, smul_smul, map_add]
  rw [hmap, hmap, euclideanOperator_conjTranspose]

/-- Formula (3.5): a supporting normal and a genuine resolvent give a
positive normalized boundary density. -/
theorem normalizedDoubleLayerDensity_isPositive
    (A R : SquareMatrix n) (sigma nu : ℂ)
    (hR : (sigma • (1 : SquareMatrix n) - A) * R = 1)
    (hsupport : ∀ w ∈ numericalRange A,
      (star nu * w).re ≤ (star nu * sigma).re) :
    (normalizedDoubleLayerDensity R nu).IsPositive := by
  rw [normalizedDoubleLayerDensity, isPositive_euclideanOperator_iff]
  have hdensity := doubleLayerDensity_posSemidef A R sigma nu hR
    (doubleLayerSupportMatrix_posSemidef_of_support A sigma nu hsupport)
  rw [normalizedDoubleLayerDensityMatrix]
  have hpi : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have hdreal := hdensity.smul hpi
  have heq :
      ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) • doubleLayerDensity R nu) =
        ((2 * Real.pi)⁻¹ : ℝ) • doubleLayerDensity R nu := by
    apply Matrix.ext
    intro i j
    simp [Complex.real_smul]
  rw [heq]
  exact hdreal

variable {i : Type*} [TopologicalSpace i] [MeasurableSpace i]
  [OpensMeasurableSpace i] {mu : Measure i}

omit [TopologicalSpace i] [OpensMeasurableSpace i] in
/-- The two ordinary Cauchy identities imply the double-layer mass identity
(3.6). -/
theorem integral_normalizedDoubleLayerDensity_eq_two_one
    (nu : i → ℂ) (R : i → SquareMatrix n)
    (hright : Integrable (fun t ↦ rightResolventBoundaryTerm (R t) (nu t)) mu)
    (hadjoint : Integrable (fun t ↦ adjointResolventBoundaryTerm (R t) (nu t)) mu)
    (hcauchyRight :
      ∫ t, rightResolventBoundaryTerm (R t) (nu t) ∂mu =
        ((2 * Real.pi : ℝ) : ℂ) • (1 : EuclideanEndomorphism n))
    (hcauchyAdjoint :
      ∫ t, adjointResolventBoundaryTerm (R t) (nu t) ∂mu =
        ((2 * Real.pi : ℝ) : ℂ) • (1 : EuclideanEndomorphism n)) :
    ∫ t, normalizedDoubleLayerDensity (R t) (nu t) ∂mu =
      (2 : ℂ) • (1 : EuclideanEndomorphism n) := by
  simp_rw [normalizedDoubleLayerDensity_eq_cauchy_terms]
  rw [integral_smul, integral_add hright hadjoint,
    hcauchyRight, hcauchyAdjoint]
  rw [← add_smul]
  simp only [smul_smul]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  congr 1
  push_cast
  field_simp
  norm_num

omit [TopologicalSpace i] [OpensMeasurableSpace i] in
/-- Integrability of the two Cauchy halves implies integrability of the
normalized density. -/
theorem integrable_normalizedDoubleLayerDensity
    (nu : i → ℂ) (R : i → SquareMatrix n)
    (hright : Integrable (fun t ↦ rightResolventBoundaryTerm (R t) (nu t)) mu)
    (hadjoint : Integrable (fun t ↦ adjointResolventBoundaryTerm (R t) (nu t)) mu) :
    Integrable (fun t ↦ normalizedDoubleLayerDensity (R t) (nu t)) mu := by
  have hadd := hright.add hadjoint
  have hscaled := hadd.smul ((((2 * Real.pi)⁻¹ : ℝ) : ℂ))
  exact hscaled.congr
    (Filter.Eventually.of_forall fun t ↦
      (normalizedDoubleLayerDensity_eq_cauchy_terms (R t) (nu t)).symm)

omit [DecidableEq n] in
/-- A bounded continuous scalar multiplier preserves integrability of an
operator-valued boundary density.  This discharges the auxiliary
`integrable_smul'` field in `PositiveBoundaryDensity` from its ordinary
integrability field. -/
theorem integrable_boundedContinuous_smul
    (P : i → EuclideanEndomorphism n) (hP : Integrable P mu)
    (h : i →ᵇ ℂ) : Integrable (fun t ↦ h t • P t) mu := by
  exact (ContinuousLinearMap.lsmul ℂ ℂ).integrable_of_bilin_of_bdd_left
    ‖h‖ h.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ↦ h.norm_coe_le_norm t) hP

/-- Concrete construction of `PositiveBoundaryDensity` from a boundary
parametrization, its outward normal, and its resolvent.  Positivity is proved
   here; the remaining assumptions are precisely integrability and the Cauchy
   mass formula (3.6). -/
def positiveBoundaryDensityOfResolvent
    (A : SquareMatrix n) (sigma nu : i → ℂ) (R : i → SquareMatrix n)
    (hresolvent : ∀ᵐ t ∂mu,
      (sigma t • (1 : SquareMatrix n) - A) * R t = 1)
    (hsupport : ∀ᵐ t ∂mu, ∀ w ∈ numericalRange A,
      (star (nu t) * w).re ≤ (star (nu t) * sigma t).re)
    (hintegrable : Integrable
      (fun t ↦ normalizedDoubleLayerDensity (R t) (nu t)) mu)
    (hmass : ∫ t, normalizedDoubleLayerDensity (R t) (nu t) ∂mu =
      (2 : ℂ) • (1 : EuclideanEndomorphism n)) :
    PositiveBoundaryDensity (n := n) mu where
  density := fun t ↦ normalizedDoubleLayerDensity (R t) (nu t)
  integrable_density := hintegrable
  integrable_smul' := fun h ↦ integrable_boundedContinuous_smul _ hintegrable h
  isPositive_ae := by
    filter_upwards [hresolvent, hsupport] with t hR hs
    exact normalizedDoubleLayerDensity_isPositive A (R t) (sigma t) (nu t) hR hs
  mass_eq_two_one := hmass

/-- The fully split Cauchy-boundary constructor.  It builds the positive
double-layer density directly from the resolvent and supporting-normal data;
ordinary integrability and the mass-two identity are both deduced from the
two Cauchy halves. -/
def positiveBoundaryDensityOfCauchyResolvent
    (A : SquareMatrix n) (sigma nu : i → ℂ) (R : i → SquareMatrix n)
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
        ((2 * Real.pi : ℝ) : ℂ) • (1 : EuclideanEndomorphism n)) :
    PositiveBoundaryDensity (n := n) mu :=
  positiveBoundaryDensityOfResolvent A sigma nu R hresolvent hsupport
    (integrable_normalizedDoubleLayerDensity nu R hright hadjoint)
    (integral_normalizedDoubleLayerDensity_eq_two_one nu R hright hadjoint
      hcauchyRight hcauchyAdjoint)

end DiskRigidity.Operator
