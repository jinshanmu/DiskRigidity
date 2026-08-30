/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.BoundaryKernelTransfer
public import DiskRigidity.Operator.HolomorphicEqualityData
public import DiskRigidity.Operator.AdjugateTransferIdentity

/-!
# The boundary transfer identity for a holomorphic extremizer

This file completes the passage from the almost-everywhere equality in the
double-layer dilation to equation (5.7).  All intermediate statements are
consequences of the canonical square root, the resolvent congruence, and the
unique supporting point of the numerical range.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {i : Type*} [TopologicalSpace i] [MeasurableSpace i]
  [OpensMeasurableSpace i] {mu : Measure i}
  [BorelSpace i] [IsFiniteMeasure mu]

omit [BorelSpace i] [IsFiniteMeasure mu] in
/-- Proposition 5.2 up to the scalar boundary identity: the canonical
double-layer kernel gives `c(σ) g(σ) = 2 a(σ)` almost everywhere on
the uniquely exposed part of the boundary. -/
theorem HolomorphicResolventDilationData.transfer_identity_ae_on
    {A : SquareMatrix n}
    {B : CauchyResolventBoundary A mu} {g : ℂ → ℂ}
    (P : HolomorphicResolventDilationData B g)
    (Q : i → Prop)
    {x y : EuclideanVector n}
    (hxy : SharpEqualityData
      (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g)) x y)
    (hkernel : ∀ᵐ t ∂mu,
      P.squareRoot.factor t (y - P.boundaryFunction t • x) = 0)
    (hboundaryNorm : ∀ᵐ t ∂mu, ‖P.boundaryFunction t‖ = 1)
    (hunique : ∀ᵐ t ∂mu, Q t → ∀ z ∈ numericalRange A,
      (star (B.outwardNormal t) * z).re =
        (star (B.outwardNormal t) * B.boundaryPoint t).re →
      z = B.boundaryPoint t) :
    ∀ᵐ t ∂mu, Q t →
      P.boundaryFunction t *
          ⟪y, euclideanOperator (B.resolvent t) x⟫_ℂ =
        2 * ⟪x, euclideanOperator (B.resolvent t) x⟫_ℂ := by
  filter_upwards [hkernel, hboundaryNorm, hunique,
    P.squareRoot.gram_ae, B.resolvent_ae] with t hker hnorm huniq hgram hR
  intro htQ
  let v : EuclideanVector n := y - P.boundaryFunction t • x
  have hv : v ≠ 0 := by
    intro hvzero
    have hyx : y = P.boundaryFunction t • x := sub_eq_zero.mp hvzero
    have hinner := congrArg (fun w ↦ ⟪x, w⟫_ℂ) hyx
    rw [hxy.inner_xy, inner_smul_right, inner_self_eq_norm_sq_to_K,
      hxy.norm_x] at hinner
    norm_num at hinner
    have hnormzero := congrArg norm hinner
    rw [norm_zero, hnorm] at hnormzero
    norm_num at hnormzero
  have hdensity :
      normalizedDoubleLayerDensity (B.resolvent t) (B.outwardNormal t) v = 0 := by
    have h := P.squareRoot.density_apply_eq_zero_of_factor_apply_eq_zero
      hgram hker
    simpa only [CauchyResolventBoundary.positiveDensity_apply] using h
  have hsupport :
      euclideanOperator
          (doubleLayerSupportMatrix A (B.boundaryPoint t) (B.outwardNormal t))
          (euclideanOperator (B.resolvent t) v) = 0 :=
    supportMatrix_apply_resolvent_eq_zero_of_density_apply_eq_zero
      A (B.resolvent t) (B.boundaryPoint t) (B.outwardNormal t) hR hdensity
  have hquad : ⟪v, euclideanOperator (B.resolvent t) v⟫_ℂ = 0 :=
    boundary_quadratic_zero_of_supportMatrix_apply_resolvent_eq_zero
      A (B.resolvent t) (B.boundaryPoint t) (B.outwardNormal t)
      hR v hv hsupport (huniq htQ)
  have hcommute := euclidean_resolvent_commutes_polynomialEval
    A (B.resolvent t) (B.boundaryPoint t)
      (DiskRigidity.Complex.spectralJetPolynomial A g) hR
  have hcomm : ∀ z,
      euclideanOperator (B.resolvent t)
          (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g) z) =
        euclideanOperator (DiskRigidity.Complex.spectralJetEval A g)
          (euclideanOperator (B.resolvent t) z) := by
    intro z
    rw [DiskRigidity.Complex.spectralJetEval_eq_polynomialEval]
    exact DFunLike.congr_fun hcommute.eq z
  exact boundary_quadratic_zero_imp_transfer_identity hxy hcomm
    (P.boundaryFunction t) hnorm hquad

omit [BorelSpace i] [IsFiniteMeasure mu] in
/-- Global specialization of `transfer_identity_ae_on`. -/
theorem HolomorphicResolventDilationData.transfer_identity_ae
    {A : SquareMatrix n}
    {B : CauchyResolventBoundary A mu} {g : ℂ → ℂ}
    (P : HolomorphicResolventDilationData B g)
    {x y : EuclideanVector n}
    (hxy : SharpEqualityData
      (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g)) x y)
    (hkernel : ∀ᵐ t ∂mu,
      P.squareRoot.factor t (y - P.boundaryFunction t • x) = 0)
    (hboundaryNorm : ∀ᵐ t ∂mu, ‖P.boundaryFunction t‖ = 1)
    (hunique : ∀ᵐ t ∂mu, ∀ z ∈ numericalRange A,
      (star (B.outwardNormal t) * z).re =
        (star (B.outwardNormal t) * B.boundaryPoint t).re →
      z = B.boundaryPoint t) :
    ∀ᵐ t ∂mu,
      P.boundaryFunction t *
          ⟪y, euclideanOperator (B.resolvent t) x⟫_ℂ =
        2 * ⟪x, euclideanOperator (B.resolvent t) x⟫_ℂ := by
  filter_upwards [P.transfer_identity_ae_on (fun _ ↦ True) hxy hkernel
    hboundaryNorm (hunique.mono fun t ht _ ↦ ht)] with t ht
  exact ht trivial

omit [BorelSpace i] [IsFiniteMeasure mu] in
/-- Clearing the common characteristic-polynomial denominator turns the
almost-everywhere scalar resolvent identity into the polynomial identity
used in the rational-collapse argument. -/
theorem HolomorphicResolventDilationData.adjugate_transfer_identity_ae_on
    {N : ℕ} {A : SquareMatrix (Fin (N + 1))}
    {B : CauchyResolventBoundary A mu} {g : ℂ → ℂ}
    (P : HolomorphicResolventDilationData B g)
    (Q : i → Prop)
    {x y : EuclideanVector (Fin (N + 1))}
    (hxy : SharpEqualityData
      (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g)) x y)
    (hkernel : ∀ᵐ t ∂mu,
      P.squareRoot.factor t (y - P.boundaryFunction t • x) = 0)
    (hboundaryNorm : ∀ᵐ t ∂mu, ‖P.boundaryFunction t‖ = 1)
    (hunique : ∀ᵐ t ∂mu, Q t → ∀ z ∈ numericalRange A,
      (star (B.outwardNormal t) * z).re =
        (star (B.outwardNormal t) * B.boundaryPoint t).re →
      z = B.boundaryPoint t)
    (hresolventPoint : ∀ᵐ t ∂mu, Q t →
      B.boundaryPoint t ∉ spectrum ℂ A) :
    ∀ᵐ t ∂mu, Q t →
      (adjugateScalarNumerator A y x).eval (B.boundaryPoint t) *
          g (B.boundaryPoint t) =
        2 * (adjugateScalarNumerator A x x).eval (B.boundaryPoint t) := by
  have htransfer := P.transfer_identity_ae_on Q hxy hkernel
    hboundaryNorm hunique
  filter_upwards [htransfer, P.boundaryFunction_eq, B.resolvent_ae,
    hresolventPoint] with t ht htrace hR hnot
  intro htQ
  have hscalar := ht htQ
  rw [htrace] at hscalar
  exact adjugate_transfer_identity_of_right_resolvent_identity
    A (B.resolvent t) x y (B.boundaryPoint t) (g (B.boundaryPoint t))
      (hnot htQ) hR hscalar

end DiskRigidity.Operator
