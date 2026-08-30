/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.ConvexHolomorphicBound
public import DiskRigidity.Complex.SpectralJetAlgebra
public import DiskRigidity.Operator.ResolventDilation

/-!
# The double-layer estimate for a holomorphic spectral-jet calculus

The existing double-layer dilation is polynomially packaged.  This module
shows that exactly the same construction applies to an arbitrary function
analytic at the finite spectrum, once its ordinary holomorphic Cauchy formula
is available on the supporting boundary.  Multiplicativity and the power law
for `spectralJetEval` discharge the only new algebraic step.
-/

noncomputable section

open Filter MeasureTheory
open scoped BoundedContinuousFunction InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Complex

@[expose] public section

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {i : Type*} [TopologicalSpace i] [MeasurableSpace i]
  [OpensMeasurableSpace i] {mu : Measure i}

/-- The holomorphic half of the boundary-resolvent Cauchy integral. -/
def holomorphicRightResolventIntegral
    {A : Operator.SquareMatrix n}
    (B : Operator.CauchyResolventBoundary A mu) (g : ℂ → ℂ) :
    Operator.EuclideanEndomorphism n :=
  ∫ t, g (B.boundaryPoint t) •
    Operator.rightResolventBoundaryTerm
      (B.resolvent t) (B.outwardNormal t) ∂mu

variable [BorelSpace i] [IsFiniteMeasure mu]

/-- The normalized sharp double-layer estimate for an arbitrary analytic
function.  The only function-specific analytic input is the ordinary Cauchy
formula for its positive powers. -/
theorem norm_spectralJetEval_le_two_of_cauchyBoundary
    [Nonempty n] {A : Operator.SquareMatrix n}
    (B : Operator.CauchyResolventBoundary A mu)
    (g : ℂ → ℂ)
    (hg : ∀ a : HermiteRoot A.charpoly, AnalyticAt ℂ g (a : ℂ))
    (f : i →ᵇ ℂ)
    (hboundary : ∀ᵐ t ∂mu, f t = g (B.boundaryPoint t))
    (hf : ‖f‖ ≤ 1)
    (hcauchy : ∀ k : ℕ, 1 ≤ k →
      holomorphicRightResolventIntegral B (fun z ↦ g z ^ k) =
        ((2 * Real.pi : ℝ) : ℂ) •
          Operator.euclideanOperator
            (spectralJetEval A (fun z ↦ g z ^ k))) :
    ‖spectralJetEval A g‖ ≤ 2 := by
  let T : Operator.EuclideanEndomorphism n :=
    Operator.euclideanOperator (spectralJetEval A g)
  let S := B.positiveDensity.canonicalSquareRoot
  have hweighted (k : ℕ) (hk : 1 ≤ k) :
      Operator.weightedAdjointResolventIntegral (mu := mu)
          B.outwardNormal B.resolvent f k =
        ((2 * Real.pi : ℝ) : ℂ) •
          (ContinuousLinearMap.adjoint T) ^ k := by
    have hright :
        ∫ t, ((f ^ k : i →ᵇ ℂ) t) •
              Operator.rightResolventBoundaryTerm
                (B.resolvent t) (B.outwardNormal t) ∂mu =
          holomorphicRightResolventIntegral B (fun z ↦ g z ^ k) := by
      rw [holomorphicRightResolventIntegral]
      apply integral_congr_ae
      filter_upwards [hboundary] with t ht
      simp [ht]
    rw [Operator.weightedAdjointResolventIntegral,
      Operator.integral_conjugateBoundary_adjointResolvent_eq_star,
      hright, hcauchy k hk, spectralJetEval_pow A hg k]
    simp [T, ContinuousLinearMap.star_eq_adjoint]
  have herr (k : ℕ) (hk : 1 ≤ k) :
      Operator.dilationError T
          (Operator.boundaryMultiplier
            (E := Operator.EuclideanVector n) (mu := mu) f)
          S.boundaryIsometry k =
        Operator.normalizedRightResolventIntegral (mu := mu)
          B.outwardNormal B.resolvent f k := by
    exact Operator.dilationError_eq_normalizedRightResolventIntegral S T
      B.outwardNormal B.resolvent f k
      (Filter.Eventually.of_forall fun t ↦ by
        simp [Operator.CauchyResolventBoundary.positiveDensity_apply])
      B.integrable_right B.integrable_adjoint (hweighted k hk)
  have herrBounded : ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k →
      ‖Operator.dilationError T
        (Operator.boundaryMultiplier
          (E := Operator.EuclideanVector n) (mu := mu) f)
        S.boundaryIsometry k‖ ≤ C := by
    refine ⟨(2 * Real.pi)⁻¹ *
      ∫ t, ‖Operator.rightResolventBoundaryTerm
        (B.resolvent t) (B.outwardNormal t)‖ ∂mu, ?_⟩
    intro k hk
    rw [herr k hk]
    exact Operator.norm_normalizedRightResolventIntegral_le
      B.outwardNormal B.resolvent f hf B.integrable_right k
  have herrCommutes : ∀ k : ℕ, 1 ≤ k →
      Commute
        (Operator.dilationError T
          (Operator.boundaryMultiplier
            (E := Operator.EuclideanVector n) (mu := mu) f)
          S.boundaryIsometry k) T := by
    intro k hk
    rw [herr k hk]
    simpa only [T, spectralJetEval_eq_polynomialEval] using
      Operator.normalizedRightResolventIntegral_commutes_polynomialEval
        A B.boundaryPoint B.outwardNormal B.resolvent f
        (spectralJetPolynomial A g) k B.resolvent_ae B.integrable_right
  let D : Operator.DilationWitness
      (K := MeasureTheory.Lp (Operator.EuclideanVector n) 2 mu) T :=
    Operator.boundaryDilationWitness T S f hf herrBounded herrCommutes
  rw [Operator.matrix_norm_eq_operator_norm]
  exact D.norm_le_two

/-- A supporting Cauchy boundary that evaluates every function holomorphic on
a neighborhood of `K`.  Its fields are the raw boundary trace and ordinary
holomorphic Cauchy formula; positivity, the adjoint formulas, the square root,
and the dilation estimate are not fields. -/
structure NeighborhoodHolomorphicCauchyBoundary
    (A : Operator.SquareMatrix n) (K : Set ℂ) (mu : Measure i)
    extends Operator.CauchyResolventBoundary A mu where
  boundaryPoint_mem : ∀ᵐ t ∂mu, boundaryPoint t ∈ K
  /-- Bounded boundary trace of a scalar function. -/
  boundaryTrace : (ℂ → ℂ) → i →ᵇ ℂ
  boundaryTrace_eq : ∀ (g : ℂ → ℂ), ContinuousOn g K →
    ∀ᵐ t ∂mu, boundaryTrace g t = g (boundaryPoint t)
  boundaryTrace_norm_le : ∀ (g : ℂ → ℂ) (r : ℝ),
    ContinuousOn g K → (∀ z ∈ K, ‖g z‖ ≤ r) →
      ‖boundaryTrace g‖ ≤ r
  holomorphic_cauchy : ∀ (g : ℂ → ℂ) (V : Set ℂ),
    IsOpen V → K ⊆ V → DifferentiableOn ℂ g V →
      holomorphicRightResolventIntegral toCauchyResolventBoundary g =
        ((2 * Real.pi : ℝ) : ℂ) •
          Operator.euclideanOperator (spectralJetEval A g)

/-- A neighborhood-holomorphic Cauchy boundary gives the normalized sharp
estimate. -/
theorem NeighborhoodHolomorphicCauchyBoundary.norm_spectralJetEval_le_two
    [Nonempty n] {A : Operator.SquareMatrix n} {K : Set ℂ}
    (B : NeighborhoodHolomorphicCauchyBoundary A K mu)
    (hroots : ∀ z ∈ A.charpoly.roots, z ∈ K)
    (g : ℂ → ℂ) (V : Set ℂ)
    (hVo : IsOpen V) (hKV : K ⊆ V) (hg : DifferentiableOn ℂ g V)
    (hgOne : ∀ z ∈ K, ‖g z‖ ≤ 1) :
    ‖spectralJetEval A g‖ ≤ 2 := by
  have hgK : ContinuousOn g K := hg.continuousOn.mono hKV
  apply norm_spectralJetEval_le_two_of_cauchyBoundary
    B.toCauchyResolventBoundary g
    (fun a ↦ hg.analyticAt (hVo.mem_nhds (hKV (hroots (a : ℂ)
      (Multiset.mem_toFinset.mp a.2)))))
    (B.boundaryTrace g) (B.boundaryTrace_eq g hgK)
    (B.boundaryTrace_norm_le g 1 hgK hgOne)
  intro k hk
  exact B.holomorphic_cauchy (fun z ↦ g z ^ k) V hVo hKV (hg.pow k)

/-- The raw supporting-boundary Cauchy package implies the exact homogeneous
neighborhood-holomorphic calculus estimate at constant two. -/
theorem NeighborhoodHolomorphicCauchyBoundary.hasNeighborhoodHolomorphicCalculusBound
    [Nonempty n] {A : Operator.SquareMatrix n} {K : Set ℂ}
    (B : NeighborhoodHolomorphicCauchyBoundary A K mu)
    (hroots : ∀ z ∈ A.charpoly.roots, z ∈ K) :
    HasNeighborhoodHolomorphicCalculusBound A K 2 := by
  intro g V r hVo hKV hg hr hgR
  rcases hr.eq_or_lt with rfl | hrpos
  · have hgzero : ∀ᵐ t ∂mu, g (B.boundaryPoint t) = 0 := by
      filter_upwards [B.boundaryPoint_mem] with t ht
      exact norm_eq_zero.mp (le_antisymm (hgR _ ht) (norm_nonneg _))
    have hintzero :
        holomorphicRightResolventIntegral B.toCauchyResolventBoundary g = 0 := by
      rw [holomorphicRightResolventIntegral]
      rw [← integral_zero]
      apply integral_congr_ae
      filter_upwards [hgzero] with t ht
      rw [ht]
      module
    have hcauchy := B.holomorphic_cauchy g V hVo hKV hg
    rw [hintzero] at hcauchy
    have hcoef : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
    have hevalOp : Operator.euclideanOperator (spectralJetEval A g) = 0 := by
      exact (smul_eq_zero.mp hcauchy.symm).resolve_left hcoef
    have heval : spectralJetEval A g = 0 := by
      apply Operator.euclideanOperator.injective
      simpa using hevalOp
    simp [heval]
  · let c : ℂ := (r : ℂ)⁻¹
    have hcnorm : ‖c‖ = r⁻¹ := by
      simp [c, abs_of_pos hrpos]
    have hnormalized : ∀ z ∈ K, ‖c * g z‖ ≤ 1 := by
      intro z hz
      rw [norm_mul, hcnorm]
      exact (mul_le_mul_of_nonneg_left (hgR z hz) (inv_nonneg.mpr hrpos.le)).trans
        (le_of_eq (inv_mul_cancel₀ hrpos.ne'))
    have hbound := B.norm_spectralJetEval_le_two hroots
      (fun z ↦ c * g z) V hVo hKV (differentiableOn_const (c := c) |>.mul hg)
      hnormalized
    rw [spectralJetEval_const_mul, norm_smul, hcnorm] at hbound
    calc
      ‖spectralJetEval A g‖ = r * (r⁻¹ * ‖spectralJetEval A g‖) := by
        field_simp
      _ ≤ r * 2 := mul_le_mul_of_nonneg_left hbound hrpos.le
      _ = 2 * r := mul_comm _ _

end

end DiskRigidity.Complex
