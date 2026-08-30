/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.BoundaryMultiplication

/-!
# Compression of boundary multiplication

This file identifies the actual `L²` compression constructed from a positive
boundary square root with the operator-valued boundary integral `boundaryPhi`.
It is the algebraic and measure-theoretic step used when deriving (3.7).
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped BoundedContinuousFunction ComplexConjugate InnerProduct InnerProductSpace

namespace DiskRigidity.Operator

variable {i E : Type*} [TopologicalSpace i] [MeasurableSpace i] [BorelSpace i]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {mu : Measure i} [IsFiniteMeasure mu]

omit [CompleteSpace E] in
/-- Powers of the concrete boundary multiplier are represented by the
corresponding pointwise powers. -/
theorem boundaryMultiplier_pow_coe_ae (f : i →ᵇ ℂ) (u : Lp E 2 mu) (k : ℕ) :
    ((((boundaryMultiplier (E := E) (mu := mu) f) ^ k) u : Lp E 2 mu) : i → E)
      =ᵐ[mu] fun t ↦ (f t) ^ k • u t := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ']
      have hmul := boundaryMultiplier_coe_ae f
        (((boundaryMultiplier (E := E) (mu := mu) f) ^ k) u)
      filter_upwards [hmul, ih] with t hmult hik
      rw [mul_apply_eq_comp, hmult, hik, smul_smul, pow_succ']

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The compression of the `k`th adjoint multiplier power is exactly the
positive boundary map applied to the conjugated `k`th boundary power. -/
theorem boundaryCompression_eq_boundaryPhi
    {D : PositiveBoundaryDensity (n := n) mu}
    (S : PositiveBoundarySquareRoot D) (f : i →ᵇ ℂ) (k : ℕ) :
    dilationCompression
        (boundaryMultiplier (E := EuclideanVector n) (mu := mu) f)
        S.boundaryIsometry k =
      boundaryPhi D (star (f ^ k)) := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  let M := boundaryMultiplier (E := EuclideanVector n) (mu := mu) f
  let V := S.boundaryIsometry
  have hadj : (M†) ^ k = ((M ^ k)†) := by
    change star M ^ k = star (M ^ k)
    exact (star_pow M k).symm
  calc
    ⟪x, dilationCompression M V k y⟫_ℂ =
        ⟪V x, ((M†) ^ k) (V y)⟫_ℂ := by
      rw [dilationCompression_apply,
        V.toContinuousLinearMap.adjoint_inner_right]
      rfl
    _ = ⟪(M ^ k) (V x), V y⟫_ℂ := by
      rw [hadj, (M ^ k).adjoint_inner_right]
    _ = ∫ t, ⟪((M ^ k) (V x) : i → EuclideanVector n) t,
          (V y : i → EuclideanVector n) t⟫_ℂ ∂mu :=
      MeasureTheory.L2.inner_def _ _
    _ = ∫ t, ⟪x,
          ((2 : ℂ)⁻¹ • ((star (f ^ k) : i →ᵇ ℂ) t • D.density t)) y⟫_ℂ ∂mu := by
      apply integral_congr_ae
      filter_upwards [boundaryMultiplier_pow_coe_ae f (V x) k,
        S.boundaryIsometry_coe_ae x, S.boundaryIsometry_coe_ae y,
        S.gram_ae] with t hpow hx hy hgram
      rw [hpow, hx, hy, inner_smul_left]
      change star ((f t) ^ k) * ⟪S.factor t x, S.factor t y⟫_ℂ = _
      rw [← (S.factor t).adjoint_inner_right]
      change star ((f t) ^ k) *
        ⟪x, ((S.factor t†) ∘L S.factor t) y⟫_ℂ = _
      rw [hgram]
      simp only [smul_apply, inner_smul_right,
        BoundedContinuousFunction.star_apply,
        BoundedContinuousFunction.pow_apply]
      ring
    _ = ⟪x, boundaryPhi D (star (f ^ k)) y⟫_ℂ := by
      rw [boundaryPhi]
      have hint := D.integrable_smul (star (f ^ k))
      let evy : EuclideanEndomorphism n →L[ℂ] EuclideanVector n :=
        ContinuousLinearMap.apply ℂ (EuclideanVector n) y
      have hevy : Integrable
          (fun t ↦ evy (((star (f ^ k) : i →ᵇ ℂ) t) • D.density t)) mu :=
        evy.integrable_comp hint
      have hevy' : Integrable
          (fun t ↦ ((((star (f ^ k) : i →ᵇ ℂ) t) • D.density t) y)) mu := by
        simpa [evy] using hevy
      have hevint :
          (∫ t, ((star (f ^ k) : i →ᵇ ℂ) t) • D.density t ∂mu) y =
            ∫ t, (((star (f ^ k) : i →ᵇ ℂ) t) • D.density t) y ∂mu := by
        change evy (∫ t, ((star (f ^ k) : i →ᵇ ℂ) t) • D.density t ∂mu) = _
        exact (evy.integral_comp_comm hint).symm
      rw [smul_apply, inner_smul_right, hevint,
        ← integral_inner hevy' x, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [smul_apply, inner_smul_right, smul_smul]
      ring

end DiskRigidity.Operator
