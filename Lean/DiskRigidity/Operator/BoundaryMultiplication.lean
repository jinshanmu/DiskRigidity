/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.BoundaryIsometry
public import DiskRigidity.Operator.SharpBound
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Boundary multiplication on `L²`

This file constructs the multiplication operator `M_f` used after (3.6).
It proves both its pointwise realization and the exact norm estimate
`||M_f|| ≤ ||f||∞`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction ENNReal

namespace DiskRigidity.Operator

variable {i E : Type*} [TopologicalSpace i] [MeasurableSpace i] [BorelSpace i]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {mu : Measure i} [IsFiniteMeasure mu]

/-- A bounded continuous scalar function regarded as an `L∞` function. -/
def boundaryScalarLp (f : i →ᵇ ℂ) : Lp ℂ ∞ mu :=
  BoundedContinuousFunction.toLp ∞ mu ℂ f

/-- Passing a bounded continuous function to `L∞` does not increase its
uniform norm. -/
theorem norm_boundaryScalarLp_le (f : i →ᵇ ℂ) :
    ‖boundaryScalarLp (mu := mu) f‖ ≤ ‖f‖ := by
  have hOp :
      ‖(BoundedContinuousFunction.toLp (E := ℂ) ∞ mu ℂ)‖ ≤ 1 := by
    simpa using BoundedContinuousFunction.toLp_norm_le
      (E := ℂ) (p := (∞ : ℝ≥0∞)) (μ := mu) (𝕜 := ℂ)
  exact ((BoundedContinuousFunction.toLp (E := ℂ) ∞ mu ℂ).le_opNorm f).trans
    (by simpa [boundaryScalarLp] using
      mul_le_mul_of_nonneg_right hOp (norm_nonneg f))

/-- Pointwise boundary multiplication as a complex-linear map on `L²`. -/
def boundaryMultiplierLinear (f : i →ᵇ ℂ) :
    Lp E 2 mu →ₗ[ℂ] Lp E 2 mu where
  toFun u := boundaryScalarLp (mu := mu) f • u
  map_add' u v := Lp.add_smul (boundaryScalarLp (mu := mu) f) u v
  map_smul' c u :=
    (Lp.smul_comm c (boundaryScalarLp (mu := mu) f) u).symm

/-- The pointwise multiplication linear map satisfies its uniform bound. -/
theorem norm_boundaryMultiplierLinear_apply_le (f : i →ᵇ ℂ)
    (u : Lp E 2 mu) :
    ‖boundaryMultiplierLinear (E := E) (mu := mu) f u‖ ≤ ‖f‖ * ‖u‖ := by
  exact (Lp.norm_smul_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_boundaryScalarLp_le f) (norm_nonneg u))

/-- The bounded multiplication operator `M_f` on the boundary `L²` space. -/
def boundaryMultiplier (f : i →ᵇ ℂ) :
    Lp E 2 mu →L[ℂ] Lp E 2 mu :=
  LinearMap.mkContinuous (boundaryMultiplierLinear (E := E) (mu := mu) f)
    ‖f‖ (norm_boundaryMultiplierLinear_apply_le f)

/-- The operator norm of boundary multiplication is bounded by the uniform
norm of the multiplier. -/
theorem norm_boundaryMultiplier_le (f : i →ᵇ ℂ) :
    ‖boundaryMultiplier (E := E) (mu := mu) f‖ ≤ ‖f‖ := by
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg f) _

/-- A normalized boundary function acts contractively on `L²`. -/
theorem norm_boundaryMultiplier_le_one (f : i →ᵇ ℂ) (hf : ‖f‖ ≤ 1) :
    ‖boundaryMultiplier (E := E) (mu := mu) f‖ ≤ 1 :=
  (norm_boundaryMultiplier_le f).trans hf

/-- The constructed operator is almost everywhere the expected pointwise
multiplication. -/
theorem boundaryMultiplier_coe_ae (f : i →ᵇ ℂ) (u : Lp E 2 mu) :
    (boundaryMultiplier (E := E) (mu := mu) f u : i → E) =ᵐ[mu]
      fun σ ↦ f σ • u σ := by
  change
    ((boundaryScalarLp (mu := mu) f • u : Lp E 2 mu) : i → E) =ᵐ[mu]
      fun σ ↦ f σ • u σ
  have hmul :
      ((boundaryScalarLp (mu := mu) f • u : Lp E 2 mu) : i → E) =ᵐ[mu]
        fun σ ↦ (boundaryScalarLp (mu := mu) f : i → ℂ) σ • u σ :=
    Lp.coeFn_lpSMul _ _
  filter_upwards [hmul,
    BoundedContinuousFunction.coeFn_toLp (p := (∞ : ℝ≥0∞)) mu ℂ f]
      with σ hmulσ hfσ
  rw [hmulσ]
  simpa [boundaryScalarLp] using congrArg (fun c : ℂ ↦ c • u σ) hfσ

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Once the Cauchy error formula has supplied boundedness and commutation,
the positive density, its square root, and normalized boundary function give
the full dilation witness required by Proposition 3.2. -/
def boundaryDilationWitness
    (T : EuclideanEndomorphism n)
    {D : PositiveBoundaryDensity (n := n) mu}
    (S : PositiveBoundarySquareRoot D) (f : i →ᵇ ℂ) (hf : ‖f‖ ≤ 1)
    (hbounded : ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k →
      ‖dilationError T
        (boundaryMultiplier (E := EuclideanVector n) (mu := mu) f)
        S.boundaryIsometry k‖ ≤ C)
    (hcomm : ∀ k : ℕ, 1 ≤ k →
      Commute
        (dilationError T
          (boundaryMultiplier (E := EuclideanVector n) (mu := mu) f)
          S.boundaryIsometry k) T) :
    DilationWitness (K := Lp (EuclideanVector n) 2 mu) T where
  multiplication := boundaryMultiplier f
  boundaryIsometry := S.boundaryIsometry
  contraction := norm_boundaryMultiplier_le_one f hf
  errors_bounded := hbounded
  errors_commute := hcomm

end DiskRigidity.Operator
