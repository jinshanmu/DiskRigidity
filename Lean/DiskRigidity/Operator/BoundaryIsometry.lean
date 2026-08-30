/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.DoubleLayer
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Normalization of the double-layer boundary embedding

Formula (3.6) says that the positive boundary density has mass `2 I`.
This file turns that operator identity into the scalar norm identity which
makes `x ↦ P(σ)^(1/2)x / √2` an isometry.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate InnerProduct InnerProductSpace

namespace DiskRigidity.Operator

variable {i n : Type*} [TopologicalSpace i] [MeasurableSpace i]
  [Fintype n] [DecidableEq n]
  {mu : Measure i}

/-- The quadratic coefficient of an integrable operator-valued density is
integrable. -/
theorem PositiveBoundaryDensity.integrable_re_inner_density
    (D : PositiveBoundaryDensity (n := n) mu) (x : EuclideanVector n) :
    Integrable (fun σ ↦ Complex.re ⟪x, D.density σ x⟫_ℂ) mu := by
  have happly := (ContinuousLinearMap.apply ℂ (EuclideanVector n) x).integrable_comp
    D.integrable_density
  have hinner := (innerSL ℂ x).integrable_comp happly
  exact hinner.re

/-- The mass identity `∫ P = 2 I` evaluated on one vector. -/
theorem PositiveBoundaryDensity.integral_re_inner_density
    (D : PositiveBoundaryDensity (n := n) mu) (x : EuclideanVector n) :
    ∫ σ, Complex.re ⟪x, D.density σ x⟫_ℂ ∂mu = 2 * ‖x‖ ^ 2 := by
  let evx : EuclideanEndomorphism n →L[ℂ] EuclideanVector n :=
    ContinuousLinearMap.apply ℂ (EuclideanVector n) x
  let coeff : EuclideanVector n →L[ℂ] ℂ := innerSL ℂ x
  have hev : Integrable (fun σ ↦ evx (D.density σ)) mu :=
    evx.integrable_comp D.integrable_density
  have hcoeff : Integrable (fun σ ↦ coeff (evx (D.density σ))) mu :=
    coeff.integrable_comp hev
  calc
    ∫ σ, Complex.re ⟪x, D.density σ x⟫_ℂ ∂mu =
        Complex.re (∫ σ, coeff (evx (D.density σ)) ∂mu) := by
      simpa [evx, coeff] using
        Complex.reCLM.integral_comp_comm hcoeff
    _ = Complex.re (coeff (∫ σ, evx (D.density σ) ∂mu)) := by
      congr 1
      exact coeff.integral_comp_comm hev
    _ = Complex.re (coeff (evx (∫ σ, D.density σ ∂mu))) := by
      congr 2
      exact evx.integral_comp_comm D.integrable_density
    _ = 2 * ‖x‖ ^ 2 := by
      rw [D.mass_eq_two_one]
      simp [evx, coeff, inner_self_eq_norm_sq_to_K]
      norm_cast

/-- Any measurable square-root factor normalized by `1 / √2` has exactly
the `L²` norm required for the boundary isometry.  This is the scalar content
of the isometry assertion immediately following (3.6). -/
theorem integral_norm_factor_sq_eq_norm_sq
    (D : PositiveBoundaryDensity (n := n) mu)
    (factor : i → EuclideanEndomorphism n) (x : EuclideanVector n)
    (hfactor : ∀ᵐ σ ∂mu,
      ‖factor σ x‖ ^ 2 =
        (2 : ℝ)⁻¹ * Complex.re ⟪x, D.density σ x⟫_ℂ) :
    ∫ σ, ‖factor σ x‖ ^ 2 ∂mu = ‖x‖ ^ 2 := by
  calc
    ∫ σ, ‖factor σ x‖ ^ 2 ∂mu =
        ∫ σ, (2 : ℝ)⁻¹ * Complex.re ⟪x, D.density σ x⟫_ℂ ∂mu :=
      integral_congr_ae hfactor
    _ = (2 : ℝ)⁻¹ *
        ∫ σ, Complex.re ⟪x, D.density σ x⟫_ℂ ∂mu := by
      rw [integral_const_mul]
    _ = ‖x‖ ^ 2 := by
      rw [D.integral_re_inner_density]
      ring

/-- A measurable operator square root of half the positive boundary density.
The Gram identity is the coordinate-free form of
`factor(σ) = P(σ)^(1/2) / √2`. -/
structure PositiveBoundarySquareRoot (D : PositiveBoundaryDensity (n := n) mu) where
  /-- Measurable square-root factor of half the boundary density. -/
  factor : i → EuclideanEndomorphism n
  aestronglyMeasurable_apply : ∀ x : EuclideanVector n,
    AEStronglyMeasurable (fun σ ↦ factor σ x) mu
  gram_ae : ∀ᵐ σ ∂mu,
    (factor σ†) ∘L factor σ = (2 : ℂ)⁻¹ • D.density σ

/-- The Gram identity of a positive boundary square root gives its pointwise
quadratic norm identity. -/
theorem PositiveBoundarySquareRoot.norm_sq_apply_ae
    {D : PositiveBoundaryDensity (n := n) mu}
    (S : PositiveBoundarySquareRoot D) (x : EuclideanVector n) :
    ∀ᵐ σ ∂mu,
      ‖S.factor σ x‖ ^ 2 =
        (2 : ℝ)⁻¹ * Complex.re ⟪x, D.density σ x⟫_ℂ := by
  filter_upwards [S.gram_ae] with σ hgram
  rw [(S.factor σ).apply_norm_sq_eq_inner_adjoint_right]
  change Complex.re ⟪x, ((S.factor σ†) ∘L S.factor σ) x⟫_ℂ = _
  rw [hgram]
  simp only [smul_apply, inner_smul_right]
  change Complex.re ((2 : ℂ)⁻¹ * ⟪x, D.density σ x⟫_ℂ) = _
  norm_num [Complex.mul_re]

/-- Each square-root column belongs to the boundary `L²` space. -/
theorem PositiveBoundarySquareRoot.memLp_two
    {D : PositiveBoundaryDensity (n := n) mu}
    (S : PositiveBoundarySquareRoot D) (x : EuclideanVector n) :
    MemLp (fun σ ↦ S.factor σ x) 2 mu := by
  rw [memLp_two_iff_integrable_sq_norm (S.aestronglyMeasurable_apply x)]
  have hsymm :
      (fun σ ↦ (2 : ℝ)⁻¹ * Complex.re ⟪x, D.density σ x⟫_ℂ) =ᵐ[mu]
        fun σ ↦ ‖S.factor σ x‖ ^ 2 := by
    filter_upwards [S.norm_sq_apply_ae x] with σ hσ
    exact hσ.symm
  exact ((D.integrable_re_inner_density x).const_mul (2 : ℝ)⁻¹).congr
    hsymm

/-- The boundary column map before its norm preservation is recorded. -/
def PositiveBoundarySquareRoot.embeddingLinear
    {D : PositiveBoundaryDensity (n := n) mu}
    (S : PositiveBoundarySquareRoot D) :
    EuclideanVector n →ₗ[ℂ] Lp (EuclideanVector n) 2 mu where
  toFun x := (S.memLp_two x).toLp (fun σ ↦ S.factor σ x)
  map_add' x y := by
    rw [← (S.memLp_two x).toLp_add (S.memLp_two y)]
    exact MemLp.toLp_congr (S.memLp_two (x + y))
      ((S.memLp_two x).add (S.memLp_two y))
      (Filter.Eventually.of_forall fun σ ↦ by simp)
  map_smul' c x := by
    change (S.memLp_two (c • x)).toLp (fun σ ↦ S.factor σ (c • x)) =
      c • (S.memLp_two x).toLp (fun σ ↦ S.factor σ x)
    rw [← (S.memLp_two x).toLp_const_smul c]
    exact MemLp.toLp_congr (S.memLp_two (c • x))
      ((S.memLp_two x).const_smul c)
      (Filter.Eventually.of_forall fun σ ↦ by simp)

/-- The squared norm of the boundary column in `L²` is the original
Euclidean squared norm. -/
theorem PositiveBoundarySquareRoot.norm_embeddingLinear_sq
    {D : PositiveBoundaryDensity (n := n) mu}
    (S : PositiveBoundarySquareRoot D) (x : EuclideanVector n) :
    ‖S.embeddingLinear x‖ ^ 2 = ‖x‖ ^ 2 := by
  let f : i → EuclideanVector n := fun σ ↦ S.factor σ x
  let hf : MemLp f 2 mu := S.memLp_two x
  have hcoe : ∀ᵐ σ ∂mu, (hf.toLp f : i → EuclideanVector n) σ = f σ :=
    hf.coeFn_toLp
  have hinner :
      ∫ σ, ⟪(hf.toLp f : i → EuclideanVector n) σ,
          (hf.toLp f : i → EuclideanVector n) σ⟫_ℂ ∂mu =
        ((∫ σ, ‖f σ‖ ^ 2 ∂mu : ℝ) : ℂ) := by
    calc
      ∫ σ, ⟪(hf.toLp f : i → EuclideanVector n) σ,
          (hf.toLp f : i → EuclideanVector n) σ⟫_ℂ ∂mu =
          ∫ σ, ((‖f σ‖ ^ 2 : ℝ) : ℂ) ∂mu := by
        apply integral_congr_ae
        filter_upwards [hcoe] with σ hσ
        rw [hσ, inner_self_eq_norm_sq_to_K]
        norm_cast
      _ = ((∫ σ, ‖f σ‖ ^ 2 ∂mu : ℝ) : ℂ) := by
        exact Complex.ofRealCLM.integral_comp_comm
          ((memLp_two_iff_integrable_sq_norm
            (S.aestronglyMeasurable_apply x)).mp hf)
  calc
    ‖S.embeddingLinear x‖ ^ 2 =
        Complex.re ⟪S.embeddingLinear x, S.embeddingLinear x⟫_ℂ :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = Complex.re
        (∫ σ, ⟪(hf.toLp f : i → EuclideanVector n) σ,
          (hf.toLp f : i → EuclideanVector n) σ⟫_ℂ ∂mu) := by
      rfl
    _ = ∫ σ, ‖f σ‖ ^ 2 ∂mu := by rw [hinner]; norm_cast
    _ = ‖x‖ ^ 2 := integral_norm_factor_sq_eq_norm_sq
      D S.factor x (S.norm_sq_apply_ae x)

/-- Formula (3.6) therefore constructs the actual boundary linear isometry
used by the dilation argument. -/
def PositiveBoundarySquareRoot.boundaryIsometry
    {D : PositiveBoundaryDensity (n := n) mu}
    (S : PositiveBoundarySquareRoot D) :
    EuclideanVector n →ₗᵢ[ℂ] Lp (EuclideanVector n) 2 mu :=
  LinearIsometry.mk S.embeddingLinear fun x ↦ by
    have hsquare := S.norm_embeddingLinear_sq x
    nlinarith [norm_nonneg (S.embeddingLinear x), norm_nonneg x]

/-- The constructed boundary isometry is represented almost everywhere by
the square-root column used to define it. -/
theorem PositiveBoundarySquareRoot.boundaryIsometry_coe_ae
    {D : PositiveBoundaryDensity (n := n) mu}
    (S : PositiveBoundarySquareRoot D) (x : EuclideanVector n) :
    (S.boundaryIsometry x : i → EuclideanVector n) =ᵐ[mu]
      fun σ ↦ S.factor σ x := by
  exact (S.memLp_two x).coeFn_toLp

end DiskRigidity.Operator
