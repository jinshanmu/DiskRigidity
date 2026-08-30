/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.ResolventTransform

/-!
# Nonvanishing of convex Cauchy transforms

This file formalizes the separation-and-positivity argument in Lemma 6.2.
The core statement is measure-theoretic: a complex integrand contained
almost everywhere in one open half-plane has nonzero integral.
-/

noncomputable section

open Filter MeasureTheory

@[expose] public section

namespace DiskRigidity.Analysis

/-- The Cauchy kernel at a point outside a closed set is integrable for every
finite measure carried by that set. -/
theorem integrable_cauchyKernel_of_mem_ae_closed
    {mu : Measure ℂ} [IsFiniteMeasure mu]
    {K : Set ℂ} (hKclosed : IsClosed K) (hmu : ∀ᵐ w ∂mu, w ∈ K)
    {z : ℂ} (hz : z ∉ K) :
    Integrable (fun w : ℂ ↦ (z - w)⁻¹) mu := by
  have hsupport : mu.support ⊆ K :=
    Measure.support_subset_of_isClosed hKclosed hmu
  have hzsupport : z ∉ mu.support := fun hzmem ↦ hz (hsupport hzmem)
  have hres : Integrable (resolvent z) mu := by
    exact MeasureTheory.integrable_resolvent (by simpa using hzsupport)
  convert hres.neg using 1
  ext w
  rw [show z - w = -(w - z) by ring, inv_neg]
  simp [resolvent]

/-- A point outside a nonempty closed convex subset of the complex plane is
strictly separated from it by multiplication by a nonzero complex scalar. -/
theorem exists_strict_complex_separator {K : Set ℂ} (hKconv : Convex ℝ K)
    (hKclosed : IsClosed K) (hKne : K.Nonempty) {z : ℂ} (hz : z ∉ K) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ w ∈ K, 0 < (c * (z - w)).re := by
  obtain ⟨f, u, hfu, huz⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
      hKconv hKclosed hz
  have hf_apply (w : ℂ) : f w = w * f 1 := by
    simpa only [smul_eq_mul, mul_one] using f.map_smul w (1 : ℂ)
  obtain ⟨w₀, hw₀⟩ := hKne
  have hc0 : f 1 ≠ 0 := by
    intro hc
    have hwzero : f w₀ = 0 := by rw [hf_apply, hc, mul_zero]
    have hzzero : f z = 0 := by rw [hf_apply, hc, mul_zero]
    have := hfu w₀ hw₀
    rw [hwzero] at this
    rw [hzzero] at huz
    norm_num at this huz
    linarith
  refine ⟨f 1, hc0, ?_⟩
  intro w hw
  have hwlt : (f w).re < (f z).re := (hfu w hw).trans huz
  calc
    0 < (f z).re - (f w).re := sub_pos.mpr hwlt
    _ = ((f 1) * (z - w)).re := by
      rw [hf_apply z, hf_apply w]
      rw [mul_sub, Complex.sub_re, mul_comm (f 1) z,
        mul_comm (f 1) w]

/-- A strictly positive integrable real function has positive integral under
a probability measure. -/
theorem integral_pos_of_ae_pos_probability
    {α : Type*} [MeasurableSpace α] {mu : Measure α}
    [IsProbabilityMeasure mu] {f : α → ℝ}
    (hf : Integrable f mu) (hpos : ∀ᵐ x ∂mu, 0 < f x) :
    0 < ∫ x, f x ∂mu := by
  rw [integral_pos_iff_support_of_nonneg_ae
    (hpos.mono fun _ hx ↦ hx.le) hf]
  by_contra hnot
  have hsuppzero : mu (Function.support f) = 0 := by
    exact nonpos_iff_eq_zero.mp (not_lt.mp hnot)
  have hout : ∀ᵐ x ∂mu, x ∈ (Function.support f)ᶜ := by
    change (Function.support f)ᶜ ∈ ae mu
    rw [mem_ae_iff]
    simpa only [compl_compl] using hsuppzero
  have hfalse : ∀ᵐ _x ∂mu, False := by
    filter_upwards [hpos, hout] with x hx hxsupp
    have hfx : f x = 0 := by
      simpa only [Set.mem_compl_iff, Function.mem_support, not_not] using hxsupp
    linarith
  have hunivzero : mu Set.univ = 0 := by
    simpa using (ae_iff.mp hfalse)
  rw [IsProbabilityMeasure.measure_univ] at hunivzero
  exact one_ne_zero hunivzero

/-- The integral of an integrable complex function lying almost everywhere
in one strict open half-plane is nonzero. -/
theorem integral_ne_zero_of_ae_openHalfPlane
    {α : Type*} [MeasurableSpace α] {mu : Measure α}
    [IsProbabilityMeasure mu] (g : α → ℂ) (hg : Integrable g mu)
    {c : ℂ} (hpos : ∀ᵐ x ∂mu, 0 < (c * g x).re) :
    ∫ x, g x ∂mu ≠ 0 := by
  have hcg : Integrable (fun x ↦ c * g x) mu := by
    exact hg.const_mul c
  have hrepos : 0 < ∫ x, (c * g x).re ∂mu :=
    integral_pos_of_ae_pos_probability hcg.re hpos
  have hre : ∫ x, (c * g x).re ∂mu =
      (c * ∫ x, g x ∂mu).re := by
    change (∫ x, RCLike.re (c * g x) ∂mu) =
      RCLike.re (c * ∫ x, g x ∂mu)
    rw [integral_re hcg, integral_const_mul]
  intro hzero
  rw [hre, hzero, mul_zero, Complex.zero_re] at hrepos
  exact lt_irrefl 0 hrepos

/-- The algebraic half-plane computation for a reciprocal.  If `c d` has
positive real part, then `conj(c) / d` does as well. -/
theorem star_mul_inv_re_pos {c d : ℂ} (hd : d ≠ 0)
    (hcd : 0 < (c * d).re) :
    0 < (star c * d⁻¹).re := by
  change 0 < ((starRingEnd ℂ c) * d⁻¹).re
  have hnorm : 0 < Complex.normSq d := Complex.normSq_pos.mpr hd
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.inv_re, Complex.inv_im, div_eq_mul_inv, div_eq_mul_inv]
  calc
    0 < (c * d).re * (Complex.normSq d)⁻¹ :=
      mul_pos hcd (inv_pos.mpr hnorm)
    _ = c.re * (d.re * (Complex.normSq d)⁻¹) -
        -c.im * (-d.im * (Complex.normSq d)⁻¹) := by
      rw [Complex.mul_re]
      ring

/-- Lemma 6.2's Cauchy-transform nonvanishing statement, with integrability
made explicit. -/
theorem cauchyTransform_ne_zero_off_convex
    {mu : Measure ℂ} [IsProbabilityMeasure mu]
    {K : Set ℂ} (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKne : K.Nonempty) (hmu : ∀ᵐ w ∂mu, w ∈ K)
    {z : ℂ} (hz : z ∉ K)
    (hint : Integrable (fun w : ℂ ↦ (z - w)⁻¹) mu) :
    ∫ w : ℂ, (z - w)⁻¹ ∂mu ≠ 0 := by
  obtain ⟨c, hc0, hc⟩ :=
    exists_strict_complex_separator hKconv hKclosed hKne hz
  apply integral_ne_zero_of_ae_openHalfPlane
    (fun w : ℂ ↦ (z - w)⁻¹) hint (c := star c)
  filter_upwards [hmu] with w hw
  apply star_mul_inv_re_pos
  · intro hzw
    apply hz
    have : z = w := sub_eq_zero.mp hzw
    rwa [this]
  · exact hc w hw

/-- The version of `cauchyTransform_ne_zero_off_convex` in which
integrability is discharged from closed support and finite mass. -/
theorem cauchyTransform_ne_zero_off_convex'
    {mu : Measure ℂ} [IsProbabilityMeasure mu]
    {K : Set ℂ} (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKne : K.Nonempty) (hmu : ∀ᵐ w ∂mu, w ∈ K)
    {z : ℂ} (hz : z ∉ K) :
    ∫ w : ℂ, (z - w)⁻¹ ∂mu ≠ 0 := by
  exact cauchyTransform_ne_zero_off_convex hKconv hKclosed hKne hmu hz
    (integrable_cauchyKernel_of_mem_ae_closed hKclosed hmu hz)

end DiskRigidity.Analysis
