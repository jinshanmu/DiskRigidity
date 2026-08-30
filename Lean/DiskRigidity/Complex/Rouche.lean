/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

module

public import DiskRigidity.Complex.RiemannMapping
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Rouché's theorem on a disc

This is the circle form needed for the local injectivity theorem.  The proof compares
logarithmic-derivative integrals and uses the argument-principle identity already established in
`DiskRigidity.Complex.RiemannMapping`.
-/

open Complex Metric

namespace DiskRigidity.Complex

@[expose] public section

variable {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}

private lemma ne_zero_left {z : ℂ} (h : ‖f z - g z‖ < ‖f z‖ + ‖g z‖) : f z ≠ 0 := by
  intro h0
  rw [h0] at h
  simp at h

private lemma ne_zero_right {z : ℂ} (h : ‖f z - g z‖ < ‖f z‖ + ‖g z‖) : g z ≠ 0 := by
  intro h0
  rw [h0] at h
  simp at h

private lemma mem_slitPlane_of_norm_one_sub_lt {w : ℂ} (h : ‖1 - w‖ < 1 + ‖w‖) :
    w ∈ slitPlane := by
  by_contra hw
  rw [mem_slitPlane_iff] at hw
  push Not at hw
  obtain ⟨hre, him⟩ := hw
  have hwe : w = (w.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hwe] at h
  have h1 : (1 : ℂ) - (w.re : ℂ) = ((1 - w.re : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h1, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - w.re),
    abs_of_nonpos hre] at h
  linarith

private lemma div_mem_slitPlane {z : ℂ} (h : ‖f z - g z‖ < ‖f z‖ + ‖g z‖) :
    g z / f z ∈ slitPlane := by
  have hfz : f z ≠ 0 := ne_zero_left h
  have hpos : (0 : ℝ) < ‖f z‖ := norm_pos_iff.2 hfz
  refine mem_slitPlane_of_norm_one_sub_lt ?_
  have e : (1 : ℂ) - g z / f z = (f z - g z) / f z := by field_simp
  rw [e, norm_div, norm_div, div_lt_iff₀ hpos]
  have e2 : (1 + ‖g z‖ / ‖f z‖) * ‖f z‖ = ‖f z‖ + ‖g z‖ := by field_simp
  rwa [e2]

private lemma circleIntegrable_logDeriv (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hne : ∀ z ∈ sphere c R, f z ≠ 0) : CircleIntegrable (logDeriv f) c R := by
  refine ContinuousOn.circleIntegrable hR.le ?_
  have hsub : sphere c R ⊆ closedBall c R := sphere_subset_closedBall
  exact ((hf.deriv.continuousOn).mono hsub).div ((hf.continuousOn).mono hsub) hne

private lemma circleIntegral_logDeriv_div_eq_zero (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hs : ∀ z ∈ sphere c R, ‖f z - g z‖ < ‖f z‖ + ‖g z‖) :
    (∮ z in C(c, R), logDeriv (fun w ↦ g w / f w) z) = 0 := by
  refine circleIntegral.integral_eq_zero_of_hasDerivWithinAt
    (f := fun w ↦ Complex.log (g w / f w)) hR.le (fun z hz ↦ ?_)
  have hzc : z ∈ closedBall c R := sphere_subset_closedBall hz
  have hlt := hs z hz
  have hfz : f z ≠ 0 := ne_zero_left hlt
  have hslit : g z / f z ∈ slitPlane := div_mem_slitPlane hlt
  have hf' : HasDerivAt f (deriv f z) z := (hf z hzc).differentiableAt.hasDerivAt
  have hg' : HasDerivAt g (deriv g z) z := (hg z hzc).differentiableAt.hasDerivAt
  have hq : HasDerivAt (fun w ↦ g w / f w)
      ((deriv g z * f z - g z * deriv f z) / f z ^ 2) z := hg'.div hf' hfz
  have hcomp := (Complex.hasDerivAt_log hslit).comp z hq
  have hval : logDeriv (fun w ↦ g w / f w) z =
      (g z / f z)⁻¹ * ((deriv g z * f z - g z * deriv f z) / f z ^ 2) := by
    rw [logDeriv_apply, hq.deriv]
    field_simp
  rw [hval]
  exact hcomp.hasDerivWithinAt

/-- Symmetric Rouché theorem on a disc, with zeros counted with multiplicity. -/
theorem rouche_symm (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hs : ∀ z ∈ sphere c R, ‖f z - g z‖ < ‖f z‖ + ‖g z‖) :
    (∑ᶠ z ∈ ball c R, analyticOrderNatAt f z) =
      ∑ᶠ z ∈ ball c R, analyticOrderNatAt g z := by
  have hnef : ∀ z ∈ sphere c R, f z ≠ 0 := fun z hz ↦ ne_zero_left (hs z hz)
  have hneg : ∀ z ∈ sphere c R, g z ≠ 0 := fun z hz ↦ ne_zero_right (hs z hz)
  have hsplit : (∮ z in C(c, R), logDeriv g z) =
      (∮ z in C(c, R), logDeriv f z) := by
    have heq : Set.EqOn (logDeriv (fun w ↦ g w / f w))
        (fun z ↦ logDeriv g z - logDeriv f z) (sphere c R) := by
      intro z hz
      exact logDeriv_div z (hneg z hz) (hnef z hz)
        (hg z (sphere_subset_closedBall hz)).differentiableAt
        (hf z (sphere_subset_closedBall hz)).differentiableAt
    have h0 := circleIntegral_logDeriv_div_eq_zero hR hf hg hs
    rw [circleIntegral.integral_congr hR.le heq,
      circleIntegral.integral_sub (circleIntegrable_logDeriv hR hg hneg)
        (circleIntegrable_logDeriv hR hf hnef)] at h0
    linear_combination h0
  rw [_root_.Complex.circleIntegral_logDeriv_eq_finsum_analyticOrderNatAdd hg hneg hR.le,
    _root_.Complex.circleIntegral_logDeriv_eq_finsum_analyticOrderNatAdd hf hnef hR.le] at hsplit
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hsum : ((∑ᶠ z ∈ ball c R, analyticOrderNatAt g z : ℕ) : ℂ) =
      ((∑ᶠ z ∈ ball c R, analyticOrderNatAt f z : ℕ) : ℂ) :=
    mul_left_cancel₀ hpi hsplit
  exact_mod_cast hsum.symm

/-- Classical asymmetric Rouché theorem on a disc. -/
theorem rouche (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hs : ∀ z ∈ sphere c R, ‖f z - g z‖ < ‖f z‖) :
    (∑ᶠ z ∈ ball c R, analyticOrderNatAt f z) =
      ∑ᶠ z ∈ ball c R, analyticOrderNatAt g z :=
  rouche_symm hR hf hg fun z hz ↦
    (hs z hz).trans_le (le_add_of_nonneg_right (norm_nonneg _))

end

end DiskRigidity.Complex
