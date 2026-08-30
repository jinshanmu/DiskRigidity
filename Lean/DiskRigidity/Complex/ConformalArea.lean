/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Area of the image of a holomorphic injection

This file records the conformal area formula needed by the convex-domain
boundary argument.  It is the complex one-dimensional specialization of
Mathlib's real change-of-variables theorem.

The proof follows the corresponding argument in Tau Ceti's
`Analysis.Complex.Conformal.Area` module (Apache-2.0).
-/

open Bornology MeasureTheory Metric Set
open scoped ENNReal

namespace DiskRigidity.Complex

public section

variable {U s : Set ℂ} {f : ℂ → ℂ}

private theorem det_restrictScalars_smulRight_one (c : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
  have h : ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c =
      ContinuousLinearMap.toSpanSingleton ℂ c := by
    ext
    simp [ContinuousLinearMap.toSpanSingleton]
  simp [h, ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq,
    Complex.normSq_eq_norm_sq]

private theorem hasFDerivWithinAt_smulRight_deriv (hUo : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hsU : s ⊆ U) {z : ℂ} (hz : z ∈ s) :
    HasFDerivWithinAt f
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f z)).restrictScalars ℝ) s z :=
  (((hf z (hsU hz)).differentiableAt
      (hUo.mem_nhds (hsU hz))).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt

private theorem ofReal_abs_det_eq (c : ℂ) :
    ENNReal.ofReal
        |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det| =
      ‖c‖ₑ ^ 2 := by
  rw [det_restrictScalars_smulRight_one, abs_of_nonneg (by positivity), ← ofReal_norm,
    ENNReal.ofReal_pow (norm_nonneg _)]

/-- The area formula for a holomorphic injection. -/
theorem volume_image_eq_lintegral_enorm_deriv_sq (hUo : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hs : NullMeasurableSet s volume) (hsU : s ⊆ U)
    (hinj : InjOn f s) :
    volume (f '' s) = ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2 := by
  rw [← MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image₀ volume hs
    (fun z hz ↦ hasFDerivWithinAt_smulRight_deriv hUo hf hsU hz) hinj]
  exact lintegral_congr fun z ↦ ofReal_abs_det_eq (deriv f z)

/-- A holomorphic injection with bounded image has finite Dirichlet integral. -/
theorem lintegral_enorm_deriv_sq_ne_top_of_isBounded (hUo : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hs : NullMeasurableSet s volume) (hsU : s ⊆ U)
    (hinj : InjOn f s) (hb : Bornology.IsBounded (f '' s)) :
    ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2 ≠ ∞ := by
  rw [← volume_image_eq_lintegral_enorm_deriv_sq hUo hf hs hsU hinj]
  exact hb.measure_lt_top.ne

end

end DiskRigidity.Complex
