/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Fundamental theorem of calculus for Banach-valued Lipschitz curves

Mathlib's absolutely-continuous fundamental theorem is stated for real-valued
functions.  Hahn--Banach separation upgrades it to Banach-valued Lipschitz
curves.  This is the form needed for rectifiable convex-boundary integrals.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped NNReal

namespace DiskRigidity.Operator

/-- The derivative of a Banach-valued globally Lipschitz curve is interval
integrable on every compact interval. -/
theorem intervalIntegrable_deriv_of_lipschitzWith
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {f : ℝ → E} {C : ℝ≥0} (hf : LipschitzWith C f) (a b : ℝ) :
    IntervalIntegrable (deriv f) volume a b := by
  rw [intervalIntegrable_iff]
  let _ : IsFiniteMeasure (volume.restrict (uIoc a b)) :=
    ⟨by simp [Real.volume_uIoc]⟩
  apply Integrable.of_bound (measurable_deriv f).aestronglyMeasurable (C : ℝ)
  exact Filter.Eventually.of_forall fun x ↦ norm_deriv_le_of_lipschitz hf

/-- Fundamental theorem of calculus for a Banach-valued Lipschitz curve.
The proof applies the real-valued absolutely-continuous theorem to every
continuous linear functional and then uses Hahn--Banach separation. -/
theorem intervalIntegral_deriv_eq_sub_of_lipschitzWith
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E]
    {f : ℝ → E} {C : ℝ≥0} (hf : LipschitzWith C f) (a b : ℝ) :
    ∫ x in a..b, deriv f x = f b - f a := by
  have hderivInt := intervalIntegrable_deriv_of_lipschitzWith hf a b
  apply sub_eq_zero.mp
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
  intro L
  rw [map_sub, map_sub, ← L.intervalIntegral_comp_comm hderivInt]
  have hLfLip : LipschitzWith (‖L‖₊ * C) (L ∘ f) :=
    L.lipschitz.comp hf
  have hLfAC : AbsolutelyContinuousOnInterval (L ∘ f) a b :=
    hLfLip.lipschitzOnWith.absolutelyContinuousOnInterval
  change (∫ x in a..b, L (deriv f x)) -
    ((L ∘ f) b - (L ∘ f) a) = 0
  rw [← hLfAC.integral_deriv_eq_sub]
  rw [sub_eq_zero]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hf.ae_differentiableAt_real] with x hx _
  exact ((L.hasFDerivAt.comp_hasDerivAt x hx.hasDerivAt).deriv).symm

end DiskRigidity.Operator
