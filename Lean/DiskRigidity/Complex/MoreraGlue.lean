/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib.Analysis.Complex.HasPrimitives

/-!
# Morera gluing across a line

A continuous function on a disk which is holomorphic away from the real
diameter is holomorphic on the whole disk.  This is the precise gluing form
of Morera's theorem used after flattening a real-analytic boundary arc.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Metric Set Topology
open scoped Interval

namespace DiskRigidity.Complex

/-- Morera gluing across the real axis: continuity fills the line omitted
from the holomorphy hypothesis. -/
theorem differentiableOn_ball_of_continuousOn_of_differentiableAt_off_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {F : ℂ → E} {c : ℂ} {r : ℝ}
    (hFcont : ContinuousOn F (ball c r))
    (hFdiff : ∀ z ∈ ball c r, z.im ≠ 0 → DifferentiableAt ℂ F z) :
    DifferentiableOn ℂ F (ball c r) := by
  rw [← Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn
    isOpen_ball]
  refine ⟨?_, hFcont⟩
  intro z w hrect
  rw [← add_eq_zero_iff_eq_neg,
    Complex.wedgeIntegral_add_wedgeIntegral_eq]
  by_cases hcross : (0 : ℝ) ∈
      Ioo (min z.im w.im) (max z.im w.im)
  · let z₀ : ℂ := z.re
    let w₀ : ℂ := w.re
    have hzero : (0 : ℝ) ∈ [[z.im, w.im]] :=
      ⟨hcross.1.le, hcross.2.le⟩
    have hmem (a b : ℝ) (ha : a ∈ [[z.re, w.re]])
        (hb : b ∈ [[z.im, w.im]]) :
        (a : ℂ) + b * Complex.I ∈ ball c r := by
      apply hrect
      change (a : ℂ) + b * Complex.I ∈
        [[z.re, w.re]] ×ℂ [[z.im, w.im]]
      rw [Complex.mem_reProdIm]
      simpa using ⟨ha, hb⟩
    have hz : z ∈ ball c r := by
      simpa only [Complex.re_add_im] using
        hmem z.re z.im left_mem_uIcc left_mem_uIcc
    have hw : w ∈ ball c r := by
      simpa only [Complex.re_add_im] using
        hmem w.re w.im right_mem_uIcc right_mem_uIcc
    have hz₀ : z₀ ∈ ball c r := by
      simpa [z₀] using hmem z.re 0 left_mem_uIcc hzero
    have hw₀ : w₀ ∈ ball c r := by
      simpa [w₀] using hmem w.re 0 right_mem_uIcc hzero
    have hzw₀ : z.re + w₀.im * Complex.I ∈ ball c r := by
      simpa [w₀] using hmem z.re 0 left_mem_uIcc hzero
    have hw₀z : w₀.re + z.im * Complex.I ∈ ball c r := by
      simpa [w₀] using hmem w.re z.im right_mem_uIcc left_mem_uIcc
    have hrectLower : Complex.Rectangle z w₀ ⊆ ball c r :=
      (show Convex ℝ (ball c r) from convex_ball c r).rectangle_subset
        hz hw₀ hzw₀ hw₀z
    have hz₀w : z₀.re + w.im * Complex.I ∈ ball c r := by
      simpa [z₀] using hmem z.re w.im left_mem_uIcc right_mem_uIcc
    have hwz₀ : w.re + z₀.im * Complex.I ∈ ball c r := by
      simpa [z₀] using hmem w.re 0 right_mem_uIcc hzero
    have hrectUpper : Complex.Rectangle z₀ w ⊆ ball c r :=
      (show Convex ℝ (ball c r) from convex_ball c r).rectangle_subset
        hz₀ hw hz₀w hwz₀
    have hlower :=
      Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
        F z w₀ (hFcont.mono hrectLower) (by
          intro q hq
          have hqBall : q ∈ ball c r := by
            apply hrectLower
            exact ⟨Ioo_subset_Icc_self hq.1, Ioo_subset_Icc_self hq.2⟩
          have hqIm : q.im ≠ 0 := by
            intro hqzero
            have him := hq.2
            change q.im ∈ Ioo (min z.im w₀.im) (max z.im w₀.im) at him
            rw [hqzero] at him
            rcases le_total z.im 0 with hzle | hzeroLe
            · simp [w₀, min_eq_left hzle, max_eq_right hzle] at him
            · simp [w₀, min_eq_right hzeroLe, max_eq_left hzeroLe] at him
          exact (hFdiff q hqBall hqIm).differentiableWithinAt)
    have hupper :=
      Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
        F z₀ w (hFcont.mono hrectUpper) (by
          intro q hq
          have hqBall : q ∈ ball c r := by
            apply hrectUpper
            exact ⟨Ioo_subset_Icc_self hq.1, Ioo_subset_Icc_self hq.2⟩
          have hqIm : q.im ≠ 0 := by
            intro hqzero
            have him := hq.2
            change q.im ∈ Ioo (min z₀.im w.im) (max z₀.im w.im) at him
            rw [hqzero] at him
            rcases le_total w.im 0 with hwle | hzeroLe
            · simp [z₀, min_eq_right hwle, max_eq_left hwle] at him
            · simp [z₀, min_eq_left hzeroLe, max_eq_right hzeroLe] at him
          exact (hFdiff q hqBall hqIm).differentiableWithinAt)
    have hright : IntervalIntegrable
        (fun y : ℝ ↦ F (w.re + y * Complex.I)) volume z.im w.im :=
      ((hFcont.mono hrect).comp (by fun_prop) (by
        intro y hy
        change (w.re : ℂ) + y * Complex.I ∈
          [[z.re, w.re]] ×ℂ [[z.im, w.im]]
        rw [Complex.mem_reProdIm]
        constructor
        · simp
        · simpa using hy)).intervalIntegrable
    have hleft : IntervalIntegrable
        (fun y : ℝ ↦ F (z.re + y * Complex.I)) volume z.im w.im :=
      ((hFcont.mono hrect).comp (by fun_prop) (by
        intro y hy
        change (z.re : ℂ) + y * Complex.I ∈
          [[z.re, w.re]] ×ℂ [[z.im, w.im]]
        rw [Complex.mem_reProdIm]
        constructor
        · simp
        · simpa using hy)).intervalIntegrable
    have hrightSplit :
        (∫ y : ℝ in z.im..w.im, F (w.re + y * Complex.I)) =
          (∫ y : ℝ in z.im..0, F (w.re + y * Complex.I)) +
          ∫ y : ℝ in 0..w.im, F (w.re + y * Complex.I) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hright.mono_set (uIcc_subset_uIcc left_mem_uIcc hzero))
        (hright.mono_set (uIcc_subset_uIcc hzero right_mem_uIcc))).symm
    have hleftSplit :
        (∫ y : ℝ in z.im..w.im, F (z.re + y * Complex.I)) =
          (∫ y : ℝ in z.im..0, F (z.re + y * Complex.I)) +
          ∫ y : ℝ in 0..w.im, F (z.re + y * Complex.I) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hleft.mono_set (uIcc_subset_uIcc left_mem_uIcc hzero))
        (hleft.mono_set (uIcc_subset_uIcc hzero right_mem_uIcc))).symm
    have hsum := congrArg₂ (fun a b : E ↦ a + b) hlower hupper
    simp only [zero_add] at hsum
    dsimp only [z₀, w₀] at hlower hupper hsum ⊢
    simp only [Complex.ofReal_re, Complex.ofReal_im] at hlower hupper hsum ⊢
    rw [hrightSplit, hleftSplit]
    convert hsum using 1
    all_goals module
  · exact
      Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
        F z w (hFcont.mono hrect) (by
          intro q hq
          have hqBall : q ∈ ball c r := by
            apply hrect
            exact ⟨Ioo_subset_Icc_self hq.1, Ioo_subset_Icc_self hq.2⟩
          have hqIm : q.im ≠ 0 := by
            intro hqzero
            apply hcross
            have him := hq.2
            change q.im ∈ Ioo (min z.im w.im) (max z.im w.im) at him
            simpa only [hqzero] using him
          exact (hFdiff q hqBall hqIm).differentiableWithinAt)

end DiskRigidity.Complex
