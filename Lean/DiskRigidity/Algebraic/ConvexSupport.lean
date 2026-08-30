/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib

/-!
# The two support offsets in a fixed direction

For a compact planar body and a nonzero normal, there are exactly two
supporting lines with that unoriented normal: the maximum and minimum of the
corresponding linear functional.  This file proves the statement directly,
including distinctness from nonempty interior.  No smoothness or strict
convexity is needed for the count of support *lines*.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace ConvexSupport

open Matrix Metric Set

/-- A point of the real affine plane. -/
abbrev Point := Fin 2 → ℝ

/-- The linear functional with normal `n`. -/
def linearValue (n x : Point) : ℝ := n ⬝ᵥ x

/-- `s` is the offset of an upper supporting line with normal `n`. -/
def IsUpperSupportOffset (K : Set Point) (n : Point) (s : ℝ) : Prop :=
  ∃ x ∈ K, linearValue n x = s ∧ ∀ y ∈ K, linearValue n y ≤ s

/-- `s` is the offset of a lower supporting line with normal `n`. -/
def IsLowerSupportOffset (K : Set Point) (n : Point) (s : ℝ) : Prop :=
  ∃ x ∈ K, linearValue n x = s ∧ ∀ y ∈ K, s ≤ linearValue n y

/-- A supporting line for the unoriented normal `[n]`. -/
def IsSupportOffset (K : Set Point) (n : Point) (s : ℝ) : Prop :=
  IsUpperSupportOffset K n s ∨ IsLowerSupportOffset K n s

theorem continuous_linearValue (n : Point) : Continuous (linearValue n) := by
  unfold linearValue dotProduct
  fun_prop

theorem exists_upperSupportOffset {K : Set Point}
    (hK : IsCompact K) (hne : K.Nonempty) (n : Point) :
    ∃ s, IsUpperSupportOffset K n s := by
  obtain ⟨x, hxK, hx⟩ := hK.exists_isMaxOn hne (continuous_linearValue n).continuousOn
  refine ⟨linearValue n x, x, hxK, rfl, ?_⟩
  intro y hy
  exact hx hy

theorem exists_lowerSupportOffset {K : Set Point}
    (hK : IsCompact K) (hne : K.Nonempty) (n : Point) :
    ∃ s, IsLowerSupportOffset K n s := by
  obtain ⟨x, hxK, hx⟩ := hK.exists_isMinOn hne (continuous_linearValue n).continuousOn
  refine ⟨linearValue n x, x, hxK, rfl, ?_⟩
  intro y hy
  exact hx hy

theorem upperSupportOffset_unique {K : Set Point} {n : Point} {s t : ℝ}
    (hs : IsUpperSupportOffset K n s) (ht : IsUpperSupportOffset K n t) :
    s = t := by
  rcases hs with ⟨x, hxK, rfl, hx⟩
  rcases ht with ⟨y, hyK, rfl, hy⟩
  exact le_antisymm (hy x hxK) (hx y hyK)

theorem lowerSupportOffset_unique {K : Set Point} {n : Point} {s t : ℝ}
    (hs : IsLowerSupportOffset K n s) (ht : IsLowerSupportOffset K n t) :
    s = t := by
  rcases hs with ⟨x, hxK, rfl, hx⟩
  rcases ht with ⟨y, hyK, rfl, hy⟩
  exact le_antisymm (hx y hyK) (hy x hxK)

/-- Nonempty interior gives positive width in every nonzero direction. -/
theorem exists_points_linearValue_ne {K : Set Point}
    (hK : (interior K).Nonempty) {n : Point} (hn : n ≠ 0) :
    ∃ x ∈ K, ∃ y ∈ K, linearValue n x ≠ linearValue n y := by
  obtain ⟨x, hx⟩ := hK
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp hx)
  have hnNorm : 0 < ‖n‖ := norm_pos_iff.mpr hn
  let c : ℝ := ε / (2 * ‖n‖)
  let y : Point := x + c • n
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hyball : y ∈ ball x ε := by
    rw [mem_ball, dist_eq_norm]
    dsimp [y]
    rw [add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hc]
    dsimp [c]
    field_simp
    nlinarith
  have hxK : x ∈ K := interior_subset hx
  have hyK : y ∈ K := hball hyball
  refine ⟨x, hxK, y, hyK, ?_⟩
  have hnn : 0 < n ⬝ᵥ n :=
    (Matrix.dotProduct_self_star_pos_iff (v := n)).mpr hn
  have hchange : linearValue n y = linearValue n x + c * (n ⬝ᵥ n) := by
    simp [linearValue, y, dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [hchange]
  exact ne_of_lt (lt_add_of_pos_right _ (mul_pos hc hnn))

theorem upper_ne_lower_of_interior {K : Set Point} {n : Point} {s t : ℝ}
    (hK : (interior K).Nonempty) (hn : n ≠ 0)
    (hs : IsUpperSupportOffset K n s) (ht : IsLowerSupportOffset K n t) :
    s ≠ t := by
  obtain ⟨x, hxK, y, hyK, hxy⟩ := exists_points_linearValue_ne hK hn
  rcases hs with ⟨xmax, hxmaxK, _hxmax, hmax⟩
  rcases ht with ⟨xmin, hxminK, _hxmin, hmin⟩
  intro hst
  have hxconst : linearValue n x = s := by
    apply le_antisymm (hmax x hxK)
    rw [hst]
    exact hmin x hxK
  have hyconst : linearValue n y = s := by
    apply le_antisymm (hmax y hyK)
    rw [hst]
    exact hmin y hyK
  exact hxy (hxconst.trans hyconst.symm)

/-- Exact support-line classification for a fixed unoriented normal. -/
theorem supportOffset_iff_eq_two {K : Set Point}
    (hcompact : IsCompact K) (hinterior : (interior K).Nonempty)
    {n : Point} (hn : n ≠ 0) :
    ∃ smin smax : ℝ,
      smin ≠ smax ∧
      ∀ s : ℝ, IsSupportOffset K n s ↔ s = smin ∨ s = smax := by
  have hne : K.Nonempty := hinterior.mono interior_subset
  obtain ⟨smax, hsmax⟩ := exists_upperSupportOffset hcompact hne n
  obtain ⟨smin, hsmin⟩ := exists_lowerSupportOffset hcompact hne n
  refine ⟨smin, smax, (upper_ne_lower_of_interior hinterior hn hsmax hsmin).symm,
    fun s ↦ ?_⟩
  constructor
  · rintro (hs | hs)
    · exact Or.inr (upperSupportOffset_unique hs hsmax)
    · exact Or.inl (lowerSupportOffset_unique hs hsmin)
  · rintro (rfl | rfl)
    · exact Or.inr hsmin
    · exact Or.inl hsmax

/-- A nonzero linear functional cannot attain an upper bound of a set at an
interior point. -/
theorem linearValue_lt_of_mem_interior_of_upper_bound
    {K : Set Point} {n x : Point} {r : ℝ}
    (hx : x ∈ interior K) (hn : n ≠ 0)
    (hbound : ∀ y ∈ K, linearValue n y ≤ r)
    (hxr : linearValue n x = r) : False := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp hx)
  have hnNorm : 0 < ‖n‖ := norm_pos_iff.mpr hn
  let c : ℝ := ε / (2 * ‖n‖)
  let y : Point := x + c • n
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hyball : y ∈ ball x ε := by
    rw [mem_ball, dist_eq_norm]
    dsimp [y]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    dsimp [c]
    field_simp
    nlinarith
  have hnn : 0 < n ⬝ᵥ n :=
    (Matrix.dotProduct_self_star_pos_iff (v := n)).mpr hn
  have hvalue : linearValue n y = linearValue n x + c * (n ⬝ᵥ n) := by
    simp [linearValue, y, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have := hbound y (hball hyball)
  rw [hvalue, hxr] at this
  nlinarith

/-- A nonzero linear functional cannot attain a lower bound of a set at an
interior point. -/
theorem linearValue_gt_of_mem_interior_of_lower_bound
    {K : Set Point} {n x : Point} {r : ℝ}
    (hx : x ∈ interior K) (hn : n ≠ 0)
    (hbound : ∀ y ∈ K, r ≤ linearValue n y)
    (hxr : linearValue n x = r) : False := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp hx)
  have hnNorm : 0 < ‖n‖ := norm_pos_iff.mpr hn
  let c : ℝ := ε / (2 * ‖n‖)
  let y : Point := x - c • n
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hyball : y ∈ ball x ε := by
    rw [mem_ball, dist_eq_norm]
    dsimp [y]
    rw [show x - c • n - x = -(c • n) by abel, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos hc]
    dsimp [c]
    field_simp
    nlinarith
  have hnn : 0 < n ⬝ᵥ n :=
    (Matrix.dotProduct_self_star_pos_iff (v := n)).mpr hn
  have hvalue : linearValue n y = linearValue n x - c * (n ⬝ᵥ n) := by
    simp [linearValue, y, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have := hbound y (hball hyball)
  rw [hvalue, hxr] at this
  nlinarith

/-- A supporting line of a strictly convex set meets the set in at most one
point. -/
theorem eq_of_mem_support_of_strictConvex
    {K : Set Point} (hstrict : StrictConvex ℝ K)
    {n : Point} (hn : n ≠ 0) {r : ℝ}
    (hsupport : IsSupportOffset K n r)
    {x y : Point} (hx : x ∈ K) (hy : y ∈ K)
    (hxline : linearValue n x = r) (hyline : linearValue n y = r) :
    x = y := by
  by_contra hxy
  let m : Point := (2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • y
  have hm : m ∈ interior K := by
    apply hstrict hx hy hxy
    · norm_num
    · norm_num
    · norm_num
  have hmline : linearValue n m = r := by
    calc
      linearValue n m = (2 : ℝ)⁻¹ * linearValue n x +
          (2 : ℝ)⁻¹ * linearValue n y := by
        simp [m, linearValue, dotProduct_add, dotProduct_smul, smul_eq_mul]
      _ = r := by rw [hxline, hyline]; ring
  rcases hsupport with hupper | hlower
  · obtain ⟨_, _, _, hbound⟩ := hupper
    exact linearValue_lt_of_mem_interior_of_upper_bound hm hn hbound hmline
  · obtain ⟨_, _, _, hbound⟩ := hlower
    exact linearValue_gt_of_mem_interior_of_lower_bound hm hn hbound hmline

/-- Rescaling a projective line by a nonzero real scalar preserves the
unoriented support-line property.  A negative scalar exchanges upper and
lower support. -/
theorem isSupportOffset_smul
    {K : Set Point} {n : Point} {r c : ℝ}
    (hsupport : IsSupportOffset K n r) (hc : c ≠ 0) :
    IsSupportOffset K (c • n) (c * r) := by
  have hvalue (x : Point) : linearValue (c • n) x = c * linearValue n x := by
    simp only [linearValue, dotProduct, Fin.sum_univ_two, Pi.smul_apply,
      smul_eq_mul]
    ring
  rcases hsupport with hupper | hlower
  · obtain ⟨x, hx, hxr, hbound⟩ := hupper
    rcases lt_or_gt_of_ne hc with hcneg | hcpos
    · right
      refine ⟨x, hx, ?_, ?_⟩
      · rw [hvalue, hxr]
      · intro y hy
        rw [hvalue]
        exact mul_le_mul_of_nonpos_left (hbound y hy) hcneg.le
    · left
      refine ⟨x, hx, ?_, ?_⟩
      · rw [hvalue, hxr]
      · intro y hy
        rw [hvalue]
        exact mul_le_mul_of_nonneg_left (hbound y hy) hcpos.le
  · obtain ⟨x, hx, hxr, hbound⟩ := hlower
    rcases lt_or_gt_of_ne hc with hcneg | hcpos
    · left
      refine ⟨x, hx, ?_, ?_⟩
      · rw [hvalue, hxr]
      · intro y hy
        rw [hvalue]
        exact mul_le_mul_of_nonpos_left (hbound y hy) hcneg.le
    · right
      refine ⟨x, hx, ?_, ?_⟩
      · rw [hvalue, hxr]
      · intro y hy
        rw [hvalue]
        exact mul_le_mul_of_nonneg_left (hbound y hy) hcpos.le

end ConvexSupport

end DiskRigidity.Algebraic
