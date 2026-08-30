/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Analysis.FullLevel
public import DiskRigidity.Operator.FoundationSymmetries
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Line segments in rational lemniscates

This file formalizes the final strict-convexity argument in Proposition 6.3:
if a rational lemniscate contains a nontrivial real line segment, its defining
real polynomial vanishes on the entire line.
-/

@[expose] public section

noncomputable section

open Complex Polynomial Set
open scoped ComplexConjugate

namespace DiskRigidity.Analysis

/-- The complex polynomial in the real line parameter whose values are
`|U|^2 - |V|^2`. -/
def lineLevelPolynomial (U V : ℂ[X]) (z₀ xi : ℂ) : ℂ[X] :=
  let line := C z₀ + C xi * X
  let reflectedLine := C (star z₀) + C (star xi) * X
  U.comp line * (Operator.conjugatePolynomial U).comp reflectedLine -
    V.comp line * (Operator.conjugatePolynomial V).comp reflectedLine

/-- Evaluation of the line polynomial at a real parameter is the squared
modulus difference. -/
theorem lineLevelPolynomial_eval_real (U V : ℂ[X]) (z₀ xi : ℂ) (t : ℝ) :
    (lineLevelPolynomial U V z₀ xi).eval (t : ℂ) =
      (Complex.normSq (U.eval (z₀ + (t : ℂ) * xi)) : ℂ) -
        (Complex.normSq (V.eval (z₀ + (t : ℂ) * xi)) : ℂ) := by
  simp only [lineLevelPolynomial, eval_sub, eval_mul, eval_comp, eval_add,
    eval_C, eval_X, Operator.conjugatePolynomial_eval]
  have hstar :
      (starRingEnd ℂ) (star z₀ + star xi * (t : ℂ)) =
        z₀ + (t : ℂ) * xi := by
    simp [mul_comm]
  rw [hstar]
  have hline : z₀ + xi * (t : ℂ) = z₀ + (t : ℂ) * xi := by ring
  rw [hline]
  change
    U.eval (z₀ + (t : ℂ) * xi) *
          conj (U.eval (z₀ + (t : ℂ) * xi)) -
        V.eval (z₀ + (t : ℂ) * xi) *
          conj (V.eval (z₀ + (t : ℂ) * xi)) = _
  rw [Complex.mul_conj, Complex.mul_conj]

/-- Equality of the two moduli is equivalent to vanishing of the line
polynomial at a real parameter. -/
theorem lineLevelPolynomial_eval_real_eq_zero_iff
    (U V : ℂ[X]) (z₀ xi : ℂ) (t : ℝ) :
    (lineLevelPolynomial U V z₀ xi).eval (t : ℂ) = 0 ↔
      ‖U.eval (z₀ + (t : ℂ) * xi)‖ =
        ‖V.eval (z₀ + (t : ℂ) * xi)‖ := by
  rw [lineLevelPolynomial_eval_real]
  norm_cast
  rw [sub_eq_zero, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  exact sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)

/-- Vanishing on one nondegenerate real interval forces the rational
lemniscate equation to hold on the whole real line. -/
theorem norm_eval_eq_on_real_line_of_eq_on_Icc
    (U V : ℂ[X]) (z₀ xi : ℂ) {a b : ℝ} (hab : a < b)
    (hsegment : ∀ t ∈ Icc a b,
      ‖U.eval (z₀ + (t : ℂ) * xi)‖ =
        ‖V.eval (z₀ + (t : ℂ) * xi)‖) :
    ∀ t : ℝ, ‖U.eval (z₀ + (t : ℂ) * xi)‖ =
      ‖V.eval (z₀ + (t : ℂ) * xi)‖ := by
  let P := lineLevelPolynomial U V z₀ xi
  have hroots : ((fun t : ℝ ↦ (t : ℂ)) '' Icc a b) ⊆
      {z : ℂ | P.IsRoot z} := by
    rintro z ⟨t, ht, rfl⟩
    exact (lineLevelPolynomial_eval_real_eq_zero_iff U V z₀ xi t).2
      (hsegment t ht)
  have hinfinite : Set.Infinite {z : ℂ | P.IsRoot z} := by
    apply Set.Infinite.mono hroots
    exact (Set.Icc_infinite hab).image Complex.ofReal_injective.injOn
  have hP : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P hinfinite
  intro t
  apply (lineLevelPolynomial_eval_real_eq_zero_iff U V z₀ xi t).1
  change P.eval (t : ℂ) = 0
  rw [hP, eval_zero]

/-- A reduced rational full level of a compact set contains no nontrivial
real line segment.  This is the strict-convexity step of Proposition 6.3 in
the exact parametrized form used in the manuscript. -/
theorem no_nontrivial_real_segment_in_rationalLevel
    {K : Set ℂ} (hKcompact : IsCompact K) (U V : ℂ[X])
    (hcoprime : IsCoprime U V)
    (hfull : rationalLevel U V = frontier K)
    {z₀ xi : ℂ} (hxi : xi ≠ 0) {a b : ℝ} (hab : a < b) :
    ¬ ∀ t ∈ Icc a b,
      z₀ + (t : ℂ) * xi ∈ rationalLevel U V := by
  intro hsegment
  have hnormSegment : ∀ t ∈ Icc a b,
      ‖U.eval (z₀ + (t : ℂ) * xi)‖ =
        ‖V.eval (z₀ + (t : ℂ) * xi)‖ := by
    intro t ht
    have htLevel := hsegment t ht
    rw [rationalLevel] at htLevel
    have hquot := htLevel.2
    rw [norm_div] at hquot
    exact (div_eq_one_iff_eq (norm_ne_zero_iff.mpr htLevel.1)).mp hquot
  have hnorm : ∀ t : ℝ,
      ‖U.eval (z₀ + (t : ℂ) * xi)‖ =
        ‖V.eval (z₀ + (t : ℂ) * xi)‖ :=
    norm_eval_eq_on_real_line_of_eq_on_Icc U V z₀ xi hab hnormSegment
  have hdenominator : ∀ t : ℝ,
      V.eval (z₀ + (t : ℂ) * xi) ≠ 0 := by
    intro t hV
    have hU : U.eval (z₀ + (t : ℂ) * xi) = 0 := by
      apply norm_eq_zero.mp
      rw [hnorm t, hV, norm_zero]
    rcases Polynomial.aeval_ne_zero_of_isCoprime hcoprime
      (z₀ + (t : ℂ) * xi) with hUne | hVne
    · exact hUne hU
    · exact hVne hV
  have hlineLevel : ∀ t : ℝ,
      z₀ + (t : ℂ) * xi ∈ rationalLevel U V := by
    intro t
    refine ⟨hdenominator t, ?_⟩
    rw [norm_div, hnorm t]
    exact div_self (norm_ne_zero_iff.mpr (hdenominator t))
  have hlineK : ∀ t : ℝ, z₀ + (t : ℂ) * xi ∈ K := by
    intro t
    have hfrontier : z₀ + (t : ℂ) * xi ∈ frontier K := by
      rw [← hfull]
      exact hlineLevel t
    rw [← hKcompact.isClosed.closure_eq]
    exact frontier_subset_closure hfrontier
  obtain ⟨R, hKR⟩ := hKcompact.isBounded.subset_ball (0 : ℂ)
  have hxiNorm : 0 < ‖xi‖ := norm_pos_iff.mpr hxi
  let t : ℝ := (|R| + ‖z₀‖ + 1) / ‖xi‖
  let z := z₀ + (t : ℂ) * xi
  have htNonneg : 0 ≤ t := by
    dsimp only [t]
    positivity
  have htzNorm : ‖(t : ℂ) * xi‖ = |R| + ‖z₀‖ + 1 := by
    rw [norm_mul]
    have htNorm : ‖(t : ℂ)‖ = t := by
      simp [abs_of_nonneg htNonneg]
    rw [htNorm]
    dsimp only [t]
    exact div_mul_cancel₀ _ hxiNorm.ne'
  have hzBound : ‖z‖ < R := by
    have hzBall := hKR (hlineK t)
    simpa [z, Metric.mem_ball, dist_zero_right] using hzBall
  have htriangle : ‖(t : ℂ) * xi‖ ≤ ‖z₀‖ + ‖z‖ := by
    calc
      ‖(t : ℂ) * xi‖ = ‖-z₀ + z‖ := by
        congr 1
        simp [z]
      _ ≤ ‖-z₀‖ + ‖z‖ := norm_add_le _ _
      _ = ‖z₀‖ + ‖z‖ := by rw [norm_neg]
  rw [htzNorm] at htriangle
  have hRle : R ≤ |R| := le_abs_self R
  linarith

/-- A compact convex set whose whole frontier is a reduced rational level is
strictly convex.  This packages the strict-convexity conclusion of
Proposition 6.3 directly from its full-level identity. -/
theorem strictConvex_of_full_rationalLevel
    {K : Set ℂ} (hKcompact : IsCompact K) (hKconvex : Convex ℝ K)
    (U V : ℂ[X]) (hcoprime : IsCoprime U V)
    (hfull : rationalLevel U V = frontier K) :
    StrictConvex ℝ K := by
  apply hKconvex.strictConvex
  rintro x ⟨hxK, hxNotInterior⟩ y ⟨hyK, hyNotInterior⟩ hxy
  have hxFrontier : x ∈ frontier K :=
    (mem_frontier_iff_notMem_interior hxK).2 hxNotInterior
  have hyFrontier : y ∈ frontier K :=
    (mem_frontier_iff_notMem_interior hyK).2 hyNotInterior
  by_contra hempty
  have hsegment : segment ℝ x y ⊆ frontier K := by
    intro z hz
    by_contra hzFrontier
    exact hempty ⟨z, hz, hzFrontier⟩
  refine no_nontrivial_real_segment_in_rationalLevel
    hKcompact U V hcoprime hfull (z₀ := x) (xi := y - x)
      (sub_ne_zero.mpr hxy.symm)
      (show (0 : ℝ) < 1 by norm_num) ?_
  intro t ht
  rw [hfull]
  apply hsegment
  have hline : x + (t : ℂ) * (y - x) = AffineMap.lineMap x y t := by
    simp [AffineMap.lineMap_apply, Complex.real_smul]
    ring
  rw [hline]
  exact lineMap_mem_segment ℝ x y ht

end DiskRigidity.Analysis
