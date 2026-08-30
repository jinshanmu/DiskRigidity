/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.BoundarySpectrum
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Data.Finset.Max
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Topology.Order.OrderClosed

/-!
# Corners and polygonal numerical ranges

Two linearly independent supporting directions at a numerical-range point
force the realizing vector to be a common eigenvector of the matrix and its
adjoint.  A finite convex hull always has such a corner, obtained by choosing
a generic real-linear functional and perturbing it slightly.  Consequently a
finite matrix whose spectrum lies in the interior of its numerical range
cannot have a polygonal numerical range.
-/

noncomputable section

open Filter Function Metric Set
open scoped ComplexConjugate ComplexOrder InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Complex

@[expose] public section

/-- A convenient one-parameter family of real support directions. -/
def affineSupportDirection (t : ℝ) : ℂ := ⟨1, t⟩

/-- The associated real-linear support functional. -/
def affineSupportValue (t : ℝ) (z : ℂ) : ℝ :=
  (affineSupportDirection t * z).re

theorem affineSupportValue_apply (t : ℝ) (z : ℂ) :
    affineSupportValue t z = z.re - t * z.im := by
  simp [affineSupportValue, affineSupportDirection, Complex.mul_re]

private theorem isLinearMap_affineSupportValue (t : ℝ) :
    IsLinearMap ℝ (affineSupportValue t) where
  map_add x y := by simp [affineSupportValue_apply]; ring
  map_smul r x := by simp [affineSupportValue_apply, Complex.real_smul]; ring

/-- A point has a genuine planar corner if it admits two real-linearly
independent supporting complex directions. -/
def IsTwoSidedSupportCorner (K : Set ℂ) (lambda : ℂ) : Prop :=
  ∃ c₁ c₂ : ℂ,
    c₁ * conj c₂ ≠ c₂ * conj c₁ ∧
    (∀ z ∈ K, (c₁ * z).re ≤ (c₁ * lambda).re) ∧
    ∀ z ∈ K, (c₂ * z).re ≤ (c₂ * lambda).re

/-- A polygonal set is the convex hull of a finite family of points. -/
def IsPolygon (K : Set ℂ) : Prop :=
  ∃ s : Finset ℂ, K = convexHull ℝ (s : Set ℂ)

private theorem injective_affineSupportValue_on_finset
    (s : Finset ℂ) :
    ∃ t : ℝ, Set.InjOn (affineSupportValue t) (s : Set ℂ) := by
  let bad : Finset ℝ := (s ×ˢ s).image fun p ↦
    (p.1 - p.2).re / (p.1 - p.2).im
  obtain ⟨t, ht⟩ := bad.exists_notMem
  refine ⟨t, ?_⟩
  intro z hz w hw hzw
  by_contra hne
  have him : (z - w).im ≠ 0 := by
    intro himzero
    have himEq : z.im = w.im := by
      simpa only [Complex.sub_im, sub_eq_zero] using himzero
    apply hne
    apply Complex.ext
    · rw [affineSupportValue_apply, affineSupportValue_apply] at hzw
      rw [himEq] at hzw
      linarith
    · exact himEq
  apply ht
  apply Finset.mem_image.mpr
  refine ⟨(z, w), Finset.mem_product.mpr ⟨hz, hw⟩, ?_⟩
  rw [affineSupportValue_apply, affineSupportValue_apply] at hzw
  simp only [Complex.sub_re, Complex.sub_im]
  rw [div_eq_iff (by simpa only [Complex.sub_im] using him)]
  linarith [hzw]

private theorem affineSupportDirection_independent {t u : ℝ} (htu : t ≠ u) :
    affineSupportDirection t * conj (affineSupportDirection u) ≠
      affineSupportDirection u * conj (affineSupportDirection t) := by
  intro h
  have him := congrArg Complex.im h
  simp [affineSupportDirection, Complex.mul_im] at him
  exact htu (by linarith)

/-- Every nonempty finite convex hull has a point with two independent
supporting directions. -/
theorem exists_twoSidedSupportCorner_convexHull_finset
    {s : Finset ℂ} (hs : s.Nonempty) :
    ∃ lambda ∈ (s : Set ℂ),
      IsTwoSidedSupportCorner (convexHull ℝ (s : Set ℂ)) lambda := by
  obtain ⟨t, htinj⟩ := injective_affineSupportValue_on_finset s
  obtain ⟨lambda, hlambda, hmax⟩ := s.exists_max_image (affineSupportValue t) hs
  have hstrict {z : ℂ} (hz : z ∈ s) (hzlambda : z ≠ lambda) :
      affineSupportValue t z < affineSupportValue t lambda := by
    exact lt_of_le_of_ne (hmax z hz) fun heq ↦
      hzlambda (htinj hz hlambda heq)
  have hevent : ∀ᶠ u in nhds t, ∀ z ∈ s,
      affineSupportValue u z ≤ affineSupportValue u lambda := by
    rw [Finset.eventually_all]
    intro z hz
    by_cases hzl : z = lambda
    · subst z
      exact Eventually.of_forall fun _ ↦ le_rfl
    · have hcontz : ContinuousAt (fun u ↦ affineSupportValue u z) t := by
        simp only [affineSupportValue_apply]
        fun_prop
      have hcontl : ContinuousAt (fun u ↦ affineSupportValue u lambda) t := by
        simp only [affineSupportValue_apply]
        fun_prop
      exact (hcontz.eventually_lt hcontl (hstrict hz hzl)).mono fun _ h ↦ h.le
  obtain ⟨u, htu, huall⟩ :=
    ((frequently_gt_nhds t).and_eventually hevent).exists
  have hsupport (q : ℝ)
      (hq : ∀ z ∈ s, affineSupportValue q z ≤ affineSupportValue q lambda) :
      ∀ z ∈ convexHull ℝ (s : Set ℂ),
        (affineSupportDirection q * z).re ≤
          (affineSupportDirection q * lambda).re := by
    have hsub : (s : Set ℂ) ⊆
        {z | affineSupportValue q z ≤ affineSupportValue q lambda} := hq
    have hconv : Convex ℝ
        {z | affineSupportValue q z ≤ affineSupportValue q lambda} :=
      convex_halfSpace_le (isLinearMap_affineSupportValue q) _
    exact convexHull_min hsub hconv
  refine ⟨lambda, hlambda, affineSupportDirection t, affineSupportDirection u,
    affineSupportDirection_independent (ne_of_lt htu), ?_, ?_⟩
  · exact hsupport t hmax
  · exact hsupport u huall

namespace NumericalRangeCorner

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem rePart_smul_mulVec_eq_of_support
    (A : Operator.SquareMatrix n) (x : Operator.EuclideanVector n)
    (hxnorm : ‖x‖ = 1) {lambda c : ℂ}
    (hlambda : ⟪x, Operator.euclideanOperator A x⟫_ℂ = lambda)
    (hsupport : ∀ z ∈ Operator.numericalRange A,
      (c * z).re ≤ (c * lambda).re) :
    Operator.rePart (c • A) *ᵥ WithLp.ofLp x =
      ((c * lambda).re : ℂ) • WithLp.ofLp x := by
  let alpha : ℝ := (c * lambda).re
  let P : Operator.SquareMatrix n :=
    ((alpha : ℂ) • (1 : Operator.SquareMatrix n)) - Operator.rePart (c • A)
  have hPpos : P.PosSemidef := by
    exact Operator.supportDefect_posSemidef A c alpha fun z hz ↦ by
      simpa only [alpha] using hsupport z hz
  let v : n → ℂ := WithLp.ofLp x
  have hvunit : star v ⬝ᵥ v = 1 := by
    have hxinner : ⟪x, x⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hxnorm]
      norm_num
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hxinner
    simpa only [v, dotProduct_comm] using hxinner
  have hqA : star v ⬝ᵥ (A *ᵥ v) = lambda := by
    rw [← Operator.inner_euclideanOperator_eq_star_dotProduct A x]
    exact hlambda
  have hqP : star v ⬝ᵥ (P *ᵥ v) = 0 := by
    rw [show P = ((alpha : ℂ) • (1 : Operator.SquareMatrix n)) -
      Operator.rePart (c • A) by rfl]
    rw [Operator.quadratic_supportDefect_of_unit A c alpha v hvunit, hqA]
    simp [alpha]
  have hPv : P *ᵥ v = 0 :=
    (hPpos.dotProduct_mulVec_zero_iff v).mp hqP
  have hzero : (alpha : ℂ) • v - Operator.rePart (c • A) *ᵥ v = 0 := by
    simpa only [P, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec] using hPv
  exact (sub_eq_zero.mp hzero).symm

/-- Two independent supporting directions force the realizing vector to be
a reducing eigenvector. -/
theorem mulVec_eq_and_conjTranspose_mulVec_eq_of_two_supports
    (A : Operator.SquareMatrix n) (x : Operator.EuclideanVector n)
    (hxnorm : ‖x‖ = 1) {lambda c₁ c₂ : ℂ}
    (hlambda : ⟪x, Operator.euclideanOperator A x⟫_ℂ = lambda)
    (hind : c₁ * conj c₂ ≠ c₂ * conj c₁)
    (hsupport₁ : ∀ z ∈ Operator.numericalRange A,
      (c₁ * z).re ≤ (c₁ * lambda).re)
    (hsupport₂ : ∀ z ∈ Operator.numericalRange A,
      (c₂ * z).re ≤ (c₂ * lambda).re) :
    A *ᵥ WithLp.ofLp x = lambda • WithLp.ofLp x ∧
      Aᴴ *ᵥ WithLp.ofLp x = conj lambda • WithLp.ofLp x := by
  let v : n → ℂ := WithLp.ofLp x
  have hre₁ := rePart_smul_mulVec_eq_of_support A x hxnorm hlambda hsupport₁
  have hre₂ := rePart_smul_mulVec_eq_of_support A x hxnorm hlambda hsupport₂
  have hreal (c : ℂ) : (2 : ℂ) * ((c * lambda).re : ℂ) =
      c * lambda + conj c * conj lambda := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have heq (c : ℂ)
      (hre : Operator.rePart (c • A) *ᵥ v = ((c * lambda).re : ℂ) • v) (i : n) :
      c * ((A *ᵥ v) i - lambda * v i) +
        conj c * ((Aᴴ *ᵥ v) i - conj lambda * v i) = 0 := by
    have hrei := congrFun hre i
    rw [Operator.rePart, Matrix.smul_mulVec, Matrix.add_mulVec,
      Matrix.conjTranspose_smul] at hrei
    simp only [Matrix.smul_mulVec] at hrei
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hrei
    change 2⁻¹ * (c * (A *ᵥ v) i + conj c * (Aᴴ *ᵥ v) i) =
      ((c * lambda).re : ℂ) * v i at hrei
    have hsum : c * (A *ᵥ v) i + conj c * (Aᴴ *ᵥ v) i =
        2 * (((c * lambda).re : ℂ) * v i) := by
      calc
        c * (A *ᵥ v) i + conj c * (Aᴴ *ᵥ v) i =
            2 * (2⁻¹ * (c * (A *ᵥ v) i + conj c * (Aᴴ *ᵥ v) i)) := by ring
        _ = 2 * (((c * lambda).re : ℂ) * v i) := by rw [hrei]
    calc
      c * ((A *ᵥ v) i - lambda * v i) +
          conj c * ((Aᴴ *ᵥ v) i - conj lambda * v i) =
          (c * (A *ᵥ v) i + conj c * (Aᴴ *ᵥ v) i) -
            (c * lambda + conj c * conj lambda) * v i := by ring
      _ = 2 * (((c * lambda).re : ℂ) * v i) -
            (c * lambda + conj c * conj lambda) * v i := by rw [hsum]
      _ = 2 * (((c * lambda).re : ℂ) * v i) -
            (2 * ((c * lambda).re : ℂ)) * v i := by rw [hreal c]
      _ = 0 := by ring
  constructor
  · funext i
    have h₁ := heq c₁ hre₁ i
    have h₂ := heq c₂ hre₂ i
    have hprod : (c₁ * conj c₂ - c₂ * conj c₁) *
        ((A *ᵥ v) i - lambda * v i) = 0 := by
      linear_combination (conj c₂) * h₁ - (conj c₁) * h₂
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hind))
  · funext i
    have h₁ := heq c₁ hre₁ i
    have h₂ := heq c₂ hre₂ i
    have hprod : (conj c₁ * c₂ - conj c₂ * c₁) *
        ((Aᴴ *ᵥ v) i - conj lambda * v i) = 0 := by
      linear_combination c₂ * h₁ - c₁ * h₂
    have hcoef : conj c₁ * c₂ - conj c₂ * c₁ ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      apply hind
      calc
        c₁ * conj c₂ = conj c₂ * c₁ := mul_comm _ _
        _ = conj c₁ * c₂ := h.symm
        _ = c₂ * conj c₁ := mul_comm _ _
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hcoef)

/-- Every two-sided corner of a numerical range belongs to the matrix
spectrum. -/
theorem mem_spectrum_of_mem_numericalRange_of_twoSidedSupportCorner
    (A : Operator.SquareMatrix n) {lambda : ℂ}
    (hlambda : lambda ∈ Operator.numericalRange A)
    (hcorner : IsTwoSidedSupportCorner (Operator.numericalRange A) lambda) :
    lambda ∈ spectrum ℂ A := by
  obtain ⟨x, hxnorm, hxvalue⟩ := hlambda
  obtain ⟨c₁, c₂, hind, hs₁, hs₂⟩ := hcorner
  have hAx := (mulVec_eq_and_conjTranspose_mulVec_eq_of_two_supports
    A x hxnorm hxvalue hind hs₁ hs₂).1
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  change A.charpoly.eval lambda = 0
  rw [Matrix.eval_charpoly]
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨WithLp.ofLp x, ?_, ?_⟩
  · intro hxzero
    have : x = 0 := by
      apply WithLp.ofLp_injective
      exact hxzero
    rw [this, norm_zero] at hxnorm
    exact zero_ne_one hxnorm
  · have hscalar : Matrix.scalar n lambda *ᵥ WithLp.ofLp x =
        lambda • WithLp.ofLp x := by
      simp [Matrix.scalar_apply]
    rw [Matrix.sub_mulVec, hscalar, hAx]
    simp

private theorem not_mem_interior_of_support {K : Set ℂ} {lambda c : ℂ}
    (hc : c ≠ 0) (hsupport : ∀ z ∈ K, (c * z).re ≤ (c * lambda).re) :
    lambda ∉ interior K := by
  intro hlambda
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior lambda hlambda
  let w : ℂ := lambda + (ε / (2 * ‖c‖)) • conj c
  have hcnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hr : 0 < ε / (2 * ‖c‖) := div_pos hε (mul_pos (by norm_num) hcnorm)
  have hwball : w ∈ ball lambda ε := by
    rw [mem_ball, dist_self_add_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hε (by positivity)), Complex.norm_conj]
    field_simp
    linarith
  have hs := hsupport w (interior_subset (hball hwball))
  have hpos : 0 <
      (c * (((ε / (2 * ‖c‖) : ℝ) : ℂ) * conj c)).re := by
    rw [← mul_assoc]
    rw [show c * ((ε / (2 * ‖c‖) : ℝ) : ℂ) =
      ((ε / (2 * ‖c‖) : ℝ) : ℂ) * c by ring]
    rw [mul_assoc]
    rw [Complex.mul_conj]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos hr (Complex.normSq_pos.mpr hc)
  dsimp [w] at hs
  simp only [mul_add, Complex.add_re] at hs
  nlinarith

/-- Under interior spectrum, the numerical range has no two-sided support
corner. -/
theorem not_isTwoSidedSupportCorner_of_spectrum_subset_interior
    (A : Operator.SquareMatrix n) (hspec : spectrum ℂ A ⊆
      interior (Operator.numericalRange A)) {lambda : ℂ}
    (hlambda : lambda ∈ Operator.numericalRange A) :
    ¬ IsTwoSidedSupportCorner (Operator.numericalRange A) lambda := by
  intro hcorner
  have hspectrum :=
    mem_spectrum_of_mem_numericalRange_of_twoSidedSupportCorner A hlambda hcorner
  obtain ⟨c₁, c₂, hind, hs₁, -⟩ := hcorner
  have hc₁ : c₁ ≠ 0 := by
    intro h
    subst c₁
    simp at hind
  exact not_mem_interior_of_support hc₁ hs₁
    (hspec hspectrum)

/-- The polygon-exclusion assertion in Lemma 5.1: if the spectrum lies in
the interior of the numerical range, that numerical range is not a polygon. -/
theorem numericalRange_not_isPolygon_of_spectrum_subset_interior
    [Nonempty n] (A : Operator.SquareMatrix n)
    (hspec : spectrum ℂ A ⊆ interior (Operator.numericalRange A)) :
    ¬ IsPolygon (Operator.numericalRange A) := by
  rintro ⟨s, hs⟩
  have hsne : s.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hs
    have hne := Operator.numericalRange_nonempty A
    exact hne.ne_empty (by simpa only [Finset.coe_empty, convexHull_empty] using hs)
  obtain ⟨lambda, hlambdaS, hcorner⟩ :=
    exists_twoSidedSupportCorner_convexHull_finset hsne
  have hlambda : lambda ∈ Operator.numericalRange A := by
    rw [hs]
    exact subset_convexHull ℝ _ hlambdaS
  apply not_isTwoSidedSupportCorner_of_spectrum_subset_interior A hspec hlambda
  rwa [hs]

end NumericalRangeCorner

end

end DiskRigidity.Complex
