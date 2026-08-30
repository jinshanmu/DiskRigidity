/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.FoundationUnitary
public import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# The support function of a numerical range

This file proves Lemma 2.1(5).  We define the largest eigenvalue by the
maximum Rayleigh quotient; finite-dimensional spectral theory proves that
this value is an eigenvalue, and the numerical-range definition identifies
the same supremum with the support function.
-/

noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator

@[expose] public section

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The largest Rayleigh value of a Hermitian matrix. -/
def largestEigenvalue (H : SquareMatrix n) : ℝ :=
  ⨆ x : {x : EuclideanVector n // x ≠ 0},
    (euclideanOperator H).rayleighQuotient x

/-- The support value of the numerical range in complex direction `c`. -/
def numericalRangeSupport (A : SquareMatrix n) (c : ℂ) : ℝ :=
  ⨆ z : numericalRange A, (c * (z : ℂ)).re

/-- The real part of a quadratic form is the quadratic form of its Hermitian
real part. -/
theorem reApplyInnerSelf_rePart (B : SquareMatrix n)
    (x : EuclideanVector n) :
    (euclideanOperator (rePart B)).reApplyInnerSelf x =
      (⟪x, euclideanOperator B x⟫_ℂ).re := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  simp only [rePart, map_smul, map_add, euclideanOperator_conjTranspose,
    smul_apply, add_apply, inner_add_left, inner_smul_left,
    Complex.conj_inv, Complex.conj_ofNat,
    ContinuousLinearMap.adjoint_inner_left]
  have hre : (⟪euclideanOperator B x, x⟫_ℂ).re =
      (⟪x, euclideanOperator B x⟫_ℂ).re := by
    rw [← inner_conj_symm (𝕜 := ℂ) (euclideanOperator B x) x]
    exact Complex.conj_re _
  norm_num [Complex.add_re, Complex.mul_re, Complex.inv_re,
    Complex.inv_im, hre]
  ring

/-- On a unit vector, the support functional is the Rayleigh quotient of the
rotated Hermitian part. -/
theorem supportForm_eq_rayleighQuotient
    (A : SquareMatrix n) (c : ℂ) (x : EuclideanVector n)
    (hx : ‖x‖ = 1) :
    (c * ⟪x, euclideanOperator A x⟫_ℂ).re =
      (euclideanOperator (rePart (c • A))).rayleighQuotient x := by
  rw [ContinuousLinearMap.rayleighQuotient,
    reApplyInnerSelf_rePart, map_smul, smul_apply,
    inner_smul_right, hx]
  norm_num

/-- Rayleigh quotients are bounded above by the operator norm. -/
theorem bddAbove_rayleighRange (H : SquareMatrix n) :
    BddAbove (Set.range fun x : {x : EuclideanVector n // x ≠ 0} ↦
      (euclideanOperator H).rayleighQuotient x) := by
  refine ⟨‖euclideanOperator H‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact le_trans (le_abs_self _)
    ((euclideanOperator H).rayleighQuotient_le_norm x)

/-- The numerical support values form a bounded family. -/
theorem bddAbove_numericalRangeSupportRange
    (A : SquareMatrix n) (c : ℂ) :
    BddAbove (Set.range fun z : numericalRange A ↦ (c * (z : ℂ)).re) := by
  refine ⟨‖c‖ * ‖A‖, ?_⟩
  rintro _ ⟨z, rfl⟩
  calc
    (c * (z : ℂ)).re ≤ ‖c * (z : ℂ)‖ := Complex.re_le_norm _
    _ = ‖c‖ * ‖(z : ℂ)‖ := norm_mul c z
    _ ≤ ‖c‖ * ‖A‖ := by
      gcongr
      exact norm_le_of_mem_numericalRange A z.property

/-- The support function is the largest eigenvalue of the rotated Hermitian
part, i.e. Lemma 2.1(5) before writing `c = exp(-iθ)`. -/
theorem numericalRangeSupport_eq_largestEigenvalue [Nonempty n]
    (A : SquareMatrix n) (c : ℂ) :
    numericalRangeSupport A c = largestEigenvalue (rePart (c • A)) := by
  let _ : Nonempty (numericalRange A) :=
    Set.nonempty_coe_sort.mpr (numericalRange_nonempty A)
  obtain ⟨xzero, hxzero⟩ : ∃ x : EuclideanVector n, x ≠ 0 := exists_ne 0
  let _ : Nonempty {x : EuclideanVector n // x ≠ 0} :=
    ⟨⟨xzero, hxzero⟩⟩
  apply le_antisymm
  · rw [numericalRangeSupport]
    apply ciSup_le
    intro z
    obtain ⟨x, hx, hz⟩ := z.property
    rw [← hz, supportForm_eq_rayleighQuotient A c x hx]
    have hx0 : x ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hx
      exact zero_ne_one hx
    exact le_ciSup (bddAbove_rayleighRange (rePart (c • A))) ⟨x, hx0⟩
  · rw [largestEigenvalue]
    apply ciSup_le
    rintro ⟨x, hx0⟩
    let u : EuclideanVector n := (‖x‖⁻¹ : ℂ) • x
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hx0
    have hc0 : (‖x‖⁻¹ : ℂ) ≠ 0 := by
      exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr hx0)
    rw [← (euclideanOperator (rePart (c • A))).rayleigh_smul x hc0]
    change (euclideanOperator (rePart (c • A))).rayleighQuotient u ≤ _
    rw [← supportForm_eq_rayleighQuotient A c u hu]
    exact le_ciSup (bddAbove_numericalRangeSupportRange A c)
      ⟨⟪u, euclideanOperator A u⟫_ℂ, ⟨u, hu, rfl⟩⟩

/-- For a Hermitian matrix, `largestEigenvalue` really is an eigenvalue. -/
theorem largestEigenvalue_hasEigenvalue [Nonempty n]
    (H : SquareMatrix n) (hH : H.IsHermitian) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin H)
      (largestEigenvalue H : ℂ) := by
  have hsym : (Matrix.toEuclideanLin H).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  rw [largestEigenvalue]
  change Module.End.HasEigenvalue (Matrix.toEuclideanLin H)
    ((⨆ x : {x : EuclideanVector n // x ≠ 0},
      RCLike.re ⟪Matrix.toEuclideanLin H x, x⟫_ℂ / ‖(x : EuclideanVector n)‖ ^ 2 : ℝ) : ℂ)
  exact hsym.hasEigenvalue_iSup_of_finiteDimensional

/-- The support-function formula in the angular notation of the manuscript. -/
theorem numericalRangeSupport_exp_eq_largestEigenvalue [Nonempty n]
    (A : SquareMatrix n) (theta : ℝ) :
    numericalRangeSupport A
        (Complex.exp (-(theta : ℂ) * Complex.I)) =
      largestEigenvalue
        (rePart (Complex.exp (-(theta : ℂ) * Complex.I) • A)) :=
  numericalRangeSupport_eq_largestEigenvalue A _

end DiskRigidity.Operator
