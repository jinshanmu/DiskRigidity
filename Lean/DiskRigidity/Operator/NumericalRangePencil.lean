/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.HermitianProjective
public import DiskRigidity.Algebraic.ConvexSupport
public import DiskRigidity.Operator.AlgebraicCircleToDisk
public import DiskRigidity.Operator.FoundationSupport
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The Hermitian pencil of a numerical range

This file formalizes the last matrix-geometric input to Proposition 7.1.
Every supporting line of the numerical range gives a singular member of the
Hermitian Kippenhahn pencil.
-/

@[expose] public section

noncomputable section

open Set
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

/-- The Hermitian matrix representing the real coordinate of the numerical
range. -/
def numericalRangeRealPart {n : Type*} (A : SquareMatrix n) : SquareMatrix n :=
  rePart A

/-- The Hermitian matrix representing the imaginary coordinate of the
numerical range. -/
def numericalRangeImaginaryPart {n : Type*} (A : SquareMatrix n) : SquareMatrix n :=
  rePart ((-Complex.I) • A)

theorem rePart_isHermitian {n : Type*} (A : SquareMatrix n) :
    (rePart A).IsHermitian := by
  change (rePart A)ᴴ = rePart A
  simp [rePart, add_comm]

theorem numericalRangeRealPart_isHermitian {n : Type*} (A : SquareMatrix n) :
    (numericalRangeRealPart A).IsHermitian :=
  rePart_isHermitian A

theorem numericalRangeImaginaryPart_isHermitian {n : Type*} (A : SquareMatrix n) :
    (numericalRangeImaginaryPart A).IsHermitian :=
  rePart_isHermitian _

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The quadratic form of the Hermitian pencil is the corresponding real
linear functional on the numerical value. -/
theorem reApplyInnerSelf_numericalRangePencil
    (A : SquareMatrix n) (u v : ℝ) (x : EuclideanVector n) :
    (euclideanOperator
      ((u : ℂ) • numericalRangeRealPart A +
        (v : ℂ) • numericalRangeImaginaryPart A)).reApplyInnerSelf x =
      u * (⟪x, euclideanOperator A x⟫_ℂ).re +
        v * (⟪x, euclideanOperator A x⟫_ℂ).im := by
  calc
    _ = u * (euclideanOperator (rePart A)).reApplyInnerSelf x +
        v * (euclideanOperator (rePart ((-Complex.I) • A))).reApplyInnerSelf x := by
      simp only [numericalRangeRealPart, numericalRangeImaginaryPart,
        map_add, map_smul, add_apply, smul_apply,
        ContinuousLinearMap.reApplyInnerSelf_apply, inner_add_left,
        inner_smul_left, Complex.conj_ofReal]
      simp
    _ = _ := by
      rw [reApplyInnerSelf_rePart, reApplyInnerSelf_rePart]
      simp only [map_smul, smul_apply, inner_smul_right]
      simp [Complex.mul_re]

/-- A supporting value is an eigenvalue of the corresponding Hermitian
pencil. -/
theorem exists_unit_eigenvector_of_numericalRange_supportOffset
    (A : SquareMatrix n) {normal : Fin 2 → ℝ} {r : ℝ}
    (hsupport : Algebraic.ConvexSupport.IsSupportOffset
      (complexPointHomeomorph '' numericalRange A) normal r) :
    ∃ x : EuclideanVector n, ‖x‖ = 1 ∧
      euclideanOperator
        ((normal 0 : ℂ) • numericalRangeRealPart A +
          (normal 1 : ℂ) • numericalRangeImaginaryPart A) x =
        (r : ℂ) • x := by
  let L : SquareMatrix n :=
    (normal 0 : ℂ) • numericalRangeRealPart A +
      (normal 1 : ℂ) • numericalRangeImaginaryPart A
  have hL : L.IsHermitian :=
    (numericalRangeRealPart_isHermitian A).smul (by
      simp [isSelfAdjoint_iff])
      |>.add ((numericalRangeImaginaryPart_isHermitian A).smul (by
        simp [isSelfAdjoint_iff]))
  have hself : IsSelfAdjoint (euclideanOperator L) := by
    rw [isSelfAdjoint_iff]
    exact (map_star euclideanOperator L).symm.trans
      (congrArg euclideanOperator hL)
  rcases hsupport with hupper | hlower
  · obtain ⟨q, hqK, hqr, hbound⟩ := hupper
    obtain ⟨z, hzW, hzq⟩ := hqK
    obtain ⟨x, hx, hzx⟩ := hzW
    have hx0 : x ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hx
      exact zero_ne_one hx
    have hform (w : EuclideanVector n) :
        (euclideanOperator L).reApplyInnerSelf w =
          normal 0 * (⟪w, euclideanOperator A w⟫_ℂ).re +
            normal 1 * (⟪w, euclideanOperator A w⟫_ℂ).im := by
      exact reApplyInnerSelf_numericalRangePencil A _ _ w
    have hxvalue : (euclideanOperator L).reApplyInnerSelf x = r := by
      rw [hform]
      have := hqr
      rw [← hzq] at this
      rw [hzx]
      simpa [Algebraic.ConvexSupport.linearValue, dotProduct,
        Fin.sum_univ_two] using this
    have hmax : IsMaxOn (euclideanOperator L).reApplyInnerSelf
        (Metric.sphere 0 ‖x‖) x := by
      intro w hw
      have hwnorm : ‖w‖ = 1 := by simpa [hx] using hw
      change (euclideanOperator L).reApplyInnerSelf w ≤
        (euclideanOperator L).reApplyInnerSelf x
      rw [hxvalue, hform]
      have hb := hbound (complexPointHomeomorph
        ⟪w, euclideanOperator A w⟫_ℂ)
        ⟨_, ⟨w, hwnorm, rfl⟩, rfl⟩
      simpa [Algebraic.ConvexSupport.linearValue, dotProduct,
        Fin.sum_univ_two] using hb
    have heigen := hself.eq_smul_self_of_isLocalExtrOn (Or.inr hmax.localize)
    have hrayleigh : (euclideanOperator L).rayleighQuotient x = r := by
      rw [ContinuousLinearMap.rayleighQuotient, hxvalue, hx]
      norm_num
    have hrayleigh' :
        ((euclideanOperator L).rayleighQuotient x : ℂ) = (r : ℂ) := by
      exact_mod_cast hrayleigh
    refine ⟨x, hx, ?_⟩
    simpa [L] using heigen.trans
      (congrArg (fun a : ℂ ↦ a • x) hrayleigh')
  · obtain ⟨q, hqK, hqr, hbound⟩ := hlower
    obtain ⟨z, hzW, hzq⟩ := hqK
    obtain ⟨x, hx, hzx⟩ := hzW
    have hx0 : x ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hx
      exact zero_ne_one hx
    have hform (w : EuclideanVector n) :
        (euclideanOperator L).reApplyInnerSelf w =
          normal 0 * (⟪w, euclideanOperator A w⟫_ℂ).re +
            normal 1 * (⟪w, euclideanOperator A w⟫_ℂ).im := by
      exact reApplyInnerSelf_numericalRangePencil A _ _ w
    have hxvalue : (euclideanOperator L).reApplyInnerSelf x = r := by
      rw [hform]
      have := hqr
      rw [← hzq] at this
      rw [hzx]
      simpa [Algebraic.ConvexSupport.linearValue, dotProduct,
        Fin.sum_univ_two] using this
    have hmin : IsMinOn (euclideanOperator L).reApplyInnerSelf
        (Metric.sphere 0 ‖x‖) x := by
      intro w hw
      have hwnorm : ‖w‖ = 1 := by simpa [hx] using hw
      change (euclideanOperator L).reApplyInnerSelf x ≤
        (euclideanOperator L).reApplyInnerSelf w
      rw [hxvalue, hform]
      have hb := hbound (complexPointHomeomorph
        ⟪w, euclideanOperator A w⟫_ℂ)
        ⟨_, ⟨w, hwnorm, rfl⟩, rfl⟩
      simpa [Algebraic.ConvexSupport.linearValue, dotProduct,
        Fin.sum_univ_two] using hb
    have heigen := hself.eq_smul_self_of_isLocalExtrOn (Or.inl hmin.localize)
    have hrayleigh : (euclideanOperator L).rayleighQuotient x = r := by
      rw [ContinuousLinearMap.rayleighQuotient, hxvalue, hx]
      norm_num
    have hrayleigh' :
        ((euclideanOperator L).rayleighQuotient x : ℂ) = (r : ℂ) := by
      exact_mod_cast hrayleigh
    refine ⟨x, hx, ?_⟩
    simpa [L] using heigen.trans
      (congrArg (fun a : ℂ ↦ a • x) hrayleigh')

/-- Every support line of the numerical range lies on its projective
Hermitian determinant curve. -/
theorem determinantPolynomial_zero_of_numericalRange_supportOffset
    (A : SquareMatrix n) {normal : Fin 2 → ℝ} {r : ℝ}
    (hsupport : Algebraic.ConvexSupport.IsSupportOffset
      (complexPointHomeomorph '' numericalRange A) normal r) :
    MvPolynomial.eval ![-(r : ℂ), (normal 0 : ℂ), (normal 1 : ℂ)]
      (Algebraic.HermitianProjective.determinantPolynomial
        (numericalRangeRealPart A) (numericalRangeImaginaryPart A)) = 0 := by
  obtain ⟨x, hx, heigen⟩ :=
    exists_unit_eigenvector_of_numericalRange_supportOffset A hsupport
  rw [Algebraic.HermitianProjective.eval_determinantPolynomial]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue]
  change (Matrix.scalar n (-(r : ℂ)) +
    (normal 0 : ℂ) • numericalRangeRealPart A +
    (normal 1 : ℂ) • numericalRangeImaginaryPart A).det = 0
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨x.ofLp, ?_, ?_⟩
  · intro hzero
    have hxzero : x = 0 := by
      apply WithLp.ofLp_injective 2
      simpa using hzero
    rw [hxzero, norm_zero] at hx
    exact zero_ne_one hx
  · rw [← Matrix.ofLp_toEuclideanCLM]
    have hop : euclideanOperator
        (Matrix.scalar n (-(r : ℂ)) +
          (normal 0 : ℂ) • numericalRangeRealPart A +
          (normal 1 : ℂ) • numericalRangeImaginaryPart A) x = 0 := by
      rw [show Matrix.scalar n (-(r : ℂ)) =
          -(r : ℂ) • (1 : SquareMatrix n) by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [Matrix.scalar_apply]
        · simp [Matrix.scalar_apply, hij]]
      simp only [map_add, map_smul, map_one, add_apply, smul_apply,
        one_apply_eq_self]
      have hdir :
          (normal 0 : ℂ) • euclideanOperator (numericalRangeRealPart A) x +
            (normal 1 : ℂ) • euclideanOperator (numericalRangeImaginaryPart A) x =
          (r : ℂ) • x := by
        simpa only [map_add, map_smul, add_apply, smul_apply] using heigen
      rw [add_assoc, hdir]
      simp
    have hopen := congrArg WithLp.ofLp hop
    simp only [map_add, map_smul, add_apply, smul_apply,
      euclideanOperator] at hopen
    simpa [Matrix.smul_mulVec] using hopen

end DiskRigidity.Operator
