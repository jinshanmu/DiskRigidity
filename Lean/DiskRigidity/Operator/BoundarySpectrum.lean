/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.NumericalRangeConvexity
public import DiskRigidity.Operator.FoundationGeometry
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Matrix.Order

/-!
# Boundary eigenvalues of a numerical range

This file formalizes the supporting-line argument in Lemma 3.4 of the
manuscript: an eigenvector whose eigenvalue lies on the boundary of the
numerical range is automatically a reducing vector.
-/

noncomputable section

open WithLp
open scoped ComplexOrder InnerProductSpace Matrix Matrix.Norms.L2Operator

@[expose] public section

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Coordinate form of the Euclidean quadratic form. -/
theorem inner_euclideanOperator_eq_star_dotProduct
    (A : SquareMatrix n) (x : EuclideanVector n) :
    ⟪x, euclideanOperator A x⟫_ℂ =
      star (ofLp x) ⬝ᵥ (A *ᵥ ofLp x) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (A *ᵥ ofLp x) ⬝ᵥ star (ofLp x) =
    star (ofLp x) ⬝ᵥ (A *ᵥ ofLp x)
  exact dotProduct_comm _ _

/-- A boundary point of a convex set with nonempty interior admits a nonzero
complex supporting functional. -/
theorem exists_nonzero_complex_support
    {K : Set ℂ} (hK : Convex ℝ K) (hKint : (interior K).Nonempty)
    {z : ℂ} (hz : z ∉ interior K) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ w ∈ K, (c * w).re ≤ (c * z).re := by
  obtain ⟨f, hf, hsupport⟩ :=
    RCLike.geometric_hahn_banach_of_nonempty_interior_point
      (𝕜 := ℂ) hK hz hKint
  have hf_apply (w : ℂ) : f w = w * f 1 := by
    simpa only [smul_eq_mul, mul_one] using f.map_smul w (1 : ℂ)
  have hf1 : f 1 ≠ 0 := by
    intro h
    apply hf
    apply ContinuousLinearMap.ext
    intro w
    rw [hf_apply, h, mul_zero, zero_apply]
  refine ⟨f 1, hf1, fun w hw ↦ ?_⟩
  calc
    ((f 1) * w).re = (f w).re := by rw [hf_apply w, mul_comm]
    _ ≤ (f z).re := hsupport w hw
    _ = ((f 1) * z).re := by rw [hf_apply z, mul_comm]

omit [DecidableEq n] in
/-- Conjugating a quadratic form is the quadratic form of the conjugate
transpose. -/
theorem star_quadratic_eq_conjTranspose (A : SquareMatrix n) (x : n → ℂ) :
    starRingEnd ℂ (star x ⬝ᵥ (A *ᵥ x)) =
      star x ⬝ᵥ (Aᴴ *ᵥ x) := by
  calc
    starRingEnd ℂ (star x ⬝ᵥ (A *ᵥ x)) =
        starRingEnd ℂ (star (star (A *ᵥ x) ⬝ᵥ x)) := by
      rw [Matrix.star_dotProduct]
    _ = star (A *ᵥ x) ⬝ᵥ x := by
      change star (star (star (A *ᵥ x) ⬝ᵥ x)) = _
      rw [star_star]
    _ = (star x ᵥ* Aᴴ) ⬝ᵥ x := by rw [Matrix.star_mulVec]
    _ = star x ⬝ᵥ (Aᴴ *ᵥ x) := by rw [Matrix.dotProduct_mulVec]

omit [DecidableEq n] in
/-- The quadratic form of the Hermitian real part is the real part of the
original quadratic form. -/
theorem quadratic_rePart (A : SquareMatrix n) (x : n → ℂ) :
    star x ⬝ᵥ (rePart A *ᵥ x) =
      ((star x ⬝ᵥ (A *ᵥ x)).re : ℂ) := by
  have h := star_quadratic_eq_conjTranspose A x
  simp only [rePart, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_add,
    dotProduct_smul]
  rw [← h]
  apply Complex.ext
  · simp
    ring
  · simp

/-- Quadratic form of the supporting half-plane defect, on a unit vector. -/
theorem quadratic_supportDefect_of_unit
    (A : SquareMatrix n) (c : ℂ) (alpha : ℝ) (x : n → ℂ)
    (hx : star x ⬝ᵥ x = 1) :
    star x ⬝ᵥ
        ((((alpha : ℂ) • (1 : SquareMatrix n)) - rePart (c • A)) *ᵥ x) =
      ((alpha - (c * (star x ⬝ᵥ (A *ᵥ x))).re : ℝ) : ℂ) := by
  rw [Matrix.sub_mulVec, dotProduct_sub, quadratic_rePart]
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    smul_eq_mul, hx, mul_one]
  norm_cast

/-- A scalar support inequality is equivalent to positive semidefiniteness of
the corresponding supporting half-plane matrix. -/
theorem supportDefect_posSemidef
    (A : SquareMatrix n) (c : ℂ) (alpha : ℝ)
    (hsupport : ∀ w ∈ numericalRange A, (c * w).re ≤ alpha) :
    (((alpha : ℂ) • (1 : SquareMatrix n)) - rePart (c • A)).PosSemidef := by
  let P : SquareMatrix n :=
    ((alpha : ℂ) • (1 : SquareMatrix n)) - rePart (c • A)
  have hP : P.IsHermitian := by
    simp [P, rePart, Matrix.IsHermitian, add_comm]
  rw [show ((alpha : ℂ) • (1 : SquareMatrix n)) - rePart (c • A) = P by rfl]
  rw [hP.posSemidef_iff_eigenvalues_nonneg]
  intro i
  let e : EuclideanVector n := hP.eigenvectorBasis i
  let x : n → ℂ := ofLp e
  have he_norm : ‖e‖ = 1 := hP.eigenvectorBasis.orthonormal.1 i
  have hx_unit : star x ⬝ᵥ x = 1 := by
    have he_inner : ⟪e, e⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, he_norm]
      norm_num
    rw [EuclideanSpace.inner_eq_star_dotProduct] at he_inner
    simpa only [x, dotProduct_comm] using he_inner
  let w : ℂ := ⟪e, euclideanOperator A e⟫_ℂ
  have hw : w ∈ numericalRange A := ⟨e, he_norm, rfl⟩
  have hs := hsupport w hw
  rw [hP.eigenvalues_eq i,
    quadratic_supportDefect_of_unit A c alpha x hx_unit]
  change 0 ≤ alpha - (c * (star x ⬝ᵥ (A *ᵥ x))).re
  rw [← inner_euclideanOperator_eq_star_dotProduct A e]
  exact sub_nonneg.mpr hs

/-- The supporting-line proof of the first assertion of Lemma 3.4 when the
numerical range has nonempty interior.  The assumption-free manuscript
interface is `conjTranspose_mulVec_eq_of_unit_eigenvector_mem_frontier`. -/
theorem conjTranspose_mulVec_eq_of_eigenvalue_mem_frontier
    (A : SquareMatrix n) {lambda : ℂ} (x : EuclideanVector n)
    (hxnorm : ‖x‖ = 1)
    (hAx : A *ᵥ ofLp x = lambda • ofLp x)
    (hInt : (interior (numericalRange A)).Nonempty)
    (hlambda : lambda ∈ frontier (numericalRange A)) :
    Aᴴ *ᵥ ofLp x = star lambda • ofLp x := by
  have hclosed : IsClosed (numericalRange A) :=
    (isCompact_numericalRange A).isClosed
  have hlambda_mem : lambda ∈ numericalRange A := by
    rw [← hclosed.closure_eq]
    exact frontier_subset_closure hlambda
  have hlambda_notInt : lambda ∉ interior (numericalRange A) :=
    (mem_frontier_iff_notMem_interior hlambda_mem).mp hlambda
  obtain ⟨c, hc, hsupport⟩ :=
    exists_nonzero_complex_support (numericalRange_convex A) hInt hlambda_notInt
  let alpha : ℝ := (c * lambda).re
  let P : SquareMatrix n :=
    ((alpha : ℂ) • (1 : SquareMatrix n)) - rePart (c • A)
  have hPpos : P.PosSemidef := by
    exact supportDefect_posSemidef A c alpha fun w hw ↦ hsupport w hw
  let v : n → ℂ := ofLp x
  have hvunit : star v ⬝ᵥ v = 1 := by
    have hxinner : ⟪x, x⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hxnorm]
      norm_num
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hxinner
    simpa only [v, dotProduct_comm] using hxinner
  have hqA : star v ⬝ᵥ (A *ᵥ v) = lambda := by
    rw [show A *ᵥ v = lambda • v by exact hAx]
    simp only [dotProduct_smul, hvunit, smul_eq_mul, mul_one]
  have hqP : star v ⬝ᵥ (P *ᵥ v) = 0 := by
    rw [show P = ((alpha : ℂ) • (1 : SquareMatrix n)) - rePart (c • A) by rfl]
    rw [quadratic_supportDefect_of_unit A c alpha v hvunit, hqA]
    simp [alpha]
  have hPv : P *ᵥ v = 0 :=
    (hPpos.dotProduct_mulVec_zero_iff v).mp hqP
  have hreal : (2 : ℂ) * (alpha : ℂ) =
      c * lambda + star c * star lambda := by
    apply Complex.ext
    · simp [alpha, Complex.mul_re]
      ring
    · simp [alpha, Complex.mul_im]
      ring
  have hre : rePart (c • A) *ᵥ v = (alpha : ℂ) • v := by
    have hzero :
        (alpha : ℂ) • v - rePart (c • A) *ᵥ v = 0 := by
      simpa only [P, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec] using hPv
    exact (sub_eq_zero.mp hzero).symm
  funext i
  have hrei := congrFun hre i
  rw [rePart, Matrix.smul_mulVec, Matrix.add_mulVec,
    Matrix.conjTranspose_smul, Matrix.smul_mulVec, hAx] at hrei
  simp only [Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] at hrei
  change (Aᴴ *ᵥ v) i = star lambda * v i
  have hcstar : star c ≠ 0 := star_ne_zero.mpr hc
  apply (mul_left_cancel₀ hcstar)
  linear_combination 2 * hrei + hreal * v i

/-- Lemma 3.4, first assertion, with exactly the hypotheses in the
manuscript: a unit eigenvector at a numerical-range frontier eigenvalue is
also an eigenvector of the conjugate transpose.  No nonempty-interior
hypothesis is needed. -/
theorem conjTranspose_mulVec_eq_of_unit_eigenvector_mem_frontier
    [Nonempty n] (A : SquareMatrix n) {lambda : ℂ} (x : EuclideanVector n)
    (hxnorm : ‖x‖ = 1)
    (hAx : A *ᵥ ofLp x = lambda • ofLp x)
    (hlambda : lambda ∈ frontier (numericalRange A)) :
    Aᴴ *ᵥ ofLp x = star lambda • ofLp x := by
  by_cases hInt : (interior (numericalRange A)).Nonempty
  · exact conjTranspose_mulVec_eq_of_eigenvalue_mem_frontier
      A x hxnorm hAx hInt hlambda
  · have hline : IsContainedInAffineLine (numericalRange A) :=
      isContainedInAffineLine_of_convex_of_interior_not_nonempty
        (numericalRange_convex A) (numericalRange_nonempty A) hInt
    have hnormalA : IsStarNormal A :=
      isStarNormal_of_numericalRange_in_line A hline
    have hnormalScalar : IsStarNormal (lambda • (1 : SquareMatrix n)) :=
      IsStarNormal.smul lambda (1 : SquareMatrix n)
    have hnormalShift : IsStarNormal (A - lambda • (1 : SquareMatrix n)) := by
      apply Commute.isStarNormal_sub (ha := hnormalA) (hb := hnormalScalar)
      rw [star_smul, star_one]
      exact (Commute.one_right A).smul_right (star lambda)
    have hnormalOperator :
        IsStarNormal (euclideanOperator (A - lambda • (1 : SquareMatrix n))) :=
      IsStarNormal.map (hr := hnormalShift) euclideanOperator
        (A - lambda • (1 : SquareMatrix n))
    have hAxOperator : euclideanOperator A x = lambda • x := by
      apply WithLp.ofLp_injective
      exact hAx
    let T := euclideanOperator (A - lambda • (1 : SquareMatrix n))
    have hxker : x ∈ T.ker := by
      rw [LinearMap.mem_ker]
      change euclideanOperator (A - lambda • (1 : SquareMatrix n)) x = 0
      rw [map_sub, map_smul, map_one]
      simp only [sub_apply, smul_apply, one_apply_eq_self, hAxOperator,
        sub_self]
    have hxadjker : x ∈ T.adjoint.ker := by
      rw [ContinuousLinearMap.IsStarNormal.ker_adjoint_eq_ker hnormalOperator]
      exact hxker
    have hadjzero : T.adjoint x = 0 :=
      LinearMap.mem_ker.mp hxadjker
    dsimp only [T] at hadjzero
    rw [← euclideanOperator_conjTranspose] at hadjzero
    have hcoordinate :
        (A - lambda • (1 : SquareMatrix n))ᴴ *ᵥ ofLp x = 0 :=
      congrArg ofLp hadjzero
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec] at hcoordinate
    exact sub_eq_zero.mp hcoordinate

end DiskRigidity.Operator
