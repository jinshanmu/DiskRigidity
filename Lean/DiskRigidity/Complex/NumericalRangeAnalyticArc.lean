/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.NumericalRangePolygon
public import DiskRigidity.Operator.FoundationSupport
public import DiskRigidity.Algebraic.HermitianRealFactor
public import DiskRigidity.Algebraic.AffineArcDensity
public import DiskRigidity.Algebraic.AnalyticImplicitCurve
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Analytic exposed arcs of numerical ranges

This file constructs the curved exposed arc in Lemma 5.1 directly from a
finite matrix.  The proof uses the real Hermitian determinant, a Baire
factor-selection argument for its support graph, and the analytic implicit
function theorem.  Thus no general Rellich perturbation theorem is needed.
-/

noncomputable section

open Filter Function Metric Set
open scoped ComplexConjugate ComplexOrder InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Complex

@[expose] public section

namespace NumericalRangeArc

open DiskRigidity.Algebraic.AnalyticImplicitCurve

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The support function of the numerical range in the affine family of
directions `1 + it`. -/
def affineNumericalRangeSupport (A : Operator.SquareMatrix n) (t : ℝ) : ℝ :=
  Operator.numericalRangeSupport A (affineSupportDirection t)

theorem affineNumericalRangeSupport_le
    (A : Operator.SquareMatrix n) (t : ℝ) {z : ℂ}
    (hz : z ∈ Operator.numericalRange A) :
    affineSupportValue t z ≤ affineNumericalRangeSupport A t := by
  rw [affineNumericalRangeSupport, Operator.numericalRangeSupport]
  exact le_ciSup (Operator.bddAbove_numericalRangeSupportRange A
    (affineSupportDirection t)) ⟨z, hz⟩

/-- Compactness gives a point realizing every affine support value. -/
theorem exists_mem_numericalRange_affineSupportValue_eq
    [Nonempty n] (A : Operator.SquareMatrix n) (t : ℝ) :
    ∃ z ∈ Operator.numericalRange A,
      affineSupportValue t z = affineNumericalRangeSupport A t := by
  obtain ⟨z, hz, hmax⟩ :=
    (Operator.isCompact_numericalRange A).exists_isMaxOn
      (Operator.numericalRange_nonempty A)
      (by
        have : Continuous (affineSupportValue t) := by
          rw [show affineSupportValue t = fun z : ℂ ↦ z.re - t * z.im by
            funext z; exact affineSupportValue_apply t z]
          fun_prop
        exact this.continuousOn)
  refine ⟨z, hz, le_antisymm (affineNumericalRangeSupport_le A t hz) ?_⟩
  let _ : Nonempty (Operator.numericalRange A) :=
    Set.nonempty_coe_sort.mpr (Operator.numericalRange_nonempty A)
  rw [affineNumericalRangeSupport, Operator.numericalRangeSupport]
  apply ciSup_le
  intro w
  exact hmax w.property

private theorem abs_im_le_matrix_norm
    (A : Operator.SquareMatrix n) {z : ℂ}
    (hz : z ∈ Operator.numericalRange A) :
    |z.im| ≤ ‖A‖ := by
  exact (Complex.abs_im_le_norm z).trans
    (Operator.norm_le_of_mem_numericalRange A hz)

/-- The affine support function is globally Lipschitz. -/
theorem lipschitzWith_affineNumericalRangeSupport
    [Nonempty n] (A : Operator.SquareMatrix n) :
    LipschitzWith (NNReal.mk ‖A‖ (norm_nonneg A))
      (affineNumericalRangeSupport A) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro t u
  obtain ⟨z, hz, hzt⟩ :=
    exists_mem_numericalRange_affineSupportValue_eq A t
  obtain ⟨w, hw, hwu⟩ :=
    exists_mem_numericalRange_affineSupportValue_eq A u
  have hzu := affineNumericalRangeSupport_le A u hz
  have hwt := affineNumericalRangeSupport_le A t hw
  have h₁ : affineNumericalRangeSupport A t -
      affineNumericalRangeSupport A u ≤ |t - u| * ‖A‖ := by
    rw [← hzt, affineSupportValue_apply] at ⊢
    rw [← hwu, affineSupportValue_apply] at hzu
    have hzIm := abs_im_le_matrix_norm A hz
    have hmul : (u - t) * z.im ≤ |t - u| * ‖A‖ := by
      calc
        (u - t) * z.im ≤ |u - t| * |z.im| := le_abs_self _ |>.trans_eq (abs_mul _ _)
        _ ≤ |u - t| * ‖A‖ := mul_le_mul_of_nonneg_left hzIm (abs_nonneg _)
        _ = |t - u| * ‖A‖ := by rw [abs_sub_comm]
    linarith
  have h₂ : affineNumericalRangeSupport A u -
      affineNumericalRangeSupport A t ≤ |t - u| * ‖A‖ := by
    rw [← hwu, affineSupportValue_apply] at ⊢
    rw [← hzt, affineSupportValue_apply] at hwt
    have hwIm := abs_im_le_matrix_norm A hw
    have hmul : (t - u) * w.im ≤ |t - u| * ‖A‖ := by
      calc
        (t - u) * w.im ≤ |t - u| * |w.im| := le_abs_self _ |>.trans_eq (abs_mul _ _)
        _ ≤ |t - u| * ‖A‖ := mul_le_mul_of_nonneg_left hwIm (abs_nonneg _)
    linarith
  simp only [Real.dist_eq, NNReal.coe_mk]
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem continuous_affineNumericalRangeSupport
    [Nonempty n] (A : Operator.SquareMatrix n) :
    Continuous (affineNumericalRangeSupport A) :=
  (lipschitzWith_affineNumericalRangeSupport A).continuous

/-- A support function is convex because it is a supremum of affine
functions. -/
theorem convexOn_affineNumericalRangeSupport
    [Nonempty n] (A : Operator.SquareMatrix n) :
    ConvexOn ℝ univ (affineNumericalRangeSupport A) := by
  refine ⟨convex_univ, ?_⟩
  intro t _ u _ a b ha hb hab
  obtain ⟨z, hz, hzmax⟩ :=
    exists_mem_numericalRange_affineSupportValue_eq A (a • t + b • u)
  have hzt := affineNumericalRangeSupport_le A t hz
  have hzu := affineNumericalRangeSupport_le A u hz
  rw [← hzmax]
  simp only [smul_eq_mul, affineSupportValue_apply]
  calc
    z.re - (a * t + b * u) * z.im =
        a * (z.re - t * z.im) + b * (z.re - u * z.im) := by
      linear_combination -z.re * hab
    _ ≤ a * affineNumericalRangeSupport A t +
        b * affineNumericalRangeSupport A u := by
      rw [affineSupportValue_apply] at hzt hzu
      gcongr

/-- The boundary point reconstructed from a differentiable affine support
function. -/
def affineBoundaryPoint (A : Operator.SquareMatrix n) (t : ℝ) : ℂ :=
  ((affineNumericalRangeSupport A t -
      t * deriv (f := affineNumericalRangeSupport A) t : ℝ) : ℂ) -
    Complex.I *
      ((deriv (f := affineNumericalRangeSupport A) t : ℝ) : ℂ)

private theorem deriv_eq_neg_im_of_support
    (A : Operator.SquareMatrix n) {t : ℝ} {z : ℂ}
    (hz : z ∈ Operator.numericalRange A)
    (hzmax : affineSupportValue t z = affineNumericalRangeSupport A t)
    (hdiff : DifferentiableAt ℝ (affineNumericalRangeSupport A) t) :
    deriv (affineNumericalRangeSupport A) t = -z.im := by
  have hsupport (u : ℝ) :
      z.re - u * z.im ≤ affineNumericalRangeSupport A u := by
    simpa only [affineSupportValue_apply] using
      affineNumericalRangeSupport_le A u hz
  have hline : HasDerivAt (fun u : ℝ ↦ z.re - u * z.im) (-z.im) t := by
    have hid : HasDerivAt (fun u : ℝ ↦ u * z.im) z.im t := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) t).mul_const z.im
    have hc : HasDerivAt (fun _ : ℝ ↦ z.re) 0 t := hasDerivAt_const t z.re
    convert! hc.sub hid using 1
    ring
  let g : ℝ → ℝ := fun u ↦
    affineNumericalRangeSupport A u - (z.re - u * z.im)
  have hgmin : IsMinOn g univ t := by
    intro u _
    dsimp [g]
    rw [← hzmax, affineSupportValue_apply]
    linarith [hsupport u]
  have hglocal : IsLocalMin g t := hgmin.isLocalMin univ_mem
  have hgderiv : HasDerivAt g
      (deriv (affineNumericalRangeSupport A) t - (-z.im)) t := by
    exact hdiff.hasDerivAt.sub hline
  have hzero := hglocal.hasDerivAt_eq_zero hgderiv
  linarith

/-- At a differentiability point the supporting line exposes exactly the
point reconstructed from the support function and its derivative. -/
theorem eq_affineBoundaryPoint_of_mem_of_support
    (A : Operator.SquareMatrix n) {t : ℝ} {z : ℂ}
    (hz : z ∈ Operator.numericalRange A)
    (hzmax : affineSupportValue t z = affineNumericalRangeSupport A t)
    (hdiff : DifferentiableAt ℝ (affineNumericalRangeSupport A) t) :
    z = affineBoundaryPoint A t := by
  have hd := deriv_eq_neg_im_of_support A hz hzmax hdiff
  apply Complex.ext
  · rw [affineBoundaryPoint]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero,
      sub_zero]
    rw [hd]
    rw [affineSupportValue_apply] at hzmax
    linarith
  · rw [affineBoundaryPoint]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul,
      zero_sub]
    rw [hd]
    ring

/-- The reconstructed point belongs to the numerical range and is the
unique point of its exposed face. -/
theorem affineBoundaryPoint_mem_and_exposes
    [Nonempty n] (A : Operator.SquareMatrix n) {t : ℝ}
    (hdiff : DifferentiableAt ℝ (affineNumericalRangeSupport A) t) :
    affineBoundaryPoint A t ∈ Operator.numericalRange A ∧
      ∀ z ∈ Operator.numericalRange A,
        affineSupportValue t z = affineNumericalRangeSupport A t →
          z = affineBoundaryPoint A t := by
  obtain ⟨z, hz, hzmax⟩ :=
    exists_mem_numericalRange_affineSupportValue_eq A t
  have hzeq := eq_affineBoundaryPoint_of_mem_of_support A hz hzmax hdiff
  refine ⟨hzeq ▸ hz, ?_⟩
  intro w hw hwmax
  exact eq_affineBoundaryPoint_of_mem_of_support A hw hwmax hdiff

@[simp]
theorem affineSupportValue_affineBoundaryPoint
    (A : Operator.SquareMatrix n) (t : ℝ) :
    affineSupportValue t (affineBoundaryPoint A t) =
      affineNumericalRangeSupport A t := by
  rw [affineSupportValue_apply, affineBoundaryPoint]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero,
    sub_zero, Complex.sub_im, Complex.mul_im, zero_sub]
  ring

/-- The coefficient of the affine parameter in the Hermitian support
pencil. -/
def affinePencilH (A : Operator.SquareMatrix n) : Operator.SquareMatrix n :=
  -Operator.rePart (Complex.I • A)

/-- The constant coefficient in the Hermitian support pencil. -/
def affinePencilJ (A : Operator.SquareMatrix n) : Operator.SquareMatrix n :=
  -Operator.rePart A

omit [Fintype n] [DecidableEq n] in
theorem affinePencilH_isHermitian (A : Operator.SquareMatrix n) :
    (affinePencilH A).IsHermitian := by
  apply Matrix.IsHermitian.neg
  simp [Operator.rePart, Matrix.IsHermitian, add_comm]

omit [Fintype n] [DecidableEq n] in
theorem affinePencilJ_isHermitian (A : Operator.SquareMatrix n) :
    (affinePencilJ A).IsHermitian := by
  apply Matrix.IsHermitian.neg
  simp [Operator.rePart, Matrix.IsHermitian, add_comm]

private theorem affinePencil_matrix_identity
    (A : Operator.SquareMatrix n) (s t : ℝ) :
    Matrix.scalar n (s : ℂ) + (t : ℂ) • affinePencilH A +
        affinePencilJ A =
      Matrix.scalar n (s : ℂ) -
        Operator.rePart (affineSupportDirection t • A) := by
  ext i j
  apply Complex.ext <;>
    simp [affinePencilH, affinePencilJ, Operator.rePart,
      affineSupportDirection, Matrix.scalar_apply, Complex.mul_re,
      Complex.mul_im] <;>
    ring

/-- The support graph lies on the real Hermitian determinant curve. -/
theorem eval_realDeterminantPolynomial_affineSupport_eq_zero
    [Nonempty n] (A : Operator.SquareMatrix n) (t : ℝ) :
    MvPolynomial.eval ![affineNumericalRangeSupport A t, t, 1]
      (Algebraic.HermitianRealFactor.realDeterminantPolynomial
        (affinePencilH A) (affinePencilJ A)) = 0 := by
  let H := Operator.rePart (affineSupportDirection t • A)
  have hH : H.IsHermitian := by
    simp [H, Operator.rePart, Matrix.IsHermitian, add_comm]
  have heig : Module.End.HasEigenvalue (Matrix.toEuclideanLin H)
      (affineNumericalRangeSupport A t : ℂ) := by
    have h := Operator.largestEigenvalue_hasEigenvalue H hH
    rw [← Operator.numericalRangeSupport_eq_largestEigenvalue A
      (affineSupportDirection t)] at h
    exact h
  have hspecLin : (affineNumericalRangeSupport A t : ℂ) ∈
      spectrum ℂ (Matrix.toEuclideanLin H) :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mp heig
  have hspec : (affineNumericalRangeSupport A t : ℂ) ∈ spectrum ℂ H := by
    simpa only [Matrix.spectrum_toLpLin] using hspecLin
  have hdet :
      (Matrix.scalar n (affineNumericalRangeSupport A t : ℂ) - H).det = 0 := by
    have hroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hspec
    change H.charpoly.eval (affineNumericalRangeSupport A t : ℂ) = 0 at hroot
    rwa [Matrix.eval_charpoly] at hroot
  have hcomplex : MvPolynomial.eval
      (fun i ↦ ((![affineNumericalRangeSupport A t, t, 1] i : ℝ) : ℂ))
      (MvPolynomial.map (algebraMap ℝ ℂ)
        (Algebraic.HermitianRealFactor.realDeterminantPolynomial
          (affinePencilH A) (affinePencilJ A))) = 0 := by
    rw [Algebraic.HermitianRealFactor.map_realDeterminantPolynomial
      (affinePencilH A) (affinePencilJ A)
      (affinePencilH_isHermitian A) (affinePencilJ_isHermitian A)]
    rw [Algebraic.HermitianProjective.eval_determinantPolynomial]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Complex.coe_smul, one_smul]
    rw [show Matrix.scalar n (affineNumericalRangeSupport A t : ℂ) +
        t • affinePencilH A + affinePencilJ A =
        Matrix.scalar n (affineNumericalRangeSupport A t : ℂ) - H by
      simpa only [H, Complex.coe_smul] using affinePencil_matrix_identity A
        (affineNumericalRangeSupport A t) t]
    exact hdet
  rw [Algebraic.HermitianRealFactor.eval_map_real] at hcomplex
  exact Complex.ofReal_eq_zero.mp hcomplex

/-- The real projective determinant whose affine zero graph contains the
support function. -/
def affineSupportDeterminant (A : Operator.SquareMatrix n) :
    MvPolynomial (Fin 3) ℝ :=
  Algebraic.HermitianRealFactor.realDeterminantPolynomial
    (affinePencilH A) (affinePencilJ A)

/-- Baire factor selection: one irreducible homogeneous factor of the
Hermitian determinant contains the support graph on a nonempty open set. -/
theorem exists_open_irreducible_factor_affineSupport
    [Nonempty n] (A : Operator.SquareMatrix n) :
    ∃ (Q : MvPolynomial (Fin 3) ℝ) (m : ℕ) (U : Set ℝ),
      IsOpen U ∧ U.Nonempty ∧ Irreducible Q ∧
      Q ∣ affineSupportDeterminant A ∧ Q.IsHomogeneous m ∧ m ≠ 0 ∧
      MvPolynomial.eval Algebraic.PlaneCurveSpecialization.distinguishedPoint Q ≠ 0 ∧
      ∀ t ∈ U, MvPolynomial.eval
        ![affineNumericalRangeSupport A t, t, 1] Q = 0 := by
  classical
  let P := affineSupportDeterminant A
  have hH := affinePencilH_isHermitian A
  have hJ := affinePencilJ_isHermitian A
  have hPzero : P ≠ 0 :=
    Algebraic.HermitianRealFactor.realDeterminantPolynomial_ne_zero
      (affinePencilH A) (affinePencilJ A) hH hJ
  have hPhom : P.IsHomogeneous (Fintype.card n) :=
    Algebraic.HermitianRealFactor.realDeterminantPolynomial_isHomogeneous
      (affinePencilH A) (affinePencilJ A) hH hJ
  let factors := UniqueFactorizationMonoid.factors P
  let ι := {Q : MvPolynomial (Fin 3) ℝ // Q ∈ factors.toFinset}
  let ell : ℝ → Fin 3 → ℝ := fun t ↦
    ![affineNumericalRangeSupport A t, t, 1]
  let Z : ι → Set ℝ := fun i ↦
    {t | MvPolynomial.eval (ell t) i.1 = 0}
  have hell : Continuous ell := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_affineNumericalRangeSupport A
    · exact continuous_id
    · exact continuous_const
  have hclosed : ∀ i, IsClosed (Z i) := by
    intro i
    exact isClosed_singleton.preimage
      ((MvPolynomial.continuous_eval i.1).comp hell)
  have hcover : ⋃ i, Z i = univ := by
    apply eq_univ_iff_forall.mpr
    intro t
    simp only [mem_iUnion]
    have hPt : MvPolynomial.eval (ell t) P = 0 := by
      exact eval_realDeterminantPolynomial_affineSupport_eq_zero A t
    have hassociated : Associated factors.prod P :=
      UniqueFactorizationMonoid.factors_prod hPzero
    have hfactorProduct : MvPolynomial.eval (ell t) factors.prod = 0 :=
      ((hassociated.map (MvPolynomial.eval (ell t))).eq_zero_iff).mpr hPt
    have hmappedProduct :
        (factors.map fun Q ↦ MvPolynomial.eval (ell t) Q).prod = 0 := by
      rw [← map_multiset_prod]
      exact hfactorProduct
    have hzeroMem : 0 ∈
        factors.map fun Q ↦ MvPolynomial.eval (ell t) Q :=
      Multiset.prod_eq_zero_iff.mp hmappedProduct
    obtain ⟨Q, hQfactors, hQeval⟩ := Multiset.mem_map.mp hzeroMem
    let i : ι := ⟨Q, Multiset.mem_toFinset.mpr hQfactors⟩
    exact ⟨i, hQeval⟩
  obtain ⟨i, hi⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  let Q := i.1
  let U := interior (Z i)
  have hQfactors : Q ∈ factors := Multiset.mem_toFinset.mp i.2
  have hQirr : Irreducible Q :=
    UniqueFactorizationMonoid.irreducible_of_factor Q hQfactors
  have hQdiv : Q ∣ P :=
    UniqueFactorizationMonoid.dvd_of_mem_factors hQfactors
  obtain ⟨m, hQhom⟩ :=
    Algebraic.HomogeneousFactor.exists_isHomogeneous_of_dvd
      hQirr.ne_zero hPzero hQdiv hPhom
  have hmapDiv : MvPolynomial.map (algebraMap ℝ ℂ) Q ∣
      Algebraic.HermitianProjective.determinantPolynomial
        (affinePencilH A) (affinePencilJ A) := by
    have h' : MvPolynomial.map (algebraMap ℝ ℂ) Q ∣
        MvPolynomial.map (algebraMap ℝ ℂ)
          (Algebraic.HermitianRealFactor.realDeterminantPolynomial
            (affinePencilH A) (affinePencilJ A)) := by
      simpa only [P, affineSupportDeterminant] using
        map_dvd (MvPolynomial.map (algebraMap ℝ ℂ)) hQdiv
    rw [Algebraic.HermitianRealFactor.map_realDeterminantPolynomial
      (affinePencilH A) (affinePencilJ A) hH hJ] at h'
    exact h'
  have he : MvPolynomial.eval
      Algebraic.PlaneCurveSpecialization.distinguishedPoint Q ≠ 0 :=
    Algebraic.HermitianProjective.eval_distinguishedPoint_ne_zero_of_dvd
      (affinePencilH A) (affinePencilJ A) Q hmapDiv
  have hm : m ≠ 0 := by
    intro hmzero
    subst m
    have hdegree : Q.totalDegree = 0 := hQhom.totalDegree hQirr.ne_zero
    have hunit : IsUnit Q := by
      rw [MvPolynomial.isUnit_iff_totalDegree_of_isReduced]
      refine ⟨?_, hdegree⟩
      rw [isUnit_iff_ne_zero]
      intro hcoeff
      apply hQirr.ne_zero
      rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree,
        hcoeff, map_zero]
    exact hQirr.not_isUnit hunit
  refine ⟨Q, m, U, isOpen_interior, hi, hQirr, hQdiv, hQhom, hm, he, ?_⟩
  intro t ht
  have htZ : t ∈ Z i := interior_subset ht
  change MvPolynomial.eval (ell t) Q = 0 at htZ
  simpa only [ell] using htZ

/-- On an open graph of an irreducible homogeneous curve, the partial in
the graph-value coordinate is nonzero somewhere.  The distinguished-point
condition rules out a curve independent of that coordinate. -/
theorem exists_pderiv_zero_ne_zero_on_open_graph
    {Q : MvPolynomial (Fin 3) ℝ} {m : ℕ}
    (hQhom : Q.IsHomogeneous m) (hQirr : Irreducible Q) (hm : m ≠ 0)
    (he : MvPolynomial.eval
      Algebraic.PlaneCurveSpecialization.distinguishedPoint Q ≠ 0)
    {U : Set ℝ} (hUopen : IsOpen U) (hU : U.Nonempty)
    (s : ℝ → ℝ)
    (hQzero : ∀ t ∈ U, MvPolynomial.eval ![s t, t, 1] Q = 0) :
    ∃ t ∈ U,
      MvPolynomial.eval ![s t, t, 1] (MvPolynomial.pderiv 0 Q) ≠ 0 := by
  by_contra hexists
  push Not at hexists
  have hpartial : ∀ t ∈ U,
      MvPolynomial.eval ![s t, t, 1] (MvPolynomial.pderiv 0 Q) = 0 :=
    hexists
  have hdiv : Q ∣ MvPolynomial.pderiv 0 Q :=
    Algebraic.AffineArcDensity.dvd_of_vanishes_on_open_graph
      hQhom (hQhom.pderiv (i := 0)) hQirr hm he hUopen hU s
      hQzero hpartial
  have hpzero : MvPolynomial.pderiv 0 Q = 0 := by
    by_contra hpzero
    have hdegreeQ : Q.totalDegree = m :=
      hQhom.totalDegree hQirr.ne_zero
    have hdegreeDiv : Q.totalDegree ≤
        (MvPolynomial.pderiv 0 Q).totalDegree :=
      MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hpzero
    have hdegreePartial :
        (MvPolynomial.pderiv 0 Q).totalDegree ≤ m - 1 :=
      (hQhom.pderiv (i := 0)).totalDegree_le
    omega
  have hEuler := Algebraic.ProjectiveDual.dot_gradient_eq_smul_eval hQhom
    Algebraic.PlaneCurveSpecialization.distinguishedPoint
  have hmReal : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hleft :
      Algebraic.PlaneCurveSpecialization.distinguishedPoint ⬝ᵥ
        Algebraic.ProjectiveDual.gradient Q
          Algebraic.PlaneCurveSpecialization.distinguishedPoint = 0 := by
    simp [Algebraic.PlaneCurveSpecialization.distinguishedPoint,
      Algebraic.ProjectiveDual.gradient, dotProduct, Fin.sum_univ_three,
      hpzero]
  rw [hleft] at hEuler
  exact (mul_ne_zero hmReal he) hEuler.symm

/-- Evaluation of a projective curve in the affine graph chart, ordered as
`(parameter, graph value)`. -/
def affineGraphEval (Q : MvPolynomial (Fin 3) ℝ) (q : ℝ × ℝ) : ℝ :=
  MvPolynomial.eval ![q.2, q.1, 1] Q

theorem analyticAt_affineGraphEval (Q : MvPolynomial (Fin 3) ℝ)
    (q : ℝ × ℝ) :
    AnalyticAt ℝ (affineGraphEval Q) q := by
  unfold affineGraphEval
  apply AnalyticAt.aeval_mvPolynomial
  intro i
  fin_cases i
  · exact analyticAt_snd
  · exact analyticAt_fst
  · exact analyticAt_const

private theorem deriv_affineGraphEval_snd
    (Q : MvPolynomial (Fin 3) ℝ) (t s : ℝ) :
    deriv (fun u ↦ affineGraphEval Q (t, u)) s =
      Algebraic.ProjectiveDual.gradient Q ![s, t, 1] 0 := by
  let ell : ℝ → Fin 3 → ℝ := fun u ↦ ![u, t, 1]
  have hell : ∀ i, AnalyticAt ℝ (fun u ↦ ell u i) s := by
    intro i
    fin_cases i
    · exact analyticAt_id
    · exact analyticAt_const
    · exact analyticAt_const
  rw [show (fun u ↦ affineGraphEval Q (t, u)) =
      (fun u ↦ MvPolynomial.eval (ell u) Q) by rfl]
  rw [Algebraic.AnalyticContact.deriv_eval_mvPolynomial Q hell]
  simp [Algebraic.ProjectiveDual.directionalDerivative,
    Algebraic.ProjectiveDual.gradient, dotProduct, Fin.sum_univ_three, ell]

private theorem fderiv_comp_inr_affineGraphEval
    (Q : MvPolynomial (Fin 3) ℝ) (t s : ℝ) :
    fderiv ℝ (affineGraphEval Q) (t, s) ∘L
        ContinuousLinearMap.inr ℝ ℝ ℝ =
      (1 : ℝ →L[ℝ] ℝ).smulRight
        (Algebraic.ProjectiveDual.gradient Q ![s, t, 1] 0) := by
  ext
  have hf := (analyticAt_affineGraphEval Q (t, s)).hasStrictFDerivAt.hasFDerivAt
  have hline : HasFDerivAt (fun u : ℝ ↦ (t, u))
      (ContinuousLinearMap.inr ℝ ℝ ℝ) s :=
    (hasFDerivAt_const t s).prodMk (hasFDerivAt_id s)
  have hcomp := hf.comp s hline
  have hderiv : deriv (fun u ↦ affineGraphEval Q (t, u)) s =
      (fderiv ℝ (affineGraphEval Q) (t, s) ∘L
        ContinuousLinearMap.inr ℝ ℝ ℝ) 1 := by
    rw [show (fun u ↦ affineGraphEval Q (t, u)) =
      affineGraphEval Q ∘ Prod.mk t by funext u; rfl]
    exact hcomp.hasDerivAt.deriv
  rw [deriv_affineGraphEval_snd] at hderiv
  simpa [ContinuousLinearMap.smulRight_apply] using hderiv.symm

private theorem isInvertible_fderiv_comp_inr_affineGraphEval
    (Q : MvPolynomial (Fin 3) ℝ) (t s : ℝ)
    (hs : Algebraic.ProjectiveDual.gradient Q ![s, t, 1] 0 ≠ 0) :
    (fderiv ℝ (affineGraphEval Q) (t, s) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
  rw [fderiv_comp_inr_affineGraphEval]
  let u : ℝˣ := Units.mk0
    (Algebraic.ProjectiveDual.gradient Q ![s, t, 1] 0) hs
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ u, ?_⟩
  ext
  simp [u, ContinuousLinearMap.smulRight_apply]

/-- A regular determinant factor makes the actual numerical-range support
function analytic; local implicit uniqueness identifies the constructed
branch with the continuous support graph. -/
theorem analyticAt_affineNumericalRangeSupport_of_factor
    [Nonempty n] (A : Operator.SquareMatrix n)
    (Q : MvPolynomial (Fin 3) ℝ) {U : Set ℝ} {t : ℝ}
    (hUopen : IsOpen U) (ht : t ∈ U)
    (hzero : ∀ u ∈ U, MvPolynomial.eval
      ![affineNumericalRangeSupport A u, u, 1] Q = 0)
    (hpartial : MvPolynomial.eval
      ![affineNumericalRangeSupport A t, t, 1]
        (MvPolynomial.pderiv 0 Q) ≠ 0) :
    AnalyticAt ℝ (affineNumericalRangeSupport A) t := by
  let h := affineNumericalRangeSupport A
  let f := affineGraphEval Q
  let u₀ : ℝ × ℝ := (t, h t)
  have hf : AnalyticAt ℝ f u₀ := analyticAt_affineGraphEval Q u₀
  let f' := fderiv ℝ f u₀
  have hstrict : HasStrictFDerivAt f f' u₀ := hf.hasStrictFDerivAt
  have hpartial' :
      Algebraic.ProjectiveDual.gradient Q ![h t, t, 1] 0 ≠ 0 := by
    exact hpartial
  have hinv : (f' ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    exact isInvertible_fderiv_comp_inr_affineGraphEval Q t (h t) hpartial'
  let psi : ℝ → ℝ := hstrict.implicitFunctionOfProdDomain hinv
  have hpsi : AnalyticAt ℝ psi t := by
    exact HasStrictFDerivAt.analyticAt_implicitFunctionOfProdDomain
      hstrict hinv hf
  have hbase : f u₀ = 0 := by
    exact hzero t ht
  have hzeroEventually : ∀ᶠ u in nhds t, f (u, h u) = f u₀ := by
    filter_upwards [hUopen.mem_nhds ht] with u hu
    rw [hbase]
    exact hzero u hu
  have hpair : Tendsto (fun u ↦ (u, h u)) (nhds t) (nhds u₀) := by
    exact continuousAt_id.prodMk
      (continuous_affineNumericalRangeSupport A).continuousAt
  have hunique : ∀ᶠ u in nhds t,
      f (u, h u) = f u₀ ↔ psi u = h u := by
    exact hpair.eventually
      (hstrict.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv)
  have heq : psi =ᶠ[nhds t] h := by
    filter_upwards [hzeroEventually, hunique] with u hzu hui
    exact hui.mp hzu
  exact hpsi.congr heq

/-- The affine support function of every finite numerical range is analytic
on some nonempty open set, obtained directly from the Hermitian determinant. -/
theorem exists_open_analytic_affineNumericalRangeSupport
    [Nonempty n] (A : Operator.SquareMatrix n) :
    ∃ V : Set ℝ, IsOpen V ∧ V.Nonempty ∧
      AnalyticOnNhd ℝ (affineNumericalRangeSupport A) V := by
  obtain ⟨Q, m, U, hUopen, hU, hQirr, _hQdiv, hQhom, hm, he, hzero⟩ :=
    exists_open_irreducible_factor_affineSupport A
  obtain ⟨t, ht, hpartial⟩ :=
    exists_pderiv_zero_ne_zero_on_open_graph hQhom hQirr hm he
      hUopen hU (affineNumericalRangeSupport A) hzero
  have hat : AnalyticAt ℝ (affineNumericalRangeSupport A) t :=
    analyticAt_affineNumericalRangeSupport_of_factor A Q hUopen ht hzero hpartial
  obtain ⟨V, hVsub, hVopen, htV⟩ :=
    _root_.mem_nhds_iff.mp hat.eventually_analyticAt
  exact ⟨V, hVopen, ⟨t, htV⟩, fun u hu ↦ hVsub hu⟩

/-- A connected interval on which the affine support function is analytic. -/
theorem exists_ball_analytic_affineNumericalRangeSupport
    [Nonempty n] (A : Operator.SquareMatrix n) :
    ∃ t : ℝ, ∃ r : ℝ, 0 < r ∧
      AnalyticOnNhd ℝ (affineNumericalRangeSupport A) (ball t r) := by
  obtain ⟨V, hVopen, ⟨t, htV⟩, hVanalytic⟩ :=
    exists_open_analytic_affineNumericalRangeSupport A
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hVopen t htV
  exact ⟨t, r, hr, fun u hu ↦ hVanalytic u (hrV hu)⟩

/-- On every analytic interval, convexity forces the second derivative of
the affine support function to be nonnegative. -/
theorem secondDeriv_affineNumericalRangeSupport_nonneg
    [Nonempty n] (A : Operator.SquareMatrix n) {V : Set ℝ}
    (hVopen : IsOpen V) (hVconv : Convex ℝ V)
    (hana : AnalyticOnNhd ℝ (affineNumericalRangeSupport A) V)
    {t : ℝ} (ht : t ∈ V) :
    0 ≤ deriv (deriv (affineNumericalRangeSupport A)) t := by
  let h := affineNumericalRangeSupport A
  have hmono : MonotoneOn (deriv h) V :=
    ((convexOn_affineNumericalRangeSupport A).subset
      (subset_univ V) hVconv).monotoneOn_deriv
      (fun u hu ↦ (hana u hu).differentiableAt)
  have hn : 0 ≤ derivWithin (deriv h) V t :=
    hmono.derivWithin_nonneg
  rw [derivWithin_of_isOpen hVopen ht] at hn
  exact hn

private theorem affineSupportDirection_independent_of_ne
    {t u : ℝ} (htu : t ≠ u) :
    affineSupportDirection t * conj (affineSupportDirection u) ≠
      affineSupportDirection u * conj (affineSupportDirection t) := by
  intro heq
  have him := congrArg Complex.im heq
  simp [affineSupportDirection, Complex.mul_im] at him
  exact htu (by linarith)

/-- If the spectrum is strictly inside the numerical range, the analytic
support interval contains a point with strictly positive second derivative.
Otherwise the exposed point would be constant on an interval, giving a
two-sided support corner. -/
theorem exists_positive_secondDeriv_affineNumericalRangeSupport
    [Nonempty n] (A : Operator.SquareMatrix n)
    (hspec : spectrum ℂ A ⊆ interior (Operator.numericalRange A)) :
    ∃ c r t : ℝ, 0 < r ∧ t ∈ ball c r ∧
      AnalyticOnNhd ℝ (affineNumericalRangeSupport A) (ball c r) ∧
      0 < deriv (deriv (affineNumericalRangeSupport A)) t := by
  obtain ⟨c, r, hr, hana⟩ :=
    exists_ball_analytic_affineNumericalRangeSupport A
  let h := affineNumericalRangeSupport A
  let B : Set ℝ := ball c r
  by_contra hpos
  push Not at hpos
  have hsecondZero : B.EqOn (deriv (deriv h)) 0 := by
    intro u hu
    have hnonneg : 0 ≤ deriv (deriv h) u := by
      exact secondDeriv_affineNumericalRangeSupport_nonneg A
        isOpen_ball (convex_ball c r) hana hu
    have hnonpos : deriv (deriv h) u ≤ 0 := by
      exact hpos c r u hr hu hana
    exact le_antisymm hnonpos hnonneg
  have hderivDiff : DifferentiableOn ℝ (deriv h) B := by
    intro u hu
    exact (hana u hu).deriv.differentiableAt.differentiableWithinAt
  have hcenter : c ∈ B := Metric.mem_ball_self hr
  have hderivConst : ∀ ⦃x y : ℝ⦄, x ∈ B → y ∈ B →
      deriv h x = deriv h y := by
    intro x y hx hy
    exact isOpen_ball.is_const_of_deriv_eq_zero Metric.isPreconnected_ball
      hderivDiff hsecondZero hx hy
  let d := deriv h c
  have hhDiff : DifferentiableOn ℝ h B := by
    intro u hu
    exact (hana u hu).differentiableAt.differentiableWithinAt
  have hlineDiff : DifferentiableOn ℝ (fun u : ℝ ↦ d * u) B := by
    fun_prop
  have hderivLine : B.EqOn (deriv h) (deriv fun u : ℝ ↦ d * u) := by
    intro u hu
    rw [hderivConst hu hcenter]
    simp [d]
  obtain ⟨a, hlinear⟩ := isOpen_ball.exists_eq_add_of_deriv_eq
    Metric.isPreconnected_ball hhDiff hlineDiff hderivLine
  let u := c + r / 2
  have hu : u ∈ B := by
    change dist u c < r
    rw [Real.dist_eq]
    dsimp [u]
    rw [abs_of_pos (by linarith : 0 < c + r / 2 - c)]
    linarith
  have hcu : c ≠ u := by
    dsimp [u]
    linarith
  have hboundaryEq : affineBoundaryPoint A c = affineBoundaryPoint A u := by
    have hcvalue := hlinear hcenter
    have huvalue := hlinear hu
    have hcderiv : deriv h c = d := rfl
    have huderiv : deriv h u = d := hderivConst hu hcenter
    rw [affineBoundaryPoint, affineBoundaryPoint]
    change ((h c - c * deriv h c : ℝ) : ℂ) -
        Complex.I * ((deriv h c : ℝ) : ℂ) =
      ((h u - u * deriv h u : ℝ) : ℂ) -
        Complex.I * ((deriv h u : ℝ) : ℂ)
    rw [hcvalue, huvalue, hcderiv, huderiv]
    push_cast
    ring
  have hdiffc : DifferentiableAt ℝ h c := (hana c hcenter).differentiableAt
  have hmem : affineBoundaryPoint A c ∈ Operator.numericalRange A :=
    (affineBoundaryPoint_mem_and_exposes A hdiffc).1
  apply NumericalRangeCorner.not_isTwoSidedSupportCorner_of_spectrum_subset_interior
    A hspec hmem
  refine ⟨affineSupportDirection c, affineSupportDirection u,
    affineSupportDirection_independent_of_ne hcu, ?_, ?_⟩
  · intro z hz
    change affineSupportValue c z ≤
      affineSupportValue c (affineBoundaryPoint A c)
    rw [affineSupportValue_affineBoundaryPoint]
    exact affineNumericalRangeSupport_le A c hz
  · intro z hz
    change affineSupportValue u z ≤
      affineSupportValue u (affineBoundaryPoint A c)
    rw [hboundaryEq, affineSupportValue_affineBoundaryPoint]
    exact affineNumericalRangeSupport_le A u hz

/-- Shrinking around a strictly convex support point gives an interval on
which the support curvature density is everywhere positive. -/
theorem exists_ball_strictlyConvex_affineNumericalRangeSupport
    [Nonempty n] (A : Operator.SquareMatrix n)
    (hspec : spectrum ℂ A ⊆ interior (Operator.numericalRange A)) :
    ∃ t r : ℝ, 0 < r ∧
      AnalyticOnNhd ℝ (affineNumericalRangeSupport A) (ball t r) ∧
      ∀ u ∈ ball t r,
        0 < deriv (deriv (affineNumericalRangeSupport A)) u := by
  obtain ⟨c, R, t, hR, ht, hana, htpos⟩ :=
    exists_positive_secondDeriv_affineNumericalRangeSupport A hspec
  let h := affineNumericalRangeSupport A
  have hcont : ContinuousAt (deriv (deriv h)) t :=
    (hana t ht).deriv.deriv.continuousAt
  have heventPos : ∀ᶠ u in nhds t, 0 < deriv (deriv h) u :=
    continuousAt_const.eventually_lt hcont htpos
  have heventBall : ∀ᶠ u in nhds t, u ∈ ball c R :=
    isOpen_ball.mem_nhds ht
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    (show {u | 0 < deriv (deriv h) u} ∩ ball c R ∈ nhds t from
      heventPos.and heventBall)
  refine ⟨t, r, hr, ?_, ?_⟩
  · intro u hu
    exact hana u (hrsub hu).2
  · intro u hu
    exact (hrsub hu).1

/-- The exposed boundary parametrization reconstructed from the analytic
support function is itself real analytic. -/
theorem analyticAt_affineBoundaryPoint
    (A : Operator.SquareMatrix n) {t : ℝ}
    (hana : AnalyticAt ℝ (affineNumericalRangeSupport A) t) :
    AnalyticAt ℝ (affineBoundaryPoint A) t := by
  let h := affineNumericalRangeSupport A
  have hh : AnalyticAt ℝ h t := hana
  have hd : AnalyticAt ℝ (deriv h) t := hh.deriv
  have hfirst : AnalyticAt ℝ (fun u ↦ h u - u * deriv h u) t :=
    hh.sub (analyticAt_id.mul hd)
  have hfirstC : AnalyticAt ℝ
      (fun u ↦ ((h u - u * deriv h u : ℝ) : ℂ)) t :=
    (Complex.ofRealCLM.analyticAt (h t - t * deriv h t)).comp
      (f := fun u ↦ h u - u * deriv h u) hfirst
  have hdC : AnalyticAt ℝ (fun u ↦ ((deriv h u : ℝ) : ℂ)) t :=
    (Complex.ofRealCLM.analyticAt (deriv h t)).comp hd
  have hidC : AnalyticAt ℝ (fun u : ℝ ↦ (u : ℂ)) t :=
    (Complex.ofRealCLM.analyticAt t).comp analyticAt_id
  have hI : AnalyticAt ℝ (fun _ : ℝ ↦ Complex.I) t := analyticAt_const
  change AnalyticAt ℝ (fun u ↦
    ((h u - u * deriv h u : ℝ) : ℂ) -
      Complex.I * ((deriv h u : ℝ) : ℂ)) t
  exact hfirstC.sub (hI.mul hdC)

/-- Every reconstructed singleton-support point lies on the boundary of the
numerical range. -/
theorem affineBoundaryPoint_mem_frontier
    [Nonempty n] (A : Operator.SquareMatrix n) {t : ℝ}
    (hdiff : DifferentiableAt ℝ (affineNumericalRangeSupport A) t) :
    affineBoundaryPoint A t ∈ frontier (Operator.numericalRange A) := by
  let lambda := affineBoundaryPoint A t
  have hlambda : lambda ∈ Operator.numericalRange A :=
    (affineBoundaryPoint_mem_and_exposes A hdiff).1
  rw [mem_frontier_iff_notMem_interior hlambda]
  intro hinterior
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp isOpen_interior lambda hinterior
  let w : ℂ := lambda + (r / 2 : ℝ)
  have hwball : w ∈ ball lambda r := by
    rw [mem_ball, Complex.dist_eq]
    dsimp [w]
    simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by linarith : 0 < r / 2)]
    linarith
  have hw : w ∈ Operator.numericalRange A := interior_subset (hrsub hwball)
  have hs := affineNumericalRangeSupport_le A t hw
  have hwvalue : affineSupportValue t w =
      affineSupportValue t lambda + r / 2 := by
    simp [w, affineSupportValue_apply]
    ring
  rw [hwvalue, affineSupportValue_affineBoundaryPoint] at hs
  linarith

/-- Exact curved-exposed-arc endpoint for Lemma 5.1.  Under strict spectral
interiority, an open interval parametrizes an injective real-analytic arc of
the numerical-range frontier.  Each point is exposed by its displayed
support line, and the affine support curvature density is strictly positive
throughout the interval. -/
theorem exists_strictlyCurved_exposed_numericalRangeArc
    [Nonempty n] (A : Operator.SquareMatrix n)
    (hspec : spectrum ℂ A ⊆ interior (Operator.numericalRange A)) :
    ∃ t r : ℝ, 0 < r ∧
      AnalyticOnNhd ℝ (affineBoundaryPoint A) (ball t r) ∧
      Set.InjOn (affineBoundaryPoint A) (ball t r) ∧
      ∀ u ∈ ball t r,
        affineBoundaryPoint A u ∈ frontier (Operator.numericalRange A) ∧
        0 < deriv (deriv (affineNumericalRangeSupport A)) u ∧
        (∀ z ∈ Operator.numericalRange A,
          affineSupportValue u z ≤
            affineSupportValue u (affineBoundaryPoint A u)) ∧
        ∀ z ∈ Operator.numericalRange A,
          affineSupportValue u z =
            affineSupportValue u (affineBoundaryPoint A u) →
          z = affineBoundaryPoint A u := by
  obtain ⟨t, r, hr, hana, hsecondPos⟩ :=
    exists_ball_strictlyConvex_affineNumericalRangeSupport A hspec
  let h := affineNumericalRangeSupport A
  let B : Set ℝ := ball t r
  have hsigmaAnalytic : AnalyticOnNhd ℝ (affineBoundaryPoint A) B := by
    intro u hu
    exact analyticAt_affineBoundaryPoint A (hana u hu)
  have hderivContinuous : ContinuousOn (deriv h) B := by
    intro u hu
    exact (hana u hu).deriv.continuousAt.continuousWithinAt
  have hderivStrict : StrictMonoOn (deriv h) B := by
    apply strictMonoOn_of_deriv_pos (convex_ball t r) hderivContinuous
    intro u hu
    exact hsecondPos u (interior_subset hu)
  have hsigmaInj : Set.InjOn (affineBoundaryPoint A) B := by
    intro x hx y hy hxy
    have him := congrArg Complex.im hxy
    have hderivEq : deriv h x = deriv h y := by
      simp only [affineBoundaryPoint, Complex.sub_im, Complex.ofReal_im,
        Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        zero_mul, one_mul, zero_sub] at him
      linarith
    exact hderivStrict.injOn hx hy hderivEq
  refine ⟨t, r, hr, hsigmaAnalytic, hsigmaInj, ?_⟩
  intro u hu
  have hdiff : DifferentiableAt ℝ h u := (hana u hu).differentiableAt
  have hexpose := affineBoundaryPoint_mem_and_exposes A hdiff
  refine ⟨affineBoundaryPoint_mem_frontier A hdiff, hsecondPos u hu, ?_, ?_⟩
  · intro z hz
    rw [affineSupportValue_affineBoundaryPoint]
    exact affineNumericalRangeSupport_le A u hz
  · intro z hz heq
    apply hexpose.2 z hz
    rwa [affineSupportValue_affineBoundaryPoint] at heq

end NumericalRangeArc

end

end DiskRigidity.Complex
