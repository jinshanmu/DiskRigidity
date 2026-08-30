/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.GenericSpecialization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Specializing a homogeneous plane curve by its normal direction

For a homogeneous equation `Q(s,u,v)`, this file forms the affine family
`Q(s,t,1)`.  It proves that the coefficient of `s^m` is the constant
`Q(1,0,0)` and hence, when this value is nonzero, every specialization has
degree exactly `m`.  This formalizes the degree-preservation assertion in the
generic-direction paragraph of Proposition 7.1.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace PlaneCurveSpecialization

open MvPolynomial Polynomial
open GenericSpecialization

/-- Substitute `(u,v)=(t,1)` into the coefficient ring left after isolating
the first coordinate `s`. -/
noncomputable def tailMap : MvPolynomial (Fin 2) ℝ →+* ℝ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 1]

/-- The bivariate affine-chart family `Q(s,t,1)`, regarded as a polynomial in
`s` with coefficients in `ℝ[t]`. -/
noncomputable def affineFamily (Q : MvPolynomial (Fin 3) ℝ) : Family :=
  (MvPolynomial.finSuccEquiv ℝ 2 Q).map tailMap

/-- The distinguished dual point `e=[1:0:0]`. -/
def distinguishedPoint : Fin 3 → ℝ := ![1, 0, 0]

/-- Evaluation of the affine family agrees with evaluation of the original
homogeneous equation at `[s:t:1]`. -/
theorem eval_specialize_affineFamily (Q : MvPolynomial (Fin 3) ℝ)
    (s t : ℝ) :
    (specialize (affineFamily Q) t).eval s =
      MvPolynomial.eval ![s, t, 1] Q := by
  rw [affineFamily, specialize, Polynomial.eval_map]
  rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_map]
  have hcomp : (Polynomial.evalRingHom t).comp tailMap =
      MvPolynomial.eval ![t, 1] := by
    ext i : 2
    · simp [tailMap]
    · fin_cases i <;> simp [tailMap]
  rw [hcomp]
  rw [← MvPolynomial.eval_eq_eval_mv_eval' ![t, 1] s Q]
  congr 2

/-- A homogeneous polynomial evaluated at `e=[1:0:0]` is its pure `s^m`
coefficient. -/
theorem eval_distinguishedPoint_eq_coeff {m : ℕ}
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Q.IsHomogeneous m) :
    MvPolynomial.eval distinguishedPoint Q =
      MvPolynomial.coeff (Finsupp.single 0 m) Q := by
  classical
  rw [MvPolynomial.eval_eq']
  rw [Finset.sum_eq_single (Finsupp.single 0 m)]
  · simp [distinguishedPoint, Fin.prod_univ_three]
  · intro d hd hdne
    have hdegree := hQ (MvPolynomial.mem_support_iff.mp hd)
    have hsum : d 0 + d 1 + d 2 = m := by
      simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at hdegree
      rw [Finsupp.sum_fintype d (fun _ c ↦ c) (by simp)] at hdegree
      simpa only [Fin.sum_univ_three] using hdegree
    have htail : d 1 ≠ 0 ∨ d 2 ≠ 0 := by
      by_contra h
      push Not at h
      have hd0 : d 0 = m := by omega
      apply hdne
      ext i
      fin_cases i <;> simp [hd0, h.1, h.2]
    rcases htail with htail | htail
    · simp [distinguishedPoint, Fin.prod_univ_three, zero_pow htail]
    · simp [distinguishedPoint, Fin.prod_univ_three, zero_pow htail]
  · intro hnot
    rw [MvPolynomial.notMem_support_iff.mp hnot]
    simp

/-- The degree-`m` coefficient of `Q(s,t,1)` is the constant polynomial
`Q(e)`. -/
theorem coeff_affineFamily_degree {m : ℕ}
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Q.IsHomogeneous m) :
    (affineFamily Q).coeff m =
      Polynomial.C (MvPolynomial.eval distinguishedPoint Q) := by
  rw [affineFamily, Polynomial.coeff_map]
  have hcoeff : ((MvPolynomial.finSuccEquiv ℝ 2 Q).coeff m).IsHomogeneous 0 :=
    hQ.finSuccEquiv_coeff_isHomogeneous m 0 (Nat.add_zero m)
  rw [← MvPolynomial.totalDegree_zero_iff_isHomogeneous,
    MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hcoeff
  rw [hcoeff]
  simp only [tailMap, MvPolynomial.eval₂Hom_C]
  rw [eval_distinguishedPoint_eq_coeff hQ]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [Finsupp.cons_zero_eq_single_zero]

/-- The family has degree at most the homogeneous degree. -/
theorem natDegree_affineFamily_le {m : ℕ}
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Q.IsHomogeneous m) :
    (affineFamily Q).natDegree ≤ m := by
  rw [affineFamily]
  calc
    ((MvPolynomial.finSuccEquiv ℝ 2 Q).map tailMap).natDegree ≤
        (MvPolynomial.finSuccEquiv ℝ 2 Q).natDegree :=
      Polynomial.natDegree_map_le
    _ = MvPolynomial.degreeOf 0 Q := MvPolynomial.natDegree_finSuccEquiv Q
    _ ≤ Q.totalDegree := MvPolynomial.degreeOf_le_totalDegree _ _
    _ ≤ m := hQ.totalDegree_le

/-- If `Q(e)≠0`, the family and every real direction-specialization have
degree exactly `m`. -/
theorem natDegree_affineFamily_eq {m : ℕ}
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Q.IsHomogeneous m)
    (he : MvPolynomial.eval distinguishedPoint Q ≠ 0) :
    (affineFamily Q).natDegree = m := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_affineFamily_le hQ)
  rw [coeff_affineFamily_degree hQ]
  exact Polynomial.C_ne_zero.mpr he

theorem leadingCoeff_affineFamily {m : ℕ}
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Q.IsHomogeneous m)
    (he : MvPolynomial.eval distinguishedPoint Q ≠ 0) :
    (affineFamily Q).leadingCoeff =
      Polynomial.C (MvPolynomial.eval distinguishedPoint Q) := by
  rw [Polynomial.leadingCoeff, natDegree_affineFamily_eq hQ he,
    coeff_affineFamily_degree hQ]

theorem isUnit_leadingCoeff_affineFamily {m : ℕ}
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Q.IsHomogeneous m)
    (he : MvPolynomial.eval distinguishedPoint Q ≠ 0) :
    IsUnit (affineFamily Q).leadingCoeff := by
  rw [leadingCoeff_affineFamily hQ he]
  exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr he)

theorem natDegree_specialize_affineFamily {m : ℕ}
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Q.IsHomogeneous m)
    (he : MvPolynomial.eval distinguishedPoint Q ≠ 0) (t : ℝ) :
    (specialize (affineFamily Q) t).natDegree = m := by
  rw [GenericSpecialization.natDegree_specialize_eq _
    (isUnit_leadingCoeff_affineFamily hQ he),
    natDegree_affineFamily_eq hQ he]

end PlaneCurveSpecialization

end DiskRigidity.Algebraic
