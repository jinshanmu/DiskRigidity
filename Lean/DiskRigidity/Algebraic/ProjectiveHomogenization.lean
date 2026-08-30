/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.PlaneCurveSpecialization
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Homogenizing an affine chart of a projective plane curve

This file supplies the algebraic step used in Proposition 7.1: an irreducible
homogeneous form remains irreducible after passing to an affine chart, provided
that the chart still has the full total degree.  The proof is the elementary
homogenization argument, written explicitly so that no algebraic-geometry
black box is needed.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace ProjectiveHomogenization

open MvPolynomial Polynomial

variable {K : Type*} [Field K]

/-- Dehomogenize a form in `N+1` variables by setting its first variable to
`1`. -/
noncomputable def dehomogenizeFirstHom (N : ℕ) :
    MvPolynomial (Fin (N + 1)) K →+* MvPolynomial (Fin N) K :=
  (Polynomial.evalRingHom 1).comp (MvPolynomial.finSuccEquiv K N).toRingHom

/-- Apply first-coordinate dehomogenization to a homogeneous form. -/
noncomputable abbrev dehomogenizeFirst {N : ℕ}
    (Q : MvPolynomial (Fin (N + 1)) K) : MvPolynomial (Fin N) K :=
  dehomogenizeFirstHom N Q

/-- Homogenize a polynomial in `N` affine variables to prescribed degree
`n`, using variable `0` as the homogenizing coordinate. -/
noncomputable def homogenizeFirst {N : ℕ}
    (p : MvPolynomial (Fin N) K) (n : ℕ) :
    MvPolynomial (Fin (N + 1)) K :=
  ∑ d ∈ p.support,
    MvPolynomial.monomial (d.cons (n - d.degree)) (MvPolynomial.coeff d p)

theorem degree_cons {N : ℕ} (d : Fin N →₀ ℕ) (k : ℕ) :
    (d.cons k).degree = k + d.degree := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ]
  simp only [Finsupp.cons_zero, Finsupp.cons_succ]
  rw [← Finsupp.degree_eq_sum]

theorem homogenizeFirst_isHomogeneous {N n : ℕ}
    {p : MvPolynomial (Fin N) K} (hp : p.totalDegree ≤ n) :
    (homogenizeFirst p n).IsHomogeneous n := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro d hd
  apply MvPolynomial.isHomogeneous_monomial
  rw [Finsupp.degree_eq_sum]
  rw [Fin.sum_univ_succ]
  simp only [Finsupp.cons_zero, Finsupp.cons_succ]
  rw [← Finsupp.degree_eq_sum]
  have hdle : d.degree ≤ n :=
    (MvPolynomial.le_totalDegree hd).trans hp
  omega

theorem finSuccEquiv_monomial_cons {N : ℕ}
    (d : Fin N →₀ ℕ) (k : ℕ) (c : K) :
    MvPolynomial.finSuccEquiv K N
        (MvPolynomial.monomial (d.cons k) c) =
      Polynomial.monomial k (MvPolynomial.monomial d c) := by
  ext i e
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  simp only [MvPolynomial.coeff_monomial, Polynomial.coeff_monomial]
  simp only [Finsupp.cons_injective2.eq_iff]
  aesop

@[simp] theorem finSuccEquiv_C {N : ℕ} (c : K) :
    MvPolynomial.finSuccEquiv K N (MvPolynomial.C c) =
      Polynomial.C (MvPolynomial.C c) := by
  simp [MvPolynomial.finSuccEquiv_apply]

theorem dehomogenizeFirst_monomial_cons {N : ℕ}
    (d : Fin N →₀ ℕ) (k : ℕ) (c : K) :
    dehomogenizeFirst (MvPolynomial.monomial (d.cons k) c) =
      MvPolynomial.monomial d c := by
  change Polynomial.eval 1
      (MvPolynomial.finSuccEquiv K N
        (MvPolynomial.monomial (d.cons k) c)) = _
  rw [finSuccEquiv_monomial_cons]
  simp

@[simp] theorem dehomogenizeFirst_C {N : ℕ} (c : K) :
    dehomogenizeFirst (N := N) (MvPolynomial.C c) =
      (MvPolynomial.C c : MvPolynomial (Fin N) K) := by
  change Polynomial.eval 1
      (MvPolynomial.finSuccEquiv K N (MvPolynomial.C c)) = _
  rw [finSuccEquiv_C]
  simp

@[simp] theorem dehomogenizeFirst_X_zero {N : ℕ} :
    dehomogenizeFirst (N := N)
      (MvPolynomial.X (R := K) (0 : Fin (N + 1))) =
        (1 : MvPolynomial (Fin N) K) := by
  change Polynomial.eval 1
      (MvPolynomial.finSuccEquiv K N (MvPolynomial.X (R := K) 0)) = _
  rw [MvPolynomial.finSuccEquiv_X_zero]
  simp

@[simp] theorem dehomogenizeFirst_X_succ {N : ℕ} (i : Fin N) :
    dehomogenizeFirst (MvPolynomial.X (R := K) i.succ) =
      MvPolynomial.X (R := K) i := by
  change Polynomial.eval 1
      (MvPolynomial.finSuccEquiv K N (MvPolynomial.X (R := K) i.succ)) = _
  rw [MvPolynomial.finSuccEquiv_X_succ]
  simp

theorem dehomogenizeFirst_homogenizeFirst {N n : ℕ}
    (p : MvPolynomial (Fin N) K) :
    dehomogenizeFirst (homogenizeFirst p n) = p := by
  classical
  change dehomogenizeFirstHom N (homogenizeFirst p n) = p
  rw [homogenizeFirst, map_sum]
  simp_rw [dehomogenizeFirst_monomial_cons]
  exact MvPolynomial.support_sum_monomial_coeff p

theorem coeff_dehomogenizeFirst_of_isHomogeneous {N n : ℕ}
    {Q : MvPolynomial (Fin (N + 1)) K} (hQ : Q.IsHomogeneous n)
    (d : Fin N →₀ ℕ) (hd : d.degree ≤ n) :
    MvPolynomial.coeff d (dehomogenizeFirst Q) =
      MvPolynomial.coeff (d.cons (n - d.degree)) Q := by
  classical
  let P := MvPolynomial.finSuccEquiv K N Q
  have hdeg : P.natDegree < n + 1 := by
    dsimp only [P]
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact lt_of_le_of_lt
      ((MvPolynomial.degreeOf_le_totalDegree Q 0).trans hQ.totalDegree_le)
      (Nat.lt_succ_self n)
  change MvPolynomial.coeff d (Polynomial.eval 1 P) = _
  rw [Polynomial.eval_eq_sum_range' hdeg]
  simp only [one_pow, mul_one, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single (n - d.degree)]
  · exact MvPolynomial.finSuccEquiv_coeff_coeff d Q (n - d.degree)
  · intro i hi hne
    rw [MvPolynomial.finSuccEquiv_coeff_coeff]
    apply hQ.coeff_eq_zero
    rw [degree_cons]
    omega
  · intro hnot
    exfalso
    apply hnot
    simp only [Finset.mem_range]
    omega

theorem totalDegree_dehomogenizeFirst_le {N n : ℕ}
    {Q : MvPolynomial (Fin (N + 1)) K} (hQ : Q.IsHomogeneous n) :
    (dehomogenizeFirst Q).totalDegree ≤ n := by
  classical
  let P := MvPolynomial.finSuccEquiv K N Q
  have hdeg : P.natDegree < n + 1 := by
    dsimp only [P]
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact lt_of_le_of_lt
      ((MvPolynomial.degreeOf_le_totalDegree Q 0).trans hQ.totalDegree_le)
      (Nat.lt_succ_self n)
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro d hd
  change d.degree ≤ n
  have hdcoeff := MvPolynomial.mem_support_iff.mp hd
  change MvPolynomial.coeff d (Polynomial.eval 1 P) ≠ 0 at hdcoeff
  rw [Polynomial.eval_eq_sum_range' hdeg] at hdcoeff
  simp only [one_pow, mul_one, MvPolynomial.coeff_sum] at hdcoeff
  obtain ⟨i, hi, hci⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdcoeff
  rw [MvPolynomial.finSuccEquiv_coeff_coeff] at hci
  have hdegree : (d.cons i).degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hQ hci
  rw [degree_cons] at hdegree
  omega

theorem eq_of_isHomogeneous_of_dehomogenizeFirst_eq {N n : ℕ}
    {P Q : MvPolynomial (Fin (N + 1)) K}
    (hP : P.IsHomogeneous n) (hQ : Q.IsHomogeneous n)
    (hdehom : dehomogenizeFirst P = dehomogenizeFirst Q) :
    P = Q := by
  ext e
  by_cases he : e.degree = n
  · have hsplit : e 0 + e.tail.degree = n := by
      rw [← degree_cons, Finsupp.cons_tail]
      exact he
    have htail : e.tail.degree ≤ n := by omega
    have hpadding : n - e.tail.degree = e 0 := by omega
    calc
      MvPolynomial.coeff e P =
          MvPolynomial.coeff (e.tail.cons (n - e.tail.degree)) P := by
            rw [hpadding, Finsupp.cons_tail]
      _ = MvPolynomial.coeff e.tail (dehomogenizeFirst P) :=
        (coeff_dehomogenizeFirst_of_isHomogeneous hP e.tail htail).symm
      _ = MvPolynomial.coeff e.tail (dehomogenizeFirst Q) := by rw [hdehom]
      _ = MvPolynomial.coeff (e.tail.cons (n - e.tail.degree)) Q :=
        coeff_dehomogenizeFirst_of_isHomogeneous hQ e.tail htail
      _ = MvPolynomial.coeff e Q := by rw [hpadding, Finsupp.cons_tail]
  · rw [hP.coeff_eq_zero he, hQ.coeff_eq_zero he]

theorem homogenizeFirst_dehomogenizeFirst {N n : ℕ}
    {Q : MvPolynomial (Fin (N + 1)) K} (hQ : Q.IsHomogeneous n) :
    homogenizeFirst (dehomogenizeFirst Q) n = Q := by
  apply eq_of_isHomogeneous_of_dehomogenizeFirst_eq
    (homogenizeFirst_isHomogeneous (totalDegree_dehomogenizeFirst_le hQ)) hQ
  rw [dehomogenizeFirst_homogenizeFirst]

theorem homogenizeFirst_mul {N a b : ℕ}
    {p q : MvPolynomial (Fin N) K}
    (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) :
    homogenizeFirst (p * q) (a + b) =
      homogenizeFirst p a * homogenizeFirst q b := by
  apply eq_of_isHomogeneous_of_dehomogenizeFirst_eq
  · apply homogenizeFirst_isHomogeneous
    exact (MvPolynomial.totalDegree_mul p q).trans (Nat.add_le_add hp hq)
  · exact (homogenizeFirst_isHomogeneous hp).mul
      (homogenizeFirst_isHomogeneous hq)
  · change dehomogenizeFirstHom N (homogenizeFirst (p * q) (a + b)) =
      dehomogenizeFirstHom N
        (homogenizeFirst p a * homogenizeFirst q b)
    rw [map_mul]
    exact (dehomogenizeFirst_homogenizeFirst (n := a + b) (p * q)).trans <|
      (congrArg₂ (fun x y ↦ x * y)
        (dehomogenizeFirst_homogenizeFirst (n := a) p)
        (dehomogenizeFirst_homogenizeFirst (n := b) q)).symm

/-- An irreducible homogeneous form stays irreducible after setting the first
coordinate to `1`, as soon as that affine chart retains its full total degree.
This is the elementary dehomogenization lemma used for the dual curve. -/
theorem irreducible_dehomogenizeFirst_of_totalDegree_eq {N n : ℕ}
    {Q : MvPolynomial (Fin (N + 1)) K}
    (hQhom : Q.IsHomogeneous n) (hQirr : Irreducible Q)
    (hn : n ≠ 0)
    (hdegree : (dehomogenizeFirst Q).totalDegree = n) :
    Irreducible (dehomogenizeFirst Q) := by
  let p := dehomogenizeFirst Q
  have hp0 : p ≠ 0 := by
    intro hp
    have : p.totalDegree = 0 := by rw [hp, MvPolynomial.totalDegree_zero]
    rw [hdegree] at this
    exact hn this
  refine ⟨?_, ?_⟩
  · intro hpunit
    have hpdegree :=
      (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hpunit).2
    rw [hdegree] at hpdegree
    exact hn hpdegree
  · intro a b hab
    have hab0 : a * b ≠ 0 := by
      rw [← hab]
      simpa [p] using hp0
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hab0
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hab0
    have habdegree : a.totalDegree + b.totalDegree = n := by
      rw [← MvPolynomial.totalDegree_mul_of_isDomain ha0 hb0, ← hab]
      exact hdegree
    have hfactor : Q =
        homogenizeFirst a a.totalDegree *
          homogenizeFirst b b.totalDegree := by
      rw [← homogenizeFirst_mul (le_refl _) (le_refl _), habdegree,
        ← hab, homogenizeFirst_dehomogenizeFirst hQhom]
    rcases hQirr.isUnit_or_isUnit hfactor with ha | hb
    · left
      have hmap := ha.map (dehomogenizeFirstHom N)
      have heval : dehomogenizeFirstHom N
          (homogenizeFirst a a.totalDegree) = a :=
        dehomogenizeFirst_homogenizeFirst a
      rw [heval] at hmap
      exact hmap
    · right
      have hmap := hb.map (dehomogenizeFirstHom N)
      have heval : dehomogenizeFirstHom N
          (homogenizeFirst b b.totalDegree) = b :=
        dehomogenizeFirst_homogenizeFirst b
      rw [heval] at hmap
      exact hmap

section PlaneCurve

open GenericSpecialization PlaneCurveSpecialization

/-- Rename `(s,u,v)` as `(v,s,u)`, so that the affine chart `v=1` is the
first-coordinate dehomogenization used above. -/
def chartRotation : Fin 3 ≃ Fin 3 :=
  (Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1)

@[simp] theorem chartRotation_zero : chartRotation 0 = 1 := by decide
@[simp] theorem chartRotation_one : chartRotation 1 = 2 := by decide
@[simp] theorem chartRotation_two : chartRotation 2 = 0 := by decide

/-- Rotate a ternary form so its last coordinate becomes the homogenizing
coordinate of the first-coordinate affine chart. -/
noncomputable def rotateForAffineChart
    (Q : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.renameEquiv ℝ chartRotation Q

/-- The canonical equivalence between bivariate polynomials in `(s,t)` and
polynomials in `s` with coefficients in `ℝ[t]`. -/
noncomputable def affineChartEquiv :
    MvPolynomial (Fin 2) ℝ ≃ₐ[ℝ] Family :=
  (MvPolynomial.finSuccEquiv ℝ 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)))

@[simp] theorem affineChartEquiv_C (r : ℝ) :
    affineChartEquiv (MvPolynomial.C r) =
      Polynomial.C (Polynomial.C r) := by
  simpa [Polynomial.algebraMap_apply] using affineChartEquiv.commutes r

@[simp] theorem affineChartEquiv_X_zero :
    affineChartEquiv (MvPolynomial.X (R := ℝ) (0 : Fin 2)) =
      Polynomial.X := by
  change Polynomial.map
      (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).toRingEquiv.toRingHom
      (MvPolynomial.finSuccEquiv ℝ 1 (MvPolynomial.X (R := ℝ) 0)) = _
  rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]

@[simp] theorem affineChartEquiv_X_one :
    affineChartEquiv (MvPolynomial.X (R := ℝ) (1 : Fin 2)) =
      Polynomial.C Polynomial.X := by
  have hindex : (1 : Fin 2) = (0 : Fin 1).succ := by decide
  rw [hindex]
  change Polynomial.map
      (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).toRingEquiv.toRingHom
      (MvPolynomial.finSuccEquiv ℝ 1
        (MvPolynomial.X (R := ℝ) (0 : Fin 1).succ)) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  simp [MvPolynomial.uniqueAlgEquiv]

@[simp] theorem dehomogenizeFirst_fin3_X_one :
    dehomogenizeFirstHom 2 (MvPolynomial.X (R := ℝ) (1 : Fin 3)) =
      MvPolynomial.X (R := ℝ) (0 : Fin 2) := by
  have hindex : (1 : Fin 3) = (0 : Fin 2).succ := by decide
  rw [hindex]
  exact dehomogenizeFirst_X_succ 0

@[simp] theorem dehomogenizeFirst_fin3_X_two :
    dehomogenizeFirstHom 2 (MvPolynomial.X (R := ℝ) (2 : Fin 3)) =
      MvPolynomial.X (R := ℝ) (1 : Fin 2) := by
  have hindex : (2 : Fin 3) = (1 : Fin 2).succ := by decide
  rw [hindex]
  exact dehomogenizeFirst_X_succ 1

/-- Convert a ternary homogeneous form to a polynomial family in the affine
support parameter. -/
noncomputable def affineFamilyHom :
    MvPolynomial (Fin 3) ℝ →+* Family :=
  (Polynomial.mapRingHom tailMap).comp
    (MvPolynomial.finSuccEquiv ℝ 2).toRingHom

@[simp] theorem affineFamilyHom_C (r : ℝ) :
    affineFamilyHom (MvPolynomial.C r) =
      Polynomial.C (Polynomial.C r) := by
  simp [affineFamilyHom, tailMap]

@[simp] theorem affineFamilyHom_X_zero :
    affineFamilyHom (MvPolynomial.X (R := ℝ) (0 : Fin 3)) =
      Polynomial.X := by
  change Polynomial.map tailMap
      (MvPolynomial.finSuccEquiv ℝ 2
        (MvPolynomial.X (R := ℝ) (0 : Fin 3))) = _
  rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]

@[simp] theorem affineFamilyHom_X_one :
    affineFamilyHom (MvPolynomial.X (R := ℝ) (1 : Fin 3)) =
      Polynomial.C Polynomial.X := by
  have hindex : (1 : Fin 3) = (0 : Fin 2).succ := by decide
  rw [hindex]
  change Polynomial.map tailMap
      (MvPolynomial.finSuccEquiv ℝ 2
        (MvPolynomial.X (R := ℝ) (0 : Fin 2).succ)) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  simp [tailMap]

@[simp] theorem affineFamilyHom_X_two :
    affineFamilyHom (MvPolynomial.X (R := ℝ) (2 : Fin 3)) = 1 := by
  have hindex : (2 : Fin 3) = (1 : Fin 2).succ := by decide
  rw [hindex]
  change Polynomial.map tailMap
      (MvPolynomial.finSuccEquiv ℝ 2
        (MvPolynomial.X (R := ℝ) (1 : Fin 2).succ)) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  simp [tailMap]

/-- The affine-chart conversion defined through dehomogenization and the
canonical bivariate-polynomial equivalence. -/
noncomputable def affineChartHom :
    MvPolynomial (Fin 3) ℝ →+* Family :=
  affineChartEquiv.toRingHom.comp <|
    (dehomogenizeFirstHom 2).comp
      (MvPolynomial.renameEquiv ℝ chartRotation).toRingHom

theorem affineChartHom_eq_affineFamilyHom :
    affineChartHom = affineFamilyHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [affineChartHom]
  · intro i
    fin_cases i <;>
      simp [affineChartHom]

/-- The abstract dehomogenization is exactly the concrete family `Q(s,t,1)`
used in the proof of Proposition 7.1. -/
theorem affineChartEquiv_dehomogenize_rotate
    (Q : MvPolynomial (Fin 3) ℝ) :
    affineChartEquiv (dehomogenizeFirst (rotateForAffineChart Q)) =
      affineFamily Q := by
  change affineChartHom Q = affineFamilyHom Q
  rw [affineChartHom_eq_affineFamilyHom]

theorem rotateForAffineChart_isHomogeneous {m : ℕ}
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Q.IsHomogeneous m) :
    (rotateForAffineChart Q).IsHomogeneous m := by
  exact hQ.rename_isHomogeneous

theorem rotateForAffineChart_irreducible
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Irreducible Q) :
    Irreducible (rotateForAffineChart Q) := by
  exact hQ.map (MvPolynomial.renameEquiv ℝ chartRotation).toMulEquiv

theorem natDegree_affineChartEquiv (p : MvPolynomial (Fin 2) ℝ) :
    (affineChartEquiv p).natDegree =
      (MvPolynomial.finSuccEquiv ℝ 1 p).natDegree := by
  change (Polynomial.map
      (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).toRingEquiv.toRingHom
        (MvPolynomial.finSuccEquiv ℝ 1 p)).natDegree = _
  exact Polynomial.natDegree_map_eq_of_injective
    (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).injective _

theorem totalDegree_dehomogenize_rotate_eq {m : ℕ}
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Q.IsHomogeneous m)
    (he : MvPolynomial.eval distinguishedPoint Q ≠ 0) :
    (dehomogenizeFirst (rotateForAffineChart Q)).totalDegree = m := by
  let p := dehomogenizeFirst (rotateForAffineChart Q)
  have hupper : p.totalDegree ≤ m :=
    totalDegree_dehomogenizeFirst_le
      (rotateForAffineChart_isHomogeneous hQ)
  have hfamily : affineChartEquiv p = affineFamily Q :=
    affineChartEquiv_dehomogenize_rotate Q
  have houter : (MvPolynomial.finSuccEquiv ℝ 1 p).natDegree = m := by
    rw [← natDegree_affineChartEquiv, hfamily,
      PlaneCurveSpecialization.natDegree_affineFamily_eq hQ he]
  rw [MvPolynomial.natDegree_finSuccEquiv] at houter
  exact le_antisymm hupper <| houter ▸
    MvPolynomial.degreeOf_le_totalDegree p 0

/-- The concrete two-variable family `Q(s,t,1)` is irreducible whenever the
projective form is irreducible, homogeneous of positive degree, and does not
vanish at `[1:0:0]`. -/
theorem irreducible_affineFamily {m : ℕ}
    {Q : MvPolynomial (Fin 3) ℝ}
    (hQhom : Q.IsHomogeneous m) (hQirr : Irreducible Q)
    (hm : m ≠ 0)
    (he : MvPolynomial.eval distinguishedPoint Q ≠ 0) :
    Irreducible (affineFamily Q) := by
  have hdehom : Irreducible
      (dehomogenizeFirst (rotateForAffineChart Q)) :=
    irreducible_dehomogenizeFirst_of_totalDegree_eq
      (rotateForAffineChart_isHomogeneous hQhom)
      (rotateForAffineChart_irreducible hQirr) hm
      (totalDegree_dehomogenize_rotate_eq hQhom he)
  have hmap := hdehom.map affineChartEquiv.toMulEquiv
  change Irreducible
      (affineChartEquiv (dehomogenizeFirst (rotateForAffineChart Q))) at hmap
  rw [affineChartEquiv_dehomogenize_rotate] at hmap
  exact hmap

/-- Divisibility detected in the affine chart `v = 1` lifts back to
projective divisibility for homogeneous forms, provided the divisor has not
lost degree in that chart. -/
theorem dvd_of_affineFamily_dvd {m n : ℕ}
    {P Q : MvPolynomial (Fin 3) ℝ}
    (hP : P.IsHomogeneous m) (hQ : Q.IsHomogeneous n)
    (heP : MvPolynomial.eval distinguishedPoint P ≠ 0)
    (hdiv : affineFamily P ∣ affineFamily Q) :
    P ∣ Q := by
  by_cases hQzero : Q = 0
  · rw [hQzero]
    exact dvd_zero P
  let p := dehomogenizeFirst (rotateForAffineChart P)
  let q := dehomogenizeFirst (rotateForAffineChart Q)
  have hdivDehom : p ∣ q := by
    apply (map_dvd_iff affineChartEquiv).mp
    simpa only [p, q, affineChartEquiv_dehomogenize_rotate] using hdiv
  obtain ⟨a, ha⟩ := hdivDehom
  have hpDegree : p.totalDegree = m :=
    totalDegree_dehomogenize_rotate_eq hP heP
  have hp0 : p ≠ 0 := by
    intro hp
    have hp' : dehomogenizeFirst (rotateForAffineChart P) = 0 := by
      simpa only [p] using hp
    have hPzero : rotateForAffineChart P = 0 := by
      rw [← homogenizeFirst_dehomogenizeFirst
        (rotateForAffineChart_isHomogeneous hP), hp']
      simp [homogenizeFirst]
    have : P = 0 :=
      (MvPolynomial.renameEquiv ℝ chartRotation).injective hPzero
    exact heP (by rw [this, map_zero])
  have hq0 : q ≠ 0 := by
    intro hq
    have hq' : dehomogenizeFirst (rotateForAffineChart Q) = 0 := by
      simpa only [q] using hq
    have hrotQzero : rotateForAffineChart Q = 0 := by
      rw [← homogenizeFirst_dehomogenizeFirst
        (rotateForAffineChart_isHomogeneous hQ), hq']
      simp [homogenizeFirst]
    exact hQzero ((MvPolynomial.renameEquiv ℝ chartRotation).injective hrotQzero)
  have ha0 : a ≠ 0 := by
    intro hazero
    apply hq0
    rw [ha, hazero, mul_zero]
  have hqDegree : q.totalDegree = p.totalDegree + a.totalDegree := by
    rw [ha, MvPolynomial.totalDegree_mul_of_isDomain hp0 ha0]
  have hqDegreeLe : q.totalDegree ≤ n :=
    totalDegree_dehomogenizeFirst_le
      (rotateForAffineChart_isHomogeneous hQ)
  have hmn : m ≤ n := by omega
  have haDegree : a.totalDegree ≤ n - m := by omega
  have hrotDiv : rotateForAffineChart P ∣ rotateForAffineChart Q := by
    refine ⟨homogenizeFirst a (n - m), ?_⟩
    calc
      rotateForAffineChart Q = homogenizeFirst q n :=
        (homogenizeFirst_dehomogenizeFirst
          (rotateForAffineChart_isHomogeneous hQ)).symm
      _ = homogenizeFirst (p * a) (m + (n - m)) := by
        rw [← ha, Nat.add_sub_of_le hmn]
      _ = homogenizeFirst p m * homogenizeFirst a (n - m) :=
        homogenizeFirst_mul (hpDegree.le) haDegree
      _ = rotateForAffineChart P * homogenizeFirst a (n - m) := by
        rw [homogenizeFirst_dehomogenizeFirst
          (rotateForAffineChart_isHomogeneous hP)]
  exact (map_dvd_iff (MvPolynomial.renameEquiv ℝ chartRotation)).mp hrotDiv

end PlaneCurve

end ProjectiveHomogenization

end DiskRigidity.Algebraic
