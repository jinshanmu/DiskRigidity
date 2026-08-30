/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Factors of homogeneous polynomials

Over an integral domain, every nonzero factor of a nonzero homogeneous
multivariable polynomial is itself homogeneous.  The proof records total
degree by adjoining one scaling variable.  The highest and lowest powers of
that variable are additive under multiplication, so a product supported in a
single degree can have no inhomogeneous factor.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace HomogeneousFactor

open MvPolynomial Polynomial

variable {σ R : Type*} [CommRing R]

/-- Simultaneously replace every variable `X i` by `X i * T`, where `T` is
the variable of the outer polynomial ring.  Thus the exponent of `T` records
the total degree of an inner monomial. -/
noncomputable def scalingFamily :
    MvPolynomial σ R →+* Polynomial (MvPolynomial σ R) :=
  MvPolynomial.eval₂Hom
    (Polynomial.C.comp MvPolynomial.C)
    (fun i ↦ Polynomial.C (MvPolynomial.X i) * Polynomial.X)

theorem eval_one_scalingFamily (P : MvPolynomial σ R) :
    Polynomial.eval 1 (scalingFamily P) = P := by
  have hhom : (Polynomial.evalRingHom (1 : MvPolynomial σ R)).comp
      scalingFamily = RingHom.id (MvPolynomial σ R) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [scalingFamily]
    · intro i
      simp [scalingFamily]
  exact DFunLike.congr_fun hhom P

theorem scalingFamily_ne_zero {P : MvPolynomial σ R} (hP : P ≠ 0) :
    scalingFamily P ≠ 0 := by
  intro h
  apply hP
  rw [← eval_one_scalingFamily P, h]
  simp

theorem scalingFamily_monomial (d : σ →₀ ℕ) (r : R) :
    scalingFamily (MvPolynomial.monomial d r) =
      Polynomial.C (MvPolynomial.monomial d r) * Polynomial.X ^ d.degree := by
  classical
  rw [scalingFamily, MvPolynomial.eval₂Hom_monomial]
  simp only [RingHom.coe_comp, Function.comp_apply, mul_pow, Finsupp.prod,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    MvPolynomial.monomial_eq, map_mul]
  simp_rw [← map_pow]
  rw [← map_prod]
  rw [← Finsupp.degree_apply]
  ring

/-- The scaling family of a homogeneous polynomial is a single outer
monomial. -/
theorem scalingFamily_of_isHomogeneous {P : MvPolynomial σ R} {n : ℕ}
    (hP : P.IsHomogeneous n) :
    scalingFamily P = Polynomial.C P * Polynomial.X ^ n := by
  induction hP using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add P Q hP hQ ihP ihQ => simp [ihP, ihQ, add_mul]
  | monomial d r hd =>
      rw [scalingFamily_monomial,
        show d.degree = n by
          rw [Finsupp.degree_eq_weight_one]
          simpa only [Pi.one_def] using hd]

/-- Coefficients of the scaling family keep precisely the monomials of the
corresponding total degree. -/
theorem coeff_coeff_scalingFamily (P : MvPolynomial σ R)
    (d : σ →₀ ℕ) (n : ℕ) :
    MvPolynomial.coeff d ((scalingFamily P).coeff n) =
      if d.degree = n then MvPolynomial.coeff d P else 0 := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d' r =>
      rw [scalingFamily_monomial]
      by_cases hdn : d.degree = n
      · subst n
        by_cases hdd : d = d'
        · subst d'
          simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        · by_cases hdeg : d.degree = d'.degree
          · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
              MvPolynomial.coeff_monomial, Ne.symm hdd, hdeg]
          · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
              MvPolynomial.coeff_monomial, Ne.symm hdd, hdeg]
      · by_cases hdd : d = d'
        · subst d'
          simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            hdn, Ne.symm hdn]
        · by_cases hdeg : n = d'.degree
          · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
              MvPolynomial.coeff_monomial, Ne.symm hdd, hdeg]
          · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
              hdn, hdeg]
  | add P Q ihP ihQ =>
      simp only [map_add, Polynomial.coeff_add, MvPolynomial.coeff_add,
        ihP, ihQ]
      by_cases hd : d.degree = n <;> simp [hd]

private theorem eq_C_mul_X_pow_of_natTrailingDegree_eq_natDegree
    {A : Type*} [Semiring A] {p : A[X]} (_hp : p ≠ 0)
    (hdegree : p.natTrailingDegree = p.natDegree) :
    p = Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree := by
  ext n
  obtain hn | rfl | hn := lt_trichotomy n p.natDegree
  · rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree]
    · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hn.ne]
    · rwa [hdegree]
  · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_natDegree]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn]
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hn.ne']

private theorem isHomogeneous_of_scalingFamily_eq_C_mul_X_pow
    {P A : MvPolynomial σ R} {n : ℕ}
    (hscale : scalingFamily P = Polynomial.C A * Polynomial.X ^ n) :
    P.IsHomogeneous n := by
  intro d hd
  have hdegree : d.degree = n := by
    by_contra hdegree
    have hcoeff := congrArg (fun p : Polynomial (MvPolynomial σ R) ↦
        MvPolynomial.coeff d (p.coeff d.degree)) hscale
    rw [coeff_coeff_scalingFamily, if_pos rfl,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg hdegree, mul_zero, MvPolynomial.coeff_zero] at hcoeff
    exact hd hcoeff
  rw [Finsupp.degree_eq_weight_one] at hdegree
  simpa only [Pi.one_def] using hdegree

/-- A nonzero factor of a nonzero homogeneous polynomial over an integral
domain is homogeneous.  The degree is produced existentially because a
factor need not have the same degree as the product. -/
theorem exists_isHomogeneous_of_mul_isHomogeneous
    [IsDomain R] {P Q : MvPolynomial σ R} {n : ℕ}
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hPQ : (P * Q).IsHomogeneous n) :
    ∃ m : ℕ, P.IsHomogeneous m := by
  let p := scalingFamily P
  let q := scalingFamily Q
  have hp : p ≠ 0 := scalingFamily_ne_zero hP
  have hq : q ≠ 0 := scalingFamily_ne_zero hQ
  have hpq : p * q = Polynomial.C (P * Q) * Polynomial.X ^ n := by
    rw [← map_mul, scalingFamily_of_isHomogeneous hPQ]
  have hPQzero : P * Q ≠ 0 := mul_ne_zero hP hQ
  have hdegreeRhs :
      (Polynomial.C (P * Q) * Polynomial.X ^ n).natDegree = n := by
    exact Polynomial.natDegree_C_mul_X_pow n (P * Q) hPQzero
  have htrailRhs :
      (Polynomial.C (P * Q) * Polynomial.X ^ n).natTrailingDegree = n := by
    rw [Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.natTrailingDegree_monomial hPQzero]
  have hdegreeSum : p.natDegree + q.natDegree = n := by
    rw [← Polynomial.natDegree_mul hp hq, hpq, hdegreeRhs]
  have htrailSum : p.natTrailingDegree + q.natTrailingDegree = n := by
    rw [← Polynomial.natTrailingDegree_mul hp hq, hpq, htrailRhs]
  have hpDegree : p.natTrailingDegree = p.natDegree := by
    have hpLe := Polynomial.natTrailingDegree_le_natDegree p
    have hqLe := Polynomial.natTrailingDegree_le_natDegree q
    omega
  refine ⟨p.natDegree, ?_⟩
  apply isHomogeneous_of_scalingFamily_eq_C_mul_X_pow
  exact eq_C_mul_X_pow_of_natTrailingDegree_eq_natDegree hp hpDegree

/-- Divisibility form of `exists_isHomogeneous_of_mul_isHomogeneous`. -/
theorem exists_isHomogeneous_of_dvd
    [IsDomain R] {P H : MvPolynomial σ R} {n : ℕ}
    (hP : P ≠ 0) (hH : H ≠ 0) (hdiv : P ∣ H)
    (hhom : H.IsHomogeneous n) :
    ∃ m : ℕ, P.IsHomogeneous m := by
  obtain ⟨Q, rfl⟩ := hdiv
  have hQ : Q ≠ 0 := by
    intro h
    apply hH
    simp [h]
  exact exists_isHomogeneous_of_mul_isHomogeneous hP hQ hhom

end HomogeneousFactor

end DiskRigidity.Algebraic
