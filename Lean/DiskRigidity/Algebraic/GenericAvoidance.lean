/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.GenericSpecialization

/-!
# Avoiding an auxiliary algebraic condition in a generic specialization

Besides the discriminant, Proposition 7.1 avoids ramification and other
finite exceptional images.  This file gives the required elementary
resultant statement for an arbitrary auxiliary bivariate polynomial.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace GenericAvoidance

open Polynomial
open GenericSpecialization

/-- The resultant, in the root variable `s`, of a family and an auxiliary
condition. -/
noncomputable def pairExceptionalPolynomial (P R : Family) : ParameterRing :=
  P.resultant R

/-- Parameters where the two specializations can meet, together with the
parameters where the degree of the auxiliary polynomial drops. -/
noncomputable def pairExceptionalSet (P R : Family) : Set ℝ :=
  (pairExceptionalPolynomial P R).rootSet ℝ ∪ R.leadingCoeff.rootSet ℝ

theorem pairExceptionalSet_finite (P R : Family) :
    (pairExceptionalSet P R).Finite :=
  (Polynomial.rootSet_finite _ _).union (Polynomial.rootSet_finite _ _)

theorem algebraMap_pairExceptionalPolynomial (P R : Family) :
    algebraMap ParameterRing (FractionRing ParameterRing)
        (pairExceptionalPolynomial P R) =
      (genericMap P).resultant (genericMap R) := by
  let φ := algebraMap ParameterRing (FractionRing ParameterRing)
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  rw [pairExceptionalPolynomial, genericMap]
  change φ (P.resultant R P.natDegree R.natDegree) =
    (P.map φ).resultant (R.map φ)
      (P.map φ).natDegree (R.map φ).natDegree
  rw [Polynomial.natDegree_map_eq_of_injective hφ,
    Polynomial.natDegree_map_eq_of_injective hφ]
  exact (Polynomial.resultant_map_map P R P.natDegree R.natDegree φ).symm

theorem pairExceptionalPolynomial_ne_zero
    {P R : Family} (hP : Irreducible (genericMap P))
    (hnotdvd : ¬ genericMap P ∣ genericMap R) :
    pairExceptionalPolynomial P R ≠ 0 := by
  have hcop : IsCoprime (genericMap P) (genericMap R) :=
    hP.coprime_iff_not_dvd.mpr hnotdvd
  have hres : (genericMap P).resultant (genericMap R) ≠ 0 := by
    intro hzero
    exact (Polynomial.resultant_eq_zero_iff.mp hzero).2 hcop
  intro hzero
  apply hres
  rw [← algebraMap_pairExceptionalPolynomial P R, hzero, map_zero]

theorem auxiliary_ne_zero
    {P R : Family} (hnotdvd : ¬ genericMap P ∣ genericMap R) :
    R ≠ 0 := by
  intro hR
  apply hnotdvd
  simp [genericMap, hR]

theorem eval_pairExceptionalPolynomial_eq_resultant
    (P R : Family) (hleadP : IsUnit P.leadingCoeff)
    {t : ℝ} (hleadR : R.leadingCoeff.eval t ≠ 0) :
    (pairExceptionalPolynomial P R).eval t =
      (specialize P t).resultant (specialize R t) := by
  let φ := Polynomial.evalRingHom t
  have hdegP : (P.map φ).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff φ hleadP
  have hdegR : (R.map φ).natDegree = R.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero φ hleadR
  rw [pairExceptionalPolynomial, specialize]
  change φ (P.resultant R P.natDegree R.natDegree) =
    (P.map φ).resultant (R.map φ)
      (P.map φ).natDegree (R.map φ).natDegree
  rw [hdegP, hdegR]
  exact (Polynomial.resultant_map_map P R P.natDegree R.natDegree φ).symm

/-- Outside the finite pair-exceptional set, the specialized curve equation
and auxiliary condition are coprime. -/
theorem isCoprime_specialize_of_not_mem
    {P R : Family} (hleadP : IsUnit P.leadingCoeff)
    (hP : Irreducible (genericMap P))
    (hnotdvd : ¬ genericMap P ∣ genericMap R)
    {t : ℝ} (ht : t ∉ pairExceptionalSet P R) :
    IsCoprime (specialize P t) (specialize R t) := by
  have hpair : pairExceptionalPolynomial P R ≠ 0 :=
    pairExceptionalPolynomial_ne_zero hP hnotdvd
  have hR0 : R ≠ 0 := auxiliary_ne_zero hnotdvd
  have hleadR0 : R.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hR0
  have htPair : t ∉ (pairExceptionalPolynomial P R).rootSet ℝ :=
    fun h ↦ ht (Or.inl h)
  have htLead : t ∉ R.leadingCoeff.rootSet ℝ :=
    fun h ↦ ht (Or.inr h)
  have hevalPair : (pairExceptionalPolynomial P R).eval t ≠ 0 := by
    intro hz
    exact htPair ((Polynomial.mem_rootSet_of_ne hpair).2 hz)
  have hevalLead : R.leadingCoeff.eval t ≠ 0 := by
    intro hz
    exact htLead ((Polynomial.mem_rootSet_of_ne hleadR0).2 hz)
  have hres : (specialize P t).resultant (specialize R t) ≠ 0 := by
    rwa [← eval_pairExceptionalPolynomial_eq_resultant P R hleadP hevalLead]
  by_contra hcop
  apply hres
  rw [Polynomial.resultant_eq_zero_iff]
  refine ⟨Or.inl ?_, hcop⟩
  intro hzero
  have hlc := Polynomial.leadingCoeff_map_eq_of_isUnit_leadingCoeff
    (Polynomial.evalRingHom t) hleadP
  have hmapUnit := (Polynomial.evalRingHom t).isUnit_map hleadP
  change P.map (Polynomial.evalRingHom t) = 0 at hzero
  rw [hzero, Polynomial.leadingCoeff_zero] at hlc
  exact hmapUnit.ne_zero hlc.symm

/-- Simultaneously avoid discriminant, one auxiliary resultant, and any
further finite set. -/
theorem exists_parameter_avoiding_pair
    (P R : Family)
    (bad : Set ℝ) (hbad : bad.Finite) :
    ∃ t : ℝ,
      t ∉ exceptionalSet P ∧
      t ∉ pairExceptionalSet P R ∧
      t ∉ bad := by
  have hfinite :
      (exceptionalSet P ∪ pairExceptionalSet P R ∪ bad).Finite :=
    ((exceptionalSet_finite P).union (pairExceptionalSet_finite P R)).union hbad
  obtain ⟨t, ht⟩ := hfinite.exists_notMem
  refine ⟨t, ?_, ?_, ?_⟩
  · intro h
    exact ht (Or.inl (Or.inl h))
  · intro h
    exact ht (Or.inl (Or.inr h))
  · intro h
    exact ht (Or.inr h)

end GenericAvoidance

end DiskRigidity.Algebraic
