/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib

/-!
# Generic one-parameter specializations of plane curves

For a polynomial `P(s,t)` viewed as a polynomial in `s` with coefficients in
`R[t]`, the resultant of `P` and its `s`-derivative is a polynomial in `t`.
This file proves directly that the resultant is nonzero when `P` is
irreducible over the function field `Frac(R[t])` in characteristic zero.  Its
real zero set is therefore finite, and outside that set the specialization in
`t` is squarefree.  This is the discriminant-exception step used in
Proposition 7.1.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace GenericSpecialization

open Polynomial

/-- The coefficient ring of polynomials in the specialization parameter. -/
abbrev ParameterRing := ℝ[X]

/-- A bivariate polynomial, with `s` the outer variable and `t` the
coefficient-ring variable. -/
abbrev Family := Polynomial ParameterRing

/-- Specialize the parameter `t`, retaining a real polynomial in `s`. -/
noncomputable def specialize (P : Family) (t : ℝ) : ℝ[X] :=
  P.map (Polynomial.evalRingHom t)

/-- Extend the coefficient ring from `R[t]` to its function field. -/
noncomputable def genericMap (P : Family) :
    Polynomial (FractionRing ParameterRing) :=
  P.map (algebraMap ParameterRing (FractionRing ParameterRing))

/-- The exceptional-parameter polynomial: the resultant in the `s`
variable of `P` and its derivative. -/
noncomputable def exceptionalPolynomial (P : Family) : ParameterRing :=
  P.resultant P.derivative

/-- The exceptional real parameter set. -/
noncomputable def exceptionalSet (P : Family) : Set ℝ :=
  (exceptionalPolynomial P).rootSet ℝ

theorem exceptionalSet_finite (P : Family) : (exceptionalSet P).Finite :=
  Polynomial.rootSet_finite _ _

/-- Mapping the resultant to the function field gives the resultant of the
generic polynomial and its derivative. -/
theorem algebraMap_exceptionalPolynomial (P : Family) :
    algebraMap ParameterRing (FractionRing ParameterRing)
        (exceptionalPolynomial P) =
      (genericMap P).resultant (genericMap P).derivative := by
  let φ := algebraMap ParameterRing (FractionRing ParameterRing)
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  rw [exceptionalPolynomial, genericMap, Polynomial.derivative_map]
  change φ (P.resultant P.derivative P.natDegree P.derivative.natDegree) =
    (P.map φ).resultant (P.derivative.map φ)
      (P.map φ).natDegree (P.derivative.map φ).natDegree
  rw [Polynomial.natDegree_map_eq_of_injective hφ,
    Polynomial.natDegree_map_eq_of_injective hφ]
  exact (Polynomial.resultant_map_map P P.derivative P.natDegree
    P.derivative.natDegree φ).symm

/-- Characteristic-zero irreducibility of the generic polynomial makes the
exceptional resultant nonzero. -/
theorem exceptionalPolynomial_ne_zero_of_generic_irreducible
    {P : Family} (hP : Irreducible (genericMap P)) :
    exceptionalPolynomial P ≠ 0 := by
  have hsep : (genericMap P).Separable := hP.separable
  have hcop : IsCoprime (genericMap P) (genericMap P).derivative :=
    (Polynomial.separable_def _).mp hsep
  have hres : (genericMap P).resultant (genericMap P).derivative ≠ 0 := by
    intro hzero
    exact (Polynomial.resultant_eq_zero_iff.mp hzero).2 hcop
  intro hzero
  apply hres
  rw [← algebraMap_exceptionalPolynomial P, hzero, map_zero]

/-- Gauss's lemma: an irreducible positive-degree family remains irreducible
over the parameter function field. -/
theorem genericMap_irreducible_of_irreducible {P : Family}
    (hP : Irreducible P) (hdegree : P.natDegree ≠ 0) :
    Irreducible (genericMap P) := by
  exact (hP.isPrimitive hdegree).irreducible_iff_irreducible_map_fraction_map.mp hP

/-- Consequently irreducibility already over `ℝ[t,s]` makes the exceptional
resultant nonzero. -/
theorem exceptionalPolynomial_ne_zero_of_irreducible {P : Family}
    (hP : Irreducible P) (hdegree : P.natDegree ≠ 0) :
    exceptionalPolynomial P ≠ 0 :=
  exceptionalPolynomial_ne_zero_of_generic_irreducible
    (genericMap_irreducible_of_irreducible hP hdegree)

/-- A unit leading coefficient is preserved by every real specialization, so
the degree in `s` never drops. -/
theorem natDegree_specialize_eq (P : Family)
    (hlead : IsUnit P.leadingCoeff) (t : ℝ) :
    (specialize P t).natDegree = P.natDegree := by
  exact Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff _ hlead

/-- Evaluation of the exceptional polynomial is the resultant of the
specialized polynomial and its derivative. -/
theorem eval_exceptionalPolynomial_eq_resultant (P : Family)
    (hlead : IsUnit P.leadingCoeff) (t : ℝ) :
    (exceptionalPolynomial P).eval t =
      (specialize P t).resultant (specialize P t).derivative := by
  let φ := Polynomial.evalRingHom t
  have hdeg : (P.map φ).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff φ hlead
  have hddeg : (P.derivative.map φ).natDegree = P.derivative.natDegree := by
    rw [← Polynomial.derivative_map, Polynomial.natDegree_derivative,
      Polynomial.natDegree_derivative, hdeg]
  rw [exceptionalPolynomial, specialize, Polynomial.derivative_map]
  change φ (P.resultant P.derivative P.natDegree P.derivative.natDegree) =
    (P.map φ).resultant (P.derivative.map φ)
      (P.map φ).natDegree (P.derivative.map φ).natDegree
  rw [hdeg, hddeg]
  exact (Polynomial.resultant_map_map P P.derivative P.natDegree
    P.derivative.natDegree φ).symm

/-- Outside the finite resultant zero set, specialization is separable. -/
theorem separable_specialize_of_not_mem_exceptional
    {P : Family} (hlead : IsUnit P.leadingCoeff)
    (hPgen : Irreducible (genericMap P)) {t : ℝ}
    (ht : t ∉ exceptionalSet P) :
    (specialize P t).Separable := by
  have hex : exceptionalPolynomial P ≠ 0 :=
    exceptionalPolynomial_ne_zero_of_generic_irreducible hPgen
  have heval : (exceptionalPolynomial P).eval t ≠ 0 := by
    intro hz
    apply ht
    exact (Polynomial.mem_rootSet_of_ne hex).2 (by simpa using hz)
  have hres : (specialize P t).resultant
      (specialize P t).derivative ≠ 0 := by
    rwa [← eval_exceptionalPolynomial_eq_resultant P hlead t]
  rw [Polynomial.separable_def]
  by_contra hcop
  apply hres
  rw [Polynomial.resultant_eq_zero_iff]
  refine ⟨Or.inl ?_, hcop⟩
  intro hs0
  have hlc := Polynomial.leadingCoeff_map_eq_of_isUnit_leadingCoeff
    (Polynomial.evalRingHom t) hlead
  rw [← specialize, hs0, Polynomial.leadingCoeff_zero] at hlc
  exact ((Polynomial.evalRingHom t).isUnit_map hlead).ne_zero hlc.symm

/-- Hence the specialized roots have no repetitions. -/
theorem roots_nodup_of_not_mem_exceptional
    {P : Family} (hlead : IsUnit P.leadingCoeff)
    (hPgen : Irreducible (genericMap P)) {t : ℝ}
    (ht : t ∉ exceptionalSet P) :
    (specialize P t).roots.Nodup :=
  Polynomial.nodup_roots
    (separable_specialize_of_not_mem_exceptional hlead hPgen ht)

/-- One may simultaneously avoid the discriminant directions and any other
finite exceptional set (singular, ramification, or forbidden-contact
directions). -/
theorem exists_parameter_avoiding
    {P : Family} (hPgen : Irreducible (genericMap P))
    (bad : Set ℝ) (hbad : bad.Finite) :
    ∃ t : ℝ, t ∉ exceptionalSet P ∧ t ∉ bad := by
  have hex : exceptionalPolynomial P ≠ 0 :=
    exceptionalPolynomial_ne_zero_of_generic_irreducible hPgen
  have hfinite : (exceptionalSet P ∪ bad).Finite :=
    (exceptionalSet_finite P).union hbad
  obtain ⟨t, ht⟩ := hfinite.exists_notMem
  exact ⟨t, fun h ↦ ht (Or.inl h), fun h ↦ ht (Or.inr h)⟩

end GenericSpecialization

end DiskRigidity.Algebraic
