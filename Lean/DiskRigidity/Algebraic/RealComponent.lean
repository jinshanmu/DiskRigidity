/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.ConnectedFactor
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Analysis.Complex.Basic

/-!
# Real equations for conjugation-stable complex components

The connected regular real arc in Proposition 7.1 first selects a complex
irreducible factor.  Conjugation selects the same factor.  Normalizing by one
nonzero coefficient then gives an equation with real coefficients.  This file
formalizes those coefficient operations.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace RealComponent

open MvPolynomial
open scoped ComplexConjugate

/-- Coefficientwise complex conjugation. -/
noncomputable def conjugatePolynomial {σ : Type*}
    (P : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  MvPolynomial.map Complex.conjAe.toRingEquiv P

@[simp] theorem conjugatePolynomial_C {σ : Type*} (c : ℂ) :
    conjugatePolynomial (MvPolynomial.C (σ := σ) c) =
      MvPolynomial.C (conj c) := by
  simp [conjugatePolynomial]

@[simp] theorem conjugatePolynomial_X {σ : Type*} (i : σ) :
    conjugatePolynomial (MvPolynomial.X (R := ℂ) i) = MvPolynomial.X i := by
  simp [conjugatePolynomial]

@[simp] theorem conjugatePolynomial_add {σ : Type*}
    (P Q : MvPolynomial σ ℂ) :
    conjugatePolynomial (P + Q) =
      conjugatePolynomial P + conjugatePolynomial Q := by
  simp only [conjugatePolynomial, map_add]

@[simp] theorem conjugatePolynomial_sub {σ : Type*}
    (P Q : MvPolynomial σ ℂ) :
    conjugatePolynomial (P - Q) =
      conjugatePolynomial P - conjugatePolynomial Q := by
  simp only [conjugatePolynomial, map_sub]

@[simp] theorem conjugatePolynomial_mul {σ : Type*}
    (P Q : MvPolynomial σ ℂ) :
    conjugatePolynomial (P * Q) =
      conjugatePolynomial P * conjugatePolynomial Q := by
  simp only [conjugatePolynomial, map_mul]

@[simp] theorem conjugatePolynomial_pow {σ : Type*}
    (P : MvPolynomial σ ℂ) (n : ℕ) :
    conjugatePolynomial (P ^ n) = conjugatePolynomial P ^ n := by
  simp only [conjugatePolynomial, map_pow]

@[simp] theorem coeff_conjugatePolynomial {σ : Type*}
    (P : MvPolynomial σ ℂ) (d : σ →₀ ℕ) :
    MvPolynomial.coeff d (conjugatePolynomial P) =
      conj (MvPolynomial.coeff d P) := by
  rw [conjugatePolynomial, MvPolynomial.coeff_map]
  rfl

theorem conjugatePolynomial_involutive {σ : Type*}
    (P : MvPolynomial σ ℂ) :
    conjugatePolynomial (conjugatePolynomial P) = P := by
  ext d
  simp

theorem eval_conjugatePolynomial {σ : Type*}
    (P : MvPolynomial σ ℂ) (z : σ → ℂ) :
    MvPolynomial.eval z (conjugatePolynomial P) =
      conj (MvPolynomial.eval (fun i ↦ conj (z i)) P) := by
  have h := MvPolynomial.map_eval Complex.conjAe.toRingEquiv.toRingHom
    (fun i ↦ conj (z i)) P
  simpa [conjugatePolynomial, Function.comp_def] using h.symm

/-- Take coefficientwise real parts. -/
noncomputable def realPartPolynomial {σ : Type*}
    (P : MvPolynomial σ ℂ) : MvPolynomial σ ℝ :=
  ∑ d ∈ P.support,
    MvPolynomial.monomial d (MvPolynomial.coeff d P).re

@[simp] theorem coeff_realPartPolynomial {σ : Type*}
    (P : MvPolynomial σ ℂ) (d : σ →₀ ℕ) :
    MvPolynomial.coeff d (realPartPolynomial P) =
      (MvPolynomial.coeff d P).re := by
  classical
  by_cases hd : d ∈ P.support
  · simp [realPartPolynomial, MvPolynomial.coeff_sum, hd]
  · have hcoeff : MvPolynomial.coeff d P = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [realPartPolynomial, MvPolynomial.coeff_sum, hd, hcoeff]

/-- A conjugation-fixed polynomial is the complexification of its real-part
polynomial. -/
theorem map_realPartPolynomial_of_conjugate_eq {σ : Type*}
    (P : MvPolynomial σ ℂ) (hP : conjugatePolynomial P = P) :
    MvPolynomial.map (algebraMap ℝ ℂ) (realPartPolynomial P) = P := by
  ext d
  rw [MvPolynomial.coeff_map, coeff_realPartPolynomial]
  have hcoeff : conj (MvPolynomial.coeff d P) =
      MvPolynomial.coeff d P := by
    have := congrArg (MvPolynomial.coeff d) hP
    simpa using this
  exact Complex.conj_eq_iff_re.mp hcoeff

/-- Complexification of a real polynomial is fixed by coefficientwise
conjugation. -/
theorem conjugatePolynomial_map_real {σ : Type*}
    (P : MvPolynomial σ ℝ) :
    conjugatePolynomial (MvPolynomial.map (algebraMap ℝ ℂ) P) =
      MvPolynomial.map (algebraMap ℝ ℂ) P := by
  ext d
  simp only [coeff_conjugatePolynomial, MvPolynomial.coeff_map]
  exact Complex.conj_ofReal _

theorem eval_map_real {σ : Type*} (P : MvPolynomial σ ℝ)
    (x : σ → ℝ) :
    MvPolynomial.eval (fun i ↦ (x i : ℂ))
      (MvPolynomial.map (algebraMap ℝ ℂ) P) =
        (MvPolynomial.eval x P : ℂ) := by
  rw [MvPolynomial.eval_map]
  change MvPolynomial.eval₂ (algebraMap ℝ ℂ)
      ((algebraMap ℝ ℂ) ∘ x) P = _
  rw [← MvPolynomial.eval₂_comp]
  rfl

theorem gradient_map_real {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (x : Fin N → ℝ) :
    ProjectiveDual.gradient (MvPolynomial.map (algebraMap ℝ ℂ) P)
        (fun i ↦ (x i : ℂ)) =
      fun i ↦ ((ProjectiveDual.gradient P x i : ℝ) : ℂ) := by
  funext i
  simp only [ProjectiveDual.gradient, MvPolynomial.pderiv_map,
    eval_map_real]

/-- Regularity at a real point is preserved by complexification. -/
theorem regularAt_map_real {N : ℕ} {P : MvPolynomial (Fin N) ℝ}
    {x : Fin N → ℝ} (hregular : ProjectiveDual.RegularAt P x) :
    ProjectiveDual.RegularAt (MvPolynomial.map (algebraMap ℝ ℂ) P)
      (fun i ↦ (x i : ℂ)) := by
  rcases hregular with ⟨⟨hx, hzero⟩, hgradient⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hxComplex
    apply hx
    funext i
    exact Complex.ofReal_injective (congrFun hxComplex i)
  · rw [MvPolynomial.eval_map]
    change MvPolynomial.eval₂ (algebraMap ℝ ℂ)
      ((algebraMap ℝ ℂ) ∘ x) P = 0
    rw [← MvPolynomial.eval₂_comp, hzero, map_zero]
  · rw [gradient_map_real]
    intro hgradientComplex
    apply hgradient
    funext i
    exact Complex.ofReal_injective (congrFun hgradientComplex i)

/-- Divisibility between complexifications of real multivariable
polynomials reflects to real divisibility.  The complex quotient is fixed by
conjugation after cancelling the nonzero divisor, and therefore descends by
taking coefficientwise real parts. -/
theorem dvd_of_map_dvd_map_real_complex {σ : Type*}
    {P Q : MvPolynomial σ ℝ}
    (hdiv : MvPolynomial.map (algebraMap ℝ ℂ) P ∣
      MvPolynomial.map (algebraMap ℝ ℂ) Q) :
    P ∣ Q := by
  by_cases hPzero : P = 0
  · subst P
    rw [map_zero, zero_dvd_iff] at hdiv
    have hQzero : Q = 0 :=
      MvPolynomial.map_injective (algebraMap ℝ ℂ)
        Complex.ofReal_injective (by simpa using hdiv)
    rw [hQzero]
  obtain ⟨T, hT⟩ := hdiv
  have hmapPzero : MvPolynomial.map (algebraMap ℝ ℂ) P ≠ 0 := by
    intro hmap
    apply hPzero
    apply MvPolynomial.map_injective (algebraMap ℝ ℂ)
      Complex.ofReal_injective
    simpa using hmap
  have hTfixed : conjugatePolynomial T = T := by
    have hc := congrArg conjugatePolynomial hT
    simp only [conjugatePolynomial_mul,
      conjugatePolynomial_map_real] at hc
    exact mul_left_cancel₀ hmapPzero (hT.symm.trans hc).symm
  let S : MvPolynomial σ ℝ := realPartPolynomial T
  have hmapS : MvPolynomial.map (algebraMap ℝ ℂ) S = T :=
    map_realPartPolynomial_of_conjugate_eq T hTfixed
  refine ⟨S, ?_⟩
  apply MvPolynomial.map_injective (algebraMap ℝ ℂ)
    Complex.ofReal_injective
  rw [map_mul, hmapS]
  exact hT

theorem isUnit_of_map_real_complex_isUnit {σ : Type*}
    {P : MvPolynomial σ ℝ}
    (hP : IsUnit (MvPolynomial.map (algebraMap ℝ ℂ) P)) :
    IsUnit P := by
  have hdata := MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hP
  have hcoeffUnit : IsUnit (MvPolynomial.coeff 0 P) := by
    rw [isUnit_iff_ne_zero]
    intro hzero
    apply hdata.1.ne_zero
    rw [MvPolynomial.coeff_map, hzero, map_zero]
  have hconstantMap : MvPolynomial.map (algebraMap ℝ ℂ) P =
      MvPolynomial.map (algebraMap ℝ ℂ)
        (MvPolynomial.C (MvPolynomial.coeff 0 P)) := by
    have hconstant := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdata.2
    rw [MvPolynomial.coeff_map] at hconstant
    simpa using hconstant
  have hconstant : P = MvPolynomial.C (MvPolynomial.coeff 0 P) :=
    MvPolynomial.map_injective (algebraMap ℝ ℂ) Complex.ofReal_injective
      hconstantMap
  exact MvPolynomial.isUnit_iff_eq_C_of_isReduced.mpr
    ⟨MvPolynomial.coeff 0 P, hcoeffUnit, hconstant⟩

theorem irreducible_of_map_real_complex_irreducible {σ : Type*}
    {P : MvPolynomial σ ℝ}
    (hP : Irreducible (MvPolynomial.map (algebraMap ℝ ℂ) P)) :
    Irreducible P := by
  refine ⟨?_, ?_⟩
  · intro hunit
    exact hP.not_isUnit
      (hunit.map (MvPolynomial.map (algebraMap ℝ ℂ)))
  · intro A B hAB
    have hmapAB : MvPolynomial.map (algebraMap ℝ ℂ) P =
        MvPolynomial.map (algebraMap ℝ ℂ) A *
          MvPolynomial.map (algebraMap ℝ ℂ) B := by
      rw [hAB, map_mul]
    exact (hP.isUnit_or_isUnit hmapAB).imp
      isUnit_of_map_real_complex_isUnit
      isUnit_of_map_real_complex_isUnit

theorem irreducible_conjugatePolynomial {σ : Type*}
    {P : MvPolynomial σ ℂ} (hP : Irreducible P) :
    Irreducible (conjugatePolynomial P) := by
  exact hP.map (MvPolynomial.mapEquiv σ Complex.conjAe.toRingEquiv)

/-- At a regular real point, an irreducible factor and its conjugate cannot
be different components: otherwise their product would divide the ambient
polynomial and the ambient gradient would vanish. -/
theorem associated_conjugatePolynomial_of_common_regular_real_point
    {N : ℕ} {P F : MvPolynomial (Fin N) ℂ}
    (hPinvariant : conjugatePolynomial P = P)
    (hFirreducible : Irreducible F) (hFdiv : F ∣ P)
    (x : Fin N → ℂ) (hxreal : ∀ i, conj (x i) = x i)
    (hFzero : MvPolynomial.eval x F = 0)
    (hPregular : ProjectiveDual.RegularAt P x) :
    Associated F (conjugatePolynomial F) := by
  let G := conjugatePolynomial F
  have hGirreducible : Irreducible G :=
    irreducible_conjugatePolynomial hFirreducible
  have hGdiv : G ∣ P := by
    have hmap := map_dvd
      (MvPolynomial.map Complex.conjAe.toRingEquiv.toRingHom) hFdiv
    change conjugatePolynomial F ∣ conjugatePolynomial P at hmap
    rw [hPinvariant] at hmap
    exact hmap
  have hGzero : MvPolynomial.eval x G = 0 := by
    change MvPolynomial.eval x (conjugatePolynomial F) = 0
    rw [eval_conjugatePolynomial]
    have hx : (fun i ↦ conj (x i)) = x := by
      funext i
      exact hxreal i
    rw [hx, hFzero, map_zero]
  by_contra hnotAssociated
  obtain ⟨R, hR⟩ := hFdiv
  have hGdivProduct : G ∣ F * R := by
    rw [← hR]
    exact hGdiv
  have hGprime : Prime G :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hGirreducible
  rcases hGprime.dvd_mul.mp hGdivProduct with hGF | hGR
  · exact hnotAssociated
      (hGirreducible.associated_of_dvd hFirreducible hGF).symm
  · obtain ⟨T, hT⟩ := hGR
    have hproductDiv : F * G ∣ P := by
      refine ⟨T, ?_⟩
      rw [hR, hT]
      simp only [mul_assoc]
    obtain ⟨T, hT⟩ := hproductDiv
    have hgradient : ProjectiveDual.gradient P x = 0 := by
      rw [hT]
      exact ConnectedFactor.gradient_mul_mul_eq_zero_of_eval_eq_zero
        F G T x hFzero hGzero
    exact hPregular.2 hgradient

/-- Normalize a conjugation-stable irreducible component by one nonzero
coefficient.  Its normalized equation is fixed coefficientwise by
conjugation and therefore descends to `ℝ`. -/
theorem exists_real_irreducible_associate_of_associated_conjugate
    {σ : Type*} {P : MvPolynomial σ ℂ}
    (hPirreducible : Irreducible P)
    (hassociated : Associated P (conjugatePolynomial P)) :
    ∃ F : MvPolynomial σ ℝ,
      Irreducible F ∧
      Irreducible (MvPolynomial.map (algebraMap ℝ ℂ) F) ∧
      Associated (MvPolynomial.map (algebraMap ℝ ℂ) F) P := by
  classical
  obtain ⟨u, hu⟩ := hassociated
  have huUnit : IsUnit (u : MvPolynomial σ ℂ) := u.isUnit
  obtain ⟨a, haUnit, hua⟩ :=
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp huUnit)
  have ha : a ≠ 0 := (isUnit_iff_ne_zero.mp haUnit)
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hPirreducible.ne_zero
  let b := MvPolynomial.coeff d P
  have hb : b ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  have hconjugate : conjugatePolynomial P = MvPolynomial.C a * P := by
    rw [hua] at hu
    simpa [mul_comm] using hu.symm
  have hcoefficient : conj b = a * b := by
    have hcoeff := congrArg (MvPolynomial.coeff d) hconjugate
    simpa [b] using hcoeff
  let G : MvPolynomial σ ℂ := MvPolynomial.C b⁻¹ * P
  have hGconjugate : conjugatePolynomial G = G := by
    change MvPolynomial.map Complex.conjAe.toRingEquiv.toRingHom
        (MvPolynomial.C b⁻¹ * P) = MvPolynomial.C b⁻¹ * P
    rw [map_mul, MvPolynomial.map_C]
    change MvPolynomial.C (conj b⁻¹) * conjugatePolynomial P =
      MvPolynomial.C b⁻¹ * P
    rw [hconjugate, ← mul_assoc, ← MvPolynomial.C_mul]
    have hscalar : conj (b⁻¹) * a = b⁻¹ := by
      rw [map_inv₀, hcoefficient]
      field_simp
    rw [hscalar]
  let F : MvPolynomial σ ℝ := realPartPolynomial G
  have hmapF : MvPolynomial.map (algebraMap ℝ ℂ) F = G := by
    exact map_realPartPolynomial_of_conjugate_eq G hGconjugate
  have hscalarUnit : IsUnit (MvPolynomial.C b⁻¹ : MvPolynomial σ ℂ) :=
    (isUnit_iff_ne_zero.mpr (inv_ne_zero hb)).map MvPolynomial.C
  have hGassociated : Associated G P := by
    exact associated_unit_mul_left P (MvPolynomial.C b⁻¹) hscalarUnit
  have hGirreducible : Irreducible G :=
    hGassociated.symm.irreducible hPirreducible
  have hmapIrreducible :
      Irreducible (MvPolynomial.map (algebraMap ℝ ℂ) F) := by
    rw [hmapF]
    exact hGirreducible
  have hFirreducible : Irreducible F :=
    irreducible_of_map_real_complex_irreducible hmapIrreducible
  exact ⟨F, hFirreducible, hmapIrreducible, hmapF ▸ hGassociated⟩

end RealComponent

end DiskRigidity.Algebraic
