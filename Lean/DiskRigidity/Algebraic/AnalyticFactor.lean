/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.HermitianProjective
public import DiskRigidity.Algebraic.HomogeneousFactor
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Polynomial

/-!
# Selecting an algebraic factor along a real-analytic arc

If a polynomial vanishes along a real-analytic arc, one irreducible factor
vanishes along the entire arc.  Unlike the connected regular-locus argument,
this uses the one-variable analytic identity theorem and therefore does not
require the ambient determinant hypersurface to be regular.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace AnalyticFactor

open MvPolynomial Set

variable {ι A : Type*} [NormedCommRing A] [IsDomain A] [NormedAlgebra ℝ A]
  {U : Set ℝ} {f : ι → ℝ → A}

omit [IsDomain A] in
private theorem analyticOnNhd_multiset_prod (s : Multiset ι)
    (hf : ∀ i ∈ s, AnalyticOnNhd ℝ (f i) U) :
    AnalyticOnNhd ℝ (fun t ↦ (s.map fun i ↦ f i t).prod) U := by
  induction s using Multiset.induction_on with
  | empty => simpa using (analyticOnNhd_const :
      AnalyticOnNhd ℝ (fun _ : ℝ ↦ (1 : A)) U)
  | @cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      exact (hf a (by simp)).mul
        (ih fun i hi ↦ hf i (by simp [hi]))

/-- A finite product of analytic complex-valued functions which vanishes on
a nonempty preconnected real set has one fixed factor vanishing everywhere
on that set. -/
theorem exists_mem_zero_on_of_multiset_prod_eq_zero
    (s : Multiset ι) (hU : U.Nonempty) (hpre : IsPreconnected U)
    (hf : ∀ i ∈ s, AnalyticOnNhd ℝ (f i) U)
    (hprod : ∀ t ∈ U, (s.map fun i ↦ f i t).prod = 0) :
    ∃ i ∈ s, ∀ t ∈ U, f i t = 0 := by
  induction s using Multiset.induction_on with
  | empty =>
      obtain ⟨t, ht⟩ := hU
      simpa using hprod t ht
  | @cons a s ih =>
      have ha : AnalyticOnNhd ℝ (f a) U := hf a (by simp)
      have hs : AnalyticOnNhd ℝ
          (fun t ↦ (s.map fun i ↦ f i t).prod) U :=
        analyticOnNhd_multiset_prod s fun i hi ↦ hf i (by simp [hi])
      have hmul : ∀ t ∈ U,
          f a t * (s.map fun i ↦ f i t).prod = 0 := by
        simpa using hprod
      rcases ha.eq_zero_or_eq_zero_of_mul_eq_zero hs hmul hpre with ha0 | hs0
      · exact ⟨a, by simp, ha0⟩
      · obtain ⟨i, hi, hi0⟩ := ih
          (fun i hi ↦ hf i (by simp [hi])) hs0
        exact ⟨i, by simp [hi], hi0⟩

section Polynomial

variable {N : ℕ} {K : Type*} [NormedField K] [NormedAlgebra ℝ K]

/-- Polynomial evaluation along a coordinatewise real-analytic complex arc
is real analytic. -/
theorem analyticOnNhd_eval
    (γ : ℝ → Fin N → K)
    (hγ : ∀ i, AnalyticOnNhd ℝ (fun t ↦ γ t i) U)
    (P : MvPolynomial (Fin N) K) :
    AnalyticOnNhd ℝ (fun t ↦ MvPolynomial.eval (γ t) P) U := by
  simpa only [MvPolynomial.aeval_eq_eval] using
    (AnalyticOnNhd.aeval_mvPolynomial hγ P)

/-- **Analytic irreducible-factor selection.**  An algebraic hypersurface
which contains a nonempty real-analytic arc has an irreducible component
which contains the whole arc. -/
theorem exists_irreducible_factor_zero_on_analytic_arc
    {P : MvPolynomial (Fin N) K} (hP : P ≠ 0)
    (γ : ℝ → Fin N → K)
    (hU : U.Nonempty) (hpre : IsPreconnected U)
    (hγ : ∀ i, AnalyticOnNhd ℝ (fun t ↦ γ t i) U)
    (hzero : ∀ t ∈ U, MvPolynomial.eval (γ t) P = 0) :
    ∃ Q : MvPolynomial (Fin N) K,
      Irreducible Q ∧ Q ∣ P ∧
        ∀ t ∈ U, MvPolynomial.eval (γ t) Q = 0 := by
  classical
  let factors := UniqueFactorizationMonoid.factors P
  let evalArc : MvPolynomial (Fin N) K → ℝ → K :=
    fun Q t ↦ MvPolynomial.eval (γ t) Q
  have hprod : ∀ t ∈ U,
      (factors.map fun Q ↦ evalArc Q t).prod = 0 := by
    intro t ht
    have hassociated : Associated factors.prod P :=
      UniqueFactorizationMonoid.factors_prod hP
    have hfactorProduct : MvPolynomial.eval (γ t) factors.prod = 0 :=
      ((hassociated.map (MvPolynomial.eval (γ t))).eq_zero_iff).mpr
        (hzero t ht)
    rw [← map_multiset_prod]
    exact hfactorProduct
  obtain ⟨Q, hQfactor, hQzero⟩ :=
    exists_mem_zero_on_of_multiset_prod_eq_zero factors hU hpre
      (fun Q _ ↦ analyticOnNhd_eval γ hγ Q) hprod
  exact ⟨Q,
    UniqueFactorizationMonoid.irreducible_of_factor Q hQfactor,
    UniqueFactorizationMonoid.dvd_of_mem_factors hQfactor,
    hQzero⟩

/-- Factor selection plus the proved fact that a factor of a homogeneous
polynomial is homogeneous. -/
theorem exists_irreducible_homogeneous_factor_zero_on_analytic_arc
    {P : MvPolynomial (Fin N) K} {d : ℕ}
    (hP : P ≠ 0) (hPhom : P.IsHomogeneous d)
    (γ : ℝ → Fin N → K)
    (hU : U.Nonempty) (hpre : IsPreconnected U)
    (hγ : ∀ i, AnalyticOnNhd ℝ (fun t ↦ γ t i) U)
    (hzero : ∀ t ∈ U, MvPolynomial.eval (γ t) P = 0) :
    ∃ (Q : MvPolynomial (Fin N) K) (m : ℕ),
      Irreducible Q ∧ Q ∣ P ∧ Q.IsHomogeneous m ∧
        ∀ t ∈ U, MvPolynomial.eval (γ t) Q = 0 := by
  obtain ⟨Q, hQirr, hQdiv, hQzero⟩ :=
    exists_irreducible_factor_zero_on_analytic_arc hP γ hU hpre hγ hzero
  obtain ⟨m, hQhom⟩ := HomogeneousFactor.exists_isHomogeneous_of_dvd
    hQirr.ne_zero hP hQdiv hPhom
  exact ⟨Q, m, hQirr, hQdiv, hQhom, hQzero⟩

end Polynomial

section Hermitian

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The factor `Q` in the dual-curve paragraph of Proposition 7.1 is
constructed directly from a real-analytic arc of tangent lines on which the
Hermitian projective determinant vanishes. -/
theorem exists_irreducible_homogeneous_determinant_factor
    (H J : Matrix n n ℂ) (γ : ℝ → Fin 3 → ℂ)
    (hU : U.Nonempty) (hpre : IsPreconnected U)
    (hγ : ∀ i, AnalyticOnNhd ℝ (fun t ↦ γ t i) U)
    (hzero : ∀ t ∈ U,
      MvPolynomial.eval (γ t)
        (HermitianProjective.determinantPolynomial H J) = 0) :
    ∃ (Q : MvPolynomial (Fin 3) ℂ) (m : ℕ),
      Irreducible Q ∧
      Q ∣ HermitianProjective.determinantPolynomial H J ∧
      Q.IsHomogeneous m ∧
      ∀ t ∈ U, MvPolynomial.eval (γ t) Q = 0 := by
  exact exists_irreducible_homogeneous_factor_zero_on_analytic_arc
    (HermitianProjective.determinantPolynomial_ne_zero H J)
    (HermitianProjective.determinantPolynomial_isHomogeneous H J)
    γ hU hpre hγ hzero

end Hermitian

end AnalyticFactor

end DiskRigidity.Algebraic
