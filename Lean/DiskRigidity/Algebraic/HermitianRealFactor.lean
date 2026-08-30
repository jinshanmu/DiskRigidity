/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.AnalyticFactor
public import DiskRigidity.Algebraic.AffineArcDensity
public import DiskRigidity.Algebraic.RealComponent
public import DiskRigidity.Algebraic.RealAnalyticIrreducibility

/-!
# Real factors of the Hermitian projective determinant

Hermitian pencils have a projective determinant with real coefficients.  We
make that real equation explicit and combine it with analytic factor
selection, producing the real irreducible homogeneous dual factor used in
Proposition 7.1.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace HermitianRealFactor

open Matrix MvPolynomial Set
open scoped ComplexConjugate

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Coefficientwise conjugation fixes the determinant of a Hermitian
projective pencil. -/
theorem conjugate_determinantPolynomial
    (H J : Matrix n n ℂ) (hH : H.IsHermitian) (hJ : J.IsHermitian) :
    RealComponent.conjugatePolynomial
      (HermitianProjective.determinantPolynomial H J) =
        HermitianProjective.determinantPolynomial H J := by
  rw [HermitianProjective.determinantPolynomial,
    RealComponent.conjugatePolynomial, RingHom.map_det]
  rw [← Matrix.det_transpose (HermitianProjective.projectivePencilMatrix H J)]
  congr 1
  funext i j
  change MvPolynomial.map Complex.conjAe.toRingEquiv.toRingHom
      (HermitianProjective.projectivePencilMatrix H J i j) =
    HermitianProjective.projectivePencilMatrix H J j i
  simp only [HermitianProjective.projectivePencilMatrix,
    map_add, map_mul, MvPolynomial.map_X, MvPolynomial.map_C]
  have hOne : Complex.conjAe.toRingEquiv.toRingHom
      ((1 : Matrix n n ℂ) i j) = (1 : Matrix n n ℂ) j i := by
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij, Ne.symm hij]
  have hHij : Complex.conjAe.toRingEquiv.toRingHom (H i j) = H j i := by
    change star (H i j) = H j i
    exact hH.apply j i
  have hJij : Complex.conjAe.toRingEquiv.toRingHom (J i j) = J j i := by
    change star (J i j) = J j i
    exact hJ.apply j i
  rw [hOne, hHij, hJij]

/-- The real equation underlying the Hermitian projective determinant. -/
noncomputable def realDeterminantPolynomial
    (H J : Matrix n n ℂ) : MvPolynomial (Fin 3) ℝ :=
  RealComponent.realPartPolynomial
    (HermitianProjective.determinantPolynomial H J)

/-- Complexifying the real determinant equation recovers the original
Hermitian determinant. -/
theorem map_realDeterminantPolynomial
    (H J : Matrix n n ℂ) (hH : H.IsHermitian) (hJ : J.IsHermitian) :
    MvPolynomial.map (algebraMap ℝ ℂ) (realDeterminantPolynomial H J) =
      HermitianProjective.determinantPolynomial H J := by
  exact RealComponent.map_realPartPolynomial_of_conjugate_eq _
    (conjugate_determinantPolynomial H J hH hJ)

theorem realDeterminantPolynomial_ne_zero
    (H J : Matrix n n ℂ) (hH : H.IsHermitian) (hJ : J.IsHermitian) :
    realDeterminantPolynomial H J ≠ 0 := by
  intro hzero
  apply HermitianProjective.determinantPolynomial_ne_zero H J
  rw [← map_realDeterminantPolynomial H J hH hJ, hzero, map_zero]

theorem realDeterminantPolynomial_isHomogeneous
    (H J : Matrix n n ℂ) (hH : H.IsHermitian) (hJ : J.IsHermitian) :
    (realDeterminantPolynomial H J).IsHomogeneous (Fintype.card n) := by
  apply IsHomogeneous.of_map (f := algebraMap ℝ ℂ) Complex.ofReal_injective
  rw [map_realDeterminantPolynomial H J hH hJ]
  exact HermitianProjective.determinantPolynomial_isHomogeneous H J

theorem eval_map_real (P : MvPolynomial (Fin 3) ℝ)
    (x : Fin 3 → ℝ) :
    MvPolynomial.eval (fun i ↦ (x i : ℂ))
      (MvPolynomial.map (algebraMap ℝ ℂ) P) =
        (MvPolynomial.eval x P : ℂ) := by
  rw [MvPolynomial.eval_map]
  change MvPolynomial.eval₂ (algebraMap ℝ ℂ)
      ((algebraMap ℝ ℂ) ∘ x) P = _
  rw [← MvPolynomial.eval₂_comp]
  rfl

/-- Construct the real irreducible homogeneous factor carrying a real
analytic tangent-line arc.  All determinant divisibility is returned after
complexification, in the form consumed by the Hermitian splitting theorem. -/
theorem exists_real_irreducible_homogeneous_determinant_factor
    (H J : Matrix n n ℂ) (hH : H.IsHermitian) (hJ : J.IsHermitian)
    (U : Set ℝ) (γ : ℝ → Fin 3 → ℝ)
    (hU : U.Nonempty) (hpre : IsPreconnected U)
    (hγ : ∀ i, AnalyticOnNhd ℝ (fun t ↦ γ t i) U)
    (hzero : ∀ t ∈ U,
      MvPolynomial.eval (fun i ↦ (γ t i : ℂ))
        (HermitianProjective.determinantPolynomial H J) = 0) :
    ∃ (Q : MvPolynomial (Fin 3) ℝ) (m : ℕ),
      Irreducible Q ∧
      MvPolynomial.map (algebraMap ℝ ℂ) Q ∣
        HermitianProjective.determinantPolynomial H J ∧
      Q.IsHomogeneous m ∧
      ∀ t ∈ U, MvPolynomial.eval (γ t) Q = 0 := by
  have hzeroReal : ∀ t ∈ U,
      MvPolynomial.eval (γ t) (realDeterminantPolynomial H J) = 0 := by
    intro t ht
    have h := hzero t ht
    rw [← map_realDeterminantPolynomial H J hH hJ,
      eval_map_real] at h
    exact Complex.ofReal_eq_zero.mp h
  obtain ⟨Q, m, hQirr, hQdiv, hQhom, hQzero⟩ :=
    AnalyticFactor.exists_irreducible_homogeneous_factor_zero_on_analytic_arc
      (realDeterminantPolynomial_ne_zero H J hH hJ)
      (realDeterminantPolynomial_isHomogeneous H J hH hJ)
      γ hU hpre hγ hzeroReal
  refine ⟨Q, m, hQirr, ?_, hQhom, hQzero⟩
  have hmapDiv := map_dvd (MvPolynomial.map (algebraMap ℝ ℂ)) hQdiv
  rw [map_realDeterminantPolynomial H J hH hJ] at hmapDiv
  exact hmapDiv

/-- Full construction of the real absolutely irreducible dual equation from
an open analytic graph of tangent lines `[s(t):t:1]` in the Hermitian
determinant.  Positive degree, the distinguished-point condition, and a
regular point on the arc are all derived. -/
theorem exists_dual_factor_on_open_analytic_graph
    (H J : Matrix n n ℂ) (hH : H.IsHermitian) (hJ : J.IsHermitian)
    (U : Set ℝ) (hUopen : IsOpen U) (hU : U.Nonempty)
    (hpre : IsPreconnected U)
    (s : ℝ → ℝ) (hs : AnalyticOnNhd ℝ s U)
    (hzero : ∀ t ∈ U,
      MvPolynomial.eval ![(s t : ℂ), (t : ℂ), 1]
        (HermitianProjective.determinantPolynomial H J) = 0) :
    ∃ (Q : MvPolynomial (Fin 3) ℝ) (m : ℕ),
      Irreducible Q ∧
      Irreducible (MvPolynomial.map (algebraMap ℝ ℂ) Q) ∧
      MvPolynomial.map (algebraMap ℝ ℂ) Q ∣
        HermitianProjective.determinantPolynomial H J ∧
      Q.IsHomogeneous m ∧ m ≠ 0 ∧
      MvPolynomial.eval PlaneCurveSpecialization.distinguishedPoint Q ≠ 0 ∧
      (∀ t ∈ U, MvPolynomial.eval ![s t, t, 1] Q = 0) ∧
      ∃ t ∈ U, ProjectiveDual.RegularAt Q ![s t, t, 1] := by
  let γ : ℝ → Fin 3 → ℝ := fun t ↦ ![s t, t, 1]
  have hγ : ∀ i, AnalyticOnNhd ℝ (fun t ↦ γ t i) U := by
    intro i
    fin_cases i
    · exact hs
    · exact analyticOnNhd_id
    · exact analyticOnNhd_const
  have hzeroγ : ∀ t ∈ U,
      MvPolynomial.eval (fun i ↦ (γ t i : ℂ))
        (HermitianProjective.determinantPolynomial H J) = 0 := by
    intro t ht
    have hvec : (fun i ↦ (γ t i : ℂ)) =
        ![(s t : ℂ), (t : ℂ), 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hvec]
    exact hzero t ht
  obtain ⟨Q, m, hQirr, hQdiv, hQhom, hQzero⟩ :=
    exists_real_irreducible_homogeneous_determinant_factor
      H J hH hJ U γ hU hpre hγ hzeroγ
  have he : MvPolynomial.eval
      PlaneCurveSpecialization.distinguishedPoint Q ≠ 0 :=
    HermitianProjective.eval_distinguishedPoint_ne_zero_of_dvd H J Q hQdiv
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
  have hQzeroGraph : ∀ t ∈ U,
      MvPolynomial.eval ![s t, t, 1] Q = 0 := by
    intro t ht
    exact hQzero t ht
  obtain ⟨t₀, ht₀, hregular⟩ :=
    AffineArcDensity.exists_regular_on_open_graph hQhom hQirr hm he
      hUopen hU s hQzeroGraph
  have hQcomplexIrr :
      Irreducible (MvPolynomial.map (algebraMap ℝ ℂ) Q) := by
    apply RealAnalyticIrreducibility.irreducible_map_real_of_regular_analytic_arc
      hQirr U γ hU hpre hγ hQzero t₀ ht₀
    exact hregular
  exact ⟨Q, m, hQirr, hQcomplexIrr, hQdiv, hQhom, hm, he,
    hQzeroGraph, t₀, ht₀, hregular⟩

end HermitianRealFactor

end DiskRigidity.Algebraic
