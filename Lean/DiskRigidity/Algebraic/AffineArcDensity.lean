/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.GenericAvoidance
public import DiskRigidity.Algebraic.ProjectiveHomogenization
public import DiskRigidity.Algebraic.ProjectiveDual

/-!
# Algebraic density of an affine graph arc

An infinite arc in the chart `[s:t:1]` of an irreducible projective plane
curve is Zariski dense.  The proof is elementary: if an auxiliary polynomial
were not divisible by the curve equation, its resultant with that equation
would allow common zeros for only finitely many parameters `t`.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace AffineArcDensity

open MvPolynomial Polynomial Set
open GenericSpecialization PlaneCurveSpecialization
open ProjectiveHomogenization

/-- Generic divisibility over `ℝ(t)` forced by common zeros over infinitely
many real parameters. -/
theorem generic_dvd_of_vanishes_on_infinite_graph
    {Q R : MvPolynomial (Fin 3) ℝ} {m : ℕ}
    (hQ : Q.IsHomogeneous m) (hQirr : Irreducible Q)
    (hm : m ≠ 0)
    (he : MvPolynomial.eval distinguishedPoint Q ≠ 0)
    {U : Set ℝ} (hU : U.Infinite) (s : ℝ → ℝ)
    (hQzero : ∀ t ∈ U, MvPolynomial.eval ![s t, t, 1] Q = 0)
    (hRzero : ∀ t ∈ U, MvPolynomial.eval ![s t, t, 1] R = 0) :
    genericMap (affineFamily Q) ∣ genericMap (affineFamily R) := by
  let P := affineFamily Q
  let S := affineFamily R
  have hPirr : Irreducible P := irreducible_affineFamily hQ hQirr hm he
  have hPdegree : P.natDegree ≠ 0 := by
    rw [natDegree_affineFamily_eq hQ he]
    exact hm
  have hPgen : Irreducible (genericMap P) :=
    genericMap_irreducible_of_irreducible hPirr hPdegree
  by_contra hnotdvd
  have hlead : IsUnit P.leadingCoeff :=
    isUnit_leadingCoeff_affineFamily hQ he
  have hsubset : U ⊆ GenericAvoidance.pairExceptionalSet P S := by
    intro t ht
    by_contra htNot
    have hcop : IsCoprime (specialize P t) (specialize S t) :=
      GenericAvoidance.isCoprime_specialize_of_not_mem
        hlead hPgen hnotdvd htNot
    have hmap := hcop.map (Polynomial.evalRingHom (s t))
    have hPzero : (specialize P t).eval (s t) = 0 := by
      rw [eval_specialize_affineFamily]
      exact hQzero t ht
    have hSzero : (specialize S t).eval (s t) = 0 := by
      rw [eval_specialize_affineFamily]
      exact hRzero t ht
    simp [hPzero, hSzero] at hmap
  exact hU (GenericAvoidance.pairExceptionalSet_finite P S |>.subset hsubset)

/-- Affine-family divisibility descends from the function field by Gauss's
lemma. -/
theorem affineFamily_dvd_of_vanishes_on_infinite_graph
    {Q R : MvPolynomial (Fin 3) ℝ} {m : ℕ}
    (hQ : Q.IsHomogeneous m) (hQirr : Irreducible Q)
    (hm : m ≠ 0)
    (he : MvPolynomial.eval distinguishedPoint Q ≠ 0)
    {U : Set ℝ} (hU : U.Infinite) (s : ℝ → ℝ)
    (hQzero : ∀ t ∈ U, MvPolynomial.eval ![s t, t, 1] Q = 0)
    (hRzero : ∀ t ∈ U, MvPolynomial.eval ![s t, t, 1] R = 0) :
    affineFamily Q ∣ affineFamily R := by
  have hPirr : Irreducible (affineFamily Q) :=
    irreducible_affineFamily hQ hQirr hm he
  have hPdegree : (affineFamily Q).natDegree ≠ 0 := by
    rw [natDegree_affineFamily_eq hQ he]
    exact hm
  exact (hPirr.isPrimitive hPdegree).dvd_of_fraction_map_dvd_fraction_map
    (generic_dvd_of_vanishes_on_infinite_graph hQ hQirr hm he hU s
      hQzero hRzero)

/-- Projective divisibility forced by vanishing on an infinite affine graph
arc. -/
theorem dvd_of_vanishes_on_infinite_graph
    {Q R : MvPolynomial (Fin 3) ℝ} {m r : ℕ}
    (hQ : Q.IsHomogeneous m) (hR : R.IsHomogeneous r)
    (hQirr : Irreducible Q) (hm : m ≠ 0)
    (he : MvPolynomial.eval distinguishedPoint Q ≠ 0)
    {U : Set ℝ} (hU : U.Infinite) (s : ℝ → ℝ)
    (hQzero : ∀ t ∈ U, MvPolynomial.eval ![s t, t, 1] Q = 0)
    (hRzero : ∀ t ∈ U, MvPolynomial.eval ![s t, t, 1] R = 0) :
    Q ∣ R := by
  apply dvd_of_affineFamily_dvd hQ hR he
  exact affineFamily_dvd_of_vanishes_on_infinite_graph
    hQ hQirr hm he hU s hQzero hRzero

/-- A nonempty open real parameter set is infinite, giving the form used for
a real-analytic open arc. -/
theorem dvd_of_vanishes_on_open_graph
    {Q R : MvPolynomial (Fin 3) ℝ} {m r : ℕ}
    (hQ : Q.IsHomogeneous m) (hR : R.IsHomogeneous r)
    (hQirr : Irreducible Q) (hm : m ≠ 0)
    (he : MvPolynomial.eval distinguishedPoint Q ≠ 0)
    {U : Set ℝ} (hUopen : IsOpen U) (hUnonempty : U.Nonempty)
    (s : ℝ → ℝ)
    (hQzero : ∀ t ∈ U, MvPolynomial.eval ![s t, t, 1] Q = 0)
    (hRzero : ∀ t ∈ U, MvPolynomial.eval ![s t, t, 1] R = 0) :
    Q ∣ R := by
  obtain ⟨t, ht⟩ := hUnonempty
  have hUinf : U.Infinite :=
    infinite_of_mem_nhds t (hUopen.mem_nhds ht)
  exact dvd_of_vanishes_on_infinite_graph hQ hR hQirr hm he hUinf s
    hQzero hRzero

/-- Rename a primal polynomial in the affine chart `[1:s:t]` to the chart
`[s:t:1]` used by `affineFamily`. -/
noncomputable def rotateFromFirstChart
    (Q : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.renameEquiv ℝ ProjectiveHomogenization.chartRotation.symm Q

@[simp] theorem chartRotation_symm_zero :
    ProjectiveHomogenization.chartRotation.symm 0 = 2 := by decide

@[simp] theorem chartRotation_symm_one :
    ProjectiveHomogenization.chartRotation.symm 1 = 0 := by decide

@[simp] theorem chartRotation_symm_two :
    ProjectiveHomogenization.chartRotation.symm 2 = 1 := by decide

theorem eval_rotateFromFirstChart_general
    (Q : MvPolynomial (Fin 3) ℝ) (z : Fin 3 → ℝ) :
    MvPolynomial.eval z (rotateFromFirstChart Q) =
      MvPolynomial.eval ![z 2, z 0, z 1] Q := by
  rw [rotateFromFirstChart, MvPolynomial.renameEquiv_apply,
    MvPolynomial.eval_rename]
  have hvec : z ∘ ProjectiveHomogenization.chartRotation.symm =
      ![z 2, z 0, z 1] := by
    funext i
    fin_cases i <;> simp
  rw [hvec]

theorem eval_rotateFromFirstChart (Q : MvPolynomial (Fin 3) ℝ)
    (s t : ℝ) :
    MvPolynomial.eval ![s, t, 1] (rotateFromFirstChart Q) =
      MvPolynomial.eval ![1, s, t] Q := by
  rw [eval_rotateFromFirstChart_general]
  rfl

theorem rotateFromFirstChart_isHomogeneous {m : ℕ}
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Q.IsHomogeneous m) :
    (rotateFromFirstChart Q).IsHomogeneous m :=
  hQ.rename_isHomogeneous

theorem rotateFromFirstChart_irreducible
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Irreducible Q) :
    Irreducible (rotateFromFirstChart Q) :=
  hQ.map (MvPolynomial.renameEquiv ℝ
    ProjectiveHomogenization.chartRotation.symm).toMulEquiv

/-- First-affine-chart version of Zariski density.  The nonvanishing point
`[0:1:0]` is the point at infinity controlling the leading coefficient after
the cyclic coordinate change. -/
theorem dvd_of_vanishes_on_open_first_chart
    {Q R : MvPolynomial (Fin 3) ℝ} {m r : ℕ}
    (hQ : Q.IsHomogeneous m) (hR : R.IsHomogeneous r)
    (hQirr : Irreducible Q) (hm : m ≠ 0)
    (he : MvPolynomial.eval ![0, 1, 0] Q ≠ 0)
    {U : Set ℝ} (hUopen : IsOpen U) (hUnonempty : U.Nonempty)
    (s : ℝ → ℝ)
    (hQzero : ∀ t ∈ U, MvPolynomial.eval ![1, s t, t] Q = 0)
    (hRzero : ∀ t ∈ U, MvPolynomial.eval ![1, s t, t] R = 0) :
    Q ∣ R := by
  have heRotated : MvPolynomial.eval distinguishedPoint
      (rotateFromFirstChart Q) ≠ 0 := by
    rw [eval_rotateFromFirstChart_general]
    simpa [distinguishedPoint] using he
  have hrotDiv : rotateFromFirstChart Q ∣ rotateFromFirstChart R := by
    apply dvd_of_vanishes_on_open_graph
      (rotateFromFirstChart_isHomogeneous hQ)
      (rotateFromFirstChart_isHomogeneous hR)
      (rotateFromFirstChart_irreducible hQirr) hm heRotated
      hUopen hUnonempty s
    · intro t ht
      rw [eval_rotateFromFirstChart]
      exact hQzero t ht
    · intro t ht
      rw [eval_rotateFromFirstChart]
      exact hRzero t ht
  exact (map_dvd_iff (MvPolynomial.renameEquiv ℝ
    ProjectiveHomogenization.chartRotation.symm)).mp hrotDiv

/-- The coordinate reflection interchanging the two projective affine
coordinates `Z₀` and `Z₂`.  It sends a graph `[s:t:1]` to
`[1:t:s]`. -/
def secondChartReflection : Fin 3 ≃ Fin 3 := Equiv.swap 0 2

@[simp] theorem secondChartReflection_zero : secondChartReflection 0 = 2 := by
  decide

@[simp] theorem secondChartReflection_one : secondChartReflection 1 = 1 := by
  decide

@[simp] theorem secondChartReflection_two : secondChartReflection 2 = 0 := by
  decide

/-- Rename a polynomial in the affine chart `[1:t:s]` to the standard
graph chart `[s:t:1]`. -/
noncomputable def reflectFromSecondChart
    (Q : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.renameEquiv ℝ secondChartReflection Q

theorem eval_reflectFromSecondChart_general
    (Q : MvPolynomial (Fin 3) ℝ) (z : Fin 3 → ℝ) :
    MvPolynomial.eval z (reflectFromSecondChart Q) =
      MvPolynomial.eval ![z 2, z 1, z 0] Q := by
  rw [reflectFromSecondChart, MvPolynomial.renameEquiv_apply,
    MvPolynomial.eval_rename]
  have hvec : z ∘ secondChartReflection = ![z 2, z 1, z 0] := by
    funext i
    fin_cases i <;> simp
  rw [hvec]

theorem eval_reflectFromSecondChart (Q : MvPolynomial (Fin 3) ℝ)
    (s t : ℝ) :
    MvPolynomial.eval ![s, t, 1] (reflectFromSecondChart Q) =
      MvPolynomial.eval ![1, t, s] Q := by
  rw [eval_reflectFromSecondChart_general]
  rfl

theorem reflectFromSecondChart_isHomogeneous {m : ℕ}
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Q.IsHomogeneous m) :
    (reflectFromSecondChart Q).IsHomogeneous m :=
  hQ.rename_isHomogeneous

theorem reflectFromSecondChart_irreducible
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Irreducible Q) :
    Irreducible (reflectFromSecondChart Q) :=
  hQ.map (MvPolynomial.renameEquiv ℝ secondChartReflection).toMulEquiv

/-- Second-affine-chart version of Zariski density for a graph
`[1:t:s(t)]`.  The point `[0:0:1]` controls the leading coefficient after
reflecting the first and last projective coordinates. -/
theorem dvd_of_vanishes_on_open_second_chart
    {Q R : MvPolynomial (Fin 3) ℝ} {m r : ℕ}
    (hQ : Q.IsHomogeneous m) (hR : R.IsHomogeneous r)
    (hQirr : Irreducible Q) (hm : m ≠ 0)
    (he : MvPolynomial.eval ![0, 0, 1] Q ≠ 0)
    {U : Set ℝ} (hUopen : IsOpen U) (hUnonempty : U.Nonempty)
    (s : ℝ → ℝ)
    (hQzero : ∀ t ∈ U, MvPolynomial.eval ![1, t, s t] Q = 0)
    (hRzero : ∀ t ∈ U, MvPolynomial.eval ![1, t, s t] R = 0) :
    Q ∣ R := by
  have heReflected : MvPolynomial.eval distinguishedPoint
      (reflectFromSecondChart Q) ≠ 0 := by
    rw [eval_reflectFromSecondChart_general]
    simpa [distinguishedPoint] using he
  have hreflectDiv :
      reflectFromSecondChart Q ∣ reflectFromSecondChart R := by
    apply dvd_of_vanishes_on_open_graph
      (reflectFromSecondChart_isHomogeneous hQ)
      (reflectFromSecondChart_isHomogeneous hR)
      (reflectFromSecondChart_irreducible hQirr) hm heReflected
      hUopen hUnonempty s
    · intro t ht
      rw [eval_reflectFromSecondChart]
      exact hQzero t ht
    · intro t ht
      rw [eval_reflectFromSecondChart]
      exact hRzero t ht
  exact (map_dvd_iff
    (MvPolynomial.renameEquiv ℝ secondChartReflection)).mp hreflectDiv

/-- An irreducible positive-degree plane curve has a regular point on every
infinite graph arc that it contains.  If the whole arc were singular, density
would make the curve divide each partial derivative; degree then forces all
partials to vanish, contradicting Euler's identity in characteristic zero. -/
theorem exists_regular_on_infinite_graph
    {Q : MvPolynomial (Fin 3) ℝ} {m : ℕ}
    (hQ : Q.IsHomogeneous m) (hQirr : Irreducible Q)
    (hm : m ≠ 0)
    (he : MvPolynomial.eval distinguishedPoint Q ≠ 0)
    {U : Set ℝ} (hU : U.Infinite) (s : ℝ → ℝ)
    (hQzero : ∀ t ∈ U, MvPolynomial.eval ![s t, t, 1] Q = 0) :
    ∃ t ∈ U, ProjectiveDual.RegularAt Q ![s t, t, 1] := by
  by_contra hexists
  push Not at hexists
  have hgradient : ∀ t ∈ U,
      ProjectiveDual.gradient Q ![s t, t, 1] = 0 := by
    intro t ht
    by_contra hgrad
    apply hexists t ht
    refine ⟨⟨?_, hQzero t ht⟩, hgrad⟩
    intro hline
    have h := congrFun hline (2 : Fin 3)
    exact one_ne_zero h
  have hpderiv : ∀ i : Fin 3, MvPolynomial.pderiv i Q = 0 := by
    intro i
    have hpartialZero : ∀ t ∈ U,
        MvPolynomial.eval ![s t, t, 1] (MvPolynomial.pderiv i Q) = 0 := by
      intro t ht
      exact congrFun (hgradient t ht) i
    have hdiv : Q ∣ MvPolynomial.pderiv i Q :=
      dvd_of_vanishes_on_infinite_graph hQ (hQ.pderiv (i := i))
        hQirr hm he hU s hQzero hpartialZero
    by_contra hpzero
    have hdegreeQ : Q.totalDegree = m := hQ.totalDegree hQirr.ne_zero
    have hdegreeDiv : Q.totalDegree ≤
        (MvPolynomial.pderiv i Q).totalDegree :=
      MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hpzero
    have hdegreePartial :
        (MvPolynomial.pderiv i Q).totalDegree ≤ m - 1 :=
      (hQ.pderiv (i := i)).totalDegree_le
    omega
  have hEuler := ProjectiveDual.dot_gradient_eq_smul_eval hQ
    distinguishedPoint
  have hgradientE : ProjectiveDual.gradient Q distinguishedPoint = 0 := by
    funext i
    simp [ProjectiveDual.gradient, hpderiv i]
  rw [hgradientE] at hEuler
  simp only [dotProduct_zero] at hEuler
  have hmReal : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  exact (mul_ne_zero hmReal he) hEuler.symm

/-- Open-arc form of `exists_regular_on_infinite_graph`. -/
theorem exists_regular_on_open_graph
    {Q : MvPolynomial (Fin 3) ℝ} {m : ℕ}
    (hQ : Q.IsHomogeneous m) (hQirr : Irreducible Q)
    (hm : m ≠ 0)
    (he : MvPolynomial.eval distinguishedPoint Q ≠ 0)
    {U : Set ℝ} (hUopen : IsOpen U) (hUnonempty : U.Nonempty)
    (s : ℝ → ℝ)
    (hQzero : ∀ t ∈ U, MvPolynomial.eval ![s t, t, 1] Q = 0) :
    ∃ t ∈ U, ProjectiveDual.RegularAt Q ![s t, t, 1] := by
  obtain ⟨t, ht⟩ := hUnonempty
  exact exists_regular_on_infinite_graph hQ hQirr hm he
    (infinite_of_mem_nhds t (hUopen.mem_nhds ht)) s hQzero

end AffineArcDensity

end DiskRigidity.Algebraic
