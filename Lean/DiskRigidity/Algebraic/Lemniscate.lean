/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogenized rational lemniscates

This file supplies the elementary polynomial calculation in equations (7.3)
and (7.4) of the paper.  We keep the two-variable homogenized evaluation
explicit; this makes the value on the line at infinity transparent and avoids
introducing any projective-geometry assumptions.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace Lemniscate

open Polynomial
open scoped ComplexConjugate

/-- Evaluation of the degree-`natDegree p` homogenization of `p` at `(z,Z)`. -/
def homogenizedEval (p : ℂ[X]) (z Z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (p.natDegree + 1),
    p.coeff k * z ^ k * Z ^ (p.natDegree - k)

/-- Coefficientwise-conjugate homogenization, with the variables left fixed. -/
def sharpHomogenizedEval (p : ℂ[X]) (w Z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (p.natDegree + 1),
    conj (p.coeff k) * w ^ k * Z ^ (p.natDegree - k)

theorem homogenizedEval_one (p : ℂ[X]) (z : ℂ) :
    homogenizedEval p z 1 = p.eval z := by
  simp [homogenizedEval, Polynomial.eval_eq_sum_range]

/-- On the affine chart, the sharp homogenization evaluated at the conjugate
variable is the conjugate polynomial value. -/
theorem sharpHomogenizedEval_conj_one (p : ℂ[X]) (z : ℂ) :
    sharpHomogenizedEval p (conj z) 1 = conj (p.eval z) := by
  simp [sharpHomogenizedEval, Polynomial.eval_eq_sum_range, map_sum,
    map_mul, map_pow]

theorem homogenizedEval_at_zero (p : ℂ[X]) (z : ℂ) :
    homogenizedEval p z 0 = p.leadingCoeff * z ^ p.natDegree := by
  classical
  rw [homogenizedEval, Finset.sum_eq_single p.natDegree]
  · rw [Nat.sub_self, pow_zero, mul_one, Polynomial.coeff_natDegree]
  · intro k hk hkne
    have hklt : k < p.natDegree := by
      have hkle : k ≤ p.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      exact lt_of_le_of_ne hkle hkne
    rw [zero_pow (Nat.sub_pos_of_lt hklt).ne', mul_zero]
  · simp

theorem sharpHomogenizedEval_at_zero (p : ℂ[X]) (w : ℂ) :
    sharpHomogenizedEval p w 0 =
      conj p.leadingCoeff * w ^ p.natDegree := by
  classical
  rw [sharpHomogenizedEval, Finset.sum_eq_single p.natDegree]
  · rw [Nat.sub_self, pow_zero, mul_one, Polynomial.coeff_natDegree]
  · intro k hk hkne
    have hklt : k < p.natDegree := by
      have hkle : k ≤ p.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      exact lt_of_le_of_ne hkle hkne
    rw [zero_pow (Nat.sub_pos_of_lt hklt).ne', mul_zero]
  · simp

/-- The degree-`natDegree p` homogenization with arbitrary multivariate
polynomials substituted for its two variables. -/
noncomputable def homogenizedPolynomial {σ : Type*} (p : ℂ[X])
    (w Z : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  ∑ k ∈ Finset.range (p.natDegree + 1),
    MvPolynomial.C (p.coeff k) * w ^ k * Z ^ (p.natDegree - k)

/-- Coefficientwise-conjugate version of `homogenizedPolynomial`. -/
noncomputable def sharpHomogenizedPolynomial {σ : Type*} (p : ℂ[X])
    (w Z : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  ∑ k ∈ Finset.range (p.natDegree + 1),
    MvPolynomial.C (conj (p.coeff k)) * w ^ k * Z ^ (p.natDegree - k)

theorem eval_homogenizedPolynomial {σ : Type*} (p : ℂ[X])
    (w Z : MvPolynomial σ ℂ) (r : σ → ℂ) :
    MvPolynomial.eval r (homogenizedPolynomial p w Z) =
      homogenizedEval p (MvPolynomial.eval r w) (MvPolynomial.eval r Z) := by
  simp [homogenizedPolynomial, homogenizedEval]

theorem eval_sharpHomogenizedPolynomial {σ : Type*} (p : ℂ[X])
    (w Z : MvPolynomial σ ℂ) (r : σ → ℂ) :
    MvPolynomial.eval r (sharpHomogenizedPolynomial p w Z) =
      sharpHomogenizedEval p (MvPolynomial.eval r w) (MvPolynomial.eval r Z) := by
  simp [sharpHomogenizedPolynomial, sharpHomogenizedEval]

theorem homogenizedPolynomial_isHomogeneous {σ : Type*} (p : ℂ[X])
    {w Z : MvPolynomial σ ℂ} (hw : w.IsHomogeneous 1) (hZ : Z.IsHomogeneous 1) :
    (homogenizedPolynomial p w Z).IsHomogeneous p.natDegree := by
  apply MvPolynomial.IsHomogeneous.sum
  intro k hk
  have hkdeg : k ≤ p.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hterm := (hw.pow k).mul (hZ.pow (p.natDegree - k))
  convert hterm.C_mul (p.coeff k) using 1 <;>
    simp [mul_assoc, Nat.add_sub_of_le hkdeg]

theorem sharpHomogenizedPolynomial_isHomogeneous {σ : Type*} (p : ℂ[X])
    {w Z : MvPolynomial σ ℂ} (hw : w.IsHomogeneous 1) (hZ : Z.IsHomogeneous 1) :
    (sharpHomogenizedPolynomial p w Z).IsHomogeneous p.natDegree := by
  apply MvPolynomial.IsHomogeneous.sum
  intro k hk
  have hkdeg : k ≤ p.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hterm := (hw.pow k).mul (hZ.pow (p.natDegree - k))
  convert hterm.C_mul (conj (p.coeff k)) using 1 <;>
    simp [mul_assoc, Nat.add_sub_of_le hkdeg]

/-- The homogeneous three-variable rational-lemniscate polynomial in equation
(7.3), with variables ordered as `X,Y,Z`. -/
noncomputable def projectiveLevelPolynomial (U V : ℂ[X]) :
    MvPolynomial (Fin 3) ℂ :=
  let X := MvPolynomial.X (0 : Fin 3)
  let Y := MvPolynomial.X (1 : Fin 3)
  let Z := MvPolynomial.X (2 : Fin 3)
  homogenizedPolynomial U (X + MvPolynomial.C Complex.I * Y) Z *
      sharpHomogenizedPolynomial U (X - MvPolynomial.C Complex.I * Y) Z -
    Z ^ (2 * (U.natDegree - V.natDegree)) *
      homogenizedPolynomial V (X + MvPolynomial.C Complex.I * Y) Z *
      sharpHomogenizedPolynomial V (X - MvPolynomial.C Complex.I * Y) Z

/-- Evaluation formula for the projective polynomial (7.3). -/
theorem eval_projectiveLevelPolynomial (U V : ℂ[X]) (r : Fin 3 → ℂ) :
    MvPolynomial.eval r (projectiveLevelPolynomial U V) =
      homogenizedEval U (r 0 + Complex.I * r 1) (r 2) *
          sharpHomogenizedEval U (r 0 - Complex.I * r 1) (r 2) -
        (r 2) ^ (2 * (U.natDegree - V.natDegree)) *
          homogenizedEval V (r 0 + Complex.I * r 1) (r 2) *
          sharpHomogenizedEval V (r 0 - Complex.I * r 1) (r 2) := by
  simp [projectiveLevelPolynomial, eval_homogenizedPolynomial,
    eval_sharpHomogenizedPolynomial]

/-- The polynomial in (7.3) is homogeneous of degree `2 * deg U`. -/
theorem projectiveLevelPolynomial_isHomogeneous (U V : ℂ[X])
    (hdeg : V.natDegree ≤ U.natDegree) :
    (projectiveLevelPolynomial U V).IsHomogeneous (2 * U.natDegree) := by
  let X : MvPolynomial (Fin 3) ℂ := MvPolynomial.X 0
  let Y : MvPolynomial (Fin 3) ℂ := MvPolynomial.X 1
  let Z : MvPolynomial (Fin 3) ℂ := MvPolynomial.X 2
  have hX : X.IsHomogeneous 1 := MvPolynomial.isHomogeneous_X (R := ℂ) 0
  have hY : Y.IsHomogeneous 1 := MvPolynomial.isHomogeneous_X (R := ℂ) 1
  have hZ : Z.IsHomogeneous 1 := MvPolynomial.isHomogeneous_X (R := ℂ) 2
  have hplus : (X + MvPolynomial.C Complex.I * Y).IsHomogeneous 1 :=
    hX.add (hY.C_mul Complex.I)
  have hminus : (X - MvPolynomial.C Complex.I * Y).IsHomogeneous 1 :=
    hX.sub (hY.C_mul Complex.I)
  have hU := (homogenizedPolynomial_isHomogeneous U hplus hZ).mul
    (sharpHomogenizedPolynomial_isHomogeneous U hminus hZ)
  have hVprod := (homogenizedPolynomial_isHomogeneous V hplus hZ).mul
    (sharpHomogenizedPolynomial_isHomogeneous V hminus hZ)
  have hV := (hZ.pow (2 * (U.natDegree - V.natDegree))).mul hVprod
  have hU' :
      (homogenizedPolynomial U (X + MvPolynomial.C Complex.I * Y) Z *
        sharpHomogenizedPolynomial U (X - MvPolynomial.C Complex.I * Y) Z).IsHomogeneous
        (2 * U.natDegree) := by
    convert hU using 1
    all_goals omega
  have hV' :
      (Z ^ (2 * (U.natDegree - V.natDegree)) *
        homogenizedPolynomial V (X + MvPolynomial.C Complex.I * Y) Z *
        sharpHomogenizedPolynomial V (X - MvPolynomial.C Complex.I * Y) Z).IsHomogeneous
        (2 * U.natDegree) := by
    simpa only [mul_assoc] using (show
      (Z ^ (2 * (U.natDegree - V.natDegree)) *
        (homogenizedPolynomial V (X + MvPolynomial.C Complex.I * Y) Z *
          sharpHomogenizedPolynomial V (X - MvPolynomial.C Complex.I * Y) Z)).IsHomogeneous
        (2 * U.natDegree) by
          convert hV using 1
          all_goals omega)
  rw [projectiveLevelPolynomial]
  change
    (homogenizedPolynomial U (X + MvPolynomial.C Complex.I * Y) Z *
        sharpHomogenizedPolynomial U (X - MvPolynomial.C Complex.I * Y) Z -
      Z ^ (2 * (U.natDegree - V.natDegree)) *
        homogenizedPolynomial V (X + MvPolynomial.C Complex.I * Y) Z *
        sharpHomogenizedPolynomial V (X - MvPolynomial.C Complex.I * Y) Z).IsHomogeneous
      (2 * U.natDegree)
  exact hU'.sub hV'

/-- The homogeneous polynomial whose affine restriction is
`|U|^2 - |V|^2`, written as an evaluation rather than as an
`MvPolynomial`. -/
def homogeneousLevelEval (U V : ℂ[X]) (X Y Z : ℝ) : ℂ :=
  homogenizedEval U (X + Y * Complex.I) Z *
      sharpHomogenizedEval U (X - Y * Complex.I) Z -
    (Z : ℂ) ^ (2 * (U.natDegree - V.natDegree)) *
      homogenizedEval V (X + Y * Complex.I) Z *
      sharpHomogenizedEval V (X - Y * Complex.I) Z

/-- Equation (7.4): when `deg U > deg V`, the rational-lemniscate
homogenization restricts at infinity to a nonzero scalar multiple of
`(X²+Y²)^deg U`. -/
theorem homogeneousLevelEval_at_infinity (U V : ℂ[X])
    (hdeg : V.natDegree < U.natDegree) (X Y : ℝ) :
    homogeneousLevelEval U V X Y 0 =
      (Complex.normSq U.leadingCoeff : ℂ) *
        ((X : ℂ) ^ 2 + (Y : ℂ) ^ 2) ^ U.natDegree := by
  have hsub : 0 < 2 * (U.natDegree - V.natDegree) := by omega
  simp only [homogeneousLevelEval, Complex.ofReal_zero]
  rw [homogenizedEval_at_zero,
    sharpHomogenizedEval_at_zero]
  rw [zero_pow hsub.ne']
  simp only [zero_mul, sub_zero]
  have hxy :
      ((X : ℂ) + (Y : ℂ) * Complex.I) *
          ((X : ℂ) - (Y : ℂ) * Complex.I) =
        (X : ℂ) ^ 2 + (Y : ℂ) ^ 2 := by
    calc
      _ = (X : ℂ) ^ 2 - (Y : ℂ) ^ 2 * Complex.I ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  calc
    U.leadingCoeff * ((X : ℂ) + (Y : ℂ) * Complex.I) ^ U.natDegree *
          (conj U.leadingCoeff *
            ((X : ℂ) - (Y : ℂ) * Complex.I) ^ U.natDegree) =
        (U.leadingCoeff * conj U.leadingCoeff) *
          ((((X : ℂ) + (Y : ℂ) * Complex.I) *
            ((X : ℂ) - (Y : ℂ) * Complex.I)) ^ U.natDegree) := by
      rw [mul_pow]
      ring
    _ = (Complex.normSq U.leadingCoeff : ℂ) *
          ((X : ℂ) ^ 2 + (Y : ℂ) ^ 2) ^ U.natDegree := by
      rw [Complex.mul_conj, hxy]

/-- Consequently the projective real locus has no point at infinity, provided
`U` is nonzero. -/
theorem homogeneousLevelEval_at_infinity_ne_zero (U V : ℂ[X])
    (hU : U ≠ 0) (hdeg : V.natDegree < U.natDegree) (X Y : ℝ)
    (hXY : (X, Y) ≠ (0, 0)) :
    homogeneousLevelEval U V X Y 0 ≠ 0 := by
  rw [homogeneousLevelEval_at_infinity U V hdeg]
  apply mul_ne_zero
  · exact_mod_cast Complex.normSq_eq_zero.not.mpr (Polynomial.leadingCoeff_ne_zero.mpr hU)
  · apply pow_ne_zero
    have hsum : X ^ 2 + Y ^ 2 ≠ 0 := by
      intro h
      have hx2 : X ^ 2 = 0 := by nlinarith [sq_nonneg X, sq_nonneg Y]
      have hy2 : Y ^ 2 = 0 := by nlinarith [sq_nonneg X, sq_nonneg Y]
      apply hXY
      exact Prod.ext (sq_eq_zero_iff.mp hx2) (sq_eq_zero_iff.mp hy2)
    exact_mod_cast hsum

/-- Reorder the polynomial from conventional `[X,Y,Z]` coordinates to the
incidence-vector order `[Z,X,Y]` used in the projective-duality files. -/
def primalCoordinateIndex : Fin 3 → Fin 3 := ![1, 2, 0]

/-- The projective rational-level polynomial in primal coordinate order
`[Z,X,Y]`. -/
noncomputable def primalOrderProjectiveLevelPolynomial (U V : ℂ[X]) :
    MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.rename primalCoordinateIndex (projectiveLevelPolynomial U V)

theorem primalOrderProjectiveLevelPolynomial_isHomogeneous
    (U V : ℂ[X]) (hdeg : V.natDegree ≤ U.natDegree) :
    (primalOrderProjectiveLevelPolynomial U V).IsHomogeneous
      (2 * U.natDegree) :=
  (projectiveLevelPolynomial_isHomogeneous U V hdeg).rename_isHomogeneous

theorem eval_primalOrderProjectiveLevelPolynomial
    (U V : ℂ[X]) (r : Fin 3 → ℂ) :
    MvPolynomial.eval r (primalOrderProjectiveLevelPolynomial U V) =
      MvPolynomial.eval ![r 1, r 2, r 0] (projectiveLevelPolynomial U V) := by
  rw [primalOrderProjectiveLevelPolynomial, MvPolynomial.eval_rename]
  have hr : r ∘ primalCoordinateIndex = ![r 1, r 2, r 0] := by
    funext i
    fin_cases i <;> rfl
  rw [hr]

/-- The affine restriction of the projective lemniscate equation is exactly
`|U(z)|² - |V(z)|²`. -/
theorem eval_primalOrderProjectiveLevelPolynomial_affine
    (U V : ℂ[X]) (X Y : ℝ) :
    MvPolynomial.eval ![(1 : ℂ), (X : ℂ), (Y : ℂ)]
        (primalOrderProjectiveLevelPolynomial U V) =
      (Complex.normSq (U.eval (X + Y * Complex.I)) : ℂ) -
        (Complex.normSq (V.eval (X + Y * Complex.I)) : ℂ) := by
  rw [eval_primalOrderProjectiveLevelPolynomial,
    eval_projectiveLevelPolynomial]
  change homogenizedEval U ((X : ℂ) + Complex.I * (Y : ℂ)) 1 *
      sharpHomogenizedEval U ((X : ℂ) - Complex.I * (Y : ℂ)) 1 -
        1 ^ (2 * (U.natDegree - V.natDegree)) *
          homogenizedEval V ((X : ℂ) + Complex.I * (Y : ℂ)) 1 *
            sharpHomogenizedEval V ((X : ℂ) - Complex.I * (Y : ℂ)) 1 = _
  have hplus : (X : ℂ) + Complex.I * (Y : ℂ) =
      (X : ℂ) + (Y : ℂ) * Complex.I := by ring
  have hconj : (X : ℂ) - Complex.I * (Y : ℂ) =
      conj ((X : ℂ) + (Y : ℂ) * Complex.I) := by
    simp
    ring
  rw [hplus, hconj, homogenizedEval_one, homogenizedEval_one,
    sharpHomogenizedEval_conj_one,
    sharpHomogenizedEval_conj_one]
  simp only [one_pow, one_mul]
  rw [Complex.mul_conj, Complex.mul_conj]

/-- Thus affine vanishing is equivalent to equality of numerator and
denominator moduli. -/
theorem eval_primalOrderProjectiveLevelPolynomial_affine_eq_zero_iff
    (U V : ℂ[X]) (X Y : ℝ) :
    MvPolynomial.eval ![(1 : ℂ), (X : ℂ), (Y : ℂ)]
        (primalOrderProjectiveLevelPolynomial U V) = 0 ↔
      ‖U.eval (X + Y * Complex.I)‖ =
        ‖V.eval (X + Y * Complex.I)‖ := by
  rw [eval_primalOrderProjectiveLevelPolynomial_affine]
  constructor
  · intro h
    have hsquares : ‖U.eval (X + Y * Complex.I)‖ ^ 2 =
        ‖V.eval (X + Y * Complex.I)‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm]
      exact_mod_cast sub_eq_zero.mp h
    nlinarith [norm_nonneg (U.eval (X + Y * Complex.I)),
      norm_nonneg (V.eval (X + Y * Complex.I))]
  · intro h
    apply sub_eq_zero.mpr
    have hsquares := congrArg (fun r : ℝ ↦ r ^ 2) h
    rw [Complex.sq_norm, Complex.sq_norm] at hsquares
    exact_mod_cast hsquares

/-- Complex form of (7.4), in incidence-vector coordinate order. -/
theorem eval_primalOrderProjectiveLevelPolynomial_at_infinity
    (U V : ℂ[X]) (hdeg : V.natDegree < U.natDegree) (X Y : ℂ) :
    MvPolynomial.eval ![0, X, Y]
        (primalOrderProjectiveLevelPolynomial U V) =
      (Complex.normSq U.leadingCoeff : ℂ) *
        (X ^ 2 + Y ^ 2) ^ U.natDegree := by
  have hsub : 0 < 2 * (U.natDegree - V.natDegree) := by omega
  rw [eval_primalOrderProjectiveLevelPolynomial,
    eval_projectiveLevelPolynomial]
  change homogenizedEval U (X + Complex.I * Y) 0 *
      sharpHomogenizedEval U (X - Complex.I * Y) 0 -
        0 ^ (2 * (U.natDegree - V.natDegree)) *
          homogenizedEval V (X + Complex.I * Y) 0 *
            sharpHomogenizedEval V (X - Complex.I * Y) 0 = _
  rw [homogenizedEval_at_zero, sharpHomogenizedEval_at_zero,
    zero_pow hsub.ne']
  simp only [zero_mul, sub_zero]
  have hxy : (X + Complex.I * Y) * (X - Complex.I * Y) =
      X ^ 2 + Y ^ 2 := by
    calc
      (X + Complex.I * Y) * (X - Complex.I * Y) =
          X ^ 2 - Complex.I ^ 2 * Y ^ 2 := by ring
      _ = X ^ 2 + Y ^ 2 := by rw [Complex.I_sq]; ring
  calc
    U.leadingCoeff * (X + Complex.I * Y) ^ U.natDegree *
          (conj U.leadingCoeff * (X - Complex.I * Y) ^ U.natDegree) =
        (U.leadingCoeff * conj U.leadingCoeff) *
          (((X + Complex.I * Y) * (X - Complex.I * Y)) ^ U.natDegree) := by
      rw [mul_pow]
      ring
    _ = (Complex.normSq U.leadingCoeff : ℂ) *
        (X ^ 2 + Y ^ 2) ^ U.natDegree := by
      rw [Complex.mul_conj, hxy]

theorem primalOrderProjectiveLevelPolynomial_ne_zero
    (U V : ℂ[X]) (hU : U ≠ 0)
    (hdeg : V.natDegree < U.natDegree) :
    primalOrderProjectiveLevelPolynomial U V ≠ 0 := by
  intro hzero
  have heval := eval_primalOrderProjectiveLevelPolynomial_at_infinity
    U V hdeg 1 0
  rw [hzero, map_zero] at heval
  have hlc : (Complex.normSq U.leadingCoeff : ℂ) ≠ 0 := by
    exact_mod_cast Complex.normSq_eq_zero.not.mpr
      (Polynomial.leadingCoeff_ne_zero.mpr hU)
  apply hlc
  simpa using heval.symm

theorem primalOrderProjectiveLevelPolynomial_not_isUnit
    (U V : ℂ[X]) (hU : U ≠ 0)
    (hdeg : V.natDegree < U.natDegree) :
    ¬ IsUnit (primalOrderProjectiveLevelPolynomial U V) := by
  intro hunit
  have htotalZero :
      (primalOrderProjectiveLevelPolynomial U V).totalDegree = 0 :=
    (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hunit).2
  have htotalDegree :
      (primalOrderProjectiveLevelPolynomial U V).totalDegree =
        2 * U.natDegree :=
    (primalOrderProjectiveLevelPolynomial_isHomogeneous U V hdeg.le).totalDegree
      (primalOrderProjectiveLevelPolynomial_ne_zero U V hU hdeg)
  rw [htotalDegree] at htotalZero
  omega

/-- Divisibility of a real primal component into the rational lemniscate
polynomial gives exactly the infinity-control hypothesis consumed by the
global projective-circle theorem. -/
theorem infinity_control_of_component_dvd
    (U V : ℂ[X]) (hU : U ≠ 0)
    (hdeg : V.natDegree < U.natDegree)
    (F : MvPolynomial (Fin 3) ℝ)
    (hdiv : MvPolynomial.map (algebraMap ℝ ℂ) F ∣
      primalOrderProjectiveLevelPolynomial U V) :
    ∀ X Y : ℂ,
      MvPolynomial.eval ![0, X, Y]
        (MvPolynomial.map (algebraMap ℝ ℂ) F) = 0 →
      X ^ 2 + Y ^ 2 = 0 := by
  intro X Y hFzero
  obtain ⟨R, hR⟩ := hdiv
  have hlevel : MvPolynomial.eval ![0, X, Y]
      (primalOrderProjectiveLevelPolynomial U V) = 0 := by
    rw [hR, map_mul, hFzero, zero_mul]
  rw [eval_primalOrderProjectiveLevelPolynomial_at_infinity U V hdeg] at hlevel
  have hlc : (Complex.normSq U.leadingCoeff : ℂ) ≠ 0 := by
    exact_mod_cast Complex.normSq_eq_zero.not.mpr
      (Polynomial.leadingCoeff_ne_zero.mpr hU)
  have hpow : (X ^ 2 + Y ^ 2) ^ U.natDegree = 0 :=
    (mul_eq_zero.mp hlevel).resolve_left hlc
  have hUnat : U.natDegree ≠ 0 := by omega
  exact (pow_eq_zero_iff hUnat).mp hpow

/-- A real projective component of (7.3) has no nonzero real point on the
line at infinity.  This discharges the corresponding real-locus field of
the convex-dual interface directly from `U,V` and component divisibility. -/
theorem no_real_infinity_of_component_dvd
    (U V : ℂ[X]) (hU : U ≠ 0)
    (hdeg : V.natDegree < U.natDegree)
    (F : MvPolynomial (Fin 3) ℝ)
    (hdiv : MvPolynomial.map (algebraMap ℝ ℂ) F ∣
      primalOrderProjectiveLevelPolynomial U V) :
    ∀ {z : Fin 3 → ℝ}, z ≠ 0 →
      MvPolynomial.eval z F = 0 → z 0 ≠ 0 := by
  intro z hz hF hz0
  have hFcomplex : MvPolynomial.eval (fun i ↦ (z i : ℂ))
      (MvPolynomial.map (algebraMap ℝ ℂ) F) = 0 := by
    rw [MvPolynomial.eval_map]
    change MvPolynomial.eval₂ (algebraMap ℝ ℂ)
      ((algebraMap ℝ ℂ) ∘ z) F = 0
    rw [← MvPolynomial.eval₂_comp, hF, map_zero]
  have hcircleComplex : (z 1 : ℂ) ^ 2 + (z 2 : ℂ) ^ 2 = 0 := by
    apply infinity_control_of_component_dvd U V hU hdeg F hdiv
    have hvec : (fun i ↦ (z i : ℂ)) = ![0, (z 1 : ℂ), (z 2 : ℂ)] := by
      funext i
      fin_cases i <;> simp [hz0]
    rw [← hvec]
    exact hFcomplex
  have hcircleReal : z 1 ^ 2 + z 2 ^ 2 = 0 := by
    exact_mod_cast hcircleComplex
  have hz1 : z 1 = 0 := by nlinarith [sq_nonneg (z 1), sq_nonneg (z 2)]
  have hz2 : z 2 = 0 := by nlinarith [sq_nonneg (z 1), sq_nonneg (z 2)]
  apply hz
  funext i
  fin_cases i <;> simp [hz0, hz1, hz2]

end Lemniscate

end DiskRigidity.Algebraic
