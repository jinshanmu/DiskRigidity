/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.AnalyticContact
public import DiskRigidity.Algebraic.LemniscateOval
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Regularity of a rational lemiscate from the rational derivative

This file proves the differential calculation used between Propositions 6.1
and 7.1.  At a real affine point of `|U| = |V|`, coprimality makes both
values nonzero.  Nonvanishing of the numerator of `(U / V)'` then forces the
real lemniscate gradient, and hence its complex projective gradient, to be
nonzero.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace LemniscateRegular

open Matrix MvPolynomial Polynomial
open ProjectiveDual
open scoped ComplexConjugate

private theorem hasDerivAt_eval_horizontal (p : ℂ[X]) (X Y : ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ p.eval ((t : ℂ) + (Y : ℂ) * Complex.I))
      (p.derivative.eval ((X : ℂ) + (Y : ℂ) * Complex.I)) X := by
  let z : ℂ := (X : ℂ) + (Y : ℂ) * Complex.I
  have hinner : HasDerivAt
      (fun w : ℂ ↦ w + (Y : ℂ) * Complex.I) 1 (X : ℂ) :=
    (hasDerivAt_id (X : ℂ)).add_const _
  simpa [z] using
    (((p.hasDerivAt z).comp (X : ℂ) hinner).comp_ofReal)

private theorem hasDerivAt_eval_vertical (p : ℂ[X]) (X Y : ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ p.eval ((X : ℂ) + (t : ℂ) * Complex.I))
      (p.derivative.eval ((X : ℂ) + (Y : ℂ) * Complex.I) * Complex.I) Y := by
  let z : ℂ := (X : ℂ) + (Y : ℂ) * Complex.I
  have hinner : HasDerivAt
      (fun w : ℂ ↦ (X : ℂ) + w * Complex.I) Complex.I (Y : ℂ) := by
    simpa using ((hasDerivAt_id (Y : ℂ)).mul_const Complex.I).const_add (X : ℂ)
  simpa [z] using
    (((p.hasDerivAt z).comp (Y : ℂ) hinner).comp_ofReal)

private theorem hasDerivAt_normSq_complex
    {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t ↦ (Complex.normSq (f t) : ℂ))
      (f' * conj (f x) + f x * conj f') x := by
  have hre : HasDerivAt (fun t ↦ (f t).re) f'.re x := by
    simpa only [Function.comp_apply, Complex.reCLM_apply] using!
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hf
  have him : HasDerivAt (fun t ↦ (f t).im) f'.im x := by
    simpa only [Function.comp_apply, Complex.imCLM_apply] using!
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hf
  have hreal : HasDerivAt (fun t ↦ Complex.normSq (f t))
      (f'.re * (f x).re + (f x).re * f'.re +
        (f'.im * (f x).im + (f x).im * f'.im)) x := by
    simpa only [Complex.normSq_apply] using! (hre.mul hre).add (him.mul him)
  convert! hreal.ofReal_comp using 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

private theorem hasDerivAt_normSq_real
    {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t ↦ Complex.normSq (f t))
      (f'.re * (f x).re + (f x).re * f'.re +
        (f'.im * (f x).im + (f x).im * f'.im)) x := by
  have hre : HasDerivAt (fun t ↦ (f t).re) f'.re x := by
    simpa only [Function.comp_apply, Complex.reCLM_apply] using!
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hf
  have him : HasDerivAt (fun t ↦ (f t).im) f'.im x := by
    simpa only [Function.comp_apply, Complex.imCLM_apply] using!
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hf
  simpa only [Complex.normSq_apply] using! (hre.mul hre).add (him.mul him)

/-- The affine value of the real lemniscate equation is
`normSq (U z) - normSq (V z)`. -/
theorem eval_realLevelPolynomial_affine (U V : ℂ[X]) (X Y : ℝ) :
    MvPolynomial.eval ![1, X, Y] (LemniscateOval.realLevelPolynomial U V) =
      Complex.normSq (U.eval ((X : ℂ) + (Y : ℂ) * Complex.I)) -
        Complex.normSq (V.eval ((X : ℂ) + (Y : ℂ) * Complex.I)) := by
  have h := Lemniscate.eval_primalOrderProjectiveLevelPolynomial_affine U V X Y
  rw [← LemniscateOval.map_realLevelPolynomial] at h
  have hvec : (![(1 : ℂ), (X : ℂ), (Y : ℂ)] : Fin 3 → ℂ) =
      fun i ↦ ((![1, X, Y] : Fin 3 → ℝ) i : ℂ) := by
    funext i
    fin_cases i <;> rfl
  rw [hvec, RealComponent.eval_map_real] at h
  apply Complex.ofReal_injective
  simpa using h

/-- Horizontal differential of the real affine lemniscate equation. -/
theorem deriv_realLevel_horizontal (U V : ℂ[X]) (X Y : ℝ) :
    deriv (fun t : ℝ ↦ MvPolynomial.eval ![1, t, Y]
      (LemniscateOval.realLevelPolynomial U V)) X =
      let z := (X : ℂ) + (Y : ℂ) * Complex.I
      let u := U.eval z
      let v := V.eval z
      let du := U.derivative.eval z
      let dv := V.derivative.eval z
      du.re * u.re + u.re * du.re + (du.im * u.im + u.im * du.im) -
        (dv.re * v.re + v.re * dv.re + (dv.im * v.im + v.im * dv.im)) := by
  let z := (X : ℂ) + (Y : ℂ) * Complex.I
  have hU := hasDerivAt_normSq_real (hasDerivAt_eval_horizontal U X Y)
  have hV := hasDerivAt_normSq_real (hasDerivAt_eval_horizontal V X Y)
  have h := hU.sub hV
  have heq : (fun t : ℝ ↦ MvPolynomial.eval ![1, t, Y]
      (LemniscateOval.realLevelPolynomial U V)) =
      (fun t : ℝ ↦
        Complex.normSq (U.eval ((t : ℂ) + (Y : ℂ) * Complex.I)) -
          Complex.normSq (V.eval ((t : ℂ) + (Y : ℂ) * Complex.I))) := by
    funext t
    exact eval_realLevelPolynomial_affine U V t Y
  rw [heq]
  change deriv
    ((fun t : ℝ ↦
      Complex.normSq (U.eval ((t : ℂ) + (Y : ℂ) * Complex.I))) -
    (fun t : ℝ ↦
      Complex.normSq (V.eval ((t : ℂ) + (Y : ℂ) * Complex.I)))) X = _
  simpa [z] using h.deriv

/-- Vertical differential of the real affine lemniscate equation. -/
theorem deriv_realLevel_vertical (U V : ℂ[X]) (X Y : ℝ) :
    deriv (fun t : ℝ ↦ MvPolynomial.eval ![1, X, t]
      (LemniscateOval.realLevelPolynomial U V)) Y =
      let z := (X : ℂ) + (Y : ℂ) * Complex.I
      let u := U.eval z
      let v := V.eval z
      let du := U.derivative.eval z * Complex.I
      let dv := V.derivative.eval z * Complex.I
      du.re * u.re + u.re * du.re + (du.im * u.im + u.im * du.im) -
        (dv.re * v.re + v.re * dv.re + (dv.im * v.im + v.im * dv.im)) := by
  let z := (X : ℂ) + (Y : ℂ) * Complex.I
  have hU := hasDerivAt_normSq_real (hasDerivAt_eval_vertical U X Y)
  have hV := hasDerivAt_normSq_real (hasDerivAt_eval_vertical V X Y)
  have h := hU.sub hV
  have heq : (fun t : ℝ ↦ MvPolynomial.eval ![1, X, t]
      (LemniscateOval.realLevelPolynomial U V)) =
      (fun t : ℝ ↦
        Complex.normSq (U.eval ((X : ℂ) + (t : ℂ) * Complex.I)) -
          Complex.normSq (V.eval ((X : ℂ) + (t : ℂ) * Complex.I))) := by
    funext t
    exact eval_realLevelPolynomial_affine U V X t
  rw [heq]
  change deriv
    ((fun t : ℝ ↦
      Complex.normSq (U.eval ((X : ℂ) + (t : ℂ) * Complex.I))) -
    (fun t : ℝ ↦
      Complex.normSq (V.eval ((X : ℂ) + (t : ℂ) * Complex.I)))) Y = _
  simpa [z] using h.deriv

/-- A real regular point remains regular after coefficient extension to
`ℂ`. -/
theorem regularAt_map_real
    {N : ℕ} {P : MvPolynomial (Fin N) ℝ} {x : Fin N → ℝ}
    (hP : RegularAt P x) :
    RegularAt (MvPolynomial.map (algebraMap ℝ ℂ) P)
      (fun i ↦ (x i : ℂ)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hx
    apply hP.1.1
    funext i
    exact Complex.ofReal_injective (congrFun hx i)
  · rw [RealComponent.eval_map_real]
    simp [hP.1.2]
  · intro hgradient
    apply hP.2
    rw [RealComponent.gradient_map_real] at hgradient
    funext i
    apply Complex.ofReal_injective
    exact congrFun hgradient i

/-- **Rational-derivative regularity bridge.**  At a point of the level
`|U| = |V|`, coprimality and nonvanishing of the numerator of `(U / V)'`
force regularity of the real projective lemniscate equation. -/
theorem regularAt_realLevelPolynomial_of_coprime_of_wronskian_ne_zero
    (U V : ℂ[X]) (hcoprime : IsCoprime U V) (X Y : ℝ)
    (hlevel : ‖U.eval ((X : ℂ) + (Y : ℂ) * Complex.I)‖ =
      ‖V.eval ((X : ℂ) + (Y : ℂ) * Complex.I)‖)
    (hwronskian :
      (U.derivative * V - U * V.derivative).eval
        ((X : ℂ) + (Y : ℂ) * Complex.I) ≠ 0) :
    RegularAt (LemniscateOval.realLevelPolynomial U V) ![1, X, Y] := by
  let z : ℂ := (X : ℂ) + (Y : ℂ) * Complex.I
  let u : ℂ := U.eval z
  let v : ℂ := V.eval z
  let du : ℂ := U.derivative.eval z
  let dv : ℂ := V.derivative.eval z
  let L := LemniscateOval.realLevelPolynomial U V
  have hvalues : u ≠ 0 ∨ v ≠ 0 := by
    simpa [u, v, Polynomial.aeval_def] using
      Polynomial.aeval_ne_zero_of_isCoprime hcoprime z
  have hu : u ≠ 0 := by
    rcases hvalues with hu | hv
    · exact hu
    · intro hu0
      apply hv
      apply norm_eq_zero.mp
      rw [← hlevel]
      simp [u, z, hu0]
  have hv : v ≠ 0 := by
    intro hv0
    apply hu
    apply norm_eq_zero.mp
    rw [hlevel]
    simp [v, z, hv0]
  have hLzero : MvPolynomial.eval ![1, X, Y] L = 0 := by
    rw [eval_realLevelPolynomial_affine]
    apply sub_eq_zero.mpr
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hlevel]
  refine ⟨⟨?_, hLzero⟩, ?_⟩
  · intro hpoint
    have := congrFun hpoint (0 : Fin 3)
    norm_num at this
  · intro hgradient
    let horizontal : ℝ → Fin 3 → ℝ := fun t ↦ ![1, t, Y]
    let vertical : ℝ → Fin 3 → ℝ := fun t ↦ ![1, X, t]
    have hhorizontalAnalytic : ∀ i,
        AnalyticAt ℝ (fun t ↦ horizontal t i) X := by
      intro i
      fin_cases i
      · simpa [horizontal] using
          (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ ↦ (1 : ℝ)) X)
      · change AnalyticAt ℝ id X
        exact analyticAt_id
      · simpa [horizontal] using
          (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ ↦ Y) X)
    have hverticalAnalytic : ∀ i,
        AnalyticAt ℝ (fun t ↦ vertical t i) Y := by
      intro i
      fin_cases i
      · simpa [vertical] using
          (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ ↦ (1 : ℝ)) Y)
      · simpa [vertical] using
          (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ ↦ X) Y)
      · change AnalyticAt ℝ id Y
        exact analyticAt_id
    have hxformula := AnalyticContact.deriv_eval_mvPolynomial L
      hhorizontalAnalytic
    have hyformula := AnalyticContact.deriv_eval_mvPolynomial L
      hverticalAnalytic
    have hxzero : deriv (fun t ↦ MvPolynomial.eval (horizontal t) L) X = 0 := by
      rw [hxformula]
      rw [directionalDerivative, hgradient]
      simp [dotProduct]
    have hyzero : deriv (fun t ↦ MvPolynomial.eval (vertical t) L) Y = 0 := by
      rw [hyformula]
      rw [directionalDerivative, hgradient]
      simp [dotProduct]
    have hx := deriv_realLevel_horizontal U V X Y
    have hy := deriv_realLevel_vertical U V X Y
    have hx' :
        du.re * u.re + u.re * du.re + (du.im * u.im + u.im * du.im) -
          (dv.re * v.re + v.re * dv.re + (dv.im * v.im + v.im * dv.im)) = 0 := by
      rw [← hx]
      simpa [horizontal, L] using hxzero
    have hy' :
        (du * Complex.I).re * u.re + u.re * (du * Complex.I).re +
            ((du * Complex.I).im * u.im + u.im * (du * Complex.I).im) -
          ((dv * Complex.I).re * v.re + v.re * (dv * Complex.I).re +
            ((dv * Complex.I).im * v.im + v.im * (dv * Complex.I).im)) = 0 := by
      rw [← hy]
      simpa [vertical, L] using hyzero
    have hcontact : du * conj u - dv * conj v = 0 := by
      rw [Complex.ext_iff]
      constructor
      · simp [Complex.mul_re]
        linarith
      · simp [Complex.mul_im]
        simp [Complex.mul_re, Complex.mul_im] at hy'
        linarith
    have hnormSq : Complex.normSq u = Complex.normSq v := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      simpa [u, v, z] using hlevel
    have hproducts : u * conj u = v * conj v := by
      rw [Complex.mul_conj, Complex.mul_conj, hnormSq]
    have hproductZero : (du * v - u * dv) * conj v = 0 := by
      calc
        (du * v - u * dv) * conj v =
            du * (v * conj v) - u * dv * conj v := by ring
        _ = du * (u * conj u) - u * dv * conj v := by rw [hproducts]
        _ = u * (du * conj u - dv * conj v) := by ring
        _ = 0 := by rw [hcontact, mul_zero]
    have hw : du * v - u * dv = 0 :=
      (mul_eq_zero.mp hproductZero).resolve_right
        ((_root_.map_ne_zero (starRingEnd ℂ)).2 hv)
    apply hwronskian
    simpa [u, v, du, dv, z] using hw

/-- Complex projective form of
`regularAt_realLevelPolynomial_of_coprime_of_wronskian_ne_zero`. -/
theorem regularAt_primalOrderProjectiveLevelPolynomial_of_coprime_of_wronskian_ne_zero
    (U V : ℂ[X]) (hcoprime : IsCoprime U V) (X Y : ℝ)
    (hlevel : ‖U.eval ((X : ℂ) + (Y : ℂ) * Complex.I)‖ =
      ‖V.eval ((X : ℂ) + (Y : ℂ) * Complex.I)‖)
    (hwronskian :
      (U.derivative * V - U * V.derivative).eval
        ((X : ℂ) + (Y : ℂ) * Complex.I) ≠ 0) :
    RegularAt (Lemniscate.primalOrderProjectiveLevelPolynomial U V)
      ![(1 : ℂ), (X : ℂ), (Y : ℂ)] := by
  rw [← LemniscateOval.map_realLevelPolynomial]
  have hregular := regularAt_map_real
    (regularAt_realLevelPolynomial_of_coprime_of_wronskian_ne_zero
      U V hcoprime X Y hlevel hwronskian)
  have hpoint : (fun i ↦ ((![1, X, Y] : Fin 3 → ℝ) i : ℂ)) =
      ![(1 : ℂ), (X : ℂ), (Y : ℂ)] := by
    funext i
    fin_cases i <;> rfl
  rwa [hpoint] at hregular

/-- Setwise coordinate form of the rational-derivative regularity bridge.
It is the direct input needed by the end-to-end circle theorem after the
analytic proof that `(U / V)'` has no boundary zero. -/
theorem regularAt_primalOrderProjectiveLevelPolynomial_on_set
    (U V : ℂ[X]) (hcoprime : IsCoprime U V)
    (S : Set (Fin 2 → ℝ))
    (hlevel : ∀ x ∈ S,
      ‖U.eval ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I)‖ =
        ‖V.eval ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I)‖)
    (hwronskian : ∀ x ∈ S,
      (U.derivative * V - U * V.derivative).eval
        ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I) ≠ 0) :
    ∀ x ∈ S, RegularAt
      (Lemniscate.primalOrderProjectiveLevelPolynomial U V)
      (LemniscateOval.complexAffinePoint x) := by
  intro x hx
  have hregular :=
    regularAt_primalOrderProjectiveLevelPolynomial_of_coprime_of_wronskian_ne_zero
      U V hcoprime (x 0) (x 1) (hlevel x hx) (hwronskian x hx)
  have hpoint : LemniscateOval.complexAffinePoint x =
      ![(1 : ℂ), (x 0 : ℂ), (x 1 : ℂ)] := by
    funext i
    fin_cases i <;> rfl
  rwa [hpoint]

/-- Horizontal differential of the affine lemniscate equation. -/
theorem deriv_affineLevel_horizontal (U V : ℂ[X]) (X Y : ℝ) :
    deriv (fun t : ℝ ↦
      MvPolynomial.eval ![(1 : ℂ), (t : ℂ), (Y : ℂ)]
        (Lemniscate.primalOrderProjectiveLevelPolynomial U V)) X =
      let z := (X : ℂ) + (Y : ℂ) * Complex.I
      U.derivative.eval z * conj (U.eval z) +
          U.eval z * conj (U.derivative.eval z) -
        (V.derivative.eval z * conj (V.eval z) +
          V.eval z * conj (V.derivative.eval z)) := by
  let z := (X : ℂ) + (Y : ℂ) * Complex.I
  have hU := hasDerivAt_normSq_complex
    (hasDerivAt_eval_horizontal U X Y)
  have hV := hasDerivAt_normSq_complex
    (hasDerivAt_eval_horizontal V X Y)
  have h := hU.sub hV
  have heq : (fun t : ℝ ↦
      MvPolynomial.eval ![(1 : ℂ), (t : ℂ), (Y : ℂ)]
        (Lemniscate.primalOrderProjectiveLevelPolynomial U V)) =
      (fun t : ℝ ↦
        (Complex.normSq (U.eval ((t : ℂ) + (Y : ℂ) * Complex.I)) : ℂ) -
        (Complex.normSq (V.eval ((t : ℂ) + (Y : ℂ) * Complex.I)) : ℂ)) := by
    funext t
    exact Lemniscate.eval_primalOrderProjectiveLevelPolynomial_affine U V t Y
  rw [heq]
  change deriv
    ((fun t : ℝ ↦
      (Complex.normSq (U.eval ((t : ℂ) + (Y : ℂ) * Complex.I)) : ℂ)) -
    (fun t : ℝ ↦
      (Complex.normSq (V.eval ((t : ℂ) + (Y : ℂ) * Complex.I)) : ℂ))) X = _
  simpa [z] using h.deriv

/-- Vertical differential of the affine lemniscate equation. -/
theorem deriv_affineLevel_vertical (U V : ℂ[X]) (X Y : ℝ) :
    deriv (fun t : ℝ ↦
      MvPolynomial.eval ![(1 : ℂ), (X : ℂ), (t : ℂ)]
        (Lemniscate.primalOrderProjectiveLevelPolynomial U V)) Y =
      let z := (X : ℂ) + (Y : ℂ) * Complex.I
      (U.derivative.eval z * Complex.I) * conj (U.eval z) +
          U.eval z * conj (U.derivative.eval z * Complex.I) -
        ((V.derivative.eval z * Complex.I) * conj (V.eval z) +
          V.eval z * conj (V.derivative.eval z * Complex.I)) := by
  let z := (X : ℂ) + (Y : ℂ) * Complex.I
  have hU := hasDerivAt_normSq_complex
    (hasDerivAt_eval_vertical U X Y)
  have hV := hasDerivAt_normSq_complex
    (hasDerivAt_eval_vertical V X Y)
  have h := hU.sub hV
  have heq : (fun t : ℝ ↦
      MvPolynomial.eval ![(1 : ℂ), (X : ℂ), (t : ℂ)]
        (Lemniscate.primalOrderProjectiveLevelPolynomial U V)) =
      (fun t : ℝ ↦
        (Complex.normSq (U.eval ((X : ℂ) + (t : ℂ) * Complex.I)) : ℂ) -
        (Complex.normSq (V.eval ((X : ℂ) + (t : ℂ) * Complex.I)) : ℂ)) := by
    funext t
    exact Lemniscate.eval_primalOrderProjectiveLevelPolynomial_affine U V X t
  rw [heq]
  change deriv
    ((fun t : ℝ ↦
      (Complex.normSq (U.eval ((X : ℂ) + (t : ℂ) * Complex.I)) : ℂ)) -
    (fun t : ℝ ↦
      (Complex.normSq (V.eval ((X : ℂ) + (t : ℂ) * Complex.I)) : ℂ))) Y = _
  simpa [z] using h.deriv

/-- Nonvanishing of the ordinary rational derivative gives nonvanishing of
its polynomial numerator.  Coprimality and the level equality discharge the
denominator condition. -/
theorem wronskian_eval_ne_zero_of_deriv_quotient_ne_zero
    (U V : ℂ[X]) (hcoprime : IsCoprime U V) (z : ℂ)
    (hlevel : ‖U.eval z‖ = ‖V.eval z‖)
    (hderiv : deriv (fun w ↦ U.eval w / V.eval w) z ≠ 0) :
    (U.derivative * V - U * V.derivative).eval z ≠ 0 := by
  have hvalues := Polynomial.aeval_ne_zero_of_isCoprime hcoprime z
  have hV : V.eval z ≠ 0 := by
    intro hVz
    have hUz : U.eval z = 0 := by
      apply norm_eq_zero.mp
      rw [hlevel, hVz, norm_zero]
    rcases hvalues with hUne | hVne
    · exact hUne hUz
    · exact hVne hVz
  have hformula := (U.hasDerivAt z).div (V.hasDerivAt z) hV
  intro hzero
  apply hderiv
  change deriv ((fun w ↦ U.eval w) / (fun w ↦ V.eval w)) z = 0
  rw [hformula.deriv]
  have hzero' :
      U.derivative.eval z * V.eval z - U.eval z * V.derivative.eval z = 0 := by
    simpa using hzero
  rw [hzero', zero_div]

end LemniscateRegular

end DiskRigidity.Algebraic
