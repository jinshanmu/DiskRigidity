/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.SpectralJetAlgebra
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Algebra.Polynomial.Div

/-!
# Division by a polynomial after cancellation of all root jets

This file supplies the elementary removable-singularity statement used by
the concrete holomorphic Cauchy formula.  If an analytic function vanishes
to at least the multiplicity of every root of a nonzero polynomial, its
pointwise quotient by that polynomial has a canonical analytic extension.
-/

@[expose] public section

noncomputable section

open Filter Function Set
open scoped Topology

namespace DiskRigidity.Complex

/-- The canonical pointwise extension of `f / p` across the finite zero set
of `p`.  At a zero it is defined by the punctured-neighborhood limit. -/
def removablePolynomialQuotient (f : ℂ → ℂ) (p : Polynomial ℂ) : ℂ → ℂ :=
  fun z ↦ if p.eval z = 0 then
    limUnder (nhdsWithin z {z}ᶜ) (fun w ↦ f w / p.eval w)
  else f z / p.eval z

@[simp]
theorem removablePolynomialQuotient_eq_of_eval_ne_zero
    (f : ℂ → ℂ) (p : Polynomial ℂ) {z : ℂ}
    (hz : p.eval z ≠ 0) :
    removablePolynomialQuotient f p z = f z / p.eval z := by
  simp [removablePolynomialQuotient, hz]

/-- Cancellation of the prescribed root jets makes the canonical quotient
holomorphic on the original open set. -/
theorem differentiableOn_removablePolynomialQuotient
    {f : ℂ → ℂ} {p : Polynomial ℂ} (hp : p ≠ 0)
    {V : Set ℂ} (hVo : IsOpen V) (hf : DifferentiableOn ℂ f V)
    (hzero : ∀ a ∈ V, p.eval a = 0 →
      ∀ k < p.rootMultiplicity a, iteratedDeriv k f a = 0) :
    DifferentiableOn ℂ (removablePolynomialQuotient f p) V := by
  intro a haV
  have hfa : AnalyticAt ℂ f a := hf.analyticAt (hVo.mem_nhds haV)
  by_cases hpa : p.eval a = 0
  · let m := p.rootMultiplicity a
    let r := p /ₘ (Polynomial.X - Polynomial.C a) ^ m
    have hrne : r.eval a ≠ 0 := by
      simpa only [r, m] using
        Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero a hp
    have horder : (m : ℕ∞) ≤ analyticOrderAt f a :=
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hfa).2
        (hzero a haV hpa)
    obtain ⟨F, hFa, hfactor⟩ :=
      (natCast_le_analyticOrderAt hfa).1 horder
    have hpfactor (z : ℂ) :
        p.eval z = (z - a) ^ m * r.eval z := by
      have hpoly := p.pow_mul_divByMonic_rootMultiplicity_eq a
      have := congrArg (fun q : Polynomial ℂ ↦ q.eval z) hpoly
      simpa [r, m] using this.symm
    have hrEventually : ∀ᶠ z in nhds a, r.eval z ≠ 0 :=
      (r.continuous.continuousAt.eventually_ne hrne)
    have hrawEq :
        (fun z ↦ f z / p.eval z) =ᶠ[nhdsWithin a {a}ᶜ]
          (fun z ↦ F z / r.eval z) := by
      filter_upwards [hfactor.filter_mono nhdsWithin_le_nhds,
        hrEventually.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with z hFz hrz hza
      have hza' : z ≠ a := by simpa using hza
      rw [hFz, hpfactor]
      have hzpow : (z - a) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hza')
      simp only [smul_eq_mul]
      field_simp
    have hquotAnalytic : AnalyticAt ℂ (fun z ↦ F z / r.eval z) a :=
      hFa.div (r.differentiable.analyticAt a) hrne
    have hrawTendsto : Tendsto (fun z ↦ f z / p.eval z) (nhdsWithin a {a}ᶜ)
        (nhds (F a / r.eval a)) :=
      (tendsto_congr' hrawEq).2
        hquotAnalytic.continuousAt.continuousWithinAt
    have hlim :
        limUnder (nhdsWithin a {a}ᶜ) (fun z ↦ f z / p.eval z) =
          F a / r.eval a := hrawTendsto.limUnder_eq
    have hpEventually : ∀ᶠ z in nhds a, z ≠ a → p.eval z ≠ 0 := by
      filter_upwards [hrEventually] with z hrz hza
      rw [hpfactor]
      exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hza)) hrz
    have heq : removablePolynomialQuotient f p =ᶠ[nhds a]
        (fun z ↦ F z / r.eval z) := by
      filter_upwards [hfactor, hrEventually, hpEventually] with z hFz hrz hpz
      by_cases hza : z = a
      · subst z
        simp [removablePolynomialQuotient, hpa, hlim]
      · have hpzne : p.eval z ≠ 0 := hpz hza
        rw [removablePolynomialQuotient_eq_of_eval_ne_zero f p hpzne,
          hFz, hpfactor]
        have hzpow : (z - a) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hza)
        simp only [smul_eq_mul]
        field_simp
    exact (hquotAnalytic.differentiableAt.congr_of_eventuallyEq heq).differentiableWithinAt
  · have hpEventually : ∀ᶠ z in nhds a, p.eval z ≠ 0 :=
      p.continuous.continuousAt.eventually_ne hpa
    have heq : removablePolynomialQuotient f p =ᶠ[nhds a]
        (fun z ↦ f z / p.eval z) := by
      filter_upwards [hpEventually] with z hz
      exact removablePolynomialQuotient_eq_of_eval_ne_zero f p hz
    have hraw : DifferentiableAt ℂ (fun z ↦ f z / p.eval z) a :=
      (hf.differentiableAt (hVo.mem_nhds haV)).div
        p.differentiable.differentiableAt hpa
    exact (hraw.congr_of_eventuallyEq heq).differentiableWithinAt

end DiskRigidity.Complex
