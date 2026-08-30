/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.ConvexBoundaryArcLength
public import DiskRigidity.Operator.LipschitzFTC
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# Polynomial moments of the rectifiable convex boundary

The radial parametrization is merely Lipschitz.  The Banach-valued
Lipschitz fundamental theorem nevertheless proves that every polynomial
differential has zero integral around one period.
-/

@[expose] public section

noncomputable section

open Bornology Filter MeasureTheory Metric Set Topology
open scoped NNReal Pointwise

namespace DiskRigidity.Operator

/-- A polynomial composed with the periodic radial boundary is globally
Lipschitz. -/
theorem exists_lipschitzWith_polynomial_radialBoundary
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (q : Polynomial ℂ) :
    ∃ C : ℝ≥0, LipschitzWith C
      (fun t ↦ q.eval (radialBoundaryParametrization K c t)) := by
  obtain ⟨Csigma, hsigma⟩ :=
    exists_lipschitzWith_radialBoundaryParametrization hconv hc hcompact
  obtain ⟨R, hKR⟩ := hcompact.isBounded.subset_closedBall (0 : ℂ)
  have hqcontDiff : ContDiff ℝ 1 (fun z : ℂ ↦ q.eval z) :=
    q.differentiable.contDiff.restrict_scalars ℝ
  obtain ⟨Cq, hq⟩ := hqcontDiff.contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_closedBall (0 : ℂ) R) (isCompact_closedBall (0 : ℂ) R)
  refine ⟨Cq * Csigma, lipschitzOnWith_univ.mp ?_⟩
  exact hq.comp hsigma.lipschitzOnWith fun t _ ↦ hKR <| by
    have hz : radialBoundaryParametrization K c t ∈ frontier K :=
      radialBoundaryParametrization_mem_frontier hconv hc hcompact t
    have hz' : radialBoundaryParametrization K c t ∈ closure K :=
      (frontier_subset_closure : frontier K ⊆ closure K) hz
    simpa only [hcompact.isClosed.closure_eq] using hz'

/-- The product of the boundary derivative with a polynomial boundary
trace is interval integrable. -/
theorem intervalIntegrable_deriv_mul_polynomial_radialBoundary
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (q : Polynomial ℂ) (a b : ℝ) :
    IntervalIntegrable
      (fun t ↦ deriv (radialBoundaryParametrization K c) t *
        q.eval (radialBoundaryParametrization K c t)) volume a b := by
  obtain ⟨C, hsigma⟩ :=
    exists_lipschitzWith_radialBoundaryParametrization hconv hc hcompact
  exact (intervalIntegrable_deriv_of_lipschitzWith hsigma a b).mul_continuousOn
    (q.differentiable.continuous.comp
      hsigma.continuous).continuousOn

/-- Every polynomial one-form has zero integral around the closed radial
boundary.  This is the nonsmooth version of the elementary identity
`∮ q(z) dz = 0`. -/
theorem intervalIntegral_deriv_mul_polynomial_radialBoundary_eq_zero
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (q : Polynomial ℂ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi),
        deriv (radialBoundaryParametrization K c) t *
          q.eval (radialBoundaryParametrization K c t) = 0 := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.eval_add]
      simp only [mul_add]
      rw [intervalIntegral.integral_add
        (intervalIntegrable_deriv_mul_polynomial_radialBoundary
          hconv hc hcompact p 0 (2 * Real.pi))
        (intervalIntegrable_deriv_mul_polynomial_radialBoundary
          hconv hc hcompact q 0 (2 * Real.pi)), hp, hq, add_zero]
  | monomial n a =>
      let d : ℂ := a / ((n + 1 : ℕ) : ℂ)
      let Q : Polynomial ℂ := Polynomial.monomial (n + 1) d
      let sigma := radialBoundaryParametrization K c
      obtain ⟨C, hQlip⟩ :=
        exists_lipschitzWith_polynomial_radialBoundary
          hconv hc hcompact Q
      have hFTC := intervalIntegral_deriv_eq_sub_of_lipschitzWith
        hQlip 0 (2 * Real.pi)
      have hclose : sigma (2 * Real.pi) = sigma 0 := by
        simpa [sigma] using
          (radialBoundaryParametrization_periodic K c 0)
      have hQclose : Q.eval (sigma (2 * Real.pi)) = Q.eval (sigma 0) := by
        rw [hclose]
      rw [hQclose, sub_self] at hFTC
      rw [← hFTC]
      apply intervalIntegral.integral_congr_ae
      filter_upwards
        [((exists_lipschitzWith_radialBoundaryParametrization
            hconv hc hcompact).choose_spec).ae_differentiableAt_real]
        with t ht _
      have hsigma : HasDerivAt sigma (deriv sigma t) t := ht.hasDerivAt
      have hpow := (hasDerivAt_pow (𝕜 := ℂ) (n + 1) (sigma t)).scomp t hsigma
      have hprimitive : HasDerivAt (fun s ↦ d * sigma s ^ (n + 1))
          (d * (deriv sigma t •
            (((n + 1 : ℕ) : ℂ) * sigma t ^ (n + 1 - 1)))) t := by
        simpa only [Function.comp_apply] using hpow.const_mul d
      have hQ : (fun s ↦ Q.eval (radialBoundaryParametrization K c s)) =
          (fun s ↦ d * sigma s ^ (n + 1)) := by
        funext s
        simp [Q, sigma]
      rw [hQ, hprimitive.deriv]
      simp only [Polynomial.eval_monomial]
      dsimp [d]
      have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      field_simp
      ring

/-- In terms of the outward normal and arclength, all polynomial moments
vanish: `∫ q(σ) ν ds = 0`. -/
theorem integral_polynomial_mul_normal_radialBoundary_eq_zero
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (q : Polynomial ℂ) :
    ∫ t, q.eval (radialBoundaryParametrization K c t) *
        radialOutwardUnitNormal K c t
      ∂radialBoundaryArcLengthMeasure K c = 0 := by
  rw [integral_radialBoundaryArcLengthMeasure_eq]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  have hzero := intervalIntegral_deriv_mul_polynomial_radialBoundary_eq_zero
    hconv hc hcompact q
  calc
    ∫ t in (0 : ℝ)..(2 * Real.pi),
        radialBoundarySpeed K c t •
          (q.eval (radialBoundaryParametrization K c t) *
            radialOutwardUnitNormal K c t) =
        Complex.I⁻¹ *
          ∫ t in (0 : ℝ)..(2 * Real.pi),
            deriv (radialBoundaryParametrization K c) t *
              q.eval (radialBoundaryParametrization K c t) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_ae
      filter_upwards
        [ae_deriv_eq_I_mul_normal_mul_speed hconv hc hcompact]
        with t ht _
      rw [ht]
      simp only [Complex.real_smul]
      field_simp
    _ = 0 := by rw [hzero, mul_zero]

end DiskRigidity.Operator
