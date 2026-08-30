/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Analysis.CauchyTransform
public import DiskRigidity.Operator.ResolventNumericalRange
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Topology.Closure

/-!
# Zeros and poles of the reduced transfer function

This file formalizes the algebraic cancellation and zero-location part of
Lemma 6.2.  The analytic input is kept in its exact usable form: the numerator
of the scalar resolvent has no zero off the convex set, the reduced rational
function is holomorphic in the interior, and its boundary values have modulus
one.
-/

@[expose] public section

open Polynomial
open MeasureTheory

namespace DiskRigidity.Analysis

/-- Equation (6.2) and positivity of a probability measure make the
polynomial numerator of a rational Cauchy transform nonzero off its convex
support. -/
theorem cauchy_numerator_ne_zero_off_convex
    {mu : Measure ℂ} [IsProbabilityMeasure mu]
    {K : Set ℂ} (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKne : K.Nonempty) (hmu : ∀ᵐ w ∂mu, w ∈ K)
    (A D : ℂ[X])
    (hquotient : ∀ z ∉ K,
      A.eval z / D.eval z = ∫ w : ℂ, (z - w)⁻¹ ∂mu) :
    ∀ z ∉ K, A.eval z ≠ 0 := by
  intro z hz hAzero
  have hnonzero :=
    cauchyTransform_ne_zero_off_convex' hKconv hKclosed hKne hmu hz
  apply hnonzero
  rw [← hquotient z hz, hAzero, zero_div]

/-- Coprimality of a reduced fraction lets one cancel its denominator from
the polynomial form of the transfer identity `U / V = 2 A / C`. -/
theorem reduced_numerator_dvd_cauchy_numerator
    {U V A C : ℂ[X]} (hUV : IsCoprime U V)
    (htransfer : U * C = (Polynomial.C 2 * A) * V) : U ∣ A := by
  have hdiv : U ∣ (Polynomial.C 2 * A) * V := by
    exact ⟨C, htransfer.symm⟩
  obtain ⟨Q, hQ⟩ := hUV.dvd_of_dvd_mul_right hdiv
  refine ⟨Polynomial.C (1 / 2) * Q, ?_⟩
  calc
    A = Polynomial.C (1 / 2) * (Polynomial.C 2 * A) := by
      rw [← mul_assoc, ← Polynomial.C_mul]
      norm_num
    _ = Polynomial.C (1 / 2) * (U * Q) := by rw [hQ]
    _ = U * (Polynomial.C (1 / 2) * Q) := by ring

/-- Coprime complex polynomials cannot vanish at the same point. -/
theorem eval_ne_zero_or_eval_ne_zero_of_isCoprime
    {U V : ℂ[X]} (hUV : IsCoprime U V) (z : ℂ) :
    U.eval z ≠ 0 ∨ V.eval z ≠ 0 := by
  simpa [Polynomial.aeval_def, Polynomial.eval₂_at_apply] using
    (Polynomial.aeval_ne_zero_of_isCoprime hUV z)

/-- Every zero of a divisor of a polynomial lies where the latter can
vanish. -/
theorem eval_zero_mem_of_dvd_of_eval_ne_zero_off
    {K : Set ℂ} {U A : ℂ[X]} (hUA : U ∣ A)
    (hA : ∀ z ∉ K, A.eval z ≠ 0) {z : ℂ} (hz : U.eval z = 0) : z ∈ K := by
  by_contra hzK
  obtain ⟨Q, rfl⟩ := hUA
  exact hA z hzK (by simp [hz])

/-- A reduced numerator which divides the nonvanishing Cauchy numerator and
has unimodular boundary quotient has all of its zeros in the interior. -/
theorem numerator_zeros_mem_interior
    {K : Set ℂ} {U V A : ℂ[X]}
    (hUV : IsCoprime U V) (hUA : U ∣ A)
    (hA : ∀ z ∉ K, A.eval z ≠ 0)
    (hlevel : ∀ z ∈ frontier K, ‖U.eval z‖ = ‖V.eval z‖)
    {z : ℂ} (hz : U.eval z = 0) : z ∈ interior K := by
  have hzK : z ∈ K := eval_zero_mem_of_dvd_of_eval_ne_zero_off hUA hA hz
  rw [mem_interior_iff_notMem_frontier hzK]
  intro hzfrontier
  have hVzero : V.eval z = 0 := by
    apply norm_eq_zero.mp
    rw [← hlevel z hzfrontier, hz, norm_zero]
  exact (eval_ne_zero_or_eval_ne_zero_of_isCoprime hUV z).elim
    (fun h ↦ h hz) (fun h ↦ h hVzero)

/-- If the reduced quotient has no pole in the interior and has unimodular
boundary values, every zero of its denominator lies outside the closed set. -/
theorem denominator_zeros_not_mem
    {K : Set ℂ} {U V : ℂ[X]}
    (hUV : IsCoprime U V)
    (hinterior : ∀ z ∈ interior K, V.eval z ≠ 0)
    (hlevel : ∀ z ∈ frontier K, ‖U.eval z‖ = ‖V.eval z‖)
    {z : ℂ} (hz : V.eval z = 0) : z ∉ K := by
  intro hzK
  have hznotint : z ∉ interior K := fun hzint ↦ hinterior z hzint hz
  have hzfrontier : z ∈ frontier K :=
    (mem_frontier_iff_notMem_interior hzK).mpr hznotint
  have hUzero : U.eval z = 0 := by
    apply norm_eq_zero.mp
    rw [hlevel z hzfrontier, hz, norm_zero]
  exact (eval_ne_zero_or_eval_ne_zero_of_isCoprime hUV z).elim
    (fun h ↦ h hUzero) (fun h ↦ h hz)

/-- Lemma 6.2 in reduced polynomial form.  The transfer identity supplies
the divisibility used for the numerator, while holomorphy and the inner
boundary condition locate the denominator zeros. -/
theorem transfer_function_zero_pole_location
    {K : Set ℂ} {U V A C : ℂ[X]}
    (hUV : IsCoprime U V)
    (htransfer : U * C = (Polynomial.C 2 * A) * V)
    (hA : ∀ z ∉ K, A.eval z ≠ 0)
    (hinterior : ∀ z ∈ interior K, V.eval z ≠ 0)
    (hlevel : ∀ z ∈ frontier K, ‖U.eval z‖ = ‖V.eval z‖) :
    (∀ z, U.eval z = 0 → z ∈ interior K) ∧
      (∀ z, V.eval z = 0 → z ∉ K) := by
  have hUA : U ∣ A :=
    reduced_numerator_dvd_cauchy_numerator hUV htransfer
  exact ⟨fun _ hz ↦ numerator_zeros_mem_interior hUV hUA hA hlevel hz,
    fun _ hz ↦ denominator_zeros_not_mem hUV hinterior hlevel hz⟩

/-- The complete measure-theoretic form of Lemma 6.2: equation (6.2), the
reduced transfer identity, interior holomorphy, and the unimodular boundary
condition imply the asserted zero and pole locations. -/
theorem transfer_function_zero_pole_location_of_state
    {mu : Measure ℂ} [IsProbabilityMeasure mu]
    {K : Set ℂ} (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKne : K.Nonempty) (hmu : ∀ᵐ w ∂mu, w ∈ K)
    {U V A C D : ℂ[X]}
    (hUV : IsCoprime U V)
    (htransfer : U * C = (Polynomial.C 2 * A) * V)
    (hquotient : ∀ z ∉ K,
      A.eval z / D.eval z = ∫ w : ℂ, (z - w)⁻¹ ∂mu)
    (hinterior : ∀ z ∈ interior K, V.eval z ≠ 0)
    (hlevel : ∀ z ∈ frontier K, ‖U.eval z‖ = ‖V.eval z‖) :
    (∀ z, U.eval z = 0 → z ∈ interior K) ∧
      (∀ z, V.eval z = 0 → z ∉ K) := by
  exact transfer_function_zero_pole_location hUV htransfer
    (cauchy_numerator_ne_zero_off_convex hKconv hKclosed hKne hmu A D hquotient)
    hinterior hlevel

/-- The matrix-resolvent form of Lemma 6.2.  For the diagonal coefficient
`x*(zI-M)⁻¹x`, nonvanishing off `W(M)` follows directly from the inverse
equation, so no representing measure is needed for the zero-location
conclusion. -/
theorem transfer_function_zero_pole_location_of_matrixResolvent
    {N : ℕ} (M : Operator.SquareMatrix (Fin (N + 1)))
    (x : Operator.EuclideanVector (Fin (N + 1))) (hx : x ≠ 0)
    {U V C : ℂ[X]}
    (hUV : IsCoprime U V)
    (htransfer : U * C =
      (Polynomial.C 2 * Operator.adjugateScalarNumerator M x x) * V)
    (hinterior : ∀ z ∈ interior (Operator.numericalRange M), V.eval z ≠ 0)
    (hlevel : ∀ z ∈ frontier (Operator.numericalRange M),
      ‖U.eval z‖ = ‖V.eval z‖) :
    (∀ z, U.eval z = 0 → z ∈ interior (Operator.numericalRange M)) ∧
      (∀ z, V.eval z = 0 → z ∉ Operator.numericalRange M) := by
  exact transfer_function_zero_pole_location hUV htransfer
    (fun z hz ↦
      Operator.adjugateScalarNumerator_ne_zero_off_numericalRange M x hx hz)
    hinterior hlevel

end DiskRigidity.Analysis
