/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Analysis.FullLevel
public import DiskRigidity.Analysis.ReducedTransfer
public import DiskRigidity.Analysis.StrictLemniscate
public import DiskRigidity.Analysis.TransferZeros
public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# From a reduced rational inner identity to the full boundary level

This file assembles Lemma 6.2 and Proposition 6.3.  Once the reduced
transfer quotient agrees with the extremizer on the closed numerical range,
coprimality removes all apparent interior poles, the direct resolvent
argument locates its zeros and poles, and the full lemniscate and strict
convexity conclusions follow.
-/

@[expose] public section

noncomputable section

open Polynomial Set
open scoped InnerProductSpace

namespace DiskRigidity.Analysis

/-- Cancellation in the analytic transfer identity.  The cross adjugate
coefficient is a nonzero polynomial, so it is nonzero on some interior
neighborhood; the identity theorem then removes it on the whole convex
interior. -/
theorem reduced_transfer_agrees_on_convex_interior
    {K : Set ℂ} (hconvex : Convex ℝ K) (hinterior : (interior K).Nonempty)
    (f : ℂ → ℂ) (U V A C : ℂ[X])
    (hC : C ≠ 0)
    (hf : DifferentiableOn ℂ f (interior K))
    (htransfer : U * C = (Polynomial.C 2 * A) * V)
    (hcross : ∀ z ∈ interior K, C.eval z * f z = 2 * A.eval z) :
    ∀ z ∈ interior K, U.eval z = f z * V.eval z := by
  have hCpoint : ∃ z ∈ interior K, C.eval z ≠ 0 := by
    by_contra hnot
    push Not at hnot
    obtain ⟨z₀, hz₀⟩ := hinterior
    have hevent : (fun z ↦ C.eval z) =ᶠ[nhds z₀] 0 := by
      filter_upwards [isOpen_interior.mem_nhds hz₀] with z hz
      exact hnot z hz
    have hfun : (fun z ↦ C.eval z) = 0 := by
      apply AnalyticOnNhd.eq_of_eventuallyEq
        (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) C) analyticOnNhd_const
      exact hevent
    apply hC
    apply Polynomial.funext
    intro z
    simpa using congrFun hfun z
  obtain ⟨z₀, hz₀, hCz₀⟩ := hCpoint
  let g : ℂ → ℂ := fun z ↦ U.eval z - f z * V.eval z
  have hganalytic : AnalyticOnNhd ℂ g (interior K) := by
    have hfanalytic : AnalyticOnNhd ℂ f (interior K) :=
      hf.analyticOnNhd isOpen_interior
    intro z hz
    exact (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) U z (mem_univ z)).sub
      ((hfanalytic z hz).mul
        (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) V z (mem_univ z)))
  have hproduct : ∀ z ∈ interior K, C.eval z * g z = 0 := by
    intro z hz
    have htransferz := congrArg (fun P : ℂ[X] ↦ P.eval z) htransfer
    simp only [Polynomial.eval_mul, Polynomial.eval_C] at htransferz
    dsimp only [g]
    rw [mul_sub]
    calc
      C.eval z * U.eval z - C.eval z * (f z * V.eval z) =
          U.eval z * C.eval z - (C.eval z * f z) * V.eval z := by ring
      _ = (2 * A.eval z) * V.eval z - (C.eval z * f z) * V.eval z := by
        rw [htransferz]
      _ = 0 := by rw [hcross z hz]; ring
  have hCevent : ∀ᶠ z in nhds z₀, C.eval z ≠ 0 :=
    C.continuous.continuousAt.eventually_ne hCz₀
  have hgevent : g =ᶠ[nhds z₀] 0 := by
    filter_upwards [hCevent, isOpen_interior.mem_nhds hz₀] with z hCz hz
    exact (mul_eq_zero.mp (hproduct z hz)).resolve_left hCz
  have hgzero : Set.EqOn g 0 (interior K) :=
    hganalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hconvex.interior.isPreconnected hz₀ hgevent
  intro z hz
  exact sub_eq_zero.mp (hgzero hz)

/-- An identity between a polynomial and a continuous polynomial multiple
which holds in the interior of a compact convex body also holds on its
boundary. -/
theorem polynomial_transfer_identity_on_compactConvex
    {K : Set ℂ} (hcompact : IsCompact K) (hconvex : Convex ℝ K)
    (hinterior : (interior K).Nonempty)
    (f : ℂ → ℂ) (U V : ℂ[X])
    (hf : ContinuousOn f K)
    (hidentity : ∀ z ∈ interior K, U.eval z = f z * V.eval z) :
    ∀ z ∈ K, U.eval z = f z * V.eval z := by
  have hclosure : closure (interior K) = K := by
    rw [hconvex.closure_interior_eq_closure_of_nonempty_interior hinterior,
      hcompact.isClosed.closure_eq]
  apply Set.EqOn.of_subset_closure hidentity
  · exact U.continuous.continuousOn
  · exact hf.mul V.continuous.continuousOn
  · exact interior_subset
  · rw [hclosure]

/-- A reduced rational identity which is inner on the boundary has the
entire numerical-range frontier as its full unit level. -/
theorem full_rationalLevel_and_strictConvex_of_reduced_inner_transfer
    {N : ℕ} (M : Operator.SquareMatrix (Fin (N + 1)))
    (x : Operator.EuclideanVector (Fin (N + 1))) (hx : x ≠ 0)
    (f : ℂ → ℂ) (U V C : ℂ[X])
    (hcoprime : IsCoprime U V)
    (hdegree : V.natDegree < U.natDegree)
    (htransfer : U * C =
      (Polynomial.C 2 * Operator.adjugateScalarNumerator M x x) * V)
    (hidentity : ∀ z ∈ Operator.numericalRange M,
      U.eval z = f z * V.eval z)
    (hinner : ∀ z ∈ interior (Operator.numericalRange M), ‖f z‖ < 1)
    (hboundary : ∀ z ∈ frontier (Operator.numericalRange M), ‖f z‖ = 1) :
    rationalSublevel U V = interior (Operator.numericalRange M) ∧
      rationalLevel U V = frontier (Operator.numericalRange M) ∧
      StrictConvex ℝ (Operator.numericalRange M) := by
  have hdenominator : ∀ z ∈ interior (Operator.numericalRange M),
      V.eval z ≠ 0 := by
    intro z hz hVz
    have hUz : U.eval z = 0 := by
      rw [hidentity z (interior_subset hz), hVz, mul_zero]
    rcases Polynomial.aeval_ne_zero_of_isCoprime hcoprime z with hUne | hVne
    · exact hUne hUz
    · exact hVne hVz
  have hlevel : ∀ z ∈ frontier (Operator.numericalRange M),
      ‖U.eval z‖ = ‖V.eval z‖ := by
    intro z hz
    have hzK : z ∈ Operator.numericalRange M := by
      rw [← (Operator.isCompact_numericalRange M).isClosed.closure_eq]
      exact frontier_subset_closure hz
    rw [hidentity z hzK, norm_mul, hboundary z hz, one_mul]
  have hinnerQuotient : ∀ z ∈ interior (Operator.numericalRange M),
      V.eval z ≠ 0 ∧ ‖U.eval z / V.eval z‖ < 1 := by
    intro z hz
    have hVz := hdenominator z hz
    refine ⟨hVz, ?_⟩
    have hquotient : U.eval z / V.eval z = f z := by
      apply (div_eq_iff hVz).2
      exact hidentity z (interior_subset hz)
    rw [hquotient]
    exact hinner z hz
  obtain ⟨hzeros, hpoles⟩ :=
    transfer_function_zero_pole_location_of_matrixResolvent
      M x hx hcoprime htransfer hdenominator hlevel
  have hfull := full_level_identity
    (Operator.isCompact_numericalRange M) hdegree hzeros hpoles
    hinnerQuotient hlevel
  refine ⟨hfull.1, hfull.2, ?_⟩
  exact strictConvex_of_full_rationalLevel
    (Operator.isCompact_numericalRange M) (Operator.numericalRange_convex M)
    U V hcoprime hfull.2

end DiskRigidity.Analysis
