/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.ConvexNoncriticalLevel
public import DiskRigidity.Analysis.RationalInnerLevel
public import DiskRigidity.Operator.RationalLevelCircle

/-!
# The full rational-level endgame

This module joins the zero/pole argument, the full-level identity, strict
convexity, and the algebraic tangent argument.  It is the end of the
interior-spectrum branch after rational collapse.
-/

@[expose] public section

noncomputable section

open Metric Polynomial Set
open scoped InnerProductSpace
open DiskRigidity.Algebraic.ConvexNoncriticalLevel
open DiskRigidity.Algebraic.LemniscateRegular

namespace DiskRigidity.Operator

/-- Once the reduced transfer quotient agrees with the boundary-continuous
inner extremizer and has no critical point on its full level, the numerical
range is a nondegenerate disk. -/
theorem numericalRange_eq_closedBall_of_reduced_inner_transfer
    {N : ℕ} (M : SquareMatrix (Fin (N + 1)))
    (hinterior : (interior (numericalRange M)).Nonempty)
    (x : EuclideanVector (Fin (N + 1))) (hx : x ≠ 0)
    (f : ℂ → ℂ) (U V C : ℂ[X])
    (hU : U ≠ 0)
    (hcoprime : IsCoprime U V)
    (hdegree : V.natDegree < U.natDegree)
    (htransfer : U * C =
      (Polynomial.C 2 * adjugateScalarNumerator M x x) * V)
    (hidentity : ∀ z ∈ numericalRange M,
      U.eval z = f z * V.eval z)
    (hinner : ∀ z ∈ interior (numericalRange M), ‖f z‖ < 1)
    (hboundary : ∀ z ∈ frontier (numericalRange M), ‖f z‖ = 1)
    (hwronskian : ∀ z ∈ frontier (numericalRange M),
      (U.derivative * V - U * V.derivative).eval z ≠ 0) :
    ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ numericalRange M = closedBall c r := by
  obtain ⟨-, hfull, hstrict⟩ :=
    Analysis.full_rationalLevel_and_strictConvex_of_reduced_inner_transfer
      M x hx f U V C hcoprime hdegree htransfer hidentity hinner hboundary
  exact numericalRange_eq_closedBall_of_full_rationalLevel
    M hinterior U V hU hdegree hcoprime hfull hstrict hwronskian

/-- Full endgame with no noncriticality assumption.  The strict rational
sublevel identity supplies a complete root-of-unity orbit in the convex
interior at any hypothetical critical level point.  Its barycenter is the
boundary point, a contradiction. -/
theorem numericalRange_eq_closedBall_of_reduced_inner_transfer_no_wronskian
    {N : ℕ} (M : SquareMatrix (Fin (N + 1)))
    (hinterior : (interior (numericalRange M)).Nonempty)
    (x : EuclideanVector (Fin (N + 1))) (hx : x ≠ 0)
    (f : ℂ → ℂ) (U V C : ℂ[X])
    (hU : U ≠ 0)
    (hcoprime : IsCoprime U V)
    (hdegree : V.natDegree < U.natDegree)
    (htransfer : U * C =
      (Polynomial.C 2 * adjugateScalarNumerator M x x) * V)
    (hidentity : ∀ z ∈ numericalRange M,
      U.eval z = f z * V.eval z)
    (hinner : ∀ z ∈ interior (numericalRange M), ‖f z‖ < 1)
    (hboundary : ∀ z ∈ frontier (numericalRange M), ‖f z‖ = 1) :
    ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ numericalRange M = closedBall c r := by
  obtain ⟨hsublevel, hfull, hstrict⟩ :=
    Analysis.full_rationalLevel_and_strictConvex_of_reduced_inner_transfer
      M x hx f U V C hcoprime hdegree htransfer hidentity hinner hboundary
  have hsublevelPoint : ∀ z,
      (V.eval z ≠ 0 ∧ ‖U.eval z / V.eval z‖ < 1) ↔
        z ∈ interior (numericalRange M) := by
    intro z
    change z ∈ Analysis.rationalSublevel U V ↔
      z ∈ interior (numericalRange M)
    rw [hsublevel]
  have hlevelNorm : ∀ z ∈ frontier (numericalRange M),
      ‖U.eval z‖ = ‖V.eval z‖ := by
    intro z hz
    apply (Analysis.mem_rationalLevel_iff_norm_eval_eq hcoprime z).mp
    rw [hfull]
    exact hz
  have hderiv : ∀ z ∈ frontier (numericalRange M),
      deriv (fun w ↦ U.eval w / V.eval w) z ≠ 0 :=
    quotient_deriv_ne_zero_on_frontier_of_coprime_convex_full_sublevel
      U V hcoprime hdegree (numericalRange_convex M)
      hsublevelPoint hlevelNorm
  have hwronskian : ∀ z ∈ frontier (numericalRange M),
      (U.derivative * V - U * V.derivative).eval z ≠ 0 := by
    intro z hz
    exact wronskian_eval_ne_zero_of_deriv_quotient_ne_zero
      U V hcoprime z (hlevelNorm z hz) (hderiv z hz)
  exact numericalRange_eq_closedBall_of_full_rationalLevel
    M hinterior U V hU hdegree hcoprime hfull hstrict hwronskian

end DiskRigidity.Operator
