/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Analysis.RationalInnerLevel
public import DiskRigidity.Operator.InteriorRationalDisk

/-!
# Algebraic endgame after the transfer identity

This file packages the last paragraph of Proposition 5.2 together with the
full-level and circle propositions.  Its input is precisely the meromorphic
adjugate transfer identity produced on the convex interior.
-/

@[expose] public section

noncomputable section

open Metric Polynomial Set
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

/-- A numerical range with planar interior cannot come from a one-by-one
matrix. -/
theorem finSucc_parameter_pos_of_interior_numericalRange
    {N : ℕ} (M : SquareMatrix (Fin (N + 1)))
    (hinterior : (interior (numericalRange M)).Nonempty) :
    0 < N := by
  by_contra hnot
  have hN : N = 0 := Nat.eq_zero_of_not_pos hnot
  subst N
  have hM : M = M 0 0 • (1 : SquareMatrix (Fin 1)) := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  have hscalar (b : ℂ) :
      numericalRange (b • (1 : SquareMatrix (Fin 1))) = {b} := by
    apply Set.Subset.antisymm
    · rintro z ⟨x, hx, rfl⟩
      rw [Set.mem_singleton_iff]
      simp only [map_smul, map_one, smul_apply, one_apply_eq_self,
        inner_smul_right, inner_self_eq_norm_sq_to_K, hx]
      norm_num
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      obtain ⟨w, hw⟩ := numericalRange_nonempty
        (b • (1 : SquareMatrix (Fin 1)))
      have hwb : w = b := by
        obtain ⟨x, hx, rfl⟩ := hw
        simp only [map_smul, map_one, smul_apply, one_apply_eq_self,
          inner_smul_right, inner_self_eq_norm_sq_to_K, hx]
        norm_num
      rwa [hwb] at hw
  rw [hM, hscalar, interior_singleton] at hinterior
  exact Set.not_nonempty_empty hinterior

/-- The cross adjugate coefficient cannot vanish identically once the
transfer identity holds on a nonempty open set. -/
theorem adjugateScalarNumerator_cross_ne_zero_of_transfer_identity
    {N : ℕ} (M : SquareMatrix (Fin (N + 1)))
    (hinterior : (interior (numericalRange M)).Nonempty)
    (x y : EuclideanVector (Fin (N + 1))) (hx : ‖x‖ = 1)
    (f : ℂ → ℂ)
    (hidentity : ∀ z ∈ interior (numericalRange M),
      (adjugateScalarNumerator M y x).eval z * f z =
        2 * (adjugateScalarNumerator M x x).eval z) :
    adjugateScalarNumerator M y x ≠ 0 := by
  let A := adjugateScalarNumerator M x x
  let C := adjugateScalarNumerator M y x
  have hA : A ≠ 0 := by
    intro hzero
    have hcoeff := coeff_adjugateScalarNumerator_card_sub_one M x x
    change A.coeff N = ⟪x, x⟫_ℂ at hcoeff
    rw [hzero, Polynomial.coeff_zero,
      inner_self_eq_norm_sq_to_K, hx] at hcoeff
    norm_num at hcoeff
  intro hC
  change C = 0 at hC
  have hAeval : ∀ z ∈ interior (numericalRange M), A.eval z = 0 := by
    intro z hz
    have h := hidentity z hz
    change C.eval z * f z = 2 * A.eval z at h
    rw [hC, Polynomial.eval_zero, zero_mul] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)
  obtain ⟨z₀, hz₀⟩ := hinterior
  have hAfun : (fun z ↦ A.eval z) = (fun _ ↦ 0) := by
    apply AnalyticOnNhd.eq_of_eventuallyEq
      (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) A) analyticOnNhd_const
    filter_upwards [isOpen_interior.mem_nhds hz₀] with z hz
    exact hAeval z hz
  apply hA
  apply Polynomial.funext
  intro z
  simpa using congrFun hAfun z

/-- The complete algebraic conclusion of Sections 5--7.  Once the
boundary-continuous inner extremizer satisfies the adjugate transfer identity
throughout the convex interior, its numerical range is a nondegenerate
closed disk. -/
theorem numericalRange_eq_closedBall_of_adjugate_transfer_identity
    {N : ℕ} (M : SquareMatrix (Fin (N + 1)))
    (hinterior : (interior (numericalRange M)).Nonempty)
    (x y : EuclideanVector (Fin (N + 1)))
    (hx : ‖x‖ = 1) (hyx : ⟪y, x⟫_ℂ = 0)
    (f : ℂ → ℂ)
    (hfDifferentiable : DifferentiableOn ℂ f (interior (numericalRange M)))
    (hfContinuous : ContinuousOn f (numericalRange M))
    (hfInterior : ∀ z ∈ interior (numericalRange M), ‖f z‖ < 1)
    (hfBoundary : ∀ z ∈ frontier (numericalRange M), ‖f z‖ = 1)
    (hidentity : ∀ z ∈ interior (numericalRange M),
      (adjugateScalarNumerator M y x).eval z * f z =
        2 * (adjugateScalarNumerator M x x).eval z) :
    ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ numericalRange M = closedBall c r := by
  let A := adjugateScalarNumerator M x x
  let C := adjugateScalarNumerator M y x
  have hN : 0 < N :=
    finSucc_parameter_pos_of_interior_numericalRange M hinterior
  have hC : C ≠ 0 := by
    exact adjugateScalarNumerator_cross_ne_zero_of_transfer_identity
      M hinterior x y hx f hidentity
  obtain ⟨U, V, hU, _hV, hcoprime, htransfer, hdegree⟩ :=
    DiskRigidity.Analysis.exists_reduced_adjugate_transfer
      hN M x y hx hyx hC
  have hinteriorIdentity : ∀ z ∈ interior (numericalRange M),
      U.eval z = f z * V.eval z :=
    DiskRigidity.Analysis.reduced_transfer_agrees_on_convex_interior
      (numericalRange_convex M) hinterior f U V A C hC
      hfDifferentiable htransfer hidentity
  have hclosedIdentity : ∀ z ∈ numericalRange M,
      U.eval z = f z * V.eval z :=
    DiskRigidity.Analysis.polynomial_transfer_identity_on_compactConvex
      (isCompact_numericalRange M) (numericalRange_convex M) hinterior
      f U V hfContinuous hinteriorIdentity
  have hxne : x ≠ 0 := by
    intro hzero
    subst x
    norm_num at hx
  exact numericalRange_eq_closedBall_of_reduced_inner_transfer_no_wronskian
    M hinterior x hxne
      f U V C hU hcoprime hdegree htransfer hclosedIdentity
      hfInterior hfBoundary

end DiskRigidity.Operator
