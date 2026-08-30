/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.AdjugateDegree
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.EuclideanDomain

/-!
# Reduction of the scalar resolvent transfer quotient

This file carries out the cancellation in the last paragraph of Proposition
5.2.  The reduced numerator and denominator are constructed explicitly by
dividing by their polynomial gcd.
-/

@[expose] public section

noncomputable section

open Polynomial
open scoped InnerProductSpace

namespace DiskRigidity.Analysis

/-- Two nonzero polynomial coefficients with a strict degree gap have a
coprime reduction of the transfer quotient `2 A / C`; the strict degree gap
survives cancellation. -/
theorem exists_reduced_transfer
    {A C : ℂ[X]} (hA : A ≠ 0) (hC : C ≠ 0)
    (hdegree : C.natDegree < A.natDegree) :
    ∃ U V : ℂ[X],
      U ≠ 0 ∧ V ≠ 0 ∧ IsCoprime U V ∧
      U * C = (Polynomial.C 2 * A) * V ∧
      V.natDegree < U.natDegree := by
  classical
  let _ := EuclideanDomain.gcdMonoid ℂ[X]
  let P : ℂ[X] := Polynomial.C 2 * A
  let G : ℂ[X] := GCDMonoid.gcd P C
  let U : ℂ[X] := P / G
  let V : ℂ[X] := C / G
  have hP : P ≠ 0 := by
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr (by norm_num)) hA
  have hG : G ≠ 0 := by
    exact gcd_ne_zero_of_right hC
  have hU : U ≠ 0 := left_div_gcd_ne_zero hP
  have hV : V ≠ 0 := right_div_gcd_ne_zero hC
  have hcoprime : IsCoprime U V := isCoprime_div_gcd_div_gcd hC
  have hPG : G * U = P := by
    exact EuclideanDomain.mul_div_cancel' hG (GCDMonoid.gcd_dvd_left P C)
  have hCG : G * V = C := by
    exact EuclideanDomain.mul_div_cancel' hG (GCDMonoid.gcd_dvd_right P C)
  have htransfer : U * C = P * V := by
    rw [← hCG, ← hPG]
    ring
  have hstrict : V.natDegree < U.natDegree := by
    apply Operator.reduced_transfer_numerator_degree_gt hU hV hA hC
      (by simpa only [P] using htransfer) hdegree
  exact ⟨U, V, hU, hV, hcoprime, by simpa only [P] using htransfer, hstrict⟩

/-- Matrix-resolvent specialization of `exists_reduced_transfer`.  The
diagonal adjugate coefficient has degree `N`, whereas orthogonality makes the
cross coefficient have smaller degree. -/
theorem exists_reduced_adjugate_transfer
    {N : ℕ} (hN : 0 < N)
    (M : Operator.SquareMatrix (Fin (N + 1)))
    (x y : Operator.EuclideanVector (Fin (N + 1)))
    (hx : ‖x‖ = 1) (hyx : ⟪y, x⟫_ℂ = 0)
    (hcross : Operator.adjugateScalarNumerator M y x ≠ 0) :
    ∃ U V : ℂ[X],
      U ≠ 0 ∧ V ≠ 0 ∧ IsCoprime U V ∧
      U * Operator.adjugateScalarNumerator M y x =
        (Polynomial.C 2 * Operator.adjugateScalarNumerator M x x) * V ∧
      V.natDegree < U.natDegree := by
  let A := Operator.adjugateScalarNumerator M x x
  let C := Operator.adjugateScalarNumerator M y x
  have hAdegree : A.natDegree = N :=
    Operator.natDegree_adjugateScalarNumerator_self_eq M x hx
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hAdegree
    omega
  have hCdegree : C.natDegree < N :=
    Operator.natDegree_adjugateScalarNumerator_lt_of_inner_eq_zero
      hN M y x hyx
  simpa only [A, C] using
    exists_reduced_transfer hA hcross (hCdegree.trans_eq hAdegree.symm)

end DiskRigidity.Analysis
