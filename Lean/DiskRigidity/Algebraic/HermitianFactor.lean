/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.ContactDegree
public import DiskRigidity.Algebraic.HermitianPencil
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Real factors of Hermitian determinant pencils

This file combines divisibility with Hermitian hyperbolicity.  If the
complexification of a real polynomial divides a Hermitian determinant pencil,
then every complex zero of that factor is real, and the original polynomial
splits over `ℝ`.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace HermitianFactor

open Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A complexified real factor of a Hermitian determinant pencil is
real-rooted. -/
theorem map_isRealRooted_of_dvd {H J : Matrix n n ℂ}
    (hH : H.IsHermitian) (hJ : J.IsHermitian) (u v : ℝ) {q : ℝ[X]}
    (hdiv : q.map (algebraMap ℝ ℂ) ∣
      HermitianPencil.determinantPolynomial H J u v) :
    ContactDegree.IsRealRooted (q.map (algebraMap ℝ ℂ)) := by
  have hp : ContactDegree.IsRealRooted
      (HermitianPencil.determinantPolynomial H J u v) := by
    intro z hz
    exact HermitianPencil.determinantPolynomial_root_im_eq_zero hH hJ u v hz
  intro z hz
  obtain ⟨r, hr⟩ := hdiv
  apply hp
  rw [hr, eval_mul, hz, zero_mul]

/-- The real factor itself splits over `ℝ`. -/
theorem splits_of_map_dvd_determinantPolynomial {H J : Matrix n n ℂ}
    (hH : H.IsHermitian) (hJ : J.IsHermitian) (u v : ℝ) {q : ℝ[X]}
    (hdiv : q.map (algebraMap ℝ ℂ) ∣
      HermitianPencil.determinantPolynomial H J u v) :
    q.Splits := by
  have hreal : ContactDegree.IsRealRooted (q.map (algebraMap ℝ ℂ)) :=
    map_isRealRooted_of_dvd hH hJ u v hdiv
  apply (IsAlgClosed.splits (q.map (algebraMap ℝ ℂ))).of_splits_map (algebraMap ℝ ℂ)
  intro z hz
  have hzIm : z.im = 0 := hreal (Polynomial.isRoot_of_mem_roots hz).eq_zero
  refine ⟨z.re, ?_⟩
  exact Complex.ext rfl hzIm.symm

end HermitianFactor

end DiskRigidity.Algebraic
