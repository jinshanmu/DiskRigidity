/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib.Analysis.Matrix.Spectrum

/-!
# Real roots of Hermitian matrix pencils

This file formalizes the hyperbolicity input used in Proposition 7.1 of the
paper.  If `H` and `J` are Hermitian and `u,v` are real, then every zero in
the scalar variable of

`det (s I + u H + v J)`

is real.  The proof is the finite-dimensional spectral theorem: the displayed
determinant is the characteristic polynomial of the negative Hermitian
matrix `-(u H + v J)`.
-/

@[expose] public section

open scoped Matrix

namespace DiskRigidity.Algebraic

namespace HermitianPencil

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Hermitian matrix occurring in a fixed real direction of the pencil. -/
def directionalMatrix (H J : Matrix n n ℂ) (u v : ℝ) : Matrix n n ℂ :=
  (u : ℂ) • H + (v : ℂ) • J

/-- The determinant pencil as a univariate polynomial in the line offset. -/
noncomputable def determinantPolynomial (H J : Matrix n n ℂ) (u v : ℝ) : Polynomial ℂ :=
  (-(directionalMatrix H J u v)).charpoly

/-- Evaluation of `determinantPolynomial` is the expected determinant. -/
theorem determinantPolynomial_eval (H J : Matrix n n ℂ) (u v : ℝ) (s : ℂ) :
    (determinantPolynomial H J u v).eval s =
      (Matrix.scalar n s + directionalMatrix H J u v).det := by
  rw [determinantPolynomial, Matrix.eval_charpoly]
  simp [sub_eq_add_neg]

omit [Fintype n] [DecidableEq n] in
theorem directionalMatrix_isHermitian {H J : Matrix n n ℂ}
    (hH : H.IsHermitian) (hJ : J.IsHermitian) (u v : ℝ) :
    (directionalMatrix H J u v).IsHermitian := by
  have hu : IsSelfAdjoint (u : ℂ) := by
    rw [isSelfAdjoint_iff, Complex.star_def]
    exact Complex.conj_ofReal u
  have hv : IsSelfAdjoint (v : ℂ) := by
    rw [isSelfAdjoint_iff, Complex.star_def]
    exact Complex.conj_ofReal v
  exact (hH.smul hu).add (hJ.smul hv)

/-- A zero of a Hermitian determinant pencil in the scalar coordinate is real. -/
theorem im_eq_zero_of_det_scalar_add_eq_zero {H J : Matrix n n ℂ}
    (hH : H.IsHermitian) (hJ : J.IsHermitian) (u v : ℝ) {s : ℂ}
    (hs : (Matrix.scalar n s + directionalMatrix H J u v).det = 0) :
    s.im = 0 := by
  let A := -(directionalMatrix H J u v)
  have hA : A.IsHermitian := (directionalMatrix_isHermitian hH hJ u v).neg
  have hsRoot : Polynomial.IsRoot A.charpoly s := by
    rw [Polynomial.IsRoot, Matrix.eval_charpoly]
    simpa [A, sub_eq_add_neg] using hs
  have hsSpectrum : s ∈ spectrum ℂ A :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hsRoot
  rw [hA.spectrum_eq_image_range] at hsSpectrum
  obtain ⟨r, ⟨i, rfl⟩, rfl⟩ := hsSpectrum
  exact Complex.ofReal_im _

/-- Equivalent pointwise formulation: every root of a Hermitian determinant
pencil is the complexification of a real number. -/
theorem exists_real_of_det_scalar_add_eq_zero {H J : Matrix n n ℂ}
    (hH : H.IsHermitian) (hJ : J.IsHermitian) (u v : ℝ) {s : ℂ}
    (hs : (Matrix.scalar n s + directionalMatrix H J u v).det = 0) :
    ∃ r : ℝ, s = r := by
  exact ⟨s.re, Complex.ext rfl (im_eq_zero_of_det_scalar_add_eq_zero hH hJ u v hs)⟩

/-- Polynomial formulation of hyperbolicity of a Hermitian pencil. -/
theorem determinantPolynomial_root_im_eq_zero {H J : Matrix n n ℂ}
    (hH : H.IsHermitian) (hJ : J.IsHermitian) (u v : ℝ) {s : ℂ}
    (hs : (determinantPolynomial H J u v).eval s = 0) :
    s.im = 0 := by
  apply im_eq_zero_of_det_scalar_add_eq_zero hH hJ u v
  rw [← determinantPolynomial_eval]
  exact hs

end HermitianPencil

end DiskRigidity.Algebraic
