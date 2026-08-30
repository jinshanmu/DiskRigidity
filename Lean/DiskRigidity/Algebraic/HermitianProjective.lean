/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.HermitianFactor
public import DiskRigidity.Algebraic.PlaneCurveSpecialization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Projective Hermitian pencils

This file connects the homogeneous Kippenhahn determinant in line
coordinates with the one-variable Hermitian pencil.  In particular, a real
homogeneous factor of the projective determinant specializes in every real
direction to a split real polynomial.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace HermitianProjective

open Matrix MvPolynomial Polynomial
open GenericSpecialization PlaneCurveSpecialization

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of linear forms `s I + u H + v J`. -/
noncomputable def projectivePencilMatrix (H J : Matrix n n ℂ) :
    Matrix n n (MvPolynomial (Fin 3) ℂ) :=
  fun i j ↦ X 0 * MvPolynomial.C ((1 : Matrix n n ℂ) i j) +
    X 1 * MvPolynomial.C (H i j) + X 2 * MvPolynomial.C (J i j)

/-- The homogeneous Kippenhahn determinant in line coordinates `[s,u,v]`. -/
noncomputable def determinantPolynomial (H J : Matrix n n ℂ) :
    MvPolynomial (Fin 3) ℂ :=
  (projectivePencilMatrix H J).det

omit [Fintype n] in
/-- Every entry of the projective pencil is a linear form. -/
theorem projectivePencilMatrix_isHomogeneous (H J : Matrix n n ℂ)
    (i j : n) :
    (projectivePencilMatrix H J i j).IsHomogeneous 1 := by
  simp only [projectivePencilMatrix]
  apply IsHomogeneous.add
  · apply IsHomogeneous.add
    · simpa only [add_zero] using
        (isHomogeneous_X ℂ (0 : Fin 3)).mul
          (isHomogeneous_C (Fin 3) ((1 : Matrix n n ℂ) i j))
    · simpa only [add_zero] using
        (isHomogeneous_X ℂ (1 : Fin 3)).mul
          (isHomogeneous_C (Fin 3) (H i j))
  · simpa only [add_zero] using
      (isHomogeneous_X ℂ (2 : Fin 3)).mul
        (isHomogeneous_C (Fin 3) (J i j))

/-- The determinant of the projective pencil is homogeneous of matrix
size. -/
theorem determinantPolynomial_isHomogeneous (H J : Matrix n n ℂ) :
    (determinantPolynomial H J).IsHomogeneous (Fintype.card n) := by
  classical
  rw [determinantPolynomial, Matrix.det_apply']
  apply IsHomogeneous.sum
  intro σ _
  have hprod :
      (∏ i, projectivePencilMatrix H J (σ i) i).IsHomogeneous
        (Fintype.card n) := by
    convert IsHomogeneous.prod Finset.univ
      (fun i ↦ projectivePencilMatrix H J (σ i) i)
      (fun _ ↦ 1) (fun i _ ↦ projectivePencilMatrix_isHomogeneous H J (σ i) i)
    simp
  change (MvPolynomial.C (((Equiv.Perm.sign σ : ℤ) : ℂ)) *
    ∏ i, projectivePencilMatrix H J (σ i) i).IsHomogeneous
      (Fintype.card n)
  simpa only [zero_add] using
    (isHomogeneous_C (Fin 3) (((Equiv.Perm.sign σ : ℤ) : ℂ))).mul hprod

/-- Evaluation is the expected determinant of the Hermitian pencil. -/
theorem eval_determinantPolynomial (H J : Matrix n n ℂ)
    (z : Fin 3 → ℂ) :
    MvPolynomial.eval z (determinantPolynomial H J) =
      (Matrix.scalar n (z 0) + (z 1) • H + (z 2) • J).det := by
  rw [determinantPolynomial, RingHom.map_det]
  congr 1
  ext i j
  simp [projectivePencilMatrix, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- The distinguished line coordinate `[1,0,0]` evaluates the determinant
to one, so the projective determinant is never the zero polynomial. -/
theorem determinantPolynomial_ne_zero (H J : Matrix n n ℂ) :
    determinantPolynomial H J ≠ 0 := by
  intro hzero
  let e : Fin 3 → ℂ := ![1, 0, 0]
  have h := congrArg (MvPolynomial.eval e) hzero
  rw [eval_determinantPolynomial] at h
  simp [e] at h

/-- Substitute the affine direction `[s,t,1]`, retaining `s` as the
polynomial variable. -/
noncomputable def affineSpecialization (t : ℝ) :
    MvPolynomial (Fin 3) ℂ →+* ℂ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C
    ![Polynomial.X, Polynomial.C (t : ℂ), 1]

/-- The corresponding specialization before extending coefficients to
`ℂ`. -/
noncomputable def affineSpecializationReal (t : ℝ) :
    MvPolynomial (Fin 3) ℝ →+* ℝ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C
    ![Polynomial.X, Polynomial.C t, 1]

theorem eval_affineSpecialization (P : MvPolynomial (Fin 3) ℂ)
    (t : ℝ) (s : ℂ) :
    (affineSpecialization t P).eval s =
      MvPolynomial.eval ![s, (t : ℂ), 1] P := by
  have hhom : (Polynomial.evalRingHom s).comp (affineSpecialization t) =
      MvPolynomial.eval ![s, (t : ℂ), 1] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [affineSpecialization]
    · intro i
      fin_cases i <;> simp [affineSpecialization]
  exact DFunLike.congr_fun hhom P

theorem eval_affineSpecializationReal (P : MvPolynomial (Fin 3) ℝ)
    (t s : ℝ) :
    (affineSpecializationReal t P).eval s =
      MvPolynomial.eval ![s, t, 1] P := by
  have hhom : (Polynomial.evalRingHom s).comp
      (affineSpecializationReal t) = MvPolynomial.eval ![s, t, 1] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [affineSpecializationReal]
    · intro i
      fin_cases i <;> simp [affineSpecializationReal]
  exact DFunLike.congr_fun hhom P

/-- The direct real specialization is the affine-family specialization used
in the generic contact-count modules. -/
theorem affineSpecializationReal_eq_specialize_affineFamily
    (Q : MvPolynomial (Fin 3) ℝ) (t : ℝ) :
    affineSpecializationReal t Q = specialize (affineFamily Q) t := by
  apply Polynomial.funext
  intro s
  rw [eval_affineSpecializationReal,
    eval_specialize_affineFamily]

/-- Complexifying a real equation commutes with affine specialization. -/
theorem affineSpecialization_map
    (Q : MvPolynomial (Fin 3) ℝ) (t : ℝ) :
    affineSpecialization t (MvPolynomial.map (algebraMap ℝ ℂ) Q) =
      (affineSpecializationReal t Q).map (algebraMap ℝ ℂ) := by
  rw [affineSpecialization, affineSpecializationReal]
  change MvPolynomial.eval₂Hom Polynomial.C
      ![Polynomial.X, Polynomial.C (t : ℂ), 1]
        (MvPolynomial.map (algebraMap ℝ ℂ) Q) =
    Polynomial.mapRingHom (algebraMap ℝ ℂ)
      (MvPolynomial.eval₂Hom Polynomial.C
        ![Polynomial.X, Polynomial.C t, 1] Q)
  rw [MvPolynomial.eval₂Hom_map_hom,
    MvPolynomial.map_eval₂Hom]
  have hC : Polynomial.C.comp (algebraMap ℝ ℂ) =
      (Polynomial.mapRingHom (algebraMap ℝ ℂ)).comp Polynomial.C := by
    ext c
    simp
  have hX : (![Polynomial.X, Polynomial.C (t : ℂ), 1] :
      Fin 3 → ℂ[X]) = fun i ↦
        Polynomial.mapRingHom (algebraMap ℝ ℂ)
          ((![Polynomial.X, Polynomial.C t, 1] : Fin 3 → ℝ[X]) i) := by
    funext i
    fin_cases i <;> simp
  rw [hC, hX]

/-- Affine specialization of the projective determinant is the
characteristic polynomial of the corresponding Hermitian matrix. -/
theorem affineSpecialization_determinantPolynomial
    (H J : Matrix n n ℂ) (t : ℝ) :
    affineSpecialization t (determinantPolynomial H J) =
      HermitianPencil.determinantPolynomial H J t 1 := by
  apply Polynomial.funext
  intro s
  rw [eval_affineSpecialization, eval_determinantPolynomial,
    HermitianPencil.determinantPolynomial_eval]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
    Matrix.cons_val_zero, Matrix.scalar_apply, Matrix.cons_val_one,
    Complex.coe_smul, Matrix.cons_val, one_smul,
    HermitianPencil.directionalMatrix]
  rw [add_assoc]

/-- A homogeneous projective factor specializes to a factor of every
one-variable Hermitian pencil. -/
theorem map_specialize_dvd_determinantPolynomial_of_dvd
    (H J : Matrix n n ℂ) (Q : MvPolynomial (Fin 3) ℝ)
    (hdiv : MvPolynomial.map (algebraMap ℝ ℂ) Q ∣
      determinantPolynomial H J) (t : ℝ) :
    (specialize (affineFamily Q) t).map (algebraMap ℝ ℂ) ∣
      HermitianPencil.determinantPolynomial H J t 1 := by
  obtain ⟨R, hR⟩ := hdiv
  refine ⟨affineSpecialization t R, ?_⟩
  rw [← affineSpecialization_determinantPolynomial, hR, map_mul,
    affineSpecialization_map,
    affineSpecializationReal_eq_specialize_affineFamily]

/-- Projective divisibility by a Hermitian determinant supplies the complete
hyperbolicity hypothesis used in the generic contact count. -/
theorem splits_specialize_affineFamily_of_dvd
    {H J : Matrix n n ℂ} (hH : H.IsHermitian) (hJ : J.IsHermitian)
    (Q : MvPolynomial (Fin 3) ℝ)
    (hdiv : MvPolynomial.map (algebraMap ℝ ℂ) Q ∣
      determinantPolynomial H J) :
    ∀ t : ℝ, (specialize (affineFamily Q) t).Splits := by
  intro t
  exact HermitianFactor.splits_of_map_dvd_determinantPolynomial
    hH hJ t 1
    (map_specialize_dvd_determinantPolynomial_of_dvd H J Q hdiv t)

/-- Since the projective determinant is one at `[1,0,0]`, none of its
factors vanishes there. -/
theorem eval_distinguishedPoint_ne_zero_of_dvd
    (H J : Matrix n n ℂ) (Q : MvPolynomial (Fin 3) ℝ)
    (hdiv : MvPolynomial.map (algebraMap ℝ ℂ) Q ∣
      determinantPolynomial H J) :
    MvPolynomial.eval distinguishedPoint Q ≠ 0 := by
  intro he
  let eℂ : Fin 3 → ℂ := fun i ↦ distinguishedPoint i
  have hQe : MvPolynomial.eval eℂ
      (MvPolynomial.map (algebraMap ℝ ℂ) Q) = 0 := by
    rw [MvPolynomial.eval_map]
    change MvPolynomial.eval₂ (algebraMap ℝ ℂ)
      ((algebraMap ℝ ℂ) ∘ distinguishedPoint) Q = 0
    rw [← MvPolynomial.eval₂_comp, he, map_zero]
  obtain ⟨R, hR⟩ := hdiv
  have hdetZero : MvPolynomial.eval eℂ (determinantPolynomial H J) = 0 := by
    rw [hR, map_mul, hQe, zero_mul]
  have hdetOne : MvPolynomial.eval eℂ (determinantPolynomial H J) = 1 := by
    rw [eval_determinantPolynomial]
    simp [eℂ, distinguishedPoint]
  exact one_ne_zero (hdetOne.symm.trans hdetZero)

end HermitianProjective

end DiskRigidity.Algebraic
