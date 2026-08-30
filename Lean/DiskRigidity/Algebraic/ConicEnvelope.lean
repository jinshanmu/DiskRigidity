/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.GaussPullback
public import DiskRigidity.Algebraic.Conic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# The primal envelope of a nonsingular dual conic

This file proves the matrix calculation at the end of Proposition 7.1 from
the polynomial itself.  For a homogeneous quadratic form `Q`, half of its
Hessian is a symmetric matrix `conicMatrix Q`; Euler's identity gives

`Q(z) = z ⬝ᵥ (conicMatrix Q *ᵥ z)` and
`gradient Q z = 2 • (conicMatrix Q *ᵥ z)`.

When that matrix is nonsingular, its inverse cuts out the primal envelope.
No coordinate expansion of the six coefficients is needed.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace ConicEnvelope

open Matrix MvPolynomial
open ProjectiveDual

/-- Half the Hessian matrix of a real homogeneous quadratic polynomial. -/
noncomputable def conicMatrix (Q : MvPolynomial (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j ↦ (2 : ℝ)⁻¹ * MvPolynomial.eval 0
    (MvPolynomial.pderiv j (MvPolynomial.pderiv i Q))

/-- The polynomial represented by a matrix as `zᵀ A z`. -/
noncomputable def matrixPolynomial {K : Type*} [CommSemiring K]
    (A : Matrix (Fin 3) (Fin 3) K) : MvPolynomial (Fin 3) K :=
  ∑ i, ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X i * MvPolynomial.X j

theorem eval_matrixPolynomial {K : Type*} [CommSemiring K]
    (A : Matrix (Fin 3) (Fin 3) K) (z : Fin 3 → K) :
    MvPolynomial.eval z (matrixPolynomial A) = z ⬝ᵥ (A *ᵥ z) := by
  classical
  simp only [matrixPolynomial, map_sum, map_mul, eval_C, eval_X,
    dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem matrixPolynomial_isHomogeneous {K : Type*} [CommSemiring K]
    (A : Matrix (Fin 3) (Fin 3) K) :
    (matrixPolynomial A).IsHomogeneous 2 := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  simpa using ((MvPolynomial.isHomogeneous_C (Fin 3) (A i j)).mul
    (MvPolynomial.isHomogeneous_X (R := K) i)).mul
      (MvPolynomial.isHomogeneous_X (R := K) j)

theorem map_matrixPolynomial {K L : Type*} [CommSemiring K] [CommSemiring L]
    (f : K →+* L) (A : Matrix (Fin 3) (Fin 3) K) :
    MvPolynomial.map f (matrixPolynomial A) = matrixPolynomial (A.map f) := by
  classical
  simp [matrixPolynomial]

private theorem eval_zero_linear
    (a b c : ℂ) :
    MvPolynomial.eval 0
      (MvPolynomial.C a * MvPolynomial.X (0 : Fin 3) +
       MvPolynomial.C b * MvPolynomial.X (1 : Fin 3) +
       MvPolynomial.C c * MvPolynomial.X (2 : Fin 3)) = 0 := by
  simp

/-- A singular symmetric ternary quadratic over `ℂ` factors into two
linear forms.  This is the elementary rank-at-most-two classification,
proved by an explicit coefficient calculation. -/
theorem exists_linear_factorization_of_isSymm_det_zero
    (A : Matrix (Fin 3) (Fin 3) ℂ) (hA : A.IsSymm)
    (hdet : A.det = 0) :
    ∃ L R : MvPolynomial (Fin 3) ℂ,
      matrixPolynomial A = L * R ∧
      MvPolynomial.eval 0 L = 0 ∧ MvPolynomial.eval 0 R = 0 := by
  let a := A 0 0
  let b := A 0 1
  let c := A 0 2
  let d := A 1 1
  let e := A 1 2
  let f := A 2 2
  let X := MvPolynomial.X (R := ℂ) (0 : Fin 3)
  let Y := MvPolynomial.X (R := ℂ) (1 : Fin 3)
  let Z := MvPolynomial.X (R := ℂ) (2 : Fin 3)
  have h10 : A 1 0 = b := by
    exact (Matrix.IsSymm.ext_iff.mp hA 0 1).trans rfl
  have h20 : A 2 0 = c := by
    exact (Matrix.IsSymm.ext_iff.mp hA 0 2).trans rfl
  have h21 : A 2 1 = e := by
    exact (Matrix.IsSymm.ext_iff.mp hA 1 2).trans rfl
  have hpoly : matrixPolynomial A =
      MvPolynomial.C a * X ^ 2 + 2 * MvPolynomial.C b * X * Y +
      2 * MvPolynomial.C c * X * Z + MvPolynomial.C d * Y ^ 2 +
      2 * MvPolynomial.C e * Y * Z + MvPolynomial.C f * Z ^ 2 := by
    simp only [matrixPolynomial, Fin.sum_univ_three]
    simp only [h10, h20, h21, a, b, c, d, e, f, X, Y, Z]
    ring
  have hdet' :
      a * d * f - a * e ^ 2 - b ^ 2 * f + 2 * b * c * e - c ^ 2 * d = 0 := by
    rw [Matrix.det_fin_three] at hdet
    simp only [h10, h20, h21, a, b, c, d, e, f] at hdet ⊢
    linear_combination hdet
  by_cases ha : a = 0
  · have hdetA : -b ^ 2 * f + 2 * b * c * e - c ^ 2 * d = 0 := by
      rw [ha] at hdet'
      simpa using hdet'
    by_cases hb : b = 0
    · by_cases hc : c = 0
      · by_cases hd : d = 0
        · by_cases he : e = 0
          · refine ⟨MvPolynomial.C f * Z, Z, ?_, ?_, ?_⟩
            · apply MvPolynomial.funext
              intro w
              rw [hpoly]
              simp [ha, hb, hc, hd, he, X, Y, Z]
              ring
            · simp [Z]
            · simp [Z]
          · refine ⟨Z, MvPolynomial.C (2 * e) * Y +
                MvPolynomial.C f * Z, ?_, ?_, ?_⟩
            · apply MvPolynomial.funext
              intro w
              rw [hpoly]
              simp [ha, hb, hc, hd, X, Y, Z]
              ring
            · simp [Z]
            · simp [Y, Z]
        · obtain ⟨δ, hδ⟩ := Complex.isSquare (e ^ 2 - d * f)
          let L := MvPolynomial.C d * Y + MvPolynomial.C (e + δ) * Z
          let R := Y + MvPolynomial.C ((e - δ) / d) * Z
          refine ⟨L, R, ?_, ?_, ?_⟩
          · apply MvPolynomial.funext
            intro w
            rw [hpoly]
            simp only [map_add, map_mul, map_pow, map_ofNat, eval_C]
            dsimp only [L, R, X, Y, Z]
            simp only [map_add, map_mul, eval_C, eval_X, ha, hb, hc,
              zero_mul]
            field_simp [hd]
            linear_combination (-w 2 ^ 2) * hδ
          · simp [L, Y, Z]
          · simp [R, Y, Z]
      · have hd : d = 0 := by
          have hdetAB : -c ^ 2 * d = 0 := by
            rw [hb] at hdetA
            simpa using hdetA
          have hcd : c ^ 2 * d = 0 := by
            linear_combination -1 * hdetAB
          exact (mul_eq_zero.mp hcd).resolve_left (pow_ne_zero 2 hc)
        refine ⟨Z, MvPolynomial.C (2 * c) * X +
            MvPolynomial.C (2 * e) * Y + MvPolynomial.C f * Z,
          ?_, ?_, ?_⟩
        · apply MvPolynomial.funext
          intro w
          rw [hpoly]
          simp [ha, hb, hd, X, Y, Z]
          ring
        · simp [Z]
        · simp [X, Y, Z]
    · let β := (2 * e * b - d * c) / b ^ 2
      let L := MvPolynomial.C b * Y + MvPolynomial.C c * Z
      let R := MvPolynomial.C 2 * X + MvPolynomial.C (d / b) * Y +
        MvPolynomial.C β * Z
      refine ⟨L, R, ?_, ?_, ?_⟩
      · apply MvPolynomial.funext
        intro w
        rw [hpoly]
        simp only [map_add, map_mul, map_pow, map_ofNat, eval_C]
        dsimp only [L, R, β, X, Y, Z]
        simp only [map_add, map_mul, eval_C, eval_X, ha, zero_mul]
        field_simp [hb]
        linear_combination (-w 2 ^ 2) * hdetA
      · simp [L, Y, Z]
      · simp [R, X, Y, Z]
  · let D := a * d - b ^ 2
    let E := a * e - b * c
    let F := a * f - c ^ 2
    let T := MvPolynomial.C a * X + MvPolynomial.C b * Y +
      MvPolynomial.C c * Z
    have hDEF : D * F = E ^ 2 := by
      dsimp only [D, E, F]
      linear_combination a * hdet'
    by_cases hD : D = 0
    · have hE : E = 0 := by
        apply (sq_eq_zero_iff.mp ?_)
        rw [← hDEF, hD, zero_mul]
      obtain ⟨φ, hφ⟩ := Complex.isSquare F
      let L := T + MvPolynomial.C (Complex.I * φ) * Z
      let R := MvPolynomial.C a⁻¹ *
        (T - MvPolynomial.C (Complex.I * φ) * Z)
      refine ⟨L, R, ?_, ?_, ?_⟩
      · apply MvPolynomial.funext
        intro w
        rw [hpoly]
        simp only [map_add, map_mul, map_pow, map_ofNat, eval_C]
        dsimp only [L, R, T, D, E, F, X, Y, Z] at hD hE hφ ⊢
        simp only [map_add, map_sub, map_mul, eval_C, eval_X]
        field_simp [ha]
        ring_nf
        rw [Complex.I_sq]
        linear_combination w 1 ^ 2 * hD +
          (2 * w 1 * w 2) * hE + w 2 ^ 2 * hφ
      · simp [L, T, X, Y, Z]
      · simp [R, T, X, Y, Z]
    · obtain ⟨δ, hδ⟩ := Complex.isSquare D
      let M := MvPolynomial.C D * Y + MvPolynomial.C E * Z
      let L := MvPolynomial.C δ * T + MvPolynomial.C Complex.I * M
      let R := MvPolynomial.C (a * D)⁻¹ *
        (MvPolynomial.C δ * T - MvPolynomial.C Complex.I * M)
      refine ⟨L, R, ?_, ?_, ?_⟩
      · apply MvPolynomial.funext
        intro w
        rw [hpoly]
        simp only [map_add, map_mul, map_pow, map_ofNat, eval_C]
        dsimp only [L, R, M, T, X, Y, Z]
        simp only [map_add, map_sub, map_mul, eval_C, eval_X]
        field_simp [ha, hD]
        dsimp only [D, E, F] at hδ hDEF ⊢
        ring_nf
        rw [Complex.I_sq]
        linear_combination (a * w 0 + b * w 1 + c * w 2) ^ 2 * hδ +
          w 2 ^ 2 * hDEF
      · simp [L, M, T, X, Y, Z]
      · simp [R, M, T, X, Y, Z]

theorem conicMatrix_isSymm (Q : MvPolynomial (Fin 3) ℝ) :
    (conicMatrix Q).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [conicMatrix]
  rw [ProjectiveDual.pderiv_pderiv_comm i j Q]

private theorem eval_secondDerivative_eq_eval_zero
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Q.IsHomogeneous 2)
    (i j : Fin 3) (z : Fin 3 → ℝ) :
    MvPolynomial.eval z (MvPolynomial.pderiv j (MvPolynomial.pderiv i Q)) =
      MvPolynomial.eval 0 (MvPolynomial.pderiv j (MvPolynomial.pderiv i Q)) := by
  let P := MvPolynomial.pderiv j (MvPolynomial.pderiv i Q)
  have hP : P.IsHomogeneous 0 := by
    exact (hQ.pderiv (i := i)).pderiv (i := j)
  have hdegree : P.totalDegree = 0 :=
    Nat.eq_zero_of_le_zero hP.totalDegree_le
  have hPC : P = MvPolynomial.C (MvPolynomial.coeff 0 P) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree
  change MvPolynomial.eval z P = MvPolynomial.eval 0 P
  rw [hPC]
  simp

/-- The gradient of a homogeneous quadratic is twice its half-Hessian times
the point. -/
theorem gradient_eq_two_smul_mulVec
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Q.IsHomogeneous 2)
    (z : Fin 3 → ℝ) :
    ProjectiveDual.gradient Q z = (2 : ℝ) • (conicMatrix Q *ᵥ z) := by
  funext i
  have hEuler := ProjectiveDual.dot_gradient_eq_smul_eval
    (hQ.pderiv (i := i)) z
  simp only [Nat.reduceSub, Nat.cast_one, one_mul,
    ProjectiveDual.gradient, dotProduct] at hEuler
  simp only [Pi.smul_apply, smul_eq_mul, conicMatrix, Matrix.mulVec]
  simp_rw [← eval_secondDerivative_eq_eval_zero hQ i _ z]
  change MvPolynomial.eval z (MvPolynomial.pderiv i Q) =
    2 * ((fun j ↦ (2 : ℝ)⁻¹ * MvPolynomial.eval z
      (MvPolynomial.pderiv j (MvPolynomial.pderiv i Q))) ⬝ᵥ z)
  rw [← hEuler]
  simp only [dotProduct]
  rw [mul_comm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Euler's identity reconstructs a homogeneous quadratic from its half
Hessian. -/
theorem eval_eq_dotProduct_mulVec
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Q.IsHomogeneous 2)
    (z : Fin 3 → ℝ) :
    MvPolynomial.eval z Q = z ⬝ᵥ (conicMatrix Q *ᵥ z) := by
  have hEuler := ProjectiveDual.dot_gradient_eq_smul_eval hQ z
  rw [gradient_eq_two_smul_mulVec hQ] at hEuler
  simp only [Nat.cast_ofNat, dotProduct, Pi.smul_apply, smul_eq_mul] at hEuler ⊢
  have hsum :
      ∑ x, z x * (2 * (conicMatrix Q *ᵥ z) x) =
        2 * ∑ x, z x * (conicMatrix Q *ᵥ z) x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum] at hEuler
  linarith

/-- A homogeneous quadratic is exactly the matrix polynomial of half its
Hessian. -/
theorem matrixPolynomial_conicMatrix
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Q.IsHomogeneous 2) :
    matrixPolynomial (conicMatrix Q) = Q := by
  apply (matrixPolynomial_isHomogeneous _).funext hQ
  intro z
  rw [eval_matrixPolynomial, eval_eq_dotProduct_mulVec hQ]

/-- Complex irreducibility supplies, rather than assumes, nonsingularity of
the conic matrix.  If the determinant vanished, the explicit preceding
classification would factor the complexified quadratic into two nonunits. -/
theorem isUnit_det_conicMatrix_of_map_irreducible
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Q.IsHomogeneous 2)
    (hQirr : Irreducible (MvPolynomial.map (algebraMap ℝ ℂ) Q)) :
    IsUnit (conicMatrix Q).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  let A : Matrix (Fin 3) (Fin 3) ℂ :=
    (conicMatrix Q).map (algebraMap ℝ ℂ)
  have hAdet : A.det = 0 := by
    change ((conicMatrix Q).map (algebraMap ℝ ℂ)).det = 0
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_zero]
  have hAsymm : A.IsSymm :=
    (conicMatrix_isSymm Q).map (algebraMap ℝ ℂ)
  obtain ⟨L, R, hfactor, hL0, hR0⟩ :=
    exists_linear_factorization_of_isSymm_det_zero A hAsymm hAdet
  have hmapQ : MvPolynomial.map (algebraMap ℝ ℂ) Q =
      matrixPolynomial A := by
    rw [← matrixPolynomial_conicMatrix hQ, map_matrixPolynomial]
  have hfac : MvPolynomial.map (algebraMap ℝ ℂ) Q = L * R :=
    hmapQ.trans hfactor
  have notUnit_of_eval_zero : ∀ {P : MvPolynomial (Fin 3) ℂ},
      MvPolynomial.eval 0 P = 0 → ¬ IsUnit P := by
    intro P hP hunit
    have hconstant : MvPolynomial.constantCoeff P = 0 := by
      simpa using hP
    have hunit0 := hunit.map
      (MvPolynomial.constantCoeff : MvPolynomial (Fin 3) ℂ →+* ℂ)
    rw [hconstant] at hunit0
    exact not_isUnit_zero hunit0
  rcases hQirr.isUnit_or_isUnit hfac with hL | hR
  · exact notUnit_of_eval_zero hL0 hL
  · exact notUnit_of_eval_zero hR0 hR

/-- The quadratic equation dual to the conic matrix, in primal point
coordinates. -/
noncomputable def primalEnvelopePolynomial
    (Q : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  matrixPolynomial (conicMatrix Q)⁻¹

theorem primalEnvelopePolynomial_isHomogeneous
    (Q : MvPolynomial (Fin 3) ℝ) :
    (primalEnvelopePolynomial Q).IsHomogeneous 2 :=
  matrixPolynomial_isHomogeneous _

/-- The six conventional coefficients of the primal envelope in coordinate
order `[X:Y:Z]`, whereas matrices in this development use `[Z,X,Y]`. -/
noncomputable def envelopeForm (Q : MvPolynomial (Fin 3) ℝ) : Conic.Form :=
  let B := (conicMatrix Q)⁻¹
  { xx := B 1 1
    xy := 2 * B 1 2
    yy := B 2 2
    xz := 2 * B 1 0
    yz := 2 * B 2 0
    zz := B 0 0 }

theorem eval_primalEnvelope_eq_evalAffine
    (Q : MvPolynomial (Fin 3) ℝ) (x y : ℝ) :
    MvPolynomial.eval ![1, x, y] (primalEnvelopePolynomial Q) =
      (envelopeForm Q).evalAffine x y := by
  have hB : ((conicMatrix Q)⁻¹).IsSymm := (conicMatrix_isSymm Q).inv
  have h10 : (conicMatrix Q)⁻¹ 1 0 = (conicMatrix Q)⁻¹ 0 1 :=
    Matrix.IsSymm.ext_iff.mp hB 0 1
  have h20 : (conicMatrix Q)⁻¹ 2 0 = (conicMatrix Q)⁻¹ 0 2 :=
    Matrix.IsSymm.ext_iff.mp hB 0 2
  have h21 : (conicMatrix Q)⁻¹ 2 1 = (conicMatrix Q)⁻¹ 1 2 :=
    Matrix.IsSymm.ext_iff.mp hB 1 2
  rw [primalEnvelopePolynomial, eval_matrixPolynomial]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  simp only [envelopeForm, Conic.Form.evalAffine]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [← h10, ← h20, h21]
  simp
  ring

theorem eval_map_primalEnvelope_eq_evalComplex
    (Q : MvPolynomial (Fin 3) ℝ) (X Y Z : ℂ) :
    MvPolynomial.eval ![Z, X, Y]
        (MvPolynomial.map (algebraMap ℝ ℂ)
          (primalEnvelopePolynomial Q)) =
      (envelopeForm Q).evalComplex X Y Z := by
  have hB : ((conicMatrix Q)⁻¹).IsSymm := (conicMatrix_isSymm Q).inv
  have h10 : (conicMatrix Q)⁻¹ 1 0 = (conicMatrix Q)⁻¹ 0 1 :=
    Matrix.IsSymm.ext_iff.mp hB 0 1
  have h20 : (conicMatrix Q)⁻¹ 2 0 = (conicMatrix Q)⁻¹ 0 2 :=
    Matrix.IsSymm.ext_iff.mp hB 0 2
  have h21 : (conicMatrix Q)⁻¹ 2 1 = (conicMatrix Q)⁻¹ 1 2 :=
    Matrix.IsSymm.ext_iff.mp hB 1 2
  rw [primalEnvelopePolynomial, map_matrixPolynomial,
    eval_matrixPolynomial]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.map_apply]
  simp only [envelopeForm, Conic.Form.evalComplex]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  push_cast
  rw [← h10, ← h20, h21]
  simp
  ring

/-- Every complex homogeneous binary quadratic has a nonzero projective
zero. -/
theorem exists_nonzero_infinity_zero (q : Conic.Form) :
    ∃ X Y : ℂ, (X ≠ 0 ∨ Y ≠ 0) ∧ q.evalComplex X Y 0 = 0 := by
  by_cases hxx : (q.xx : ℂ) = 0
  · by_cases hxy : (q.xy : ℂ) = 0
    · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
      simp [Conic.Form.evalComplex, hxx]
    · refine ⟨-(q.yy : ℂ), (q.xy : ℂ), Or.inr hxy, ?_⟩
      simp [Conic.Form.evalComplex, hxx]
      ring
  · obtain ⟨δ, hδ⟩ := Complex.isSquare
        ((q.xy : ℂ) ^ 2 - 4 * (q.xx : ℂ) * (q.yy : ℂ))
    refine ⟨-(q.xy : ℂ) + δ, 2 * (q.xx : ℂ), ?_, ?_⟩
    · right
      exact mul_ne_zero (OfNat.ofNat_ne_zero 2) hxx
    · simp [Conic.Form.evalComplex]
      linear_combination (-(q.xx : ℂ)) * hδ

/-- The inverse half-Hessian vanishes at every Gauss image of the dual
conic.  This is the explicit envelope calculation
`(Σℓ)ᵀ Σ⁻¹ (Σℓ) = ℓᵀΣℓ`. -/
theorem eval_primalEnvelope_gradient_eq_zero
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Q.IsHomogeneous 2)
    (hdet : IsUnit (conicMatrix Q).det)
    {ell : Fin 3 → ℝ} (hell : MvPolynomial.eval ell Q = 0) :
    MvPolynomial.eval (ProjectiveDual.gradient Q ell)
      (primalEnvelopePolynomial Q) = 0 := by
  let A := conicMatrix Q
  have hAell : ell ⬝ᵥ (A *ᵥ ell) = 0 := by
    rw [← eval_eq_dotProduct_mulVec hQ]
    exact hell
  rw [primalEnvelopePolynomial, eval_matrixPolynomial,
    gradient_eq_two_smul_mulVec hQ]
  have hinv : A⁻¹ *ᵥ (A *ᵥ ell) = ell := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet,
      Matrix.one_mulVec]
  change ((2 : ℝ) • (A *ᵥ ell)) ⬝ᵥ
    (A⁻¹ *ᵥ ((2 : ℝ) • (A *ᵥ ell))) = 0
  rw [Matrix.mulVec_smul, hinv]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  change ∑ x, ell x * (A *ᵥ ell) x = 0 at hAell
  calc
    ∑ x, 2 * (A *ᵥ ell) x * (2 * ell x) =
        4 * ∑ x, ell x * (A *ᵥ ell) x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = 4 * 0 := by rw [hAell]
    _ = 0 := by norm_num

/-- Conversely every nonzero point of the primal envelope is the Gauss
image of a dual-conic point, up to the harmless scalar `2`. -/
theorem exists_dual_contact_of_primalEnvelope_zero
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Q.IsHomogeneous 2)
    (hdet : IsUnit (conicMatrix Q).det)
    {z : Fin 3 → ℝ}
    (hz : MvPolynomial.eval z (primalEnvelopePolynomial Q) = 0) :
    let ell := (conicMatrix Q)⁻¹ *ᵥ z
    MvPolynomial.eval ell Q = 0 ∧
      ProjectiveDual.gradient Q ell = (2 : ℝ) • z := by
  let A := conicMatrix Q
  let ell := A⁻¹ *ᵥ z
  have hAell : A *ᵥ ell = z := by
    change A *ᵥ (A⁻¹ *ᵥ z) = z
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet,
      Matrix.one_mulVec]
  have hzMatrix : z ⬝ᵥ (A⁻¹ *ᵥ z) = 0 := by
    simpa [primalEnvelopePolynomial, eval_matrixPolynomial, A] using hz
  refine ⟨?_, ?_⟩
  · rw [eval_eq_dotProduct_mulVec hQ, hAell]
    rw [dotProduct_comm]
    exact hzMatrix
  · rw [gradient_eq_two_smul_mulVec hQ, hAell]

/-- Substitute the linear coordinate change represented by `A`.  Evaluation
of `linearSubstitution A P` at `z` is evaluation of `P` at `A z`. -/
noncomputable def linearSubstitution
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ →+* MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun i ↦
    ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j

theorem eval_linearSubstitution
    (A : Matrix (Fin 3) (Fin 3) ℝ)
    (P : MvPolynomial (Fin 3) ℝ) (z : Fin 3 → ℝ) :
    MvPolynomial.eval z (linearSubstitution A P) =
      MvPolynomial.eval (A *ᵥ z) P := by
  classical
  change MvPolynomial.eval z
    (MvPolynomial.eval₂ MvPolynomial.C
      (fun i ↦ ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j) P) = _
  rw [MvPolynomial.eval_eval₂]
  have hcomp : (MvPolynomial.eval z).comp MvPolynomial.C =
      RingHom.id ℝ := by
    ext c
    simp
  rw [hcomp]
  congr 1
  funext i
  simp [Matrix.mulVec, dotProduct]

theorem linearSubstitution_comp
    (A B : Matrix (Fin 3) (Fin 3) ℝ)
    (P : MvPolynomial (Fin 3) ℝ) :
    linearSubstitution B (linearSubstitution A P) =
      linearSubstitution (A * B) P := by
  apply MvPolynomial.funext
  intro z
  rw [eval_linearSubstitution, eval_linearSubstitution,
    eval_linearSubstitution, Matrix.mulVec_mulVec]

@[simp] theorem linearSubstitution_one
    (P : MvPolynomial (Fin 3) ℝ) :
    linearSubstitution 1 P = P := by
  apply MvPolynomial.funext
  intro z
  rw [eval_linearSubstitution, Matrix.one_mulVec]

/-- For a quadratic, the Gauss pullback is the explicit linear substitution
by twice the conic matrix. -/
theorem gradientPullback_eq_linearSubstitution
    (F Q : MvPolynomial (Fin 3) ℝ) (hQ : Q.IsHomogeneous 2) :
    GaussPullback.gradientPullback F Q =
      linearSubstitution ((2 : ℝ) • conicMatrix Q) F := by
  apply MvPolynomial.funext
  intro ell
  rw [GaussPullback.eval_gradientPullback, eval_linearSubstitution,
    gradient_eq_two_smul_mulVec hQ, Matrix.smul_mulVec]

/-- Pulling a dual conic back by the inverse Gauss linear map gives one
quarter of its primal envelope equation. -/
theorem linearSubstitution_inverseGauss_eq_envelope
    {Q : MvPolynomial (Fin 3) ℝ} (hQ : Q.IsHomogeneous 2)
    (hdet : IsUnit (conicMatrix Q).det) :
    let B := (2 : ℝ)⁻¹ • (conicMatrix Q)⁻¹
    linearSubstitution B Q =
      MvPolynomial.C (4 : ℝ)⁻¹ * primalEnvelopePolynomial Q := by
  let A := conicMatrix Q
  let B := (2 : ℝ)⁻¹ • A⁻¹
  apply MvPolynomial.funext
  intro z
  rw [eval_linearSubstitution, eval_eq_dotProduct_mulVec hQ,
    map_mul, eval_C, primalEnvelopePolynomial, eval_matrixPolynomial]
  change (B *ᵥ z) ⬝ᵥ (A *ᵥ (B *ᵥ z)) =
    (4 : ℝ)⁻¹ * (z ⬝ᵥ (A⁻¹ *ᵥ z))
  have hAB : A * B = (2 : ℝ)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    change A * ((2 : ℝ)⁻¹ • A⁻¹) = (2 : ℝ)⁻¹ • 1
    rw [Matrix.mul_smul, Matrix.mul_nonsing_inv A hdet]
  have hBz : B *ᵥ z = (2 : ℝ)⁻¹ • (A⁻¹ *ᵥ z) := by
    change (((2 : ℝ)⁻¹ • A⁻¹) *ᵥ z) = _
    rw [Matrix.smul_mulVec]
  have hABz : A *ᵥ (B *ᵥ z) = (2 : ℝ)⁻¹ • z := by
    rw [Matrix.mulVec_mulVec, hAB, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hABz, hBz]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  norm_num
  ring

/-- The bidual divisor identity already implies, by the inverse linear Gauss
change of coordinates, that the primal envelope conic divides the primal
curve equation.  Thus no separate global biduality black box is needed in
the quadratic case. -/
theorem primalEnvelopePolynomial_dvd_of_gradientPullback_dvd
    {F Q : MvPolynomial (Fin 3) ℝ} (hQ : Q.IsHomogeneous 2)
    (hdet : IsUnit (conicMatrix Q).det)
    (hbidual : Q ∣ GaussPullback.gradientPullback F Q) :
    primalEnvelopePolynomial Q ∣ F := by
  let A := conicMatrix Q
  let G := (2 : ℝ) • A
  let B := (2 : ℝ)⁻¹ • A⁻¹
  have hGB : G * B = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    change ((2 : ℝ) • A) * ((2 : ℝ)⁻¹ • A⁻¹) = 1
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.mul_nonsing_inv A hdet]
    norm_num
  have hdiv : Q ∣ linearSubstitution G F := by
    rw [← gradientPullback_eq_linearSubstitution F Q hQ]
    exact hbidual
  obtain ⟨R, hR⟩ := hdiv
  have hmapped : linearSubstitution B Q ∣
      linearSubstitution B (linearSubstitution G F) := by
    refine ⟨linearSubstitution B R, ?_⟩
    rw [hR, map_mul]
  have hright : linearSubstitution B (linearSubstitution G F) = F := by
    rw [linearSubstitution_comp, hGB, linearSubstitution_one]
  have hleft : linearSubstitution B Q =
      MvPolynomial.C (4 : ℝ)⁻¹ * primalEnvelopePolynomial Q := by
    exact linearSubstitution_inverseGauss_eq_envelope hQ hdet
  rw [hright, hleft] at hmapped
  obtain ⟨R', hR'⟩ := hmapped
  refine ⟨MvPolynomial.C (4 : ℝ)⁻¹ * R', ?_⟩
  rw [hR']
  ring

theorem primalEnvelopePolynomial_not_isUnit
    (Q : MvPolynomial (Fin 3) ℝ) :
    ¬ IsUnit (primalEnvelopePolynomial Q) := by
  intro hunit
  have heval : MvPolynomial.eval 0 (primalEnvelopePolynomial Q) = 0 := by
    rw [primalEnvelopePolynomial, eval_matrixPolynomial]
    simp [dotProduct]
  have hconstant : MvPolynomial.constantCoeff
      (primalEnvelopePolynomial Q) = 0 := by
    simpa using heval
  have hunit0 := hunit.map
    (MvPolynomial.constantCoeff : MvPolynomial (Fin 3) ℝ →+* ℝ)
  rw [hconstant] at hunit0
  exact not_isUnit_zero hunit0

/-- If all infinity points of the primal curve are circular, then the
quadratic envelope contains the circular points.  Existence of an infinity
point is proved directly for a binary quadratic; no Bézout theorem is used. -/
theorem envelopeForm_eval_circularPoint_eq_zero_of_infinity_control
    {F Q : MvPolynomial (Fin 3) ℝ}
    (hdiv : primalEnvelopePolynomial Q ∣ F)
    (hInfinity : ∀ X Y : ℂ,
      MvPolynomial.eval ![0, X, Y]
        (MvPolynomial.map (algebraMap ℝ ℂ) F) = 0 →
      X ^ 2 + Y ^ 2 = 0) :
    (envelopeForm Q).evalComplex 1 Complex.I 0 = 0 := by
  let q := envelopeForm Q
  obtain ⟨X, Y, hXY, hq⟩ := exists_nonzero_infinity_zero q
  have hEzero : MvPolynomial.eval ![0, X, Y]
      (MvPolynomial.map (algebraMap ℝ ℂ)
        (primalEnvelopePolynomial Q)) = 0 := by
    rw [eval_map_primalEnvelope_eq_evalComplex]
    exact hq
  obtain ⟨R, hR⟩ := hdiv
  have hFzero : MvPolynomial.eval ![0, X, Y]
      (MvPolynomial.map (algebraMap ℝ ℂ) F) = 0 := by
    rw [hR, map_mul, map_mul, hEzero, zero_mul]
  have hsum : X ^ 2 + Y ^ 2 = 0 := hInfinity X Y hFzero
  have hX : X ≠ 0 := by
    intro hX
    have hYsq : Y ^ 2 = 0 := by simpa [hX] using hsum
    have hY : Y = 0 := sq_eq_zero_iff.mp hYsq
    exact hXY.elim (fun hx ↦ hx hX) (fun hy ↦ hy hY)
  have hfactor : (Y - Complex.I * X) * (Y + Complex.I * X) = 0 := by
    calc
      (Y - Complex.I * X) * (Y + Complex.I * X) =
          Y ^ 2 - Complex.I ^ 2 * X ^ 2 := by ring
      _ = Y ^ 2 + X ^ 2 := by rw [Complex.I_sq]; ring
      _ = 0 := by linear_combination hsum
  rcases mul_eq_zero.mp hfactor with hplus | hminus
  · have hY : Y = Complex.I * X := sub_eq_zero.mp hplus
    have hscale : q.evalComplex X (Complex.I * X) 0 =
        X ^ 2 * q.evalComplex 1 Complex.I 0 := by
      rw [Conic.Form.evalComplex, Conic.Form.evalComplex]
      norm_num
      rw [mul_pow, Complex.I_sq]
      ring
    rw [hY, hscale] at hq
    exact (mul_eq_zero.mp hq).resolve_left (pow_ne_zero 2 hX)
  · have hY : Y = -Complex.I * X := by
      linear_combination hminus
    have hscale : q.evalComplex X (-Complex.I * X) 0 =
        X ^ 2 * q.evalComplex 1 (-Complex.I) 0 := by
      rw [Conic.Form.evalComplex, Conic.Form.evalComplex]
      norm_num
      rw [mul_pow, Complex.I_sq]
      ring
    rw [hY, hscale] at hq
    have hqminus : q.evalComplex 1 (-Complex.I) 0 = 0 :=
      (mul_eq_zero.mp hq).resolve_left (pow_ne_zero 2 hX)
    have hre := congrArg Complex.re hqminus
    have him := congrArg Complex.im hqminus
    simp [Conic.Form.evalComplex, Complex.I_sq] at hre him
    apply (Conic.eval_circularPoint_eq_zero_iff q).2
    constructor <;> linarith

/-- A nonsingular envelope conic through a circular point has nonzero
Euclidean quadratic coefficient. -/
theorem envelopeForm_xx_ne_zero
    {Q : MvPolynomial (Fin 3) ℝ}
    (hdet : IsUnit (conicMatrix Q).det)
    (hcircular : (envelopeForm Q).evalComplex 1 Complex.I 0 = 0) :
    (envelopeForm Q).xx ≠ 0 := by
  obtain ⟨hyy, hxy⟩ :=
    (Conic.eval_circularPoint_eq_zero_iff (envelopeForm Q)).mp hcircular
  simp only [envelopeForm] at hyy hxy ⊢
  intro hxx
  have h22 : (conicMatrix Q)⁻¹ 2 2 = 0 := by
    rw [hyy, hxx]
  have h12 : (conicMatrix Q)⁻¹ 1 2 = 0 := by
    exact (mul_eq_zero.mp hxy).resolve_left (by norm_num)
  have hsymm : ((conicMatrix Q)⁻¹).IsSymm :=
    (conicMatrix_isSymm Q).inv
  have h21 : (conicMatrix Q)⁻¹ 2 1 = 0 := by
    rw [Matrix.IsSymm.ext_iff.mp hsymm 1 2, h12]
  have hdet0 : ((conicMatrix Q)⁻¹).det = 0 := by
    rw [Matrix.det_fin_three]
    simp [hxx, h22, h12, h21]
  have hunitInv := (conicMatrix Q).isUnit_nonsing_inv_det hdet
  rw [hdet0] at hunitInv
  exact not_isUnit_zero hunitInv

end ConicEnvelope

end DiskRigidity.Algebraic
