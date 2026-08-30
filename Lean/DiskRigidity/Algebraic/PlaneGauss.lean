/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.GaussPullback
public import DiskRigidity.Algebraic.GenericAvoidance
public import DiskRigidity.Algebraic.ProjectiveHomogenization

/-!
# Explicit Gauss-map ramification for a plane curve

In the affine dual chart `[s:t:1]`, the vector `(-Q_t,Q_s,0)` is tangent to
`Q=0`.  This file writes its image under the Gauss differential as a
polynomial vector.  A nonzero component of the resulting cross product is an
explicit certificate that the Gauss map is unramified.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace PlaneGauss

open Matrix MvPolynomial Polynomial
open ProjectiveDual
open GenericSpecialization PlaneCurveSpecialization

variable {K : Type*} [Field K]

/-- The polynomial tangent direction `(-Q_u,Q_s,0)` in the chart `v=1`. -/
noncomputable def affineTangentPolynomial
    (Q : MvPolynomial (Fin 3) K) : Fin 3 → MvPolynomial (Fin 3) K :=
  ![-MvPolynomial.pderiv 1 Q, MvPolynomial.pderiv 0 Q, 0]

/-- Polynomial coordinates of the Gauss differential in the affine tangent
direction. -/
noncomputable def gaussVelocityPolynomial
    (Q : MvPolynomial (Fin 3) K) : Fin 3 → MvPolynomial (Fin 3) K :=
  fun i ↦ ∑ j, affineTangentPolynomial Q j *
    MvPolynomial.pderiv j (MvPolynomial.pderiv i Q)

/-- Polynomial cross product detecting projective ramification. -/
noncomputable def gaussCrossPolynomial
    (Q : MvPolynomial (Fin 3) K) : Fin 3 → MvPolynomial (Fin 3) K :=
  (fun i ↦ MvPolynomial.pderiv i Q) ⨯₃ gaussVelocityPolynomial Q

theorem affineTangent_isTangent (Q : MvPolynomial (Fin 3) K)
    (ell : Fin 3 → K) :
    IsTangentVector Q ell
      (fun i ↦ MvPolynomial.eval ell (affineTangentPolynomial Q i)) := by
  classical
  simp only [IsTangentVector, directionalDerivative, ProjectiveDual.gradient, dotProduct,
    affineTangentPolynomial, Fin.sum_univ_three]
  simp
  ring

theorem eval_gaussVelocityPolynomial (Q : MvPolynomial (Fin 3) K)
    (ell : Fin 3 → K) (i : Fin 3) :
    MvPolynomial.eval ell (gaussVelocityPolynomial Q i) =
      gaussDifferential Q ell
        (fun j ↦ MvPolynomial.eval ell (affineTangentPolynomial Q j)) i := by
  classical
  simp [gaussVelocityPolynomial, gaussDifferential, directionalDerivative,
    ProjectiveDual.gradient, dotProduct]

theorem eval_gaussCrossPolynomial (Q : MvPolynomial (Fin 3) K)
    (ell : Fin 3 → K) (i : Fin 3) :
    MvPolynomial.eval ell (gaussCrossPolynomial Q i) =
      (gradient Q ell ⨯₃
        gaussDifferential Q ell
          (fun j ↦ MvPolynomial.eval ell (affineTangentPolynomial Q j))) i := by
  fin_cases i <;>
    simp [gaussCrossPolynomial, cross_apply, ProjectiveDual.gradient,
      eval_gaussVelocityPolynomial]

/-- Nonvanishing of one explicit cross-product coordinate is precisely the
local nonramification input needed by bidual tangent recovery. -/
theorem linearIndependent_of_eval_gaussCross_ne_zero
    (Q : MvPolynomial (Fin 3) K) (ell : Fin 3 → K) (i : Fin 3)
    (hi : MvPolynomial.eval ell (gaussCrossPolynomial Q i) ≠ 0) :
    LinearIndependent K
      ![gradient Q ell,
        gaussDifferential Q ell
          (fun j ↦ MvPolynomial.eval ell (affineTangentPolynomial Q j))] := by
  rw [← crossProduct_ne_zero_iff_linearIndependent]
  intro hzero
  apply hi
  rw [eval_gaussCrossPolynomial, hzero]
  rfl

section RealSpecialization

/-- Isolating the first variable turns `∂Q/∂s` into the ordinary
derivative in `s`. -/
theorem finSuccEquiv_pderiv_zero (Q : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.finSuccEquiv ℝ 2 (MvPolynomial.pderiv 0 Q) =
      (MvPolynomial.finSuccEquiv ℝ 2 Q).derivative := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add P R hP hR => simp [hP, hR]
  | mul_X P i hP =>
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp only [MvPolynomial.pderiv_mul,
          MvPolynomial.pderiv_X_self, mul_one, map_add, map_mul,
          Polynomial.derivative_mul, hP]
        rw [MvPolynomial.finSuccEquiv_X_zero]
        simp [mul_comm]
      · simp only [MvPolynomial.pderiv_mul,
          MvPolynomial.pderiv_X_of_ne (Fin.succ_ne_zero j), mul_zero,
          add_zero, map_mul, Polynomial.derivative_mul, hP]
        rw [MvPolynomial.finSuccEquiv_X_succ]
        simp [mul_comm]

theorem affineFamily_pderiv_zero (Q : MvPolynomial (Fin 3) ℝ) :
    affineFamily (MvPolynomial.pderiv 0 Q) =
      (affineFamily Q).derivative := by
  rw [affineFamily, affineFamily, finSuccEquiv_pderiv_zero,
    Polynomial.derivative_map]

theorem specialize_affineFamily_derivative
    (Q : MvPolynomial (Fin 3) ℝ) (t : ℝ) :
    specialize (affineFamily (MvPolynomial.pderiv 0 Q)) t =
      (specialize (affineFamily Q) t).derivative := by
  rw [affineFamily_pderiv_zero]
  change (affineFamily Q).derivative.map (Polynomial.evalRingHom t) =
    ((affineFamily Q).map (Polynomial.evalRingHom t)).derivative
  exact (Polynomial.derivative_map _ _).symm

theorem eval_pderiv_zero_eq_eval_derivative
    (Q : MvPolynomial (Fin 3) ℝ) (s t : ℝ) :
    MvPolynomial.eval ![s, t, 1] (MvPolynomial.pderiv 0 Q) =
      ((specialize (affineFamily Q) t).derivative).eval s := by
  rw [← specialize_affineFamily_derivative]
  exact (eval_specialize_affineFamily (MvPolynomial.pderiv 0 Q) s t).symm

theorem eval_ne_zero_of_isCoprime_of_eval_eq_zero
    {p r : ℝ[X]} {s : ℝ} (hcop : IsCoprime p r)
    (hp : p.eval s = 0) : r.eval s ≠ 0 := by
  intro hr
  have hmap := hcop.map (Polynomial.evalRingHom s)
  simp [hp, hr] at hmap

/-- A single affine point at which one Gauss cross minor is nonzero rules out
generic divisibility of that minor by the curve equation.  The proof is
Gauss's lemma: generic divisibility over `ℝ(t)` descends to divisibility over
`ℝ[t]`, and hence would force the minor to vanish at every affine point of
the curve.  This turns the abstract `hnotdvd` input below into the concrete
local nonramification witness supplied by a curved tangent arc. -/
theorem not_generic_dvd_of_affine_unramified
    {Q : MvPolynomial (Fin 3) ℝ}
    (hPirr : Irreducible (affineFamily Q))
    (hPdegree : (affineFamily Q).natDegree ≠ 0)
    (k : Fin 3) (s t : ℝ)
    (hQell : MvPolynomial.eval ![s, t, 1] Q = 0)
    (hcross : MvPolynomial.eval ![s, t, 1]
      (gaussCrossPolynomial Q k) ≠ 0) :
    ¬ genericMap (affineFamily Q) ∣
      genericMap (affineFamily (gaussCrossPolynomial Q k)) := by
  intro hdvd
  have hprimitive : (affineFamily Q).IsPrimitive :=
    hPirr.isPrimitive hPdegree
  have hdvdFamily : affineFamily Q ∣
      affineFamily (gaussCrossPolynomial Q k) :=
    hprimitive.dvd_of_fraction_map_dvd_fraction_map hdvd
  have hdvdSpecialized : specialize (affineFamily Q) t ∣
      specialize (affineFamily (gaussCrossPolynomial Q k)) t :=
    map_dvd (Polynomial.evalRingHom t) hdvdFamily
  obtain ⟨R, hR⟩ := hdvdSpecialized
  apply hcross
  rw [← eval_specialize_affineFamily (gaussCrossPolynomial Q k) s t,
    hR, Polynomial.eval_mul, eval_specialize_affineFamily Q s t,
    hQell, zero_mul]

/-- Outside the discriminant and one explicit Gauss-minor resultant, every
root gives a smooth dual point where the Gauss map is unramified. -/
theorem regular_and_unramified_of_generic_root
    {Q : MvPolynomial (Fin 3) ℝ} (k : Fin 3)
    (hlead : IsUnit (affineFamily Q).leadingCoeff)
    (hPgen : Irreducible (genericMap (affineFamily Q)))
    (hnotdvd : ¬ genericMap (affineFamily Q) ∣
      genericMap (affineFamily (gaussCrossPolynomial Q k)))
    {t s : ℝ}
    (htDisc : t ∉ exceptionalSet (affineFamily Q))
    (htGauss : t ∉ GenericAvoidance.pairExceptionalSet
      (affineFamily Q) (affineFamily (gaussCrossPolynomial Q k)))
    (hs : (specialize (affineFamily Q) t).eval s = 0) :
    let ell : Fin 3 → ℝ := ![s, t, 1]
    RegularAt Q ell ∧
      LinearIndependent ℝ
        ![ProjectiveDual.gradient Q ell,
          gaussDifferential Q ell
            (fun j ↦ MvPolynomial.eval ell (affineTangentPolynomial Q j))] := by
  let ell : Fin 3 → ℝ := ![s, t, 1]
  let p := specialize (affineFamily Q) t
  let r := specialize (affineFamily (gaussCrossPolynomial Q k)) t
  have hsep : p.Separable :=
    separable_specialize_of_not_mem_exceptional hlead hPgen htDisc
  have hcopDeriv : IsCoprime p p.derivative :=
    (Polynomial.separable_def p).mp hsep
  have hderiv : p.derivative.eval s ≠ 0 :=
    eval_ne_zero_of_isCoprime_of_eval_eq_zero hcopDeriv hs
  have hcopGauss : IsCoprime p r :=
    GenericAvoidance.isCoprime_specialize_of_not_mem
      hlead hPgen hnotdvd htGauss
  have hram : r.eval s ≠ 0 :=
    eval_ne_zero_of_isCoprime_of_eval_eq_zero hcopGauss hs
  have hQell : MvPolynomial.eval ell Q = 0 := by
    rw [← eval_specialize_affineFamily Q s t]
    exact hs
  have hell0 : ell ≠ 0 := by
    intro hzero
    have := congrFun hzero (2 : Fin 3)
    change (1 : ℝ) = 0 at this
    exact one_ne_zero this
  have hgrad0 : ProjectiveDual.gradient Q ell ≠ 0 := by
    intro hzero
    apply hderiv
    rw [← eval_pderiv_zero_eq_eval_derivative Q s t]
    exact congrFun hzero 0
  refine ⟨⟨⟨hell0, hQell⟩, hgrad0⟩, ?_⟩
  apply linearIndependent_of_eval_gaussCross_ne_zero Q ell k
  rw [← eval_specialize_affineFamily (gaussCrossPolynomial Q k) s t]
  exact hram

end RealSpecialization

end PlaneGauss

end DiskRigidity.Algebraic
