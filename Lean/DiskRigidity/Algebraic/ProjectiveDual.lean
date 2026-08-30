/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Tangent lines, the Gauss differential, and local biduality for plane curves

This file develops the algebraic identities behind the bidual/contact step in
Proposition 7.1.  Points and line coordinates are represented by nonzero
vectors in `Fin 3 → K`; all statements are invariant under rescaling.

No global duality theorem is assumed here.  The main result
`gradient_dual_eq_smul_contact` recovers the primal contact point from the
gradient of a homogeneous equation of the dual curve.  Its hypotheses are the
explicit conormal and Zariski-tangent equations.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace ProjectiveDual

open Matrix MvPolynomial

variable {K : Type*} [Field K]

/-- The gradient of a multivariate polynomial at a point. -/
noncomputable def gradient {n : ℕ} (F : MvPolynomial (Fin n) K)
    (z : Fin n → K) : Fin n → K :=
  fun i ↦ MvPolynomial.eval z (MvPolynomial.pderiv i F)

/-- The formal directional derivative of a polynomial at a point. -/
noncomputable def directionalDerivative {n : ℕ}
    (F : MvPolynomial (Fin n) K) (z dz : Fin n → K) : K :=
  dz ⬝ᵥ gradient F z

/-- The differential of the Gauss map `z ↦ gradient F z`. -/
noncomputable def gaussDifferential (F : MvPolynomial (Fin 3) K)
    (z dz : Fin 3 → K) : Fin 3 → K :=
  fun i ↦ directionalDerivative (MvPolynomial.pderiv i F) z dz

/-- A representative of a projective point lies on the homogeneous curve. -/
def OnCurve {n : ℕ} (F : MvPolynomial (Fin n) K) (z : Fin n → K) : Prop :=
  z ≠ 0 ∧ MvPolynomial.eval z F = 0

/-- A projective curve is regular at a representative when its gradient is
nonzero there. -/
def RegularAt {n : ℕ} (F : MvPolynomial (Fin n) K) (z : Fin n → K) : Prop :=
  OnCurve F z ∧ gradient F z ≠ 0

/-- A Zariski tangent vector to `F = 0` at `z`. -/
def IsTangentVector {n : ℕ} (F : MvPolynomial (Fin n) K)
    (z dz : Fin n → K) : Prop :=
  directionalDerivative F z dz = 0

/-- The explicit conormal relation for a regular plane-curve point. -/
def IsConormalPoint (F : MvPolynomial (Fin 3) K)
    (z ell : Fin 3 → K) : Prop :=
  RegularAt F z ∧ ell = gradient F z

/-- Scaling all projective coordinates scales a homogeneous form by the
corresponding power. -/
theorem eval_smul_of_isHomogeneous {n d : ℕ}
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous d)
    (a : K) (z : Fin n → K) :
    MvPolynomial.eval (a • z) F = a ^ d * MvPolynomial.eval z F := by
  classical
  induction hF using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add P Q hP hQ ihP ihQ => simp [ihP, ihQ, mul_add]
  | monomial e r he =>
      simp only [MvPolynomial.eval_monomial, Pi.smul_apply, smul_eq_mul,
        mul_pow, Finsupp.prod, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum]
      rw [show ∑ i ∈ e.support, e i = d by
        rw [← Finsupp.degree_apply, Finsupp.degree_eq_weight_one]
        simpa only [Pi.one_def] using he]
      ring

/-- The gradient of a degree-`d` homogeneous form is homogeneous of degree
`d - 1`.  This is the coordinate identity needed to pass freely between an
affine representative and an arbitrary representative of a projective
point. -/
theorem gradient_smul_of_isHomogeneous {n d : ℕ}
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous d)
    (a : K) (z : Fin n → K) :
    gradient F (a • z) = a ^ (d - 1) • gradient F z := by
  funext i
  exact eval_smul_of_isHomogeneous (hF.pderiv (i := i)) a z

/-- Regularity of a homogeneous projective curve is unchanged after
rescaling a representative by a nonzero scalar. -/
theorem regularAt_smul_of_isHomogeneous {n d : ℕ}
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous d)
    {z : Fin n → K} (hz : RegularAt F z) {a : K} (ha : a ≠ 0) :
    RegularAt F (a • z) := by
  refine ⟨⟨smul_ne_zero ha hz.1.1, ?_⟩, ?_⟩
  · rw [eval_smul_of_isHomogeneous hF, hz.1.2, mul_zero]
  · rw [gradient_smul_of_isHomogeneous hF]
    exact smul_ne_zero (pow_ne_zero _ ha) hz.2

/-- The converse rescaling form of `regularAt_smul_of_isHomogeneous`. -/
theorem regularAt_of_smul_of_isHomogeneous {n d : ℕ}
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous d)
    {z : Fin n → K} {a : K} (ha : a ≠ 0)
    (hz : RegularAt F (a • z)) : RegularAt F z := by
  have h := regularAt_smul_of_isHomogeneous hF hz (inv_ne_zero ha)
  simpa [smul_smul, ha] using h

/-- Euler's identity after evaluation: the gradient of a degree-`d`
homogeneous polynomial is incident with every zero of the polynomial. -/
theorem dot_gradient_eq_smul_eval {n d : ℕ}
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous d) (z : Fin n → K) :
    z ⬝ᵥ gradient F z = (d : K) * MvPolynomial.eval z F := by
  classical
  have h := congrArg (MvPolynomial.eval z) hF.sum_X_mul_pderiv
  simpa [gradient, dotProduct, nsmul_eq_mul] using h

/-- At a projective zero, the gradient gives an incident line. -/
theorem dot_gradient_eq_zero {n d : ℕ}
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous d)
    {z : Fin n → K} (hz : MvPolynomial.eval z F = 0) :
    z ⬝ᵥ gradient F z = 0 := by
  rw [dot_gradient_eq_smul_eval hF, hz, mul_zero]

/-- Mixed formal partial derivatives of a multivariate polynomial commute. -/
theorem pderiv_pderiv_comm {n : ℕ} (i j : Fin n)
    (F : MvPolynomial (Fin n) K) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j F) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i F) := by
  classical
  ext a
  simp only [MvPolynomial.coeff_pderiv]
  by_cases hij : i = j
  · subst j
    rfl
  · simp only [Finsupp.add_apply, Finsupp.single_apply, hij, Ne.symm hij,
      if_false]
    rw [show a + Finsupp.single i 1 + Finsupp.single j 1 =
      a + Finsupp.single j 1 + Finsupp.single i 1 by abel]
    ring_nf

/-- The differentiated Euler identity.  Contracting the Gauss differential
with the original point is `(d-1)` times the tangent equation. -/
theorem dot_gaussDifferential_eq {d : ℕ}
    {F : MvPolynomial (Fin 3) K} (hF : F.IsHomogeneous d)
    (z dz : Fin 3 → K) :
    z ⬝ᵥ gaussDifferential F z dz =
      ((d - 1 : ℕ) : K) * directionalDerivative F z dz := by
  classical
  simp only [gaussDifferential, directionalDerivative, gradient, dotProduct]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hj := congrArg (MvPolynomial.eval z) (hF.pderiv (i := j)).sum_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, nsmul_eq_mul, map_natCast] at hj
  calc
    ∑ i, z i * (dz j * MvPolynomial.eval z
        (MvPolynomial.pderiv j (MvPolynomial.pderiv i F))) =
        dz j * ∑ i, z i * MvPolynomial.eval z
          (MvPolynomial.pderiv i (MvPolynomial.pderiv j F)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pderiv_pderiv_comm]
      ring_nf
    _ = dz j * (((d - 1 : ℕ) : K) *
        MvPolynomial.eval z (MvPolynomial.pderiv j F)) := by rw [hj]
    _ = ((d - 1 : ℕ) : K) *
        (dz j * MvPolynomial.eval z (MvPolynomial.pderiv j F)) := by ring_nf

/-- A tangent vector to a homogeneous curve makes the Gauss differential
annihilate the original point. -/
theorem dot_gaussDifferential_eq_zero {d : ℕ}
    {F : MvPolynomial (Fin 3) K} (hF : F.IsHomogeneous d)
    {z dz : Fin 3 → K} (hdz : IsTangentVector F z dz) :
    gaussDifferential F z dz ⬝ᵥ z = 0 := by
  rw [dotProduct_comm, dot_gaussDifferential_eq hF, hdz, mul_zero]

/-- In three dimensions, two independent covectors have a one-dimensional
common annihilator. -/
theorem eq_smul_of_common_annihilator
    {ell dell x y : Fin 3 → K}
    (hli : LinearIndependent K ![ell, dell])
    (hellx : ell ⬝ᵥ x = 0) (hdellx : dell ⬝ᵥ x = 0)
    (helly : ell ⬝ᵥ y = 0) (hdelly : dell ⬝ᵥ y = 0)
    (hx : x ≠ 0) : ∃ a : K, y = a • x := by
  have hc : ell ⨯₃ dell ≠ 0 :=
    crossProduct_ne_zero_iff_linearIndependent.mpr hli
  have hcx : (ell ⨯₃ dell) ⨯₃ x = 0 := by
    rw [cross_cross_eq_smul_sub_smul]
    simp [hellx, hdellx]
  have hcy : (ell ⨯₃ dell) ⨯₃ y = 0 := by
    rw [cross_cross_eq_smul_sub_smul]
    simp [helly, hdelly]
  have hnotlix : ¬ LinearIndependent K ![ell ⨯₃ dell, x] := by
    intro h
    exact crossProduct_ne_zero_iff_linearIndependent.mpr h hcx
  have hnotliy : ¬ LinearIndependent K ![ell ⨯₃ dell, y] := by
    intro h
    exact crossProduct_ne_zero_iff_linearIndependent.mpr h hcy
  rw [LinearIndependent.pair_iff' hc, not_forall_not] at hnotlix hnotliy
  obtain ⟨a, ha⟩ := hnotlix
  obtain ⟨b, hb⟩ := hnotliy
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hx
    simpa [ha0] using ha.symm
  refine ⟨b / a, ?_⟩
  rw [← hb, ← ha]
  simp [div_eq_mul_inv, ha0, smul_smul]

/-- **Explicit local biduality/contact recovery.**

Let `ell` be a smooth point of a homogeneous dual equation `Q`, and let
`dell` be a nonradial tangent direction there.  If the primal point `z` is
incident with both `ell` and `dell`, then the gradient of `Q` at `ell`
recovers `z` up to projective rescaling.
-/
theorem gradient_dual_eq_smul_contact {m : ℕ}
    {Q : MvPolynomial (Fin 3) K} (hQ : Q.IsHomogeneous m)
    {z ell dell : Fin 3 → K}
    (hz : z ≠ 0)
    (hQell : MvPolynomial.eval ell Q = 0)
    (htangent : IsTangentVector Q ell dell)
    (hli : LinearIndependent K ![ell, dell])
    (hincidence : ell ⬝ᵥ z = 0)
    (hdincidence : dell ⬝ᵥ z = 0) :
    ∃ a : K, gradient Q ell = a • z := by
  apply eq_smul_of_common_annihilator hli hincidence hdincidence
  · exact dot_gradient_eq_zero hQ hQell
  · exact htangent
  · exact hz

/-- Contact recovery specialized to the Gauss differential of a homogeneous
primal curve.  Every incidence equation is derived from the two polynomial
equations and the stated tangent directions. -/
theorem gradient_dual_eq_smul_of_conormal {d m : ℕ}
    {F Q : MvPolynomial (Fin 3) K}
    (hF : F.IsHomogeneous d) (hQ : Q.IsHomogeneous m)
    {z dz ell : Fin 3 → K}
    (hconormal : IsConormalPoint F z ell)
    (hdz : IsTangentVector F z dz)
    (hQell : MvPolynomial.eval ell Q = 0)
    (hQgauss : IsTangentVector Q ell (gaussDifferential F z dz))
    (hli : LinearIndependent K ![ell, gaussDifferential F z dz]) :
    ∃ a : K, gradient Q ell = a • z := by
  rcases hconormal with ⟨⟨⟨hz, hFz⟩, _⟩, rfl⟩
  apply gradient_dual_eq_smul_contact hQ hz hQell hQgauss hli
  · rw [dotProduct_comm]
    exact dot_gradient_eq_zero hF hFz
  · exact dot_gaussDifferential_eq_zero hF hdz

end ProjectiveDual

end DiskRigidity.Algebraic
