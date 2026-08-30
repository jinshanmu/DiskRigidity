/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.ProjectiveDual
public import DiskRigidity.Algebraic.ZariskiDivisibility

/-!
# The bidual Gauss pullback

For homogeneous plane-curve equations `F` and `Q`, the polynomial
`F(∇Q)` cuts out the points obtained by applying the Gauss map of `Q`.
This file proves the formal chain rule and the local bidual tangent statement
used in the generic-contact paragraph of Proposition 7.1.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace GaussPullback

open Matrix MvPolynomial
open ProjectiveDual

variable {K : Type*} [Field K]

/-- Substitute the three partial derivatives of `Q` into `F`. -/
noncomputable def gradientPullback
    (F Q : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 3) K :=
  MvPolynomial.eval₂ MvPolynomial.C (fun i ↦ MvPolynomial.pderiv i Q) F

/-- The Gauss pullback of a degree-`d` form by the gradient of a degree-`m`
form is homogeneous of degree `(m-1)d`. -/
theorem gradientPullback_isHomogeneous {d m : ℕ}
    {F Q : MvPolynomial (Fin 3) K}
    (hF : F.IsHomogeneous d) (hQ : Q.IsHomogeneous m) :
    (gradientPullback F Q).IsHomogeneous ((m - 1) * d) := by
  exact hF.eval₂ MvPolynomial.C (fun i ↦ MvPolynomial.pderiv i Q)
    (fun c ↦ isHomogeneous_C (Fin 3) c)
    (fun i ↦ hQ.pderiv (i := i))

theorem eval_gradientPullback (F Q : MvPolynomial (Fin 3) K)
    (ell : Fin 3 → K) :
  MvPolynomial.eval ell (gradientPullback F Q) =
      MvPolynomial.eval (gradient Q ell) F := by
  rw [gradientPullback, MvPolynomial.eval_eval₂]
  have hcomp : (MvPolynomial.eval ell).comp MvPolynomial.C =
      RingHom.id K := by
    ext c
    simp
  rw [hcomp]
  rfl

theorem directionalDerivative_add (P R : MvPolynomial (Fin 3) K)
    (z dz : Fin 3 → K) :
    directionalDerivative (P + R) z dz =
      directionalDerivative P z dz + directionalDerivative R z dz := by
  classical
  simp [directionalDerivative, gradient, dotProduct, Finset.sum_add_distrib,
    mul_add]

theorem directionalDerivative_mul (P R : MvPolynomial (Fin 3) K)
    (z dz : Fin 3 → K) :
    directionalDerivative (P * R) z dz =
      MvPolynomial.eval z R * directionalDerivative P z dz +
        MvPolynomial.eval z P * directionalDerivative R z dz := by
  classical
  simp only [directionalDerivative, gradient, MvPolynomial.pderiv_mul,
    map_add, map_mul, dotProduct, Finset.mul_sum]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1 <;>
    apply Finset.sum_congr rfl <;>
    intro i _ <;>
    ring

@[simp] theorem directionalDerivative_C (c : K)
    (z dz : Fin 3 → K) :
    directionalDerivative (MvPolynomial.C c) z dz = 0 := by
  classical
  simp [directionalDerivative, gradient, dotProduct]

theorem directionalDerivative_X (i : Fin 3) (z dz : Fin 3 → K) :
    directionalDerivative (MvPolynomial.X i) z dz = dz i := by
  classical
  simp [directionalDerivative, gradient, dotProduct, Pi.single_apply]

/-- Formal chain rule for the Gauss substitution `ell ↦ ∇Q(ell)`. -/
theorem directionalDerivative_gradientPullback
    (F Q : MvPolynomial (Fin 3) K) (ell dell : Fin 3 → K) :
    directionalDerivative (gradientPullback F Q) ell dell =
      directionalDerivative F (gradient Q ell)
        (gaussDifferential Q ell dell) := by
  induction F using MvPolynomial.induction_on with
  | C c =>
      simp [gradientPullback]
  | add P R hP hR =>
      rw [gradientPullback, MvPolynomial.eval₂_add]
      rw [directionalDerivative_add, directionalDerivative_add]
      exact congrArg₂ (fun x y ↦ x + y) hP hR
  | mul_X P i hP =>
      rw [gradientPullback, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
      rw [directionalDerivative_mul, directionalDerivative_mul]
      have hevalP : MvPolynomial.eval ell
          (MvPolynomial.eval₂ MvPolynomial.C
            (fun j ↦ MvPolynomial.pderiv j Q) P) =
          MvPolynomial.eval (gradient Q ell) P := by
        simpa only [gradientPullback] using eval_gradientPullback P Q ell
      have hdirP : directionalDerivative
          (MvPolynomial.eval₂ MvPolynomial.C
            (fun j ↦ MvPolynomial.pderiv j Q) P) ell dell =
          directionalDerivative P (gradient Q ell)
            (gaussDifferential Q ell dell) := by
        simpa only [gradientPullback] using hP
      have hpartial : directionalDerivative (MvPolynomial.pderiv i Q)
          ell dell = gaussDifferential Q ell dell i := rfl
      rw [hevalP, hdirP, hpartial, directionalDerivative_X]
      simp only [MvPolynomial.eval_X, gradient]

/-- A divisor identity `Q ∣ F(∇Q)` makes the Gauss image of every zero
of `Q` lie on `F`. -/
theorem eval_gradient_eq_zero_of_dvd
    {F Q : MvPolynomial (Fin 3) K}
    (hdiv : Q ∣ gradientPullback F Q)
    {ell : Fin 3 → K} (hQell : MvPolynomial.eval ell Q = 0) :
    MvPolynomial.eval (gradient Q ell) F = 0 := by
  obtain ⟨R, hR⟩ := hdiv
  rw [← eval_gradientPullback, hR, map_mul, hQell, zero_mul]

/-- Differentiating `Q ∣ F(∇Q)` along a tangent direction to `Q`
shows that the Gauss differential is tangent to `F`. -/
theorem gaussDifferential_isTangent_of_dvd
    {F Q : MvPolynomial (Fin 3) K}
    (hdiv : Q ∣ gradientPullback F Q)
    {ell dell : Fin 3 → K}
    (hQell : MvPolynomial.eval ell Q = 0)
    (hdell : IsTangentVector Q ell dell) :
    IsTangentVector F (gradient Q ell)
      (gaussDifferential Q ell dell) := by
  obtain ⟨R, hR⟩ := hdiv
  rw [IsTangentVector] at hdell ⊢
  rw [← directionalDerivative_gradientPullback, hR,
    directionalDerivative_mul, hQell, hdell]
  simp

/-- **Explicit bidual tangent recovery.**  Away from ramification of the
Gauss map of `Q`, the line `ell` is the tangent to `F` at `∇Q(ell)`.
All global input is the concrete divisor identity `Q ∣ F(∇Q)`. -/
theorem gradient_primal_eq_smul_line_of_dvd {d m : ℕ}
    {F Q : MvPolynomial (Fin 3) K}
    (hF : F.IsHomogeneous d) (hQ : Q.IsHomogeneous m)
    (hdiv : Q ∣ gradientPullback F Q)
    {ell dell : Fin 3 → K}
    (hregular : RegularAt Q ell)
    (hdell : IsTangentVector Q ell dell)
    (hnonramified : LinearIndependent K
      ![gradient Q ell, gaussDifferential Q ell dell]) :
    ∃ a : K, gradient F (gradient Q ell) = a • ell := by
  apply gradient_dual_eq_smul_of_conormal hQ hF
  · exact ⟨hregular, rfl⟩
  · exact hdell
  · exact eval_gradient_eq_zero_of_dvd hdiv hregular.1.2
  · exact gaussDifferential_isTangent_of_dvd hdiv hregular.1.2 hdell
  · exact hnonramified

section ComplexDensity

/-- A dense set of already-recovered contact points yields the global
bidual divisor identity. -/
theorem dvd_gradientPullback_of_dense_contacts
    {F Q : MvPolynomial (Fin 3) ℂ} {A : Set (Fin 3 → ℂ)}
    (hA : ZariskiDivisibility.IsDenseInHypersurface Q A)
    (hcontact : ∀ ell ∈ A,
      MvPolynomial.eval (gradient Q ell) F = 0) :
    Q ∣ gradientPullback F Q := by
  apply ZariskiDivisibility.dvd_of_vanishes_on_dense hA
  intro ell hell
  change MvPolynomial.eval ell (gradientPullback F Q) = 0
  rw [eval_gradientPullback]
  exact hcontact ell hell

end ComplexDensity

end GaussPullback

end DiskRigidity.Algebraic
