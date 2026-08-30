/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.HomogeneousFactor
public import DiskRigidity.Algebraic.LemniscateComponent

/-!
# The real projective oval selected by a rational lemniscate

This file constructs the primal equation used in Proposition 7.1 directly
from the connected smooth full level set.  It proves homogeneity, the exact
real affine locus, absence of real points at infinity, and regularity of the
selected factor; none of these facts is left in a bundled geometric
interface.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace LemniscateOval

open Matrix MvPolynomial Polynomial Set
open ProjectiveDual
open scoped ComplexConjugate

/-- The standard real affine chart in primal coordinate order `[Z:X:Y]`. -/
def affinePoint (x : Fin 2 → ℝ) : Fin 3 → ℝ := ![1, x 0, x 1]

/-- Complexification of `affinePoint`. -/
def complexAffinePoint (x : Fin 2 → ℝ) : Fin 3 → ℂ :=
  fun i ↦ (affinePoint x i : ℂ)

/-- The real equation underlying the conjugation-invariant primal
lemniscate equation. -/
noncomputable def realLevelPolynomial (U V : ℂ[X]) :
    MvPolynomial (Fin 3) ℝ :=
  RealComponent.realPartPolynomial
    (Lemniscate.primalOrderProjectiveLevelPolynomial U V)

theorem map_realLevelPolynomial (U V : ℂ[X]) :
    MvPolynomial.map (algebraMap ℝ ℂ) (realLevelPolynomial U V) =
      Lemniscate.primalOrderProjectiveLevelPolynomial U V := by
  exact RealComponent.map_realPartPolynomial_of_conjugate_eq _
    (LemniscateComponent.conjugate_primalOrderProjectiveLevelPolynomial U V)

theorem realLevelPolynomial_isHomogeneous (U V : ℂ[X])
    (hdeg : V.natDegree ≤ U.natDegree) :
    (realLevelPolynomial U V).IsHomogeneous (2 * U.natDegree) := by
  apply IsHomogeneous.of_map (f := algebraMap ℝ ℂ) Complex.ofReal_injective
  rw [map_realLevelPolynomial]
  exact Lemniscate.primalOrderProjectiveLevelPolynomial_isHomogeneous U V hdeg

theorem complexAffinePoint_ne_zero (x : Fin 2 → ℝ) :
    complexAffinePoint x ≠ 0 := by
  intro h
  have := congrFun h (0 : Fin 3)
  norm_num [complexAffinePoint, affinePoint] at this

/-- A factor vanishing at a regular zero of a product is itself regular
there. -/
theorem regularAt_factor_of_regularAt
    {K : Type*} [Field K] {N : ℕ}
    {F P : MvPolynomial (Fin N) K} {z : Fin N → K}
    (hdiv : F ∣ P) (hFzero : MvPolynomial.eval z F = 0)
    (hPregular : RegularAt P z) : RegularAt F z := by
  refine ⟨⟨hPregular.1.1, hFzero⟩, ?_⟩
  intro hFgradient
  apply hPregular.2
  obtain ⟨R, hR⟩ := hdiv
  funext i
  rw [hR]
  have hi := congrFun hFgradient i
  change MvPolynomial.eval z (MvPolynomial.pderiv i F) = 0 at hi
  simp [ProjectiveDual.gradient, hFzero, hi]

/-- At a regular zero of an ambient equation, the gradient of a vanishing
factor differs from the ambient gradient by a nonzero scalar. -/
theorem exists_ne_zero_gradient_scale_of_factor
    {K : Type*} [Field K] {N : ℕ}
    {F P : MvPolynomial (Fin N) K} {z : Fin N → K}
    (hdiv : F ∣ P) (hFzero : MvPolynomial.eval z F = 0)
    (hPregular : RegularAt P z) :
    ∃ c : K, c ≠ 0 ∧ gradient P z = c • gradient F z := by
  obtain ⟨R, hR⟩ := hdiv
  let c := MvPolynomial.eval z R
  have hgradient : gradient P z = c • gradient F z := by
    funext i
    rw [hR]
    simp [ProjectiveDual.gradient, hFzero, c]
  have hc : c ≠ 0 := by
    intro hc0
    apply hPregular.2
    rw [hgradient, hc0, zero_smul]
  exact ⟨c, hc, hgradient⟩

/-- Regularity of a real polynomial can be read off from its
complexification at a real point. -/
theorem regularAt_of_map_real
    {N : ℕ} {F : MvPolynomial (Fin N) ℝ} {z : Fin N → ℝ}
    (hregular : RegularAt (MvPolynomial.map (algebraMap ℝ ℂ) F)
      (fun i ↦ (z i : ℂ))) : RegularAt F z := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hz
    apply hregular.1.1
    funext i
    simp [hz]
  · have hzero := hregular.1.2
    rw [RealComponent.eval_map_real] at hzero
    exact Complex.ofReal_eq_zero.mp hzero
  · intro hgradient
    apply hregular.2
    rw [RealComponent.gradient_map_real]
    funext i
    simp [hgradient]

theorem regularAt_realLevelPolynomial_of_complex
    (U V : ℂ[X]) {x : Fin 2 → ℝ}
    (hregular : RegularAt
      (Lemniscate.primalOrderProjectiveLevelPolynomial U V)
      (complexAffinePoint x)) :
    RegularAt (realLevelPolynomial U V) (affinePoint x) := by
  apply regularAt_of_map_real
  rw [map_realLevelPolynomial]
  exact hregular

/-- **Primal component construction from the full smooth level.**

`hfullLevel` is the polynomial form of equation (7.1), including the
denominator nonvanishing already established in the analytic part of the
paper.  Connectedness and ambient regularity select one irreducible real
factor.  All remaining projective oval properties are derived. -/
theorem exists_primal_oval_component
    (U V : ℂ[X]) (hU : U ≠ 0)
    (hdeg : V.natDegree < U.natDegree)
    (K : Set (Fin 2 → ℝ))
    (hconnected : IsConnected (frontier K))
    (hfullLevel : ∀ x : Fin 2 → ℝ,
      MvPolynomial.eval (complexAffinePoint x)
        (Lemniscate.primalOrderProjectiveLevelPolynomial U V) = 0 ↔
          x ∈ frontier K)
    (hlevelRegular : ∀ x ∈ frontier K,
      RegularAt (Lemniscate.primalOrderProjectiveLevelPolynomial U V)
        (complexAffinePoint x)) :
    ∃ (F : MvPolynomial (Fin 3) ℝ) (d : ℕ),
      Irreducible F ∧
      Irreducible (MvPolynomial.map (algebraMap ℝ ℂ) F) ∧
      F.IsHomogeneous d ∧
      d ≠ 0 ∧
      F ∣ realLevelPolynomial U V ∧
      MvPolynomial.map (algebraMap ℝ ℂ) F ∣
        Lemniscate.primalOrderProjectiveLevelPolynomial U V ∧
      frontier K = {x | MvPolynomial.eval (affinePoint x) F = 0} ∧
      (∀ {z : Fin 3 → ℝ}, z ≠ 0 → MvPolynomial.eval z F = 0 →
        z 0 ≠ 0) ∧
      (∀ {z : Fin 3 → ℝ}, z ≠ 0 → MvPolynomial.eval z F = 0 →
        RegularAt F z) := by
  let S : Set (Fin 3 → ℂ) := complexAffinePoint '' frontier K
  have hcontinuous : Continuous complexAffinePoint := by
    unfold complexAffinePoint affinePoint
    fun_prop
  have hSconnected : IsConnected S :=
    hconnected.image complexAffinePoint hcontinuous.continuousOn
  have hSreal : ∀ z ∈ S, ∀ i, conj (z i) = z i := by
    rintro z ⟨x, _, rfl⟩ i
    exact Complex.conj_ofReal _
  have hSzero : ∀ z ∈ S,
      MvPolynomial.eval z
        (Lemniscate.primalOrderProjectiveLevelPolynomial U V) = 0 := by
    rintro z ⟨x, hx, rfl⟩
    exact (hfullLevel x).2 hx
  have hSregular : ∀ z ∈ S,
      RegularAt (Lemniscate.primalOrderProjectiveLevelPolynomial U V) z := by
    rintro z ⟨x, hx, rfl⟩
    exact hlevelRegular x hx
  obtain ⟨F, hFirreducible, hmapIrreducible, hdiv, hvanish⟩ :=
    LemniscateComponent.exists_real_irreducible_component U V hU hdeg S
      hSconnected hSreal hSzero hSregular
  have hmapFzero : MvPolynomial.map (algebraMap ℝ ℂ) F ≠ 0 :=
    hmapIrreducible.ne_zero
  obtain ⟨d, hmapHomogeneous⟩ := HomogeneousFactor.exists_isHomogeneous_of_dvd
    hmapFzero
    (Lemniscate.primalOrderProjectiveLevelPolynomial_ne_zero U V hU hdeg)
    hdiv (Lemniscate.primalOrderProjectiveLevelPolynomial_isHomogeneous
      U V hdeg.le)
  have hFhomogeneous : F.IsHomogeneous d := by
    apply IsHomogeneous.of_map (f := algebraMap ℝ ℂ) Complex.ofReal_injective
    exact hmapHomogeneous
  have hrealDiv : F ∣ realLevelPolynomial U V := by
    apply RealComponent.dvd_of_map_dvd_map_real_complex
    rw [map_realLevelPolynomial]
    exact hdiv
  have hd : d ≠ 0 := by
    intro hd0
    have htotal : F.totalDegree = 0 := by
      rw [hFhomogeneous.totalDegree hFirreducible.ne_zero, hd0]
    have hcoeff : MvPolynomial.coeff 0 F ≠ 0 := by
      intro hcoeff0
      apply hFirreducible.ne_zero
      have hconstant := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htotal
      rw [hconstant, hcoeff0, MvPolynomial.C_0]
    have hunit : IsUnit F :=
      MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mpr
        ⟨(isUnit_iff_ne_zero.mpr hcoeff), htotal⟩
    exact hFirreducible.not_isUnit hunit
  have hboundaryZero : ∀ x ∈ frontier K,
      MvPolynomial.eval (affinePoint x) F = 0 := by
    intro x hx
    have hcomplex := hvanish (complexAffinePoint x) ⟨x, hx, rfl⟩
    change MvPolynomial.eval (fun i ↦ (affinePoint x i : ℂ))
      (MvPolynomial.map (algebraMap ℝ ℂ) F) = 0 at hcomplex
    rw [RealComponent.eval_map_real] at hcomplex
    exact Complex.ofReal_eq_zero.mp hcomplex
  have hlocus : frontier K =
      {x | MvPolynomial.eval (affinePoint x) F = 0} := by
    ext x
    constructor
    · exact hboundaryZero x
    · intro hFx
      have hmapFx : MvPolynomial.eval (complexAffinePoint x)
          (MvPolynomial.map (algebraMap ℝ ℂ) F) = 0 := by
        change MvPolynomial.eval (fun i ↦ (affinePoint x i : ℂ))
          (MvPolynomial.map (algebraMap ℝ ℂ) F) = 0
        rw [RealComponent.eval_map_real, hFx]
        exact Complex.ofReal_zero
      obtain ⟨R, hR⟩ := hdiv
      apply (hfullLevel x).1
      rw [hR, map_mul, hmapFx, zero_mul]
  have hnoInfinity : ∀ {z : Fin 3 → ℝ}, z ≠ 0 →
      MvPolynomial.eval z F = 0 → z 0 ≠ 0 :=
    Lemniscate.no_real_infinity_of_component_dvd U V hU hdeg F hdiv
  have hregular : ∀ {z : Fin 3 → ℝ}, z ≠ 0 →
      MvPolynomial.eval z F = 0 → RegularAt F z := by
    intro z hz hFz
    have hz0 := hnoInfinity hz hFz
    let x : Fin 2 → ℝ := ![z 1 / z 0, z 2 / z 0]
    have hnormalize : affinePoint x = (z 0)⁻¹ • z := by
      funext i
      fin_cases i
      · simp [affinePoint, hz0]
      · simpa [affinePoint, x, div_eq_mul_inv] using
          (mul_comm (z 1) (z 0)⁻¹)
      · simpa [affinePoint, x, div_eq_mul_inv] using
          (mul_comm (z 2) (z 0)⁻¹)
    have hFnorm : MvPolynomial.eval (affinePoint x) F = 0 := by
      rw [hnormalize, eval_smul_of_isHomogeneous hFhomogeneous, hFz,
        mul_zero]
    have hx : x ∈ frontier K := by
      rw [hlocus]
      exact hFnorm
    have hlevelRegularNorm := hlevelRegular x hx
    have hmapFNorm : MvPolynomial.eval (complexAffinePoint x)
        (MvPolynomial.map (algebraMap ℝ ℂ) F) = 0 := by
      change MvPolynomial.eval (fun i ↦ (affinePoint x i : ℂ))
        (MvPolynomial.map (algebraMap ℝ ℂ) F) = 0
      rw [RealComponent.eval_map_real, hFnorm]
      exact Complex.ofReal_zero
    have hmapRegularNorm := regularAt_factor_of_regularAt hdiv hmapFNorm
      hlevelRegularNorm
    have hFregularNorm : RegularAt F (affinePoint x) :=
      regularAt_of_map_real hmapRegularNorm
    rw [hnormalize] at hFregularNorm
    exact regularAt_of_smul_of_isHomogeneous hFhomogeneous
      (inv_ne_zero hz0) hFregularNorm
  exact ⟨F, d, hFirreducible, hmapIrreducible, hFhomogeneous, hd,
    hrealDiv, hdiv,
    hlocus, hnoInfinity, hregular⟩

end LemniscateOval

end DiskRigidity.Algebraic
