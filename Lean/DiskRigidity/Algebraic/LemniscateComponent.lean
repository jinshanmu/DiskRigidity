/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.ConnectedFactor
public import DiskRigidity.Algebraic.Lemniscate
public import DiskRigidity.Algebraic.RealComponent

/-!
# The irreducible component carrying a rational lemniscate oval

This file applies UFD factorization and connectedness to equation (7.3).  It
constructs, rather than assumes, the complex irreducible factor containing a
connected regular portion of the lemniscate.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace LemniscateComponent

open MvPolynomial Polynomial Set
open ProjectiveDual
open scoped ComplexConjugate

/-- A connected subset of the regular locus of the rational lemniscate lies
on one complex irreducible component of (7.3). -/
theorem exists_irreducible_component
    (U V : ℂ[X]) (hU : U ≠ 0)
    (hdeg : V.natDegree < U.natDegree)
    (S : Set (Fin 3 → ℂ)) (hS : IsConnected S)
    (hzero : ∀ z ∈ S,
      MvPolynomial.eval z
        (Lemniscate.primalOrderProjectiveLevelPolynomial U V) = 0)
    (hregular : ∀ z ∈ S,
      RegularAt (Lemniscate.primalOrderProjectiveLevelPolynomial U V) z) :
    ∃ F : MvPolynomial (Fin 3) ℂ,
      Irreducible F ∧
      F ∣ Lemniscate.primalOrderProjectiveLevelPolynomial U V ∧
      ∀ z ∈ S, MvPolynomial.eval z F = 0 := by
  exact ConnectedFactor.exists_irreducible_factor_zero_on_connected_regular
    hS (Lemniscate.primalOrderProjectiveLevelPolynomial_ne_zero U V hU hdeg)
    (Lemniscate.primalOrderProjectiveLevelPolynomial_not_isUnit U V hU hdeg)
    hzero hregular

theorem conjugate_homogenizedPolynomial {σ : Type*}
    (p : ℂ[X]) (w Z : MvPolynomial σ ℂ) :
    RealComponent.conjugatePolynomial
        (Lemniscate.homogenizedPolynomial p w Z) =
      Lemniscate.sharpHomogenizedPolynomial p
        (RealComponent.conjugatePolynomial w)
        (RealComponent.conjugatePolynomial Z) := by
  simp [RealComponent.conjugatePolynomial,
    Lemniscate.homogenizedPolynomial,
    Lemniscate.sharpHomogenizedPolynomial]

theorem conjugate_sharpHomogenizedPolynomial {σ : Type*}
    (p : ℂ[X]) (w Z : MvPolynomial σ ℂ) :
    RealComponent.conjugatePolynomial
        (Lemniscate.sharpHomogenizedPolynomial p w Z) =
      Lemniscate.homogenizedPolynomial p
        (RealComponent.conjugatePolynomial w)
        (RealComponent.conjugatePolynomial Z) := by
  simp [RealComponent.conjugatePolynomial,
    Lemniscate.homogenizedPolynomial,
    Lemniscate.sharpHomogenizedPolynomial]

/-- Equation (7.3) is fixed by coefficientwise conjugation. -/
theorem conjugate_projectiveLevelPolynomial (U V : ℂ[X]) :
    RealComponent.conjugatePolynomial
        (Lemniscate.projectiveLevelPolynomial U V) =
      Lemniscate.projectiveLevelPolynomial U V := by
  let X : MvPolynomial (Fin 3) ℂ := MvPolynomial.X 0
  let Y : MvPolynomial (Fin 3) ℂ := MvPolynomial.X 1
  let Z : MvPolynomial (Fin 3) ℂ := MvPolynomial.X 2
  rw [Lemniscate.projectiveLevelPolynomial]
  change RealComponent.conjugatePolynomial
      (Lemniscate.homogenizedPolynomial U (X + MvPolynomial.C Complex.I * Y) Z *
          Lemniscate.sharpHomogenizedPolynomial U
            (X - MvPolynomial.C Complex.I * Y) Z -
        Z ^ (2 * (U.natDegree - V.natDegree)) *
          Lemniscate.homogenizedPolynomial V (X + MvPolynomial.C Complex.I * Y) Z *
          Lemniscate.sharpHomogenizedPolynomial V
            (X - MvPolynomial.C Complex.I * Y) Z) = _
  simp only [RealComponent.conjugatePolynomial_sub,
    RealComponent.conjugatePolynomial_mul,
    RealComponent.conjugatePolynomial_pow,
    conjugate_homogenizedPolynomial,
    conjugate_sharpHomogenizedPolynomial]
  simp [RealComponent.conjugatePolynomial, X, Y, Z, mul_comm]
  simp only [sub_eq_add_neg]
  ring

theorem conjugate_primalOrderProjectiveLevelPolynomial
    (U V : ℂ[X]) :
    RealComponent.conjugatePolynomial
        (Lemniscate.primalOrderProjectiveLevelPolynomial U V) =
      Lemniscate.primalOrderProjectiveLevelPolynomial U V := by
  rw [Lemniscate.primalOrderProjectiveLevelPolynomial,
    RealComponent.conjugatePolynomial, MvPolynomial.map_rename,
    ← RealComponent.conjugatePolynomial,
    conjugate_projectiveLevelPolynomial]

/-- The component carrying a connected regular real arc admits a real
equation.  Both irreducibility over `ℝ` and absolute irreducibility of its
complexification are derived, as is divisibility into (7.3). -/
theorem exists_real_irreducible_component
    (U V : ℂ[X]) (hU : U ≠ 0)
    (hdeg : V.natDegree < U.natDegree)
    (S : Set (Fin 3 → ℂ)) (hS : IsConnected S)
    (hSreal : ∀ z ∈ S, ∀ i, conj (z i) = z i)
    (hzero : ∀ z ∈ S,
      MvPolynomial.eval z
        (Lemniscate.primalOrderProjectiveLevelPolynomial U V) = 0)
    (hregular : ∀ z ∈ S,
      RegularAt (Lemniscate.primalOrderProjectiveLevelPolynomial U V) z) :
    ∃ F : MvPolynomial (Fin 3) ℝ,
      Irreducible F ∧
      Irreducible (MvPolynomial.map (algebraMap ℝ ℂ) F) ∧
      MvPolynomial.map (algebraMap ℝ ℂ) F ∣
        Lemniscate.primalOrderProjectiveLevelPolynomial U V ∧
      ∀ z ∈ S,
        MvPolynomial.eval z (MvPolynomial.map (algebraMap ℝ ℂ) F) = 0 := by
  obtain ⟨G, hGirreducible, hGdiv, hGzero⟩ :=
    exists_irreducible_component U V hU hdeg S hS hzero hregular
  obtain ⟨z, hz⟩ := hS.nonempty
  have hGassociated : Associated G (RealComponent.conjugatePolynomial G) :=
    RealComponent.associated_conjugatePolynomial_of_common_regular_real_point
      (conjugate_primalOrderProjectiveLevelPolynomial U V)
      hGirreducible hGdiv z (hSreal z hz) (hGzero z hz) (hregular z hz)
  obtain ⟨F, hFirreducible, hmapIrreducible, hmapAssociated⟩ :=
    RealComponent.exists_real_irreducible_associate_of_associated_conjugate
      hGirreducible hGassociated
  have hmapDiv : MvPolynomial.map (algebraMap ℝ ℂ) F ∣
      Lemniscate.primalOrderProjectiveLevelPolynomial U V :=
    hmapAssociated.dvd.trans hGdiv
  refine ⟨F, hFirreducible, hmapIrreducible, hmapDiv, ?_⟩
  intro w hw
  obtain ⟨R, hR⟩ := hmapAssociated.symm.dvd
  rw [hR, map_mul, hGzero w hw, zero_mul]

end LemniscateComponent

end DiskRigidity.Algebraic
