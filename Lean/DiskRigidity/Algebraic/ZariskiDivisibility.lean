/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Zariski density and divisibility of hypersurface equations

This file formalizes the algebraic step behind equation (7.5).  If a
polynomial vanishes on a Zariski-dense subset of an irreducible hypersurface,
then the irreducible equation divides it.  A second theorem derives the same
conclusion directly from vanishing on the whole zero locus, using Hilbert's
Nullstellensatz from Mathlib.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace ZariskiDivisibility

open MvPolynomial

variable {σ : Type*} [Finite σ]

/-- A subset has the full vanishing ideal of the hypersurface cut out by
`Q`.  This is the affine-coordinate formulation of Zariski density used for
an open arc of an irreducible curve. -/
def IsDenseInHypersurface (Q : MvPolynomial σ ℂ) (A : Set (σ → ℂ)) : Prop :=
  MvPolynomial.vanishingIdeal ℂ A = Ideal.span {Q}

omit [Finite σ] in
/-- Vanishing on a dense subset of a hypersurface implies divisibility by its
equation. -/
theorem dvd_of_vanishes_on_dense {Q P : MvPolynomial σ ℂ} {A : Set (σ → ℂ)}
    (hA : IsDenseInHypersurface Q A)
    (hP : ∀ x ∈ A, MvPolynomial.aeval x P = 0) :
    Q ∣ P := by
  rw [← Ideal.mem_span_singleton, ← hA]
  exact hP

/-- The full zero locus of a prime hypersurface has vanishing ideal generated
by its defining equation. -/
theorem zeroLocus_isDenseInHypersurface {Q : MvPolynomial σ ℂ} (hQ : Prime Q) :
    IsDenseInHypersurface Q
      (MvPolynomial.zeroLocus ℂ (Ideal.span {Q})) := by
  let _ : (Ideal.span {Q}).IsPrime := Ideal.isPrime_span_singleton_of_prime hQ
  exact MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) (Ideal.span {Q})

/-- Nullstellensatz form: a polynomial vanishing at every complex zero of a
prime hypersurface is divisible by the prime equation. -/
theorem dvd_of_vanishes_on_zeroLocus {Q P : MvPolynomial σ ℂ} (hQ : Prime Q)
    (hP : ∀ x : σ → ℂ, MvPolynomial.aeval x Q = 0 →
      MvPolynomial.aeval x P = 0) :
    Q ∣ P := by
  apply dvd_of_vanishes_on_dense (zeroLocus_isDenseInHypersurface hQ)
  intro x hx
  apply hP x
  exact hx Q (Ideal.mem_span_singleton_self Q)

end ZariskiDivisibility

end DiskRigidity.Algebraic
