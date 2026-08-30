/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.SpectralJetAlgebra
public import DiskRigidity.Complex.HolomorphicExtremizer
public import DiskRigidity.Operator.FoundationGeometry
public import DiskRigidity.Operator.FoundationUnitary
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# Spectral radius of a strict Schur spectral-jet value

The spectral mapping theorem and the zeroth Hermite interpolation condition
show that a function strictly bounded by one on the matrix spectrum has a
spectral-jet value of spectral radius strictly below one.
-/

@[expose] public section

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator NNReal

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A strict scalar bound on the spectrum passes to the spectral radius of
the finite holomorphic functional calculus. -/
theorem spectralRadius_spectralJetEval_lt_one
    [Nonempty n] (A : SquareMatrix n) (g : ℂ → ℂ)
    (hg : ∀ z ∈ spectrum ℂ A, ‖g z‖ < 1) :
    spectralRadius ℂ
      (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g)) < 1 := by
  let p := DiskRigidity.Complex.spectralJetPolynomial A g
  rw [DiskRigidity.Complex.spectralJetEval_eq_polynomialEval,
    euclideanOperator_polynomialEval]
  apply spectrum.spectralRadius_lt_of_forall_lt
  intro w hw
  rw [spectrum.map_polynomial_aeval] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  have hzMatrix : z ∈ spectrum ℂ A := by
    rwa [AlgEquiv.spectrum_eq euclideanOperator A] at hz
  have hzRoot : Polynomial.IsRoot A.charpoly z :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mp hzMatrix
  let a : DiskRigidity.Complex.HermiteRoot A.charpoly :=
    ⟨z, Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero).mpr hzRoot)⟩
  have hzero : 0 < A.charpoly.rootMultiplicity (a : ℂ) :=
    (Polynomial.rootMultiplicity_pos (Matrix.charpoly_monic A).ne_zero).2 hzRoot
  have hp : p.eval z = g z := by
    have hjet :=
      DiskRigidity.Complex.iteratedDeriv_spectralJetPolynomial_eval
        (f := g) A a hzero
    simpa only [p, iteratedDeriv_zero] using hjet
  change ‖p.eval z‖₊ < 1
  rw [hp]
  exact_mod_cast hg z hzMatrix

/-- A nonconstant finite-Blaschke composition is strictly contractive in
the domain, so its matrix value has spectral radius below one. -/
theorem spectralRadius_spectralJetEval_lt_one_of_finiteBlaschke_comp
    [Nonempty n] (A : SquareMatrix n) {U : Set ℂ}
    (hspectrum : spectrum ℂ A ⊆ U)
    {g phi B : ℂ → ℂ}
    (hphi : Set.MapsTo phi U (Metric.ball 0 1))
    (hB : DiskRigidity.Complex.IsSchurFiniteBlaschke B)
    (hgeq : Set.EqOn g (B ∘ phi) U)
    (hnonconstant : DiskRigidity.Complex.IsNonconstantOn U g) :
    spectralRadius ℂ
      (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g)) < 1 := by
  have hBball : Set.MapsTo B (Metric.ball 0 1) (Metric.ball 0 1) := by
    rcases hB.isSchur.eqOn_unimodular_const_or_mapsTo_ball with
      ⟨c, _hc, hconst⟩ | hmaps
    · exfalso
      apply hnonconstant
      refine ⟨c, ?_⟩
      intro z hz
      exact (hgeq hz).trans (hconst (hphi hz))
    · exact hmaps
  apply spectralRadius_spectralJetEval_lt_one A g
  intro z hz
  have hzU := hspectrum hz
  rw [hgeq hzU]
  simpa only [Function.comp_apply, Metric.mem_ball, dist_zero_right] using
    hBball (hphi hzU)

end DiskRigidity.Operator
