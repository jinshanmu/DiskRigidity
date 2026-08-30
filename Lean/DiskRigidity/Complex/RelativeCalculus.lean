/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.HolomorphicExtremizer

/-!
# Relative holomorphic-calculus norms

These elementary supremum lemmas turn a normalized polynomial maximizing
sequence into the lower bound for the Schur-class calculus norm on any domain
where the same polynomials are bounded.  They are the quantitative part of
equation (4.5) in the manuscript.
-/

@[expose] public section

noncomputable section

open Filter Metric Set Topology
open scoped Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Complex

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A Schur-class polynomial sequence whose matrix norms tend to two forces
the corresponding holomorphic calculus norm to equal two, provided the sharp
upper bound two is available. -/
theorem holomorphicCalculusNorm_eq_two_of_polynomial_sequence
    (A : Operator.SquareMatrix n) {U : Set ℂ}
    (hcalc : HasHolomorphicCalculusBound A U 2)
    (P : ℕ → Polynomial ℂ)
    (hP : ∀ m, IsSchurOn U (fun z ↦ (P m).eval z))
    (hlim : Tendsto (fun m ↦ ‖Operator.polynomialEval (P m) A‖)
      atTop (nhds 2)) :
    holomorphicCalculusNorm A U = 2 := by
  have hupper : holomorphicCalculusNorm A U ≤ 2 :=
    holomorphicCalculusNorm_le_of_bound A hcalc
  have hbounded : BddAbove (schurSpectralEvalNorms A U) :=
    bddAbove_schurSpectralEvalNorms_of_bound A hcalc
  have hmem : ∀ m, ‖Operator.polynomialEval (P m) A‖ ∈
      schurSpectralEvalNorms A U := by
    intro m
    exact ⟨fun z ↦ (P m).eval z, hP m,
      congrArg norm (spectralJetEval_polynomial A (P m))⟩
  have hlower : 2 ≤ holomorphicCalculusNorm A U := by
    rw [holomorphicCalculusNorm]
    exact le_of_tendsto' hlim (fun m ↦ le_csSup hbounded (hmem m))
  exact le_antisymm hupper hlower

/-- A polynomial bounded by one on a set is Schur on every open subset of
that set. -/
theorem isSchurOn_polynomial_of_norm_le_on
    {K U : Set ℂ} (hUK : U ⊆ K) (p : Polynomial ℂ)
    (hp : ∀ z ∈ K, ‖p.eval z‖ ≤ 1) :
    IsSchurOn U (fun z ↦ p.eval z) := by
  refine ⟨p.differentiable.differentiableOn, fun z hz ↦ ?_⟩
  rw [mem_closedBall_zero_iff]
  exact hp z (hUK hz)

end DiskRigidity.Complex
