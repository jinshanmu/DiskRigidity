/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Analysis.StateRepresentation
public import DiskRigidity.Operator.ExtremalState
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# From the extremal variation to a probability measure

This file joins the two halves of Lemma 6.1: the exponential variation gives
positivity of the vector state, and Hahn--Banach plus Riesz--Markov represents
that state by a probability measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace DiskRigidity.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The vector functional `S ↦ ⟪x, Sx⟫`. -/
def vectorStateOnOperators (x : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H x)

omit [CompleteSpace H] in
@[simp]
theorem vectorStateOnOperators_apply (x : H) (S : H →L[ℂ] H) :
    vectorStateOnOperators x S = ⟪x, S x⟫_ℂ :=
  rfl

/-- Pull the vector state back through a continuous linear functional
calculus on a function subspace. -/
def vectorStateOfCalculus {X : Type*} [TopologicalSpace X]
    (P : Subspace ℂ C(X, ℂ))
    (Phi : P →L[ℂ] (H →L[ℂ] H)) (x : H) : StrongDual ℂ P :=
  (vectorStateOnOperators x).comp Phi

omit [CompleteSpace H] in
@[simp]
theorem vectorStateOfCalculus_apply {X : Type*} [TopologicalSpace X]
    (P : Subspace ℂ C(X, ℂ))
    (Phi : P →L[ℂ] (H →L[ℂ] H)) (x : H) (f : P) :
    vectorStateOfCalculus P Phi x f = ⟪x, Phi f x⟫_ℂ :=
  rfl

/-- Lemma 6.1, with the sharp-bound input stated exactly as the family of
one-sided exponential variations to which it is applied in the manuscript. -/
theorem exists_probabilityMeasure_of_extremalVariation
    {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (P : Subspace ℂ C(X, ℂ))
    (Phi : P →L[ℂ] (H →L[ℂ] H))
    (honeMem : (1 : C(X, ℂ)) ∈ P)
    (hPhiOne : Phi ⟨1, honeMem⟩ = 1)
    (T : H →L[ℂ] H) (x y : H)
    (hp : DiskRigidity.Operator.DilationEqualityPair T x y)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hcomm : ∀ f : P, ∀ z, Phi f (T z) = T (Phi f z))
    (hvariation : ∀ f : P, (∀ q, 0 ≤ (f.1 q).re) →
      ∀ t : ℝ, 0 ≤ t →
        ‖T (NormedSpace.exp (t • (-(Phi f))) x)‖ ≤ 2) :
    ∃ mu : Measure X, IsProbabilityMeasure mu ∧
      ∀ f : P, ∫ q, f.1 q ∂mu = ⟪x, Phi f x⟫_ℂ := by
  let L : StrongDual ℂ P := vectorStateOfCalculus P Phi x
  have hLone : L ⟨1, honeMem⟩ = 1 := by
    change ⟪x, Phi ⟨1, honeMem⟩ x⟫_ℂ = 1
    rw [hPhiOne]
    simp [hx]
  have hpositive : ∀ f : P,
      (∀ q, 0 ≤ (f.1 q).re) → 0 ≤ (L f).re := by
    intro f hf
    change 0 ≤ Complex.re ⟪x, Phi f x⟫_ℂ
    exact DiskRigidity.Operator.extremalState_re_nonneg
      T (Phi f) x y hp hy (hcomm f) (hvariation f hf)
  obtain ⟨mu, hmu, hrepr⟩ :=
    exists_probabilityMeasure_of_subspace_state
      P L honeMem hLone hpositive
  refine ⟨mu, hmu, fun f ↦ ?_⟩
  simpa [L] using hrepr f

end DiskRigidity.Analysis
