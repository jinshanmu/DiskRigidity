/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.FoundationDirectSum
public import DiskRigidity.Operator.ConvexPolynomialCauchy

/-!
# Sharp constants of finite direct sums

This file removes the boundedness premises from the foundational binary
direct-sum estimate by supplying the global sharp polynomial bound.  It then
iterates that estimate over a nonempty finite family whose block dimensions
may vary with the index, completing the second assertion of Lemma 2.1(4).
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

universe u

/-- The global sharp polynomial estimate makes the normalized polynomial
values of every nonempty finite matrix bounded above. -/
theorem bddAbove_normalizedPolynomialValues_of_sharp_bound
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : SquareMatrix n) :
    BddAbove (normalizedPolynomialValues A) := by
  refine ⟨2, ?_⟩
  rintro r ⟨p, hp, rfl⟩
  exact (sharp_polynomial_bound A p).trans (by
    nlinarith [maxPolynomialModulus_nonneg A p])

/-- Unconditional binary form of the direct-sum inequality in Lemma 2.1(4). -/
theorem crouzeixConstant_matrixDirectSum_le_unconditional
    {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Nonempty m] [Nonempty n]
    (A : SquareMatrix m) (B : SquareMatrix n) :
    crouzeixConstant (matrixDirectSum A B) ≤
      max (crouzeixConstant A) (crouzeixConstant B) :=
  crouzeixConstant_matrixDirectSum_le A B
    (bddAbove_normalizedPolynomialValues_of_sharp_bound A)
    (bddAbove_normalizedPolynomialValues_of_sharp_bound B)

/-- Varying-dimension finite form of the second assertion in Lemma 2.1(4):
the Crouzeix constant of a nonempty finite direct sum is bounded by the
largest Crouzeix constant of its blocks.  All supremum boundedness is
discharged internally by the global sharp estimate. -/
theorem crouzeixConstant_matrixFiniteFamilyDirectSum_le
    (k : ℕ) {d : Fin (k + 1) → Type u}
    [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]
    [∀ i, Nonempty (d i)]
    (A : (i : Fin (k + 1)) → SquareMatrix (d i)) :
    crouzeixConstant (matrixFiniteFamilyDirectSum k A) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun i ↦ crouzeixConstant (A i)) := by
  induction k with
  | zero =>
      rw [matrixFiniteFamilyDirectSum_zero]
      exact Finset.le_sup'
        (fun i : Fin 1 ↦ crouzeixConstant (A i))
        (b := (0 : Fin 1)) (Finset.mem_univ _)
  | succ k ih =>
      rw [matrixFiniteFamilyDirectSum_succ]
      let _ : ∀ j, Fintype ((Fin.tail d) j) := fun j =>
        show Fintype (d j.succ) from inferInstance
      let _ : ∀ j, DecidableEq ((Fin.tail d) j) := fun j =>
        show DecidableEq (d j.succ) from inferInstance
      let _ : ∀ j, Nonempty ((Fin.tail d) j) := fun j =>
        show Nonempty (d j.succ) from inferInstance
      change crouzeixConstant
        (matrixDirectSum (A 0)
          (matrixFiniteFamilyDirectSum k (fun j => A j.succ))) ≤ _
      calc
        crouzeixConstant
            (matrixDirectSum (A 0)
              (matrixFiniteFamilyDirectSum k (fun j => A j.succ))) ≤
            max (crouzeixConstant (A 0))
              (crouzeixConstant
                (matrixFiniteFamilyDirectSum k (fun j => A j.succ))) :=
          crouzeixConstant_matrixDirectSum_le_unconditional _ _
        _ ≤ max (crouzeixConstant (A 0))
              (Finset.univ.sup' Finset.univ_nonempty
                (fun j : Fin (k + 1) ↦ crouzeixConstant (A j.succ))) := by
          apply max_le_max_left
          exact ih (d := fun j : Fin (k + 1) => d j.succ)
            (fun j => A j.succ)
        _ ≤ Finset.univ.sup' Finset.univ_nonempty
              (fun i ↦ crouzeixConstant (A i)) := by
          apply max_le
          · exact Finset.le_sup'
              (fun i : Fin (k + 2) ↦ crouzeixConstant (A i))
              (b := (0 : Fin (k + 2))) (Finset.mem_univ _)
          · apply Finset.sup'_le _ _
            intro j hj
            exact Finset.le_sup'
              (fun i : Fin (k + 2) ↦ crouzeixConstant (A i))
              (b := j.succ) (Finset.mem_univ _)

end DiskRigidity.Operator
