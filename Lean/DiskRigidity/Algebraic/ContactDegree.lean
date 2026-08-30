/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib

/-!
# The generic contact count

This file isolates the finite algebraic count in the middle of Proposition
7.1.  After projective biduality supplies one contact point for each simple
root of a generic dual specialization, strict convexity says that the roots
are exactly the two support lines with the chosen unoriented normal.  A split,
squarefree polynomial with exactly those two roots has degree two.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace ContactDegree

open Polynomial

/-- A complex polynomial has only real roots, phrased without choosing a
factorization. -/
def IsRealRooted (p : ℂ[X]) : Prop :=
  ∀ {z : ℂ}, p.eval z = 0 → z.im = 0

/-- Real-rootedness passes to every polynomial divisor.  This is the exact
algebraic implication used after the dual equation divides the Hermitian
determinant. -/
theorem IsRealRooted.of_dvd {p q : ℂ[X]} (hp : IsRealRooted p) (hqp : q ∣ p) :
    IsRealRooted q := by
  rintro z hz
  obtain ⟨r, rfl⟩ := hqp
  apply hp
  simp [hz]

/-- The discrete core of the generic contact argument: if a split
specialization has no repeated roots and its roots are exactly two distinct
support offsets, then its degree is two. -/
theorem natDegree_eq_two_of_two_support_roots {p : ℝ[X]} {a b : ℝ}
    (hsplits : p.Splits) (hnodup : p.roots.Nodup) (hab : a ≠ b)
    (hroots : ∀ x : ℝ, x ∈ p.roots ↔ x = a ∨ x = b) :
    p.natDegree = 2 := by
  have hfinset : p.roots.toFinset = {a, b} := by
    ext x
    simp [hroots]
  calc
    p.natDegree = p.roots.card := hsplits.natDegree_eq_card_roots
    _ = p.roots.toFinset.card := (Multiset.toFinset_card_of_nodup hnodup).symm
    _ = 2 := by rw [hfinset]; simp [hab]

/-- Version in which the two support roots are supplied separately and every
root is known to be one of them. -/
theorem natDegree_eq_two_of_support_bound {p : ℝ[X]} {a b : ℝ}
    (hsplits : p.Splits) (hnodup : p.roots.Nodup) (hab : a ≠ b)
    (ha : a ∈ p.roots) (hb : b ∈ p.roots)
    (hatMost : ∀ x : ℝ, x ∈ p.roots → x = a ∨ x = b) :
    p.natDegree = 2 := by
  apply natDegree_eq_two_of_two_support_roots hsplits hnodup hab
  intro x
  constructor
  · exact hatMost x
  · rintro (rfl | rfl)
    · exact ha
    · exact hb

end ContactDegree

end DiskRigidity.Algebraic
