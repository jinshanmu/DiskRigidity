/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.Dilation
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The extremal-state variation

This file formalizes the one-sided variation `f exp (-t h)` in Lemma 6.1 of
the manuscript.  The sharp norm bound makes the squared norm attain a
one-sided maximum at zero; differentiating the Banach-algebra exponential
then proves positivity of the extremal matrix coefficient.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped InnerProductSpace

namespace DiskRigidity.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The derivative of the exact variation used in Lemma 6.1:
`t ↦ T (exp (t (-S)) x)` has derivative `-T(Sx)` at zero. -/
theorem hasDerivAt_extremalVariation
    (T S : H →L[ℂ] H) (x : H) :
    HasDerivAt (fun t : ℝ ↦ T (NormedSpace.exp (t • (-S)) x))
      (-T (S x)) 0 := by
  let evx : (H →L[ℂ] H) →L[ℝ] H :=
    (ContinuousLinearMap.apply ℂ H x).restrictScalars ℝ
  let Tr : H →L[ℝ] H := T.restrictScalars ℝ
  have hExp : HasDerivAt (fun t : ℝ ↦ NormedSpace.exp (t • (-S))) (-S) 0 := by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) (-S) (0 : ℝ)
  have hEval :
      HasDerivAt (fun t : ℝ ↦ evx (NormedSpace.exp (t • (-S))))
        (evx (-S)) 0 := by
    simpa using (hasDerivAt_const (x := (0 : ℝ)) evx).clm_apply hExp
  have hT :
      HasDerivAt
        (fun t : ℝ ↦ Tr (evx (NormedSpace.exp (t • (-S)))))
        (Tr (evx (-S))) 0 := by
    simpa using (hasDerivAt_const (x := (0 : ℝ)) Tr).clm_apply hEval
  simpa [evx, Tr] using hT

/-- The one-sided maximum computation in Lemma 6.1.  The hypothesis is
exactly the sharp estimate applied to `f exp (-t h)` for `t ≥ 0`. -/
theorem re_inner_nonneg_of_extremalVariation
    (T S : H →L[ℂ] H) (x y : H)
    (hp : DilationEqualityPair T x y) (hy : ‖y‖ = 1)
    (hcomm : ∀ z, S (T z) = T (S z))
    (hbound : ∀ t : ℝ, 0 ≤ t →
      ‖T (NormedSpace.exp (t • (-S)) x)‖ ≤ 2) :
    0 ≤ Complex.re ⟪y, S y⟫_ℂ := by
  let _ : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  let g : ℝ → H := fun t ↦ T (NormedSpace.exp (t • (-S)) x)
  let Φ : ℝ → ℝ := fun t ↦ ‖g t‖ ^ 2
  have hg : HasDerivAt g (-T (S x)) 0 := by
    simpa [g] using hasDerivAt_extremalVariation T S x
  have hΦ : HasDerivAt Φ (2 * ⟪g 0, -T (S x)⟫_ℝ) 0 := by
    simpa [Φ] using hg.norm_sq
  have hΦ0 : Φ 0 = 4 := by
    norm_num [Φ, g, hp.map_x, norm_smul, hy]
  have hmax : IsLocalMaxOn Φ (Ici 0) 0 := by
    change ∀ᶠ t in nhdsWithin 0 (Ici 0), Φ t ≤ Φ 0
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hΦ0]
    have htbound := hbound t ht
    have hsquared :=
      (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mpr htbound
    norm_num at hsquared
    simpa [Φ, g] using hsquared
  have hone : (1 : ℝ) ∈ posTangentConeAt (Ici 0) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    rw [show (0 : ℝ) + 1 = 1 by norm_num,
      segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)]
    exact fun _ hz ↦ hz.1
  have hnonpos : 2 * ⟪g 0, -T (S x)⟫_ℝ ≤ 0 := by
    simpa using hmax.hasFDerivWithinAt_nonpos
      hΦ.hasFDerivAt.hasFDerivWithinAt hone
  have hgzero : g 0 = (2 : ℂ) • y := by
    simp [g, hp.map_x]
  have hTS : T (S x) = (2 : ℂ) • S y := by
    rw [← hcomm, hp.map_x, map_smul]
  rw [hgzero, hTS, real_inner_eq_re_inner] at hnonpos
  norm_num [inner_neg_right, inner_smul_left, inner_smul_right,
    Complex.mul_re] at hnonpos
  nlinarith

/-- Positivity of the extremal functional `L(S) = ⟨x,Sx⟩`.  The last
coefficient identity in (3.11) transfers the preceding `y`-coefficient to
the state vector `x`. -/
theorem extremalState_re_nonneg
    (T S : H →L[ℂ] H) (x y : H)
    (hp : DilationEqualityPair T x y) (hy : ‖y‖ = 1)
    (hcomm : ∀ z, S (T z) = T (S z))
    (hbound : ∀ t : ℝ, 0 ≤ t →
      ‖T (NormedSpace.exp (t • (-S)) x)‖ ≤ 2) :
    0 ≤ Complex.re ⟪x, S x⟫_ℂ := by
  have hypos := re_inner_nonneg_of_extremalVariation
    T S x y hp hy hcomm hbound
  have hcoeff := (dilationEquality_coefficient_identities
    T S x y hp hcomm).2.2.2
  rw [hcoeff] at hypos
  exact hypos

end DiskRigidity.Operator
