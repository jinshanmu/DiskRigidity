/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.LemniscateOval
public import DiskRigidity.Analysis.FullLevel
public import DiskRigidity.Operator.AlgebraicCircleToDisk

/-!
# From a complex rational level to its real projective equation

This file is the coordinate bridge between Proposition 6.3 and Proposition
7.1.  It translates the full rational level into the affine zero set of the
homogenized lemniscate polynomial.
-/

@[expose] public section

noncomputable section

open Polynomial Set

namespace DiskRigidity.Analysis

/-- The real coordinate homeomorphism sends `X + iY` to the vector `[X,Y]`. -/
theorem complexPointHomeomorph_apply_mk (X Y : ℝ) :
    Operator.complexPointHomeomorph (X + Y * Complex.I) = ![X, Y] := by
  funext i
  fin_cases i
  · simp
  · simp

/-- Compactness is preserved by passage to real affine coordinates. -/
theorem isCompact_complexPointHomeomorph_image
    {K : Set ℂ} (hK : IsCompact K) :
    IsCompact (Operator.complexPointHomeomorph '' K) :=
  hK.image Operator.complexPointHomeomorph.continuous

/-- Convexity is preserved by passage to real affine coordinates. -/
theorem convex_complexPointHomeomorph_image
    {K : Set ℂ} (hK : Convex ℝ K) :
    Convex ℝ (Operator.complexPointHomeomorph '' K) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  refine ⟨a • x + b • y, hK hx hy ha hb hab, ?_⟩
  funext i
  fin_cases i <;> simp

/-- Nonempty interior is preserved by passage to real affine coordinates. -/
theorem interior_complexPointHomeomorph_image_nonempty
    {K : Set ℂ} (hK : (interior K).Nonempty) :
    (interior (Operator.complexPointHomeomorph '' K)).Nonempty := by
  rw [← Operator.complexPointHomeomorph.image_interior]
  exact hK.image Operator.complexPointHomeomorph

/-- Strict convexity is preserved by passage to real affine coordinates. -/
theorem strictConvex_complexPointHomeomorph_image
    {K : Set ℂ} (hK : StrictConvex ℝ K) :
    StrictConvex ℝ (Operator.complexPointHomeomorph '' K) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy a b ha hb hab
  have hxy' : x ≠ y := by
    intro h
    subst y
    exact hxy rfl
  rw [← Operator.complexPointHomeomorph.image_interior]
  refine ⟨a • x + b • y, hK hx hy hxy' ha hb hab, ?_⟩
  funext i
  fin_cases i <;> simp

/-- Connectedness of the frontier is preserved by passage to real affine
coordinates. -/
theorem isConnected_frontier_complexPointHomeomorph_image
    {K : Set ℂ} (hK : IsConnected (frontier K)) :
    IsConnected (frontier (Operator.complexPointHomeomorph '' K)) := by
  rw [← Operator.complexPointHomeomorph.image_frontier]
  exact hK.image Operator.complexPointHomeomorph
    Operator.complexPointHomeomorph.continuous.continuousOn

/-- Coprimality upgrades equality of numerator and denominator moduli to
membership in the finite rational level. -/
theorem mem_rationalLevel_iff_norm_eval_eq
    {U V : ℂ[X]} (hUV : IsCoprime U V) (z : ℂ) :
    z ∈ rationalLevel U V ↔ ‖U.eval z‖ = ‖V.eval z‖ := by
  constructor
  · rintro ⟨hV, hquotient⟩
    rw [norm_div] at hquotient
    exact (div_eq_one_iff_eq (norm_ne_zero_iff.mpr hV)).mp hquotient
  · intro hnorm
    have hV : V.eval z ≠ 0 := by
      intro hVzero
      have hUzero : U.eval z = 0 := by
        apply norm_eq_zero.mp
        rw [hnorm, hVzero, norm_zero]
      rcases Polynomial.aeval_ne_zero_of_isCoprime hUV z with hUne | hVne
      · exact hUne hUzero
      · exact hVne hVzero
    refine ⟨hV, ?_⟩
    rw [norm_div, hnorm]
    exact div_self (norm_ne_zero_iff.mpr hV)

/-- A full rational-level identity is exactly the real affine zero-locus
hypothesis used by the algebraic tangent argument. -/
theorem projectiveLevel_zero_iff_mem_frontier_realImage
    {K : Set ℂ} {U V : ℂ[X]} (hUV : IsCoprime U V)
    (hfull : rationalLevel U V = frontier K) (x : Fin 2 → ℝ) :
    MvPolynomial.eval (Algebraic.LemniscateOval.complexAffinePoint x)
        (Algebraic.Lemniscate.primalOrderProjectiveLevelPolynomial U V) = 0 ↔
      x ∈ frontier (Operator.complexPointHomeomorph '' K) := by
  let z : ℂ := x 0 + x 1 * Complex.I
  have hzcoord : Operator.complexPointHomeomorph z = x := by
    rw [show x = ![x 0, x 1] by funext i; fin_cases i <;> rfl]
    exact complexPointHomeomorph_apply_mk (x 0) (x 1)
  have hzero :
      MvPolynomial.eval (Algebraic.LemniscateOval.complexAffinePoint x)
          (Algebraic.Lemniscate.primalOrderProjectiveLevelPolynomial U V) = 0 ↔
        ‖U.eval z‖ = ‖V.eval z‖ := by
    have hxaff : Algebraic.LemniscateOval.complexAffinePoint x =
        ![(1 : ℂ), (x 0 : ℂ), (x 1 : ℂ)] := by
      funext i
      fin_cases i <;> rfl
    rw [hxaff]
    simpa only [z] using
      Algebraic.Lemniscate.eval_primalOrderProjectiveLevelPolynomial_affine_eq_zero_iff
        U V (x 0) (x 1)
  rw [hzero, ← mem_rationalLevel_iff_norm_eval_eq hUV z, hfull,
    ← Operator.complexPointHomeomorph.image_frontier]
  constructor
  · intro hz
    exact ⟨z, hz, hzcoord⟩
  · rintro ⟨w, hw, hwcoord⟩
    have hwz : w = z := Operator.complexPointHomeomorph.injective
      (hwcoord.trans hzcoord.symm)
    simpa [hwz] using hw

end DiskRigidity.Analysis
