/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.BoundarySpectrum
public import DiskRigidity.Operator.FoundationGeometry
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Matrix.Order

/-!
# Numerical range of a finite normal matrix

Mathlib supplies the continuous functional calculus for normal elements and
the Hermitian matrix spectral theorem, but not the classical finite-dimensional
identity `W(A) = conv (spectrum A)` for a normal matrix.  This file proves the
missing statement by strict separation and the continuous functional calculus
for the real part of a scalar multiple of `A`.
-/

@[expose] public section

noncomputable section

open Set WithLp
open scoped ComplexOrder InnerProductSpace Matrix Matrix.Norms.L2Operator MatrixOrder

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- A real continuous functional on `ℂ` is the real part of multiplication by
one complex scalar. -/
theorem exists_complex_real_part_representation
    (f : StrongDual ℝ ℂ) :
    ∃ c : ℂ, ∀ z : ℂ, (c * z).re = f z := by
  let a : ℂ := (InnerProductSpace.toDual ℝ ℂ).symm f
  refine ⟨star a, fun z ↦ ?_⟩
  have h : ⟪a, z⟫_ℝ = f z := InnerProductSpace.toDual_symm_apply
  simpa [Complex.inner, mul_comm] using h

omit [Nonempty n] in
/-- For a normal matrix, the numerical range is contained in the convex hull
of its spectrum. -/
theorem numericalRange_subset_convexHull_spectrum_of_isStarNormal
    (A : SquareMatrix n) (hA : IsStarNormal A) :
    numericalRange A ⊆ convexHull ℝ (spectrum ℂ A) := by
  let _ : IsStarNormal A := hA
  rintro z ⟨x, hx, rfl⟩
  by_contra hz
  let S : Set ℂ := convexHull ℝ (spectrum ℂ A)
  have hfinite : (spectrum ℂ A).Finite := A.finite_spectrum
  have hSclosed : IsClosed S :=
    (hfinite.isCompact_convexHull ℝ).isClosed
  obtain ⟨f, u, hfu, huz⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hSclosed hz
  obtain ⟨c, hfc⟩ := exists_complex_real_part_representation f
  let P : SquareMatrix n :=
    ((u : ℂ) • (1 : SquareMatrix n)) - rePart (c • A)
  let g : ℂ → ℂ := fun w ↦ (u : ℂ) - ((c * w).re : ℂ)
  have hcA : IsStarNormal (c • A) := inferInstance
  have hre : cfc (fun w : ℂ ↦ (w.re : ℂ)) (c • A) =
      rePart (c • A) := by
    rw [cfc_re_id (c • A) (hp := hcA)]
    have hstar : star A = Aᴴ := rfl
    rw [realPart_apply_coe,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    norm_num [rePart, hstar, smul_add, smul_smul]
  have hrecfc : cfc (fun w : ℂ ↦ ((c * w).re : ℂ)) A =
      rePart (c • A) := by
    rw [cfc_comp_const_mul c (fun w : ℂ ↦ (w.re : ℂ)) A
      (hf := by fun_prop) (ha := hA)]
    exact hre
  have hPcfc : P = cfc g A := by
    change ((u : ℂ) • (1 : SquareMatrix n)) - rePart (c • A) =
      cfc (fun w : ℂ ↦ (u : ℂ) - ((c * w).re : ℂ)) A
    rw [cfc_sub (fun _ : ℂ ↦ (u : ℂ))
      (fun w : ℂ ↦ ((c * w).re : ℂ)) A
      (hf := by fun_prop) (hg := by fun_prop),
      cfc_const (u : ℂ) A hA, hrecfc]
    simp only [Algebra.algebraMap_eq_smul_one]
  have hPherm : P.IsHermitian := by
    simp [P, rePart, Matrix.IsHermitian, add_comm]
  have hspecP : spectrum ℂ P = g '' spectrum ℂ A := by
    rw [hPcfc, cfc_map_spectrum g A (ha := hA) (hf := by fun_prop)]
  have hspecnonneg : spectrum ℂ P ⊆ {w : ℂ | 0 ≤ w} := by
    rw [hspecP]
    rintro _ ⟨lambda, hlambda, rfl⟩
    have hlambdaS : lambda ∈ S := subset_convexHull ℝ _ hlambda
    have hlt := hfu lambda hlambdaS
    change 0 ≤ (u : ℂ) - ((c * lambda).re : ℂ)
    rw [hfc]
    exact_mod_cast sub_nonneg.mpr hlt.le
  have hPpos : P.PosSemidef :=
    Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.mpr
      ⟨hPherm, hspecnonneg⟩
  let v : n → ℂ := ofLp x
  have hvunit : star v ⬝ᵥ v = 1 := by
    have hxinner : ⟪x, x⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hx]
      norm_num
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hxinner
    simpa only [v, dotProduct_comm] using hxinner
  have hquad : 0 ≤ star v ⬝ᵥ (P *ᵥ v) :=
    hPpos.dotProduct_mulVec_nonneg v
  have hformula := quadratic_supportDefect_of_unit A c u v hvunit
  rw [show P = ((u : ℂ) • (1 : SquareMatrix n)) - rePart (c • A) by rfl,
    hformula] at hquad
  have hquadReal : 0 ≤ u - (c * (star v ⬝ᵥ (A *ᵥ v))).re := by
    exact_mod_cast hquad
  have hcz : (c * (star v ⬝ᵥ (A *ᵥ v))).re =
      f ⟪x, euclideanOperator A x⟫_ℂ := by
    rw [← inner_euclideanOperator_eq_star_dotProduct A x]
    exact hfc _
  rw [hcz] at hquadReal
  linarith

omit [Nonempty n] in
/-- Classical normal-matrix formula for the numerical range. -/
theorem numericalRange_eq_convexHull_spectrum_of_isStarNormal
    (A : SquareMatrix n) (hA : IsStarNormal A) :
    numericalRange A = convexHull ℝ (spectrum ℂ A) := by
  apply Set.Subset.antisymm
  · exact numericalRange_subset_convexHull_spectrum_of_isStarNormal A hA
  · exact convexHull_min (spectrum_subset_numericalRange A)
      (numericalRange_convex A)

end DiskRigidity.Operator
