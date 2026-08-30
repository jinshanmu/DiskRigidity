/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.NormalNumericalRange
public import DiskRigidity.Operator.BoundaryCompressionMatrix
public import Mathlib.Analysis.Convex.Strict.Extreme
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Separation.Connected

/-!
# The second boundary peel

This file formalizes the geometric core of the second peeling step in
Lemma 4.2 of the manuscript.  If the numerical range before the peel is a
nondegenerate disk, its circle consists of extreme points.  Apart from the
finite spectrum of the normal boundary block, those points must lie in the
interior spectral block.  Density, closedness, and convexity then force that
block to have the whole disk as its numerical range.
-/

@[expose] public section

noncomputable section

open Metric Set
open scoped Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

/-- Removing finitely many points from a nondegenerate complex circle leaves
a set dense in that circle, expressed in the ambient complex plane. -/
theorem sphere_subset_closure_sdiff_finite
    (c : ℂ) {r : ℝ} (hr : 0 < r) {F : Set ℂ} (hF : F.Finite) :
    sphere c r ⊆ closure (sphere c r \ F) := by
  let S : Set ℂ := sphere c r
  have hconnected : IsConnected S :=
    isConnected_sphere (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) c hr.le
  let _ : ConnectedSpace S := isConnected_iff_connectedSpace.mp hconnected
  let zplus : S := ⟨c + (r : ℂ), by
    rw [mem_sphere_iff_norm]
    simp [abs_of_pos hr]⟩
  let zminus : S := ⟨c - (r : ℂ), by
    rw [mem_sphere_iff_norm]
    simp [abs_of_pos hr]⟩
  have hz_ne : zplus ≠ zminus := by
    intro h
    have hval := congrArg Subtype.val h
    apply_fun Complex.re at hval
    simp [zplus, zminus] at hval
    linarith
  let _ : Nontrivial S := ⟨⟨zplus, zminus, hz_ne⟩⟩
  let T : Set S := (Subtype.val : S → ℂ) ⁻¹' F
  have hT : T.Finite := hF.preimage Subtype.val_injective.injOn
  have hdense : Dense (Set.univ \ T) := dense_univ.sdiff_finite hT
  have himage : (Subtype.val : S → ℂ) '' (Set.univ \ T) = S \ F := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.property, hx.2⟩
    · rintro ⟨hzS, hzF⟩
      exact ⟨⟨z, hzS⟩, ⟨mem_univ _, hzF⟩, rfl⟩
  intro z hz
  let zS : S := ⟨z, hz⟩
  have hzclosure : zS ∈ closure (Set.univ \ T) := by
    rw [hdense.closure_eq]
    exact mem_univ zS
  rw [← himage]
  exact mem_closure_image continuous_subtype_val.continuousAt hzclosure

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
/-- If a matrix has a nondegenerate disk as numerical range, then the
interior spectral block remaining after the boundary spectrum is peeled off
has exactly the same numerical range. -/
theorem numericalRange_boundaryComplementMatrix_eq_of_eq_closedBall
    (A : SquareMatrix n) (hInt : (interior (numericalRange A)).Nonempty)
    (c : ℂ) {r : ℝ} (hr : 0 < r)
    (hball : numericalRange A = closedBall c r) :
    numericalRange (boundaryComplementMatrix A hInt) = numericalRange A := by
  let C := boundarySpaceMatrix A
  let D := boundaryComplementMatrix A hInt
  have hdecomp : numericalRange A =
      convexHull ℝ (numericalRange C ∪ numericalRange D) := by
    rw [← numericalRange_boundaryDecompositionMatrix A,
      boundaryDecompositionMatrix_eq_matrixDirectSum A hInt,
      numericalRange_matrixDirectSum]
  have hCsub : numericalRange C ⊆ numericalRange A :=
    numericalRange_boundarySpaceMatrix_subset A
  have hDsub : numericalRange D ⊆ numericalRange A :=
    numericalRange_boundaryComplementMatrix_subset A hInt
  rcases isEmpty_or_nonempty (boundarySpaceIndex A) with hCempty | hCnonempty
  · let _ : IsEmpty (boundarySpaceIndex A) := hCempty
    have hCemptyRange : numericalRange C = ∅ := by
      ext z
      constructor
      · rintro ⟨x, hx, -⟩
        have hx0 : x = 0 := Subsingleton.elim x 0
        rw [hx0, norm_zero] at hx
        norm_num at hx
      · simp
    rw [hCemptyRange, empty_union,
      (numericalRange_convex D).convexHull_eq] at hdecomp
    exact hdecomp.symm
  · let _ : Nonempty (boundarySpaceIndex A) := hCnonempty
    have hnormalC : IsStarNormal C := isStarNormal_boundarySpaceMatrix A hInt
    have hWC : numericalRange C = convexHull ℝ (spectrum ℂ C) :=
      numericalRange_eq_convexHull_spectrum_of_isStarNormal C hnormalC
    have hsphereMinus : sphere c r \ spectrum ℂ C ⊆ numericalRange D := by
      rintro z ⟨hzsphere, hzspec⟩
      have hzextA : z ∈ (numericalRange A).extremePoints ℝ := by
        rw [hball]
        exact StrictConvexSpace.sphere_subset_extremePoints_closedBall
          c hr.ne' hzsphere
      have hzunion : z ∈ numericalRange C ∪ numericalRange D := by
        apply extremePoints_convexHull_subset (𝕜 := ℝ)
        rw [← hdecomp]
        exact hzextA
      rcases hzunion with hzC | hzD
      · have hzextC : z ∈ (numericalRange C).extremePoints ℝ :=
          inter_extremePoints_subset_extremePoints_of_subset hCsub
            ⟨hzC, hzextA⟩
        rw [hWC] at hzextC
        exact (hzspec
          (extremePoints_convexHull_subset (𝕜 := ℝ) hzextC)).elim
      · exact hzD
    have hsphereClosure : sphere c r ⊆
        closure (sphere c r \ spectrum ℂ C) :=
      sphere_subset_closure_sdiff_finite c hr C.finite_spectrum
    have hsphereD : sphere c r ⊆ numericalRange D :=
      hsphereClosure.trans <|
        closure_minimal hsphereMinus (isCompact_numericalRange D).isClosed
    have hballD : closedBall c r ⊆ numericalRange D := by
      rw [← convexHull_sphere_eq_closedBall c hr.le]
      exact convexHull_min hsphereD (numericalRange_convex D)
    apply Subset.antisymm hDsub
    rw [hball]
    exact hballD

end DiskRigidity.Operator
