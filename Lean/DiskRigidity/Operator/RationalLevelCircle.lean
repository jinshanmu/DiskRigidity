/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.PropositionCircle
public import DiskRigidity.Analysis.AlgebraicLevelBridge
public import DiskRigidity.Operator.ConvexBoundaryTopology
public import DiskRigidity.Operator.NumericalRangePencil

/-!
# From a full rational numerical-range level to a disk

This is the coordinate-free assembly of Proposition 7.1.  The rational
level is transported to real affine coordinates, the Kippenhahn support-line
determinant supplies the required dual curve, and the resulting real circle
is transported back to the complex plane.
-/

@[expose] public section

noncomputable section

open Metric Polynomial Set
open DiskRigidity.Algebraic.PropositionCircle

namespace DiskRigidity.Operator

/-- A coprime, regular, full rational level bounding a strictly convex
numerical range is a nondegenerate closed disk. -/
theorem numericalRange_eq_closedBall_of_full_regular_rationalLevel
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : SquareMatrix n)
    (hinterior : (interior (numericalRange A)).Nonempty)
    (U V : ℂ[X]) (hU : U ≠ 0)
    (hdegree : V.natDegree < U.natDegree)
    (hcoprime : IsCoprime U V)
    (hfull : Analysis.rationalLevel U V = frontier (numericalRange A))
    (hstrict : StrictConvex ℝ (numericalRange A))
    (hregular : ∀ x ∈ frontier (complexPointHomeomorph '' numericalRange A),
      Algebraic.ProjectiveDual.RegularAt
        (Algebraic.Lemniscate.primalOrderProjectiveLevelPolynomial U V)
        (Algebraic.LemniscateOval.complexAffinePoint x)) :
    ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ numericalRange A = closedBall c r := by
  let Kreal : Set (Fin 2 → ℝ) := complexPointHomeomorph '' numericalRange A
  have hcompactReal : IsCompact Kreal :=
    Analysis.isCompact_complexPointHomeomorph_image
      (isCompact_numericalRange A)
  have hinteriorReal : (interior Kreal).Nonempty :=
    Analysis.interior_complexPointHomeomorph_image_nonempty hinterior
  have hstrictReal : StrictConvex ℝ Kreal :=
    Analysis.strictConvex_complexPointHomeomorph_image hstrict
  have hconnected : IsConnected (frontier (numericalRange A)) :=
    isConnected_frontier_of_compact_convex
      (numericalRange_convex A) (isCompact_numericalRange A) hinterior
  have hconnectedReal : IsConnected (frontier Kreal) :=
    Analysis.isConnected_frontier_complexPointHomeomorph_image hconnected
  have hfullReal : ∀ x : Fin 2 → ℝ,
      MvPolynomial.eval (Algebraic.LemniscateOval.complexAffinePoint x)
          (Algebraic.Lemniscate.primalOrderProjectiveLevelPolynomial U V) = 0 ↔
        x ∈ frontier Kreal := by
    intro x
    exact Analysis.projectiveLevel_zero_iff_mem_frontier_realImage
      hcoprime hfull x
  obtain ⟨q, hq, hcircle⟩ :=
    boundary_is_circle_of_full_regular_strictly_convex_level_and_support_determinant
        U V hU hdegree
        (numericalRangeRealPart A) (numericalRangeImaginaryPart A)
        (numericalRangeRealPart_isHermitian A)
        (numericalRangeImaginaryPart_isHermitian A)
        Kreal hcompactReal hinteriorReal hstrictReal hconnectedReal
        hfullReal hregular
        (fun hsupport ↦
          determinantPolynomial_zero_of_numericalRange_supportOffset A hsupport)
  refine ⟨q.centerX + q.centerY * Complex.I, Real.sqrt q.radiusSq,
    Real.sqrt_pos.2 hq, ?_⟩
  exact eq_closedBall_of_realAffine_circle
    (isCompact_numericalRange A) (numericalRange_convex A) q hq hcircle

/-- Proposition 7.1 in the exact form used by the manuscript.  Analytic
noncriticality of the reduced quotient supplies projective regularity
internally through the explicit Wronskian calculation. -/
theorem numericalRange_eq_closedBall_of_full_rationalLevel
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : SquareMatrix n)
    (hinterior : (interior (numericalRange A)).Nonempty)
    (U V : ℂ[X]) (hU : U ≠ 0)
    (hdegree : V.natDegree < U.natDegree)
    (hcoprime : IsCoprime U V)
    (hfull : Analysis.rationalLevel U V = frontier (numericalRange A))
    (hstrict : StrictConvex ℝ (numericalRange A))
    (hwronskian : ∀ z ∈ frontier (numericalRange A),
      (U.derivative * V - U * V.derivative).eval z ≠ 0) :
    ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ numericalRange A = closedBall c r := by
  let Kreal : Set (Fin 2 → ℝ) := complexPointHomeomorph '' numericalRange A
  have hcompactReal : IsCompact Kreal :=
    Analysis.isCompact_complexPointHomeomorph_image
      (isCompact_numericalRange A)
  have hinteriorReal : (interior Kreal).Nonempty :=
    Analysis.interior_complexPointHomeomorph_image_nonempty hinterior
  have hstrictReal : StrictConvex ℝ Kreal :=
    Analysis.strictConvex_complexPointHomeomorph_image hstrict
  have hconnected : IsConnected (frontier (numericalRange A)) :=
    isConnected_frontier_of_compact_convex
      (numericalRange_convex A) (isCompact_numericalRange A) hinterior
  have hconnectedReal : IsConnected (frontier Kreal) :=
    Analysis.isConnected_frontier_complexPointHomeomorph_image hconnected
  have hfullReal : ∀ x : Fin 2 → ℝ,
      MvPolynomial.eval (Algebraic.LemniscateOval.complexAffinePoint x)
          (Algebraic.Lemniscate.primalOrderProjectiveLevelPolynomial U V) = 0 ↔
        x ∈ frontier Kreal := by
    intro x
    exact Analysis.projectiveLevel_zero_iff_mem_frontier_realImage
      hcoprime hfull x
  have hwronskianReal : ∀ x ∈ frontier Kreal,
      (U.derivative * V - U * V.derivative).eval
        ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I) ≠ 0 := by
    intro x hx
    have hximage : x ∈ complexPointHomeomorph '' frontier (numericalRange A) := by
      rwa [complexPointHomeomorph.image_frontier]
    obtain ⟨z, hz, rfl⟩ := hximage
    have hcoord :
        ((complexPointHomeomorph z 0 : ℝ) : ℂ) +
            ((complexPointHomeomorph z 1 : ℝ) : ℂ) * Complex.I = z := by
      apply Complex.ext
      · simp
      · simp
    simpa only [hcoord] using hwronskian z hz
  obtain ⟨q, hq, hcircle⟩ :=
    boundary_is_circle_of_full_strictly_convex_level_and_support_determinant
      U V hcoprime hU hdegree
      (numericalRangeRealPart A) (numericalRangeImaginaryPart A)
      (numericalRangeRealPart_isHermitian A)
      (numericalRangeImaginaryPart_isHermitian A)
      Kreal hcompactReal hinteriorReal hstrictReal hconnectedReal
      hfullReal hwronskianReal
      (fun hsupport ↦
        determinantPolynomial_zero_of_numericalRange_supportOffset A hsupport)
  refine ⟨q.centerX + q.centerY * Complex.I, Real.sqrt q.radiusSq,
    Real.sqrt_pos.2 hq, ?_⟩
  exact eq_closedBall_of_realAffine_circle
    (isCompact_numericalRange A) (numericalRange_convex A) q hq hcircle

end DiskRigidity.Operator
