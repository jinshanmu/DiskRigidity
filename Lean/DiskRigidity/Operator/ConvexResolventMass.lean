/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.ConvexBoundaryWinding
public import DiskRigidity.Operator.ConvexCauchyBoundary
public import DiskRigidity.Operator.FoundationAffine
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Mass of the convex-boundary resolvent

We deform a matrix linearly to the scalar matrix at the chosen interior
center.  Along the open deformation interval its numerical range lies
strictly inside the convex body.  Differentiation of the boundary resolvent
mass and the closed-loop Lipschitz FTC show that the mass is constant.
-/

@[expose] public section

noncomputable section

open Bornology Filter MeasureTheory Metric Set Topology
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator NNReal Pointwise

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Straight-line deformation from the scalar center to the matrix. -/
def convexMatrixHomotopy (A : SquareMatrix n) (c : ℂ) (s : ℝ) : SquareMatrix n :=
  (s : ℂ) • A + (((1 - s : ℝ) : ℂ) * c) • 1

omit [Fintype n] in
@[simp]
theorem convexMatrixHomotopy_zero (A : SquareMatrix n) (c : ℂ) :
    convexMatrixHomotopy A c 0 = c • 1 := by
  simp [convexMatrixHomotopy]

omit [Fintype n] in
@[simp]
theorem convexMatrixHomotopy_one (A : SquareMatrix n) (c : ℂ) :
    convexMatrixHomotopy A c 1 = A := by
  simp [convexMatrixHomotopy]

/-- At every nontrivial deformation time, the whole numerical range is in
the interior of the convex body. -/
theorem numericalRange_convexMatrixHomotopy_subset_interior
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K)
    (hWA : numericalRange A ⊆ K) {s : ℝ} (hs : s ∈ Set.Ioo 0 1) :
    numericalRange (convexMatrixHomotopy A c s) ⊆ interior K := by
  rw [convexMatrixHomotopy, numericalRange_affine]
  rintro z ⟨w, hw, rfl⟩
  have hwK := hWA hw
  have hcombo := hconv.combo_self_interior_mem_interior hwK hc
    hs.1.le (sub_pos.mpr hs.2) (by linarith : s + (1 - s) = 1)
  simpa [Complex.real_smul] using hcombo

/-- Hence every point of the concrete boundary is in the resolvent set of
the deformed matrix for `0 < s < 1`. -/
theorem radialBoundary_mem_resolventSet_convexMatrixHomotopy
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) {s : ℝ} (hs : s ∈ Set.Ioo 0 1) (t : ℝ) :
    radialBoundaryParametrization K c t ∈
      resolventSet ℂ (convexMatrixHomotopy A c s) := by
  apply radialBoundaryParametrization_mem_resolventSet
    (convexMatrixHomotopy A c s) hconv hc hcompact
  exact (spectrum_subset_numericalRange _).trans <|
    numericalRange_convexMatrixHomotopy_subset_interior A hconv hc hWA hs

/-- The boundary remains in the resolvent set at the scalar endpoint
`s = 0` as well as throughout the open homotopy. -/
theorem radialBoundary_mem_resolventSet_convexMatrixHomotopy_Ico
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) {s : ℝ} (hs : s ∈ Set.Ico 0 1) (t : ℝ) :
    radialBoundaryParametrization K c t ∈
      resolventSet ℂ (convexMatrixHomotopy A c s) := by
  rcases hs.1.eq_or_lt with rfl | hspos
  · rw [convexMatrixHomotopy_zero]
    apply radialBoundaryParametrization_mem_resolventSet
      (c • (1 : SquareMatrix n)) hconv hc hcompact
    intro z hz
    have hspectrum : spectrum ℂ (c • (1 : SquareMatrix n)) = {c} := by
      simpa only [Algebra.algebraMap_eq_smul_one] using
        (CFC.spectrum_algebraMap_eq (A := SquareMatrix n) c)
    rw [hspectrum] at hz
    simpa only [Set.mem_singleton_iff] using hz.symm ▸ hc
  · exact radialBoundary_mem_resolventSet_convexMatrixHomotopy
      A hconv hc hcompact hWA ⟨hspos, hs.2⟩ t

/-- If the original spectrum is strictly inside the convex body, the
boundary stays in the resolvent set on the closed homotopy interval. -/
theorem radialBoundary_mem_resolventSet_convexMatrixHomotopy_Icc
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K)
    {s : ℝ} (hs : s ∈ Set.Icc 0 1) (t : ℝ) :
    radialBoundaryParametrization K c t ∈
      resolventSet ℂ (convexMatrixHomotopy A c s) := by
  rcases hs.2.eq_or_lt with rfl | hslt
  · rw [convexMatrixHomotopy_one]
    exact radialBoundaryParametrization_mem_resolventSet
      A hconv hc hcompact hspectrum t
  · exact radialBoundary_mem_resolventSet_convexMatrixHomotopy_Ico
      A hconv hc hcompact hWA ⟨hs.1, hslt⟩ t

/-- Matrix-valued boundary resolvent along the straight-line deformation. -/
def homotopyBoundaryResolvent
    (A : SquareMatrix n) (K : Set ℂ) (c : ℂ) (s t : ℝ) : SquareMatrix n :=
  resolvent (convexMatrixHomotopy A c s)
    (radialBoundaryParametrization K c t)

/-- The deformation velocity. -/
def convexMatrixHomotopyVelocity (A : SquareMatrix n) (c : ℂ) : SquareMatrix n :=
  A - c • 1

omit [Fintype n] in
/-- The homotopy is affine with the stated real derivative. -/
theorem hasDerivAt_convexMatrixHomotopy [Finite n]
    (A : SquareMatrix n) (c : ℂ) (s : ℝ) :
    HasDerivAt (convexMatrixHomotopy A c)
      (convexMatrixHomotopyVelocity A c) s := by
  let _ := Fintype.ofFinite n
  let B := convexMatrixHomotopyVelocity A c
  have heq : convexMatrixHomotopy A c = fun x : ℝ ↦ x • B + c • 1 := by
    funext x
    dsimp [B, convexMatrixHomotopyVelocity, convexMatrixHomotopy]
    simp only [smul_sub]
    module
  rw [heq]
  simpa [B] using ((hasDerivAt_id (x := s)).smul_const B).const_add (c • 1)

/-- Operator form of the straight-line deformation. -/
def convexOperatorHomotopy (A : SquareMatrix n) (c : ℂ) (s : ℝ) :
    EuclideanEndomorphism n :=
  (s : ℂ) • euclideanOperator A +
    (((1 - s : ℝ) : ℂ) * c) • 1

/-- Operator deformation velocity. -/
def convexOperatorHomotopyVelocity (A : SquareMatrix n) (c : ℂ) :
    EuclideanEndomorphism n :=
  euclideanOperator A - c • 1

/-- The operator deformation is affine with constant derivative. -/
theorem hasDerivAt_convexOperatorHomotopy
    (A : SquareMatrix n) (c : ℂ) (s : ℝ) :
    HasDerivAt (convexOperatorHomotopy A c)
      (convexOperatorHomotopyVelocity A c) s := by
  let B := convexOperatorHomotopyVelocity A c
  have heq : convexOperatorHomotopy A c = fun x : ℝ ↦ x • B + c • 1 := by
    funext x
    dsimp [B, convexOperatorHomotopyVelocity, convexOperatorHomotopy]
    simp only [smul_sub]
    module
  rw [heq]
  simpa [B] using ((hasDerivAt_id (x := s)).smul_const B).const_add (c • 1)

/-- The operator homotopy is exactly the Euclidean image of the matrix
homotopy. -/
theorem convexOperatorHomotopy_eq_euclideanOperator
    (A : SquareMatrix n) (c : ℂ) (s : ℝ) :
    convexOperatorHomotopy A c s =
      euclideanOperator (convexMatrixHomotopy A c s) := by
  simp only [convexOperatorHomotopy, convexMatrixHomotopy, map_add, map_smul,
    map_one]

theorem convexOperatorHomotopy_zero (A : SquareMatrix n) (c : ℂ) :
    convexOperatorHomotopy A c 0 = c • 1 := by
  unfold convexOperatorHomotopy
  module

/-- Operator-valued boundary resolvent along the deformation. -/
def homotopyBoundaryOperatorResolvent
    (A : SquareMatrix n) (K : Set ℂ) (c : ℂ) (s t : ℝ) :
    EuclideanEndomorphism n :=
  resolvent (convexOperatorHomotopy A c s)
    (radialBoundaryParametrization K c t)

/-- At the scalar endpoint, the boundary resolvent is the scalar reciprocal
of the radial displacement. -/
theorem homotopyBoundaryOperatorResolvent_zero
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) (t : ℝ) :
    homotopyBoundaryOperatorResolvent A K c 0 t =
      (radialBoundaryParametrization K c t - c)⁻¹ •
        (1 : EuclideanEndomorphism n) := by
  let σ := radialBoundaryParametrization K c t
  let d := σ - c
  have hRmatrix := radialBoundary_mem_resolventSet_convexMatrixHomotopy_Ico
    A hconv hc hcompact hWA (by norm_num : (0 : ℝ) ∈ Set.Ico 0 1) t
  have hR := AlgHom.mem_resolventSet_apply
    (euclideanOperator (n := n)) hRmatrix
  rw [← convexOperatorHomotopy_eq_euclideanOperator] at hR
  have hd : d ≠ 0 := by
    intro hd0
    have : radialBoundaryRadius K c t = 0 := by
      simp only [radialBoundaryRadius, d] at hd0 ⊢
      exact norm_eq_zero.mpr hd0
    exact (radialBoundaryRadius_pos hconv hc hcompact t).ne' this
  have hleft :
      (σ • (1 : EuclideanEndomorphism n) - c • 1) *
          (d⁻¹ • (1 : EuclideanEndomorphism n)) = 1 := by
    have hsub : σ • (1 : EuclideanEndomorphism n) - c • 1 =
        d • (1 : EuclideanEndomorphism n) := by
      dsimp only [d]
      module
    rw [hsub]
    simp [hd]
  have hright0 :
      resolvent (convexOperatorHomotopy A c 0)
          (radialBoundaryParametrization K c t) *
        (radialBoundaryParametrization K c t •
            (1 : EuclideanEndomorphism n) -
          convexOperatorHomotopy A c 0) = 1 := by
    rw [spectrum.resolvent_eq hR]
    simpa only [Algebra.algebraMap_eq_smul_one, hR.unit_spec] using
      hR.unit.inv_mul
  have hright :
      resolvent (convexOperatorHomotopy A c 0) σ *
          (σ • (1 : EuclideanEndomorphism n) - c • 1) = 1 := by
    rw [← convexOperatorHomotopy_zero A c]
    simpa only [σ] using hright0
  change resolvent (convexOperatorHomotopy A c 0) σ = d⁻¹ • 1
  exact left_inv_eq_right_inv hright hleft

/-- The boundary resolvent inherits the period of the radial boundary. -/
theorem homotopyBoundaryOperatorResolvent_periodic
    (A : SquareMatrix n) (K : Set ℂ) (c : ℂ) (s : ℝ) :
    Function.Periodic
      (homotopyBoundaryOperatorResolvent A K c s) (2 * Real.pi) := by
  intro t
  simp only [homotopyBoundaryOperatorResolvent]
  rw [radialBoundaryParametrization_periodic]

/-- For an interior homotopy time, the boundary resolvent is continuous in
the boundary parameter. -/
theorem continuous_homotopyBoundaryOperatorResolvent
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) {s : ℝ} (hs : s ∈ Set.Ioo 0 1) :
    Continuous (homotopyBoundaryOperatorResolvent A K c s) := by
  obtain ⟨C, hsigma⟩ :=
    exists_lipschitzWith_radialBoundaryParametrization hconv hc hcompact
  apply continuous_iff_continuousAt.mpr
  intro t
  have hRmatrix := radialBoundary_mem_resolventSet_convexMatrixHomotopy
    A hconv hc hcompact hWA hs t
  have hR := AlgHom.mem_resolventSet_apply (euclideanOperator (n := n)) hRmatrix
  rw [← convexOperatorHomotopy_eq_euclideanOperator] at hR
  exact (spectrum.hasDerivAt_resolvent_const_left hR).continuousAt.comp
    hsigma.continuous.continuousAt

/-- The operator norm of the boundary resolvent has a uniform bound over
the whole periodic parametrization. -/
theorem exists_uniform_norm_bound_homotopyBoundaryOperatorResolvent
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) {s : ℝ} (hs : s ∈ Set.Ioo 0 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t,
      ‖homotopyBoundaryOperatorResolvent A K c s t‖ ≤ M := by
  have hbounded :=
    (homotopyBoundaryOperatorResolvent_periodic A K c s).isBounded_of_continuous
      (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      (continuous_homotopyBoundaryOperatorResolvent
        A hconv hc hcompact hWA hs)
  obtain ⟨M, hM⟩ := hbounded.exists_norm_le
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro t
  exact (hM _ ⟨t, rfl⟩).trans (le_max_left _ _)

/-- The first resolvent identity, in the scalar argument, for continuous
endomorphisms.  The identity is purely algebraic, so it is stated for an
arbitrary complex algebra. -/
theorem resolvent_sub_resolvent_scalar
    {𝔸 : Type*} [Ring 𝔸] [Algebra ℂ 𝔸]
    (T : 𝔸) {r s : ℂ}
    (hr : r ∈ resolventSet ℂ T) (hs : s ∈ resolventSet ℂ T) :
    resolvent T r - resolvent T s =
      (s - r) • (resolvent T r * resolvent T s) := by
  have hrmul : resolvent T r * (r • (1 : 𝔸) - T) = 1 := by
    rw [spectrum.resolvent_eq hr]
    simpa only [Algebra.algebraMap_eq_smul_one] using hr.val_inv_mul
  have hsmul : (s • (1 : 𝔸) - T) * resolvent T s = 1 := by
    rw [spectrum.resolvent_eq hs]
    simpa only [Algebra.algebraMap_eq_smul_one] using hs.mul_val_inv
  calc
    resolvent T r - resolvent T s =
        resolvent T r * 1 - 1 * resolvent T s := by simp
    _ = resolvent T r *
          ((s • (1 : 𝔸) - T) * resolvent T s) -
        (resolvent T r * (r • (1 : 𝔸) - T)) *
          resolvent T s := by rw [hsmul, hrmul]
    _ = (resolvent T r * (s • (1 : 𝔸) - T)) *
          resolvent T s -
        (resolvent T r * (r • (1 : 𝔸) - T)) *
          resolvent T s := by
      simp only [mul_assoc]
    _ = ((resolvent T r * (s • (1 : 𝔸) - T)) -
        (resolvent T r * (r • (1 : 𝔸) - T))) *
          resolvent T s := by rw [sub_mul]
    _ = (resolvent T r *
        ((s • (1 : 𝔸) - T) -
          (r • (1 : 𝔸) - T))) * resolvent T s := by
      congr 1
      exact (mul_sub _ _ _).symm
    _ = (s - r) • (resolvent T r * resolvent T s) := by
      have hmiddle :
          (s • (1 : 𝔸) - T) - (r • (1 : 𝔸) - T) =
            (s - r) • (1 : 𝔸) := by
        module
      rw [hmiddle]
      simp only [mul_smul_comm, mul_one, smul_mul_assoc]

/-- At every interior homotopy time the boundary resolvent is globally
Lipschitz in the periodic boundary parameter. -/
theorem exists_lipschitzWith_homotopyBoundaryOperatorResolvent
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) {s : ℝ} (hs : s ∈ Set.Ioo 0 1) :
    ∃ C : ℝ≥0, LipschitzWith C
      (homotopyBoundaryOperatorResolvent A K c s) := by
  obtain ⟨Cσ, hσ⟩ :=
    exists_lipschitzWith_radialBoundaryParametrization hconv hc hcompact
  obtain ⟨M, hM0, hM⟩ :=
    exists_uniform_norm_bound_homotopyBoundaryOperatorResolvent
      A hconv hc hcompact hWA hs
  let C : ℝ≥0 := ⟨M ^ 2 * Cσ, mul_nonneg (sq_nonneg M) Cσ.coe_nonneg⟩
  refine ⟨C, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  have hRxMatrix := radialBoundary_mem_resolventSet_convexMatrixHomotopy
    A hconv hc hcompact hWA hs x
  have hRyMatrix := radialBoundary_mem_resolventSet_convexMatrixHomotopy
    A hconv hc hcompact hWA hs y
  have hRx := AlgHom.mem_resolventSet_apply
    (euclideanOperator (n := n)) hRxMatrix
  have hRy := AlgHom.mem_resolventSet_apply
    (euclideanOperator (n := n)) hRyMatrix
  rw [← convexOperatorHomotopy_eq_euclideanOperator] at hRx hRy
  rw [dist_eq_norm]
  change ‖resolvent (convexOperatorHomotopy A c s)
      (radialBoundaryParametrization K c x) -
    resolvent (convexOperatorHomotopy A c s)
      (radialBoundaryParametrization K c y)‖ ≤ (C : ℝ) * dist x y
  rw [resolvent_sub_resolvent_scalar
    (convexOperatorHomotopy A c s) hRx hRy]
  rw [norm_smul]
  change
    ‖radialBoundaryParametrization K c y -
        radialBoundaryParametrization K c x‖ *
      ‖resolvent (convexOperatorHomotopy A c s)
          (radialBoundaryParametrization K c x) *
        resolvent (convexOperatorHomotopy A c s)
          (radialBoundaryParametrization K c y)‖ ≤
      M ^ 2 * (Cσ : ℝ) * dist x y
  calc
    ‖radialBoundaryParametrization K c y -
          radialBoundaryParametrization K c x‖ *
        ‖resolvent (convexOperatorHomotopy A c s)
            (radialBoundaryParametrization K c x) *
          resolvent (convexOperatorHomotopy A c s)
            (radialBoundaryParametrization K c y)‖ ≤
      ‖radialBoundaryParametrization K c y -
          radialBoundaryParametrization K c x‖ * (M * M) := by
        gcongr
        exact (norm_mul_le _ _).trans <| mul_le_mul
          (hM x) (hM y) (norm_nonneg _) hM0
    _ ≤ ((Cσ : ℝ) * dist y x) * (M * M) := by
      gcongr
      simpa only [dist_eq_norm] using hσ.dist_le_mul y x
    _ = M ^ 2 * (Cσ : ℝ) * dist x y := by
      rw [dist_comm x y]
      ring

/-- The closed-loop primitive whose boundary derivative controls the
homotopy derivative of the resolvent mass. -/
def homotopyResolventPrimitive
    (A : SquareMatrix n) (K : Set ℂ) (c : ℂ) (s t : ℝ) :
    EuclideanEndomorphism n :=
  (radialBoundaryParametrization K c t - c) •
    homotopyBoundaryOperatorResolvent A K c s t

/-- The resolvent primitive closes after one turn. -/
theorem homotopyResolventPrimitive_periodic
    (A : SquareMatrix n) (K : Set ℂ) (c : ℂ) (s : ℝ) :
    Function.Periodic (homotopyResolventPrimitive A K c s)
      (2 * Real.pi) := by
  intro t
  simp only [homotopyResolventPrimitive]
  rw [radialBoundaryParametrization_periodic,
    homotopyBoundaryOperatorResolvent_periodic]

/-- The resolvent primitive is globally Lipschitz. -/
theorem exists_lipschitzWith_homotopyResolventPrimitive
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) {s : ℝ} (hs : s ∈ Set.Ioo 0 1) :
    ∃ C : ℝ≥0, LipschitzWith C (homotopyResolventPrimitive A K c s) := by
  obtain ⟨Cσ, hσ⟩ :=
    exists_lipschitzWith_radialBoundaryParametrization hconv hc hcompact
  obtain ⟨CR, hRlip⟩ :=
    exists_lipschitzWith_homotopyBoundaryOperatorResolvent
      A hconv hc hcompact hWA hs
  obtain ⟨M, hM0, hM⟩ :=
    exists_uniform_norm_bound_homotopyBoundaryOperatorResolvent
      A hconv hc hcompact hWA hs
  obtain ⟨r, R, hr, hrR, hradius⟩ :=
    exists_uniform_bounds_radialBoundaryRadius hconv hc hcompact
  have hR0 : 0 ≤ R := hr.le.trans hrR
  let C : ℝ≥0 :=
    ⟨R * CR + Cσ * M,
      add_nonneg (mul_nonneg hR0 CR.coe_nonneg)
        (mul_nonneg Cσ.coe_nonneg hM0)⟩
  refine ⟨C, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  rw [dist_eq_norm]
  have hdecomp :
      homotopyResolventPrimitive A K c s x -
          homotopyResolventPrimitive A K c s y =
        (radialBoundaryParametrization K c x - c) •
            (homotopyBoundaryOperatorResolvent A K c s x -
              homotopyBoundaryOperatorResolvent A K c s y) +
          ((radialBoundaryParametrization K c x - c) -
            (radialBoundaryParametrization K c y - c)) •
              homotopyBoundaryOperatorResolvent A K c s y := by
    simp only [homotopyResolventPrimitive]
    module
  rw [hdecomp]
  calc
    ‖(radialBoundaryParametrization K c x - c) •
            (homotopyBoundaryOperatorResolvent A K c s x -
              homotopyBoundaryOperatorResolvent A K c s y) +
          ((radialBoundaryParametrization K c x - c) -
            (radialBoundaryParametrization K c y - c)) •
              homotopyBoundaryOperatorResolvent A K c s y‖ ≤
        ‖radialBoundaryParametrization K c x - c‖ *
            ‖homotopyBoundaryOperatorResolvent A K c s x -
              homotopyBoundaryOperatorResolvent A K c s y‖ +
          ‖(radialBoundaryParametrization K c x - c) -
            (radialBoundaryParametrization K c y - c)‖ *
              ‖homotopyBoundaryOperatorResolvent A K c s y‖ := by
      simpa only [norm_smul] using norm_add_le
        ((radialBoundaryParametrization K c x - c) •
          (homotopyBoundaryOperatorResolvent A K c s x -
            homotopyBoundaryOperatorResolvent A K c s y))
        (((radialBoundaryParametrization K c x - c) -
          (radialBoundaryParametrization K c y - c)) •
            homotopyBoundaryOperatorResolvent A K c s y)
    _ ≤ R * ((CR : ℝ) * dist x y) +
          ((Cσ : ℝ) * dist x y) * M := by
      gcongr
      · exact hradius x |>.2
      · simpa only [dist_eq_norm] using hRlip.dist_le_mul x y
      · simpa only [sub_sub_sub_cancel_right, dist_eq_norm] using
          hσ.dist_le_mul x y
      · exact hM y
    _ = (C : ℝ) * dist x y := by
      change _ = (R * (CR : ℝ) + (Cσ : ℝ) * M) * dist x y
      ring

/-- Algebraic identity behind the vanishing homotopy derivative: the
resolvent-square expression is a scalar-boundary derivative. -/
theorem homotopy_resolvent_primitive_algebra
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) {s : ℝ} (hs : s ∈ Set.Ioo 0 1)
    (t : ℝ) :
    homotopyBoundaryOperatorResolvent A K c s t -
        (radialBoundaryParametrization K c t - c) •
          homotopyBoundaryOperatorResolvent A K c s t ^ 2 =
      (-(s : ℂ)) •
        (homotopyBoundaryOperatorResolvent A K c s t *
          convexOperatorHomotopyVelocity A c *
            homotopyBoundaryOperatorResolvent A K c s t) := by
  let σ := radialBoundaryParametrization K c t
  let R := homotopyBoundaryOperatorResolvent A K c s t
  let B := convexOperatorHomotopyVelocity A c
  have hRmatrix := radialBoundary_mem_resolventSet_convexMatrixHomotopy
    A hconv hc hcompact hWA hs t
  have hRmem := AlgHom.mem_resolventSet_apply
    (euclideanOperator (n := n)) hRmatrix
  rw [← convexOperatorHomotopy_eq_euclideanOperator] at hRmem
  have hleft :
      (σ • (1 : EuclideanEndomorphism n) -
          convexOperatorHomotopy A c s) * R = 1 := by
    dsimp only [R, homotopyBoundaryOperatorResolvent, σ]
    rw [spectrum.resolvent_eq hRmem]
    simpa only [Algebra.algebraMap_eq_smul_one, hRmem.unit_spec] using
      hRmem.unit.mul_inv
  have hhomotopy :
      convexOperatorHomotopy A c s =
        c • (1 : EuclideanEndomorphism n) + (s : ℂ) • B := by
    dsimp only [B, convexOperatorHomotopyVelocity, convexOperatorHomotopy]
    module
  have hfactor :
      ((σ - c) • (1 : EuclideanEndomorphism n) - (s : ℂ) • B) * R = 1 := by
    have hbase :
        ((σ - c) • (1 : EuclideanEndomorphism n) - (s : ℂ) • B) =
          σ • 1 - (c • 1 + (s : ℂ) • B) := by
      module
    rw [hbase, ← hhomotopy]
    exact hleft
  have hlinear :
      1 - (σ - c) • R = (-(s : ℂ)) • (B * R) := by
    have hexpand : (σ - c) • R - (s : ℂ) • (B * R) = 1 := by
      rw [← hfactor]
      simp only [sub_mul, smul_mul_assoc, one_mul]
    rw [← hexpand]
    module
  change R - (σ - c) • R ^ 2 = (-(s : ℂ)) • (R * B * R)
  calc
    R - (σ - c) • R ^ 2 = R * (1 - (σ - c) • R) := by
      simp only [mul_sub, mul_one, mul_smul_comm, pow_two]
    _ = R * ((-(s : ℂ)) • (B * R)) := by rw [hlinear]
    _ = (-(s : ℂ)) • (R * B * R) := by
      simp only [mul_smul_comm, mul_assoc]

/-- Every real continuous linear functional sees the exact derivative of
the resolvent primitive.  Stating this scalarwise avoids the harmless
algebraic/normed instance diamond for continuous endomorphisms. -/
theorem hasDerivAt_dual_homotopyResolventPrimitive
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) {s : ℝ} (hs : s ∈ Set.Ioo 0 1)
    (L : EuclideanEndomorphism n →L[ℝ] ℝ) {t : ℝ}
    (ht : DifferentiableAt ℝ (radialBoundaryParametrization K c) t) :
    HasDerivAt (fun u ↦ L (homotopyResolventPrimitive A K c s u))
      (L ((deriv (radialBoundaryParametrization K c) t : ℂ) •
        ((-(s : ℂ)) •
          (homotopyBoundaryOperatorResolvent A K c s t *
            convexOperatorHomotopyVelocity A c *
              homotopyBoundaryOperatorResolvent A K c s t)))) t := by
  let σ := radialBoundaryParametrization K c t
  let σ' := deriv (radialBoundaryParametrization K c) t
  let R := homotopyBoundaryOperatorResolvent A K c s t
  let B := convexOperatorHomotopyVelocity A c
  have hRmatrix := radialBoundary_mem_resolventSet_convexMatrixHomotopy
    A hconv hc hcompact hWA hs t
  have hRmem := AlgHom.mem_resolventSet_apply
    (euclideanOperator (n := n)) hRmatrix
  rw [← convexOperatorHomotopy_eq_euclideanOperator] at hRmem
  have hres :=
    (spectrum.hasDerivAt_resolvent_const_left hRmem).scomp t ht.hasDerivAt
  have hscalar := ht.hasDerivAt.sub_const c
  have hprimitive := hscalar.smul hres
  have halgebra := homotopy_resolvent_primitive_algebra
    A hconv hc hcompact hWA hs t
  have hderivative :
      ((σ - c) • ((σ' : ℂ) • (-R ^ 2)) + (σ' : ℂ) • R) =
        (σ' : ℂ) • ((-(s : ℂ)) • (R * B * R)) := by
    change _ = (σ' : ℂ) •
      ((-(s : ℂ)) •
        (homotopyBoundaryOperatorResolvent A K c s t *
          convexOperatorHomotopyVelocity A c *
            homotopyBoundaryOperatorResolvent A K c s t))
    rw [← halgebra]
    dsimp only [σ, R]
    module
  change HasDerivAt (homotopyResolventPrimitive A K c s)
    ((σ - c) • ((σ' : ℂ) • (-R ^ 2)) + (σ' : ℂ) • R) t at hprimitive
  rw [hderivative] at hprimitive
  have hcomp := (hasDerivAt_const (x := t) L).clm_apply hprimitive
  rw [hasDerivAt_iff_tendsto_slope] at hcomp ⊢
  simpa only [slope, Function.comp_apply, zero_apply, zero_add, σ', R, B] using hcomp

/-- The boundary integrand occurring in the derivative of the resolvent
mass is Bochner integrable. -/
theorem integrable_homotopyResolventMassDerivative
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) {s : ℝ} (hs : s ∈ Set.Ioo 0 1) :
    Integrable
      (fun t ↦ radialOutwardUnitNormal K c t •
        (homotopyBoundaryOperatorResolvent A K c s t *
          convexOperatorHomotopyVelocity A c *
            homotopyBoundaryOperatorResolvent A K c s t))
      (radialBoundaryArcLengthMeasure K c) := by
  let _ : IsFiniteMeasure (radialBoundaryArcLengthMeasure K c) :=
    isFiniteMeasure_radialBoundaryArcLengthMeasure hconv hc hcompact
  obtain ⟨M, hM0, hM⟩ :=
    exists_uniform_norm_bound_homotopyBoundaryOperatorResolvent
      A hconv hc hcompact hWA hs
  have hRcont := continuous_homotopyBoundaryOperatorResolvent
    A hconv hc hcompact hWA hs
  have hmeas : Measurable
      (fun t ↦ radialOutwardUnitNormal K c t •
        (homotopyBoundaryOperatorResolvent A K c s t *
          convexOperatorHomotopyVelocity A c *
            homotopyBoundaryOperatorResolvent A K c s t)) := by
    exact (measurable_radialOutwardUnitNormal K c).smul
      ((hRcont.mul continuous_const).mul hRcont).measurable
  apply Integrable.of_bound hmeas.aestronglyMeasurable
    (M * ‖convexOperatorHomotopyVelocity A c‖ * M)
  filter_upwards with t
  rw [norm_smul]
  calc
    ‖radialOutwardUnitNormal K c t‖ *
        ‖homotopyBoundaryOperatorResolvent A K c s t *
          convexOperatorHomotopyVelocity A c *
            homotopyBoundaryOperatorResolvent A K c s t‖ ≤
      1 * (M * ‖convexOperatorHomotopyVelocity A c‖ * M) := by
        gcongr
        · exact norm_radialOutwardUnitNormal_le_one K c t
        · exact ((norm_mul_le _ _).trans <| mul_le_mul
              ((norm_mul_le _ _).trans <| mul_le_mul
                (hM t) le_rfl (norm_nonneg _) hM0)
              (hM t) (norm_nonneg _) (mul_nonneg hM0 (norm_nonneg _)))
    _ = M * ‖convexOperatorHomotopyVelocity A c‖ * M := one_mul _

/-- The boundary integral of the homotopy derivative vanishes.  This is
the concrete nonsmooth contour argument replacing any assumed Cauchy
formula. -/
theorem integral_homotopyResolventMassDerivative_eq_zero
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) {s : ℝ} (hs : s ∈ Set.Ioo 0 1) :
    ∫ t, radialOutwardUnitNormal K c t •
        (homotopyBoundaryOperatorResolvent A K c s t *
          convexOperatorHomotopyVelocity A c *
            homotopyBoundaryOperatorResolvent A K c s t)
      ∂radialBoundaryArcLengthMeasure K c = 0 := by
  let μ := radialBoundaryArcLengthMeasure K c
  let F : ℝ → EuclideanEndomorphism n := fun t ↦
    radialOutwardUnitNormal K c t •
      (homotopyBoundaryOperatorResolvent A K c s t *
        convexOperatorHomotopyVelocity A c *
          homotopyBoundaryOperatorResolvent A K c s t)
  let α : ℂ := Complex.I * (-(s : ℂ))
  have hFint : Integrable F μ :=
    integrable_homotopyResolventMassDerivative
      A hconv hc hcompact hWA hs
  have hα : α ≠ 0 := by
    dsimp only [α]
    exact mul_ne_zero Complex.I_ne_zero <| neg_ne_zero.mpr <| by
      exact_mod_cast hs.1.ne'
  have hαzero : α • (∫ t, F t ∂μ) = 0 := by
    apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
    intro L
    let S : EuclideanEndomorphism n →L[ℝ] EuclideanEndomorphism n :=
      (α • ContinuousLinearMap.id ℂ (EuclideanEndomorphism n)).restrictScalars ℝ
    let Lα : EuclideanEndomorphism n →L[ℝ] ℝ := L.comp S
    calc
      L (α • (∫ t, F t ∂μ)) = Lα (∫ t, F t ∂μ) := by
        simp only [Lα, S, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.coe_restrictScalars', smul_apply,
          ContinuousLinearMap.id_apply]
      _ = ∫ t, Lα (F t) ∂μ := by
        rw [Lα.integral_comp_comm hFint]
      _ = ∫ t, L (α • F t) ∂μ := by
        apply integral_congr_ae
        filter_upwards with t
        simp only [Lα, S, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.coe_restrictScalars', smul_apply,
          ContinuousLinearMap.id_apply]
      _ = 0 := by
        dsimp only [μ]
        rw [integral_radialBoundaryArcLengthMeasure_eq]
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le
            (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
        obtain ⟨CH, hHlip⟩ :=
          exists_lipschitzWith_homotopyResolventPrimitive
            A hconv hc hcompact hWA hs
        have hLHlip : LipschitzWith (‖L‖₊ * CH)
            (fun u ↦ L (homotopyResolventPrimitive A K c s u)) :=
          L.lipschitz.comp hHlip
        have hFTC := intervalIntegral_deriv_eq_sub_of_lipschitzWith
          hLHlip 0 (2 * Real.pi)
        have hclose : homotopyResolventPrimitive A K c s (2 * Real.pi) =
            homotopyResolventPrimitive A K c s 0 := by
          simpa only [zero_add] using
            homotopyResolventPrimitive_periodic A K c s 0
        rw [hclose, sub_self] at hFTC
        calc
          ∫ t in (0 : ℝ)..(2 * Real.pi),
              radialBoundarySpeed K c t • L (α • F t) =
            ∫ t in (0 : ℝ)..(2 * Real.pi),
              deriv (fun u ↦ L (homotopyResolventPrimitive A K c s u)) t := by
                apply intervalIntegral.integral_congr_ae
                obtain ⟨Cσ, hσlip⟩ :=
                  exists_lipschitzWith_radialBoundaryParametrization
                    hconv hc hcompact
                filter_upwards
                  [hσlip.ae_differentiableAt_real,
                    ae_deriv_eq_I_mul_normal_mul_speed hconv hc hcompact]
                  with t ht hnormal _
                have hd := hasDerivAt_dual_homotopyResolventPrimitive
                  A hconv hc hcompact hWA hs L ht
                rw [hd.deriv, hnormal]
                dsimp only [F, α]
                rw [← L.map_smul]
                congr 1
                module
          _ = 0 := hFTC
  change ∫ t, F t ∂μ = 0
  exact (smul_eq_zero.mp hαzero).resolve_left hα

/-- The normal-weighted boundary resolvent mass along the homotopy. -/
def homotopyResolventMass
    (A : SquareMatrix n) (K : Set ℂ) (c : ℂ) (s : ℝ) :
    EuclideanEndomorphism n :=
  ∫ t, radialOutwardUnitNormal K c t •
      homotopyBoundaryOperatorResolvent A K c s t
    ∂radialBoundaryArcLengthMeasure K c

/-- At the scalar endpoint the concrete resolvent mass is exactly
`2π` times the identity. -/
theorem homotopyResolventMass_zero_eq_two_pi_one
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) :
    homotopyResolventMass A K c 0 =
      (((2 * Real.pi : ℝ) : ℂ) • (1 : EuclideanEndomorphism n)) := by
  rw [homotopyResolventMass]
  calc
    ∫ t, radialOutwardUnitNormal K c t •
          homotopyBoundaryOperatorResolvent A K c 0 t
        ∂radialBoundaryArcLengthMeasure K c =
        ∫ t, (radialOutwardUnitNormal K c t /
            (radialBoundaryParametrization K c t - c)) •
              (1 : EuclideanEndomorphism n)
          ∂radialBoundaryArcLengthMeasure K c := by
            apply integral_congr_ae
            filter_upwards with t
            rw [homotopyBoundaryOperatorResolvent_zero
              A hconv hc hcompact hWA]
            simp only [div_eq_mul_inv, smul_smul]
    _ = (∫ t, radialOutwardUnitNormal K c t /
            (radialBoundaryParametrization K c t - c)
          ∂radialBoundaryArcLengthMeasure K c) •
            (1 : EuclideanEndomorphism n) :=
      integral_smul_const _ _
    _ = (((2 * Real.pi : ℝ) : ℂ) •
          (1 : EuclideanEndomorphism n)) := by
      rw [integral_normal_div_sub_center_radialBoundary hconv hc hcompact]

/-- The normal-weighted boundary resolvent is integrable at the scalar
endpoint as well. -/
theorem integrable_homotopyResolventMass_zero
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) :
    Integrable
      (fun t ↦ radialOutwardUnitNormal K c t •
        homotopyBoundaryOperatorResolvent A K c 0 t)
      (radialBoundaryArcLengthMeasure K c) := by
  have hscalar :=
    (integrable_normal_div_sub_center_radialBoundary hconv hc hcompact).smul_const
      (1 : EuclideanEndomorphism n)
  apply hscalar.congr
  filter_upwards with t
  rw [homotopyBoundaryOperatorResolvent_zero A hconv hc hcompact hWA]
  simp only [div_eq_mul_inv, smul_smul]

/-- The boundary resolvent mass is well-defined at every interior
homotopy time. -/
theorem integrable_homotopyResolventMass
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) {s : ℝ} (hs : s ∈ Set.Ioo 0 1) :
    Integrable
      (fun t ↦ radialOutwardUnitNormal K c t •
        homotopyBoundaryOperatorResolvent A K c s t)
      (radialBoundaryArcLengthMeasure K c) := by
  let _ : IsFiniteMeasure (radialBoundaryArcLengthMeasure K c) :=
    isFiniteMeasure_radialBoundaryArcLengthMeasure hconv hc hcompact
  obtain ⟨M, hM0, hM⟩ :=
    exists_uniform_norm_bound_homotopyBoundaryOperatorResolvent
      A hconv hc hcompact hWA hs
  have hmeas : Measurable
      (fun t ↦ radialOutwardUnitNormal K c t •
        homotopyBoundaryOperatorResolvent A K c s t) :=
    (measurable_radialOutwardUnitNormal K c).smul
      (continuous_homotopyBoundaryOperatorResolvent
        A hconv hc hcompact hWA hs).measurable
  apply Integrable.of_bound hmeas.aestronglyMeasurable M
  filter_upwards with t
  rw [norm_smul]
  exact (mul_le_mul
    (norm_radialOutwardUnitNormal_le_one K c t) (hM t)
    (norm_nonneg _) zero_le_one).trans (one_mul M).le

/-- Scalarwise differentiation of the normal-weighted resolvent with
respect to homotopy time. -/
theorem hasDerivAt_dual_homotopyBoundaryResolvent_time
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) (L : EuclideanEndomorphism n →L[ℝ] ℝ)
    {s : ℝ} (hs : s ∈ Set.Ioo 0 1) (t : ℝ) :
    HasDerivAt
      (fun u ↦ L (radialOutwardUnitNormal K c t •
        homotopyBoundaryOperatorResolvent A K c u t))
      (L (radialOutwardUnitNormal K c t •
        (homotopyBoundaryOperatorResolvent A K c s t *
          convexOperatorHomotopyVelocity A c *
            homotopyBoundaryOperatorResolvent A K c s t))) s := by
  have hRmatrix := radialBoundary_mem_resolventSet_convexMatrixHomotopy
    A hconv hc hcompact hWA hs t
  have hR := AlgHom.mem_resolventSet_apply
    (euclideanOperator (n := n)) hRmatrix
  rw [← convexOperatorHomotopy_eq_euclideanOperator] at hR
  have hres := (spectrum.hasFDerivAt_resolvent hR).restrictScalars ℝ
  have htime := hres.comp_hasDerivAt s
    (hasDerivAt_convexOperatorHomotopy A c s)
  change HasDerivAt
    (fun u ↦ homotopyBoundaryOperatorResolvent A K c u t)
    (homotopyBoundaryOperatorResolvent A K c s t *
      convexOperatorHomotopyVelocity A c *
        homotopyBoundaryOperatorResolvent A K c s t) s at htime
  have hnormal := (hasDerivAt_const (x := s)
    (radialOutwardUnitNormal K c t)).smul htime
  have hcomp := (hasDerivAt_const (x := s) L).clm_apply hnormal
  rw [hasDerivAt_iff_tendsto_slope] at hcomp ⊢
  convert hcomp using 1 <;>
    simp only [homotopyBoundaryOperatorResolvent,
      Pi.smul_apply', zero_apply, zero_add]
  congr 2
  module

/-- Joint continuity of the boundary resolvent in homotopy time and
boundary parameter, as long as the time is interior. -/
theorem continuousAt_homotopyBoundaryOperatorResolvent_joint
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) (p : ℝ × ℝ)
    (hp : p.1 ∈ Set.Ico 0 1) :
    ContinuousAt
      (fun q : ℝ × ℝ ↦
        homotopyBoundaryOperatorResolvent A K c q.1 q.2) p := by
  have hRmatrix := radialBoundary_mem_resolventSet_convexMatrixHomotopy_Ico
    A hconv hc hcompact hWA hp p.2
  have hR := AlgHom.mem_resolventSet_apply
    (euclideanOperator (n := n)) hRmatrix
  rw [← convexOperatorHomotopy_eq_euclideanOperator] at hR
  obtain ⟨Cσ, hσ⟩ :=
    exists_lipschitzWith_radialBoundaryParametrization hconv hc hcompact
  have hT : Continuous (fun q : ℝ × ℝ ↦
      convexOperatorHomotopy A c q.1) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    exact (hasDerivAt_convexOperatorHomotopy A c q.1).continuousAt.comp
      continuousAt_fst
  have harg : Continuous (fun q : ℝ × ℝ ↦
      radialBoundaryParametrization K c q.2 •
        (1 : EuclideanEndomorphism n) - convexOperatorHomotopy A c q.1) :=
    ((hσ.continuous.comp continuous_snd).smul continuous_const).sub hT
  have hargAt : ContinuousAt (fun q : ℝ × ℝ ↦
      radialBoundaryParametrization K c q.2 •
        (1 : EuclideanEndomorphism n) - convexOperatorHomotopy A c q.1) p :=
    harg.continuousAt
  have hunitEq :
      radialBoundaryParametrization K c p.2 •
          (1 : EuclideanEndomorphism n) - convexOperatorHomotopy A c p.1 =
        (hR.unit : EuclideanEndomorphism n) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using hR.unit_spec.symm
  have hraw :=
    (NormedRing.inverse_continuousAt hR.unit).comp_of_eq hargAt hunitEq
  rw [Metric.continuousAt_iff] at hraw ⊢
  simpa only [homotopyBoundaryOperatorResolvent, resolvent,
    Algebra.algebraMap_eq_smul_one, Function.comp_apply] using hraw

/-- Joint continuity extends to the original-matrix endpoint when the
original spectrum is strictly inside the convex body. -/
theorem continuousAt_homotopyBoundaryOperatorResolvent_joint_Icc
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K) (p : ℝ × ℝ)
    (hp : p.1 ∈ Set.Icc 0 1) :
    ContinuousAt
      (fun q : ℝ × ℝ ↦
        homotopyBoundaryOperatorResolvent A K c q.1 q.2) p := by
  have hRmatrix := radialBoundary_mem_resolventSet_convexMatrixHomotopy_Icc
    A hconv hc hcompact hWA hspectrum hp p.2
  have hR := AlgHom.mem_resolventSet_apply
    (euclideanOperator (n := n)) hRmatrix
  rw [← convexOperatorHomotopy_eq_euclideanOperator] at hR
  obtain ⟨Cσ, hσ⟩ :=
    exists_lipschitzWith_radialBoundaryParametrization hconv hc hcompact
  have hT : Continuous (fun q : ℝ × ℝ ↦
      convexOperatorHomotopy A c q.1) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    exact (hasDerivAt_convexOperatorHomotopy A c q.1).continuousAt.comp
      continuousAt_fst
  have harg : Continuous (fun q : ℝ × ℝ ↦
      radialBoundaryParametrization K c q.2 •
        (1 : EuclideanEndomorphism n) - convexOperatorHomotopy A c q.1) :=
    ((hσ.continuous.comp continuous_snd).smul continuous_const).sub hT
  have hargAt : ContinuousAt (fun q : ℝ × ℝ ↦
      radialBoundaryParametrization K c q.2 •
        (1 : EuclideanEndomorphism n) - convexOperatorHomotopy A c q.1) p :=
    harg.continuousAt
  have hunitEq :
      radialBoundaryParametrization K c p.2 •
          (1 : EuclideanEndomorphism n) - convexOperatorHomotopy A c p.1 =
        (hR.unit : EuclideanEndomorphism n) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using hR.unit_spec.symm
  have hraw :=
    (NormedRing.inverse_continuousAt hR.unit).comp_of_eq hargAt hunitEq
  rw [Metric.continuousAt_iff] at hraw ⊢
  simpa only [homotopyBoundaryOperatorResolvent, resolvent,
    Algebra.algebraMap_eq_smul_one, Function.comp_apply] using hraw

/-- On a compact time interval strictly inside `(0,1)`, the whole
periodic family of boundary resolvents has one uniform norm bound. -/
theorem exists_uniform_norm_bound_homotopyBoundaryOperatorResolvent_on
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) {J : Set ℝ}
    (hJcompact : IsCompact J) (hJ : J ⊆ Set.Ico 0 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u ∈ J, ∀ t ∈ Set.Icc 0 (2 * Real.pi),
      ‖homotopyBoundaryOperatorResolvent A K c u t‖ ≤ M := by
  let Q : Set (ℝ × ℝ) := J ×ˢ Set.Icc 0 (2 * Real.pi)
  have hQcompact : IsCompact Q := hJcompact.prod isCompact_Icc
  have hcont : ContinuousOn
      (fun q : ℝ × ℝ ↦
        homotopyBoundaryOperatorResolvent A K c q.1 q.2) Q := by
    intro q hq
    exact (continuousAt_homotopyBoundaryOperatorResolvent_joint
      A hconv hc hcompact hWA q (hJ hq.1)).continuousWithinAt
  have hbounded := (hQcompact.image_of_continuousOn hcont).isBounded
  obtain ⟨M, hM⟩ := hbounded.exists_norm_le
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro u hu t ht
  exact (hM _ ⟨⟨u, t⟩, ⟨hu, ht⟩, rfl⟩).trans (le_max_left _ _)

/-- Uniform boundary-resolvent bound on a compact time set in the closed
homotopy interval, under strict spectral containment at time one. -/
theorem exists_uniform_norm_bound_homotopyBoundaryOperatorResolvent_on_Icc
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K) {J : Set ℝ}
    (hJcompact : IsCompact J) (hJ : J ⊆ Set.Icc 0 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u ∈ J, ∀ t ∈ Set.Icc 0 (2 * Real.pi),
      ‖homotopyBoundaryOperatorResolvent A K c u t‖ ≤ M := by
  let Q : Set (ℝ × ℝ) := J ×ˢ Set.Icc 0 (2 * Real.pi)
  have hQcompact : IsCompact Q := hJcompact.prod isCompact_Icc
  have hcont : ContinuousOn
      (fun q : ℝ × ℝ ↦
        homotopyBoundaryOperatorResolvent A K c q.1 q.2) Q := by
    intro q hq
    exact (continuousAt_homotopyBoundaryOperatorResolvent_joint_Icc
      A hconv hc hcompact hWA hspectrum q (hJ hq.1)).continuousWithinAt
  have hbounded := (hQcompact.image_of_continuousOn hcont).isBounded
  obtain ⟨M, hM⟩ := hbounded.exists_norm_le
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro u hu t ht
  exact (hM _ ⟨⟨u, t⟩, ⟨hu, ht⟩, rfl⟩).trans (le_max_left _ _)

/-- Scalar evaluation of the boundary resolvent mass. -/
def dualHomotopyResolventMass
    (A : SquareMatrix n) (K : Set ℂ) (c : ℂ)
    (L : EuclideanEndomorphism n →L[ℝ] ℝ) (s : ℝ) : ℝ :=
  ∫ t, L (radialOutwardUnitNormal K c t •
      homotopyBoundaryOperatorResolvent A K c s t)
    ∂radialBoundaryArcLengthMeasure K c

/-- Every scalar evaluation of the resolvent mass has derivative zero on
the open homotopy interval. -/
theorem hasDerivAt_dualHomotopyResolventMass_zero
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) (L : EuclideanEndomorphism n →L[ℝ] ℝ)
    {s : ℝ} (hs : s ∈ Set.Ioo 0 1) :
    HasDerivAt (dualHomotopyResolventMass A K c L) 0 s := by
  let μ := radialBoundaryArcLengthMeasure K c
  let J : Set ℝ := Set.Icc (s / 2) ((s + 1) / 2)
  have hsleft : s / 2 < s := by linarith [hs.1]
  have hsright : s < (s + 1) / 2 := by linarith [hs.2]
  have hJnhds : J ∈ nhds s := Icc_mem_nhds hsleft hsright
  have hJ : J ⊆ Set.Ioo 0 1 := by
    intro u hu
    dsimp only [J] at hu
    exact ⟨by linarith [hu.1, hs.1], by linarith [hu.2, hs.2]⟩
  obtain ⟨M, hM0, hM⟩ :=
    exists_uniform_norm_bound_homotopyBoundaryOperatorResolvent_on
      A hconv hc hcompact hWA isCompact_Icc
        (hJ.trans Set.Ioo_subset_Ico_self)
  let F : ℝ → ℝ → ℝ := fun u t ↦
    L (radialOutwardUnitNormal K c t •
      homotopyBoundaryOperatorResolvent A K c u t)
  let F' : ℝ → ℝ → ℝ := fun u t ↦
    L (radialOutwardUnitNormal K c t •
      (homotopyBoundaryOperatorResolvent A K c u t *
        convexOperatorHomotopyVelocity A c *
          homotopyBoundaryOperatorResolvent A K c u t))
  let C : ℝ := ‖L‖ * (M * ‖convexOperatorHomotopyVelocity A c‖ * M)
  have hFmeas : ∀ᶠ u in nhds s, AEStronglyMeasurable (F u) μ := by
    filter_upwards [hJnhds] with u hu
    exact (L.integrable_comp <|
      integrable_homotopyResolventMass
        A hconv hc hcompact hWA (hJ hu)).aestronglyMeasurable
  have hFint : Integrable (F s) μ := by
    exact L.integrable_comp <|
      integrable_homotopyResolventMass A hconv hc hcompact hWA hs
  have hF'meas : AEStronglyMeasurable (F' s) μ := by
    exact (L.integrable_comp <|
      integrable_homotopyResolventMassDerivative
        A hconv hc hcompact hWA hs).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂μ, ∀ u ∈ J, ‖F' u t‖ ≤ C := by
    filter_upwards [ae_mem_Icc_radialBoundaryArcLengthMeasure K c] with t ht
    intro u hu
    dsimp only [F', C]
    calc
      ‖L (radialOutwardUnitNormal K c t •
          (homotopyBoundaryOperatorResolvent A K c u t *
            convexOperatorHomotopyVelocity A c *
              homotopyBoundaryOperatorResolvent A K c u t))‖ ≤
        ‖L‖ * ‖radialOutwardUnitNormal K c t •
          (homotopyBoundaryOperatorResolvent A K c u t *
            convexOperatorHomotopyVelocity A c *
              homotopyBoundaryOperatorResolvent A K c u t)‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (1 * (M * ‖convexOperatorHomotopyVelocity A c‖ * M)) := by
        gcongr
        rw [norm_smul]
        gcongr
        · exact norm_radialOutwardUnitNormal_le_one K c t
        · exact ((norm_mul_le _ _).trans <| mul_le_mul
              ((norm_mul_le _ _).trans <| mul_le_mul
                (hM u hu t ht) le_rfl (norm_nonneg _) hM0)
              (hM u hu t ht) (norm_nonneg _)
                (mul_nonneg hM0 (norm_nonneg _)))
      _ = ‖L‖ * (M * ‖convexOperatorHomotopyVelocity A c‖ * M) := by
        rw [one_mul]
  have hCint : Integrable (fun _ : ℝ ↦ C) μ := by
    let _ : IsFiniteMeasure μ :=
      isFiniteMeasure_radialBoundaryArcLengthMeasure hconv hc hcompact
    exact integrable_const C
  have hdiff : ∀ᵐ t ∂μ, ∀ u ∈ J,
      HasDerivAt (F · t) (F' u t) u := by
    filter_upwards with t
    intro u hu
    exact hasDerivAt_dual_homotopyBoundaryResolvent_time
      A hconv hc hcompact hWA L (hJ hu) t
  have hraw := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ ↦ C)
    hJnhds hFmeas hFint hF'meas hbound hCint hdiff).2
  have hVecInt :=
    integrable_homotopyResolventMassDerivative
      A hconv hc hcompact hWA hs
  have hderivativeZero : ∫ t, F' s t ∂μ = 0 := by
    change ∫ t, L (radialOutwardUnitNormal K c t •
      (homotopyBoundaryOperatorResolvent A K c s t *
        convexOperatorHomotopyVelocity A c *
          homotopyBoundaryOperatorResolvent A K c s t)) ∂μ = 0
    rw [L.integral_comp_comm hVecInt]
    rw [integral_homotopyResolventMassDerivative_eq_zero
      A hconv hc hcompact hWA hs, map_zero]
  rw [hderivativeZero] at hraw
  change HasDerivAt
    (fun u ↦ ∫ t, L (radialOutwardUnitNormal K c t •
      homotopyBoundaryOperatorResolvent A K c u t)
        ∂radialBoundaryArcLengthMeasure K c) 0 s
  rw [hasDerivAt_iff_tendsto_slope] at hraw ⊢
  simpa only [F, μ] using hraw

/-- Scalar evaluations of the boundary resolvent mass are constant on
the open homotopy interval. -/
theorem dualHomotopyResolventMass_eq
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) (L : EuclideanEndomorphism n →L[ℝ] ℝ)
    {s u : ℝ} (hs : s ∈ Set.Ioo 0 1) (hu : u ∈ Set.Ioo 0 1) :
    dualHomotopyResolventMass A K c L s =
      dualHomotopyResolventMass A K c L u := by
  apply isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
  · intro x hx
    exact (hasDerivAt_dualHomotopyResolventMass_zero
      A hconv hc hcompact hWA L hx).differentiableAt.differentiableWithinAt
  · intro x hx
    exact (hasDerivAt_dualHomotopyResolventMass_zero
      A hconv hc hcompact hWA L hx).deriv
  · exact hs
  · exact hu

/-- Scalar integration commutes with the concrete resolvent mass. -/
theorem dualHomotopyResolventMass_eq_apply_mass
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) (L : EuclideanEndomorphism n →L[ℝ] ℝ)
    {s : ℝ} (hs : s ∈ Set.Ioo 0 1) :
    dualHomotopyResolventMass A K c L s =
      L (homotopyResolventMass A K c s) := by
  rw [dualHomotopyResolventMass, homotopyResolventMass]
  exact L.integral_comp_comm
    (integrable_homotopyResolventMass A hconv hc hcompact hWA hs)

/-- Scalar integration commutes with the resolvent mass at the scalar
endpoint. -/
theorem dualHomotopyResolventMass_zero_eq_apply_mass
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) (L : EuclideanEndomorphism n →L[ℝ] ℝ) :
    dualHomotopyResolventMass A K c L 0 =
      L (homotopyResolventMass A K c 0) := by
  rw [dualHomotopyResolventMass, homotopyResolventMass]
  exact L.integral_comp_comm
    (integrable_homotopyResolventMass_zero A hconv hc hcompact hWA)

/-- The operator-valued boundary resolvent mass is constant throughout
the open homotopy interval. -/
theorem homotopyResolventMass_eq
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    {s u : ℝ} (hs : s ∈ Set.Ioo 0 1) (hu : u ∈ Set.Ioo 0 1) :
    homotopyResolventMass A K c s = homotopyResolventMass A K c u := by
  apply sub_eq_zero.mp
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
  intro L
  rw [map_sub]
  rw [← dualHomotopyResolventMass_eq_apply_mass
      A hconv hc hcompact hWA L hs,
    ← dualHomotopyResolventMass_eq_apply_mass
      A hconv hc hcompact hWA L hu,
    dualHomotopyResolventMass_eq A hconv hc hcompact hWA L hs hu,
    sub_self]

/-- Boundary-parameter continuity also holds at the scalar endpoint of
the homotopy. -/
theorem continuous_homotopyBoundaryOperatorResolvent_Ico
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) {s : ℝ} (hs : s ∈ Set.Ico 0 1) :
    Continuous (homotopyBoundaryOperatorResolvent A K c s) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hraw := (continuousAt_homotopyBoundaryOperatorResolvent_joint
    A hconv hc hcompact hWA (s, t) hs).comp
      (continuousAt_const.prodMk continuousAt_id)
  rw [Metric.continuousAt_iff] at hraw ⊢
  simpa only [Function.comp_apply] using hraw

/-- Boundary-parameter continuity on the closed homotopy interval under
strict spectral containment at the original-matrix endpoint. -/
theorem continuous_homotopyBoundaryOperatorResolvent_Icc
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K)
    {s : ℝ} (hs : s ∈ Set.Icc 0 1) :
    Continuous (homotopyBoundaryOperatorResolvent A K c s) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hraw := (continuousAt_homotopyBoundaryOperatorResolvent_joint_Icc
    A hconv hc hcompact hWA hspectrum (s, t) hs).comp
      (continuousAt_const.prodMk continuousAt_id)
  rw [Metric.continuousAt_iff] at hraw ⊢
  simpa only [Function.comp_apply] using hraw

/-- The normal-weighted resolvent is integrable at every time in the
closed homotopy interval when the endpoint spectrum is strictly inside. -/
theorem integrable_homotopyResolventMass_Icc
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K)
    {s : ℝ} (hs : s ∈ Set.Icc 0 1) :
    Integrable
      (fun t ↦ radialOutwardUnitNormal K c t •
        homotopyBoundaryOperatorResolvent A K c s t)
      (radialBoundaryArcLengthMeasure K c) := by
  let _ : IsFiniteMeasure (radialBoundaryArcLengthMeasure K c) :=
    isFiniteMeasure_radialBoundaryArcLengthMeasure hconv hc hcompact
  obtain ⟨M, hM0, hM⟩ :=
    exists_uniform_norm_bound_homotopyBoundaryOperatorResolvent_on_Icc
      A hconv hc hcompact hWA hspectrum isCompact_singleton
        (by simpa only [Set.singleton_subset_iff] using hs)
  have hmeas : Measurable
      (fun t ↦ radialOutwardUnitNormal K c t •
        homotopyBoundaryOperatorResolvent A K c s t) :=
    (measurable_radialOutwardUnitNormal K c).smul
      (continuous_homotopyBoundaryOperatorResolvent_Icc
        A hconv hc hcompact hWA hspectrum hs).measurable
  apply Integrable.of_bound hmeas.aestronglyMeasurable M
  filter_upwards [ae_mem_Icc_radialBoundaryArcLengthMeasure K c] with t ht
  rw [norm_smul]
  exact (mul_le_mul
    (norm_radialOutwardUnitNormal_le_one K c t)
    (hM s (Set.mem_singleton s) t ht)
    (norm_nonneg _) zero_le_one).trans (one_mul M).le

/-- Scalar integration commutes with the concrete mass throughout the
closed homotopy interval under strict spectral containment. -/
theorem dualHomotopyResolventMass_eq_apply_mass_Icc
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K)
    (L : EuclideanEndomorphism n →L[ℝ] ℝ)
    {s : ℝ} (hs : s ∈ Set.Icc 0 1) :
    dualHomotopyResolventMass A K c L s =
      L (homotopyResolventMass A K c s) := by
  rw [dualHomotopyResolventMass, homotopyResolventMass]
  exact L.integral_comp_comm
    (integrable_homotopyResolventMass_Icc
      A hconv hc hcompact hWA hspectrum hs)

/-- Scalar resolvent masses converge to the scalar endpoint from positive
homotopy times. -/
theorem tendsto_dualHomotopyResolventMass_nhdsGT_zero
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) (L : EuclideanEndomorphism n →L[ℝ] ℝ) :
    Tendsto (dualHomotopyResolventMass A K c L)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (dualHomotopyResolventMass A K c L 0)) := by
  let μ := radialBoundaryArcLengthMeasure K c
  let J : Set ℝ := Set.Icc 0 (1 / 2)
  have hJ : J ⊆ Set.Ico 0 1 := by
    intro u hu
    dsimp only [J] at hu
    constructor <;> linarith [hu.1, hu.2]
  have hJeff : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0), u ∈ J := by
    exact Icc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨M, hM0, hM⟩ :=
    exists_uniform_norm_bound_homotopyBoundaryOperatorResolvent_on
      A hconv hc hcompact hWA isCompact_Icc hJ
  let G : ℝ → ℝ → ℝ := fun u t ↦
    L (radialOutwardUnitNormal K c t •
      homotopyBoundaryOperatorResolvent A K c u t)
  let C : ℝ := ‖L‖ * M
  have hGmeas : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      AEStronglyMeasurable (G u) μ := by
    filter_upwards [hJeff] with u hu
    exact (L.continuous.measurable.comp
      ((measurable_radialOutwardUnitNormal K c).smul
        (continuous_homotopyBoundaryOperatorResolvent_Ico
          A hconv hc hcompact hWA (hJ hu)).measurable)).aestronglyMeasurable
  have hbound : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ᵐ t ∂μ, ‖G u t‖ ≤ C := by
    filter_upwards [hJeff] with u hu
    filter_upwards [ae_mem_Icc_radialBoundaryArcLengthMeasure K c] with t ht
    dsimp only [G, C]
    calc
      ‖L (radialOutwardUnitNormal K c t •
          homotopyBoundaryOperatorResolvent A K c u t)‖ ≤
        ‖L‖ * ‖radialOutwardUnitNormal K c t •
          homotopyBoundaryOperatorResolvent A K c u t‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (1 * M) := by
        gcongr
        rw [norm_smul]
        exact mul_le_mul
          (norm_radialOutwardUnitNormal_le_one K c t)
          (hM u hu t ht) (norm_nonneg _) zero_le_one
      _ = ‖L‖ * M := by rw [one_mul]
  have hCint : Integrable (fun _ : ℝ ↦ C) μ := by
    let _ : IsFiniteMeasure μ :=
      isFiniteMeasure_radialBoundaryArcLengthMeasure hconv hc hcompact
    exact integrable_const C
  have hlim : ∀ᵐ t ∂μ, Tendsto (fun u ↦ G u t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (G 0 t)) := by
    filter_upwards with t
    have hRjoint := continuousAt_homotopyBoundaryOperatorResolvent_joint
      A hconv hc hcompact hWA (0, t)
        (by norm_num : (0 : ℝ) ∈ Set.Ico 0 1)
    have hpair : ContinuousAt (fun u : ℝ ↦ (u, t)) 0 :=
      continuousAt_id.prodMk continuousAt_const
    have hRtimeRaw :=
      ContinuousAt.comp (x := (0 : ℝ)) hRjoint hpair
    have hRtime : ContinuousAt
        (fun u ↦ homotopyBoundaryOperatorResolvent A K c u t) 0 := by
      rw [Metric.continuousAt_iff] at hRtimeRaw ⊢
      simpa only [Function.comp_apply] using hRtimeRaw
    have hnormal : ContinuousAt
        (fun _ : ℝ ↦ radialOutwardUnitNormal K c t) 0 := continuousAt_const
    have hGtimeRaw := L.continuous.continuousAt.comp (hnormal.smul hRtime)
    have hGtime : ContinuousAt (fun u ↦ G u t) 0 := by
      rw [Metric.continuousAt_iff] at hGtimeRaw ⊢
      simpa only [G, Function.comp_apply, Pi.smul_apply'] using hGtimeRaw
    exact hGtime.mono_left inf_le_left
  have htendsto := tendsto_integral_filter_of_dominated_convergence
    (F := G) (f := G 0) (bound := fun _ ↦ C)
    hGmeas hbound hCint hlim
  change Tendsto
    (fun u ↦ ∫ t, L (radialOutwardUnitNormal K c t •
      homotopyBoundaryOperatorResolvent A K c u t)
        ∂radialBoundaryArcLengthMeasure K c)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds (∫ t, L (radialOutwardUnitNormal K c t •
      homotopyBoundaryOperatorResolvent A K c 0 t)
        ∂radialBoundaryArcLengthMeasure K c))
  simpa only [G, μ] using htendsto

/-- Scalar resolvent masses converge to the original-matrix endpoint from
interior homotopy times when its spectrum is strictly inside the body. -/
theorem tendsto_dualHomotopyResolventMass_nhdsLT_one
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K)
    (L : EuclideanEndomorphism n →L[ℝ] ℝ) :
    Tendsto (dualHomotopyResolventMass A K c L)
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (dualHomotopyResolventMass A K c L 1)) := by
  let μ := radialBoundaryArcLengthMeasure K c
  let J : Set ℝ := Set.Icc (1 / 2) 1
  have hJ : J ⊆ Set.Icc 0 1 := by
    intro u hu
    dsimp only [J] at hu
    constructor <;> linarith [hu.1, hu.2]
  have hJeff : ∀ᶠ u in nhdsWithin (1 : ℝ) (Set.Iio 1), u ∈ J := by
    exact Icc_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨M, hM0, hM⟩ :=
    exists_uniform_norm_bound_homotopyBoundaryOperatorResolvent_on_Icc
      A hconv hc hcompact hWA hspectrum isCompact_Icc hJ
  let G : ℝ → ℝ → ℝ := fun u t ↦
    L (radialOutwardUnitNormal K c t •
      homotopyBoundaryOperatorResolvent A K c u t)
  let C : ℝ := ‖L‖ * M
  have hGmeas : ∀ᶠ u in nhdsWithin (1 : ℝ) (Set.Iio 1),
      AEStronglyMeasurable (G u) μ := by
    filter_upwards [hJeff] with u hu
    exact (L.continuous.measurable.comp
      ((measurable_radialOutwardUnitNormal K c).smul
        (continuous_homotopyBoundaryOperatorResolvent_Icc
          A hconv hc hcompact hWA hspectrum (hJ hu)).measurable)).aestronglyMeasurable
  have hbound : ∀ᶠ u in nhdsWithin (1 : ℝ) (Set.Iio 1),
      ∀ᵐ t ∂μ, ‖G u t‖ ≤ C := by
    filter_upwards [hJeff] with u hu
    filter_upwards [ae_mem_Icc_radialBoundaryArcLengthMeasure K c] with t ht
    dsimp only [G, C]
    calc
      ‖L (radialOutwardUnitNormal K c t •
          homotopyBoundaryOperatorResolvent A K c u t)‖ ≤
        ‖L‖ * ‖radialOutwardUnitNormal K c t •
          homotopyBoundaryOperatorResolvent A K c u t‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (1 * M) := by
        gcongr
        rw [norm_smul]
        exact mul_le_mul
          (norm_radialOutwardUnitNormal_le_one K c t)
          (hM u hu t ht) (norm_nonneg _) zero_le_one
      _ = ‖L‖ * M := by rw [one_mul]
  have hCint : Integrable (fun _ : ℝ ↦ C) μ := by
    let _ : IsFiniteMeasure μ :=
      isFiniteMeasure_radialBoundaryArcLengthMeasure hconv hc hcompact
    exact integrable_const C
  have hlim : ∀ᵐ t ∂μ, Tendsto (fun u ↦ G u t)
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (G 1 t)) := by
    filter_upwards with t
    have hRjoint := continuousAt_homotopyBoundaryOperatorResolvent_joint_Icc
      A hconv hc hcompact hWA hspectrum (1, t)
        (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
    have hpair : ContinuousAt (fun u : ℝ ↦ (u, t)) 1 :=
      continuousAt_id.prodMk continuousAt_const
    have hRtimeRaw :=
      ContinuousAt.comp (x := (1 : ℝ)) hRjoint hpair
    have hRtime : ContinuousAt
        (fun u ↦ homotopyBoundaryOperatorResolvent A K c u t) 1 := by
      rw [Metric.continuousAt_iff] at hRtimeRaw ⊢
      simpa only [Function.comp_apply] using hRtimeRaw
    have hnormal : ContinuousAt
        (fun _ : ℝ ↦ radialOutwardUnitNormal K c t) 1 := continuousAt_const
    have hGtimeRaw := L.continuous.continuousAt.comp (hnormal.smul hRtime)
    have hGtime : ContinuousAt (fun u ↦ G u t) 1 := by
      rw [Metric.continuousAt_iff] at hGtimeRaw ⊢
      simpa only [G, Function.comp_apply, Pi.smul_apply'] using hGtimeRaw
    exact hGtime.mono_left inf_le_left
  have htendsto := tendsto_integral_filter_of_dominated_convergence
    (F := G) (f := G 1) (bound := fun _ ↦ C)
    hGmeas hbound hCint hlim
  change Tendsto
    (fun u ↦ ∫ t, L (radialOutwardUnitNormal K c t •
      homotopyBoundaryOperatorResolvent A K c u t)
        ∂radialBoundaryArcLengthMeasure K c)
    (nhdsWithin (1 : ℝ) (Set.Iio 1))
    (nhds (∫ t, L (radialOutwardUnitNormal K c t •
      homotopyBoundaryOperatorResolvent A K c 1 t)
        ∂radialBoundaryArcLengthMeasure K c))
  simpa only [G, μ] using htendsto

/-- Constancy on positive times and the right-endpoint limit identify
every scalar resolvent mass with its scalar endpoint value. -/
theorem dualHomotopyResolventMass_eq_zero
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) (L : EuclideanEndomorphism n →L[ℝ] ℝ)
    {s : ℝ} (hs : s ∈ Set.Ioo 0 1) :
    dualHomotopyResolventMass A K c L s =
      dualHomotopyResolventMass A K c L 0 := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have heq : dualHomotopyResolventMass A K c L =ᶠ[l]
      fun _ ↦ dualHomotopyResolventMass A K c L s := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with u hu
    exact dualHomotopyResolventMass_eq
      A hconv hc hcompact hWA L hu hs
  have htendstoS : Tendsto (dualHomotopyResolventMass A K c L) l
      (nhds (dualHomotopyResolventMass A K c L s)) := by
    exact (tendsto_congr' heq).mpr tendsto_const_nhds
  have htendsto0 : Tendsto (dualHomotopyResolventMass A K c L) l
      (nhds (dualHomotopyResolventMass A K c L 0)) := by
    exact tendsto_dualHomotopyResolventMass_nhdsGT_zero
      A hconv hc hcompact hWA L
  exact tendsto_nhds_unique htendstoS htendsto0

/-- Constancy at interior times and the left-endpoint limit identify every
scalar resolvent mass with its value at the original matrix. -/
theorem dualHomotopyResolventMass_eq_one
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K)
    (L : EuclideanEndomorphism n →L[ℝ] ℝ)
    {s : ℝ} (hs : s ∈ Set.Ioo 0 1) :
    dualHomotopyResolventMass A K c L s =
      dualHomotopyResolventMass A K c L 1 := by
  let l : Filter ℝ := nhdsWithin (1 : ℝ) (Set.Iio 1)
  have heq : dualHomotopyResolventMass A K c L =ᶠ[l]
      fun _ ↦ dualHomotopyResolventMass A K c L s := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with u hu
    exact dualHomotopyResolventMass_eq
      A hconv hc hcompact hWA L hu hs
  have htendstoS : Tendsto (dualHomotopyResolventMass A K c L) l
      (nhds (dualHomotopyResolventMass A K c L s)) := by
    exact (tendsto_congr' heq).mpr tendsto_const_nhds
  have htendsto1 : Tendsto (dualHomotopyResolventMass A K c L) l
      (nhds (dualHomotopyResolventMass A K c L 1)) := by
    exact tendsto_dualHomotopyResolventMass_nhdsLT_one
      A hconv hc hcompact hWA hspectrum L
  exact tendsto_nhds_unique htendstoS htendsto1

/-- The concrete normal-weighted resolvent mass is `2π I` at every
strictly interior homotopy time. -/
theorem homotopyResolventMass_eq_two_pi_one
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K) {s : ℝ} (hs : s ∈ Set.Ioo 0 1) :
    homotopyResolventMass A K c s =
      (((2 * Real.pi : ℝ) : ℂ) • (1 : EuclideanEndomorphism n)) := by
  apply sub_eq_zero.mp
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
  intro L
  rw [map_sub]
  rw [← dualHomotopyResolventMass_eq_apply_mass
      A hconv hc hcompact hWA L hs,
    dualHomotopyResolventMass_eq_zero A hconv hc hcompact hWA L hs,
    dualHomotopyResolventMass_zero_eq_apply_mass
      A hconv hc hcompact hWA L,
    homotopyResolventMass_zero_eq_two_pi_one A hconv hc hcompact hWA,
    sub_self]

/-- The normal-weighted boundary resolvent of the original matrix is
exactly `2π I`.  This is the ordinary resolvent Cauchy formula for the
constant polynomial, derived from raw convex geometry. -/
theorem homotopyResolventMass_one_eq_two_pi_one
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K) :
    homotopyResolventMass A K c 1 =
      (((2 * Real.pi : ℝ) : ℂ) • (1 : EuclideanEndomorphism n)) := by
  let s : ℝ := 1 / 2
  have hs : s ∈ Set.Ioo 0 1 := by
    dsimp only [s]
    norm_num
  apply sub_eq_zero.mp
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
  intro L
  rw [map_sub]
  rw [← dualHomotopyResolventMass_eq_apply_mass_Icc
      A hconv hc hcompact hWA hspectrum L
        (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1),
    ← dualHomotopyResolventMass_eq_one
      A hconv hc hcompact hWA hspectrum L hs,
    dualHomotopyResolventMass_eq_apply_mass
      A hconv hc hcompact hWA L hs,
    homotopyResolventMass_eq_two_pi_one A hconv hc hcompact hWA hs,
    sub_self]

end DiskRigidity.Operator
