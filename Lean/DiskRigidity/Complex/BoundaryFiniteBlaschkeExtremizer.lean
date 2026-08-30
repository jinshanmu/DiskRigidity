/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.ConvexCaratheodory
public import DiskRigidity.Complex.NumericalRangeExtremizer

/-!
# Boundary-continuous finite-Blaschke extremizers

The convex Carathéodory homeomorphism turns every finite Blaschke
composition on a bounded convex domain into a function continuous on the
closed domain and unimodular on its frontier.  The final theorem applies this
construction to the finite-jet extremizer for a matrix numerical range.
-/

noncomputable section

open Bornology Filter Function Metric Set Topology
open scoped Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Complex

@[expose] public section

/-- A finite Blaschke product composed with a Riemann map of a bounded convex
domain has an `A(closure U)` representative.  The representative agrees with
the composition in `U` and is unimodular on `frontier U`. -/
theorem exists_diffContOnCl_extension_finiteBlaschke_comp
    {U : Set ℂ} {phi B : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hUb : IsBounded U)
    (hphi : DifferentiableOn ℂ phi U)
    (hbij : BijOn phi U (ball 0 1))
    (hB : IsSchurFiniteBlaschke B) :
    ∃ g : ℂ → ℂ, ∃ Phi : closure U ≃ₜ closedBall (0 : ℂ) 1,
      DiffContOnCl ℂ g U ∧
      (∀ z : U,
        Phi ⟨z, subset_closure z.2⟩ =
          ⟨phi z, ball_subset_closedBall (hbij.mapsTo z.2)⟩) ∧
      EqOn g (B ∘ phi) U ∧
      (∀ (z : ℂ) (hz : z ∈ closure U),
        g z = B (Phi ⟨z, hz⟩)) ∧
      ∀ z ∈ frontier U, ‖g z‖ = 1 := by
  classical
  obtain ⟨Phi, hPhiExt⟩ :=
    exists_homeomorph_closure_closedDisc_extends_riemannMap
      hUo hUc hUb hphi hbij
  let g : ℂ → ℂ := fun z ↦
    if hz : z ∈ closure U then B (Phi ⟨z, hz⟩) else 0
  have hgClosure (z : ℂ) (hz : z ∈ closure U) :
      g z = B (Phi ⟨z, hz⟩) := by
    dsimp [g]
    rw [dif_pos hz]
  have hBcont : Continuous (fun z : closedBall (0 : ℂ) 1 ↦ B z) :=
    hB.analyticOnNhd.continuousOn.comp_continuous
      continuous_subtype_val fun z ↦ z.2
  have hcompCont : Continuous (fun z : closure U ↦ B (Phi z)) :=
    hBcont.comp Phi.continuous
  have hgcont : ContinuousOn g (closure U) := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert hcompCont using 1
    funext z
    exact hgClosure z z.2
  have hgeq : EqOn g (B ∘ phi) U := by
    intro z hz
    rw [hgClosure z (subset_closure hz)]
    change B (Phi ⟨z, subset_closure hz⟩) = B (phi z)
    rw [hPhiExt ⟨z, hz⟩]
  have hgdiff : DifferentiableOn ℂ g U :=
    (hB.isSchur.comp_biholomorphic hphi hbij).differentiableOn.congr hgeq
  refine ⟨g, Phi, ⟨hgdiff, hgcont⟩, hPhiExt, hgeq, hgClosure, ?_⟩
  intro z hz
  rw [hgClosure z (frontier_subset_closure hz)]
  apply hB.norm_eq_one
  exact homeomorph_closure_closedDisc_maps_frontier_to_sphere
    hUo hbij Phi hPhiExt hz

/-- A boundary-continuous finite-Blaschke extremizer on a matrix numerical
range, obtained directly from `crouzeixConstant A = 2`.  It is holomorphic on
the interior, continuous on the whole numerical range, unimodular on its
frontier, bounded by one throughout, and its finite spectral-jet calculus has
norm exactly two. -/
theorem exists_boundaryContinuous_finiteBlaschke_extremizer_direct
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Operator.SquareMatrix n)
    (hInt : (interior (Operator.numericalRange A)).Nonempty)
    (hspec : spectrum ℂ A ⊆ interior (Operator.numericalRange A))
    (hpsi : Operator.crouzeixConstant A = 2) :
    ∃ g phi B : ℂ → ℂ,
      DiffContOnCl ℂ g (interior (Operator.numericalRange A)) ∧
      IsSchurOn (interior (Operator.numericalRange A)) g ∧
      DifferentiableOn ℂ phi (interior (Operator.numericalRange A)) ∧
      BijOn phi (interior (Operator.numericalRange A)) (ball 0 1) ∧
      IsSchurFiniteBlaschke B ∧
      EqOn g (B ∘ phi) (interior (Operator.numericalRange A)) ∧
      ‖spectralJetEval A g‖ = 2 ∧
      IsNonconstantOn (interior (Operator.numericalRange A)) g ∧
      (∀ z ∈ frontier (Operator.numericalRange A), ‖g z‖ = 1) ∧
      ∀ z ∈ Operator.numericalRange A, ‖g z‖ ≤ 1 := by
  let W := Operator.numericalRange A
  let U := interior W
  have hWc : Convex ℝ W := Operator.numericalRange_convex A
  have hWcompact : IsCompact W := Operator.isCompact_numericalRange A
  have hWclosed : IsClosed W := hWcompact.isClosed
  have hUo : IsOpen U := isOpen_interior
  have hUc : Convex ℝ U := hWc.interior
  have hUb : IsBounded U := hWcompact.isBounded.subset interior_subset
  have hclosure : closure U = W := by
    rw [show U = interior W from rfl,
      hWc.closure_interior_eq_closure_of_nonempty_interior hInt,
      hWclosed.closure_eq]
  have hfrontier : frontier U = frontier W := by
    rw [frontier, hUo.interior_eq, hclosure, frontier,
      hWclosed.closure_eq]
  obtain ⟨f, phi, B, hf, hfeval, hphi, hbij, hB, _hjet,
      _heval, hcompEval, hcompNonconst⟩ :=
    exists_finiteBlaschke_extremizer_direct_of_crouzeixConstant_eq_two
      A hInt hspec hpsi
  obtain ⟨g, _Phi, hgcl, _hPhiExt, hgeq, _hgClosure, hgfrontier⟩ :=
    exists_diffContOnCl_extension_finiteBlaschke_comp
      hUo hUc hUb hphi hbij hB
  have hroots := charpoly_roots_subset_of_spectrum_subset A hspec
  have hgeval : spectralJetEval A g = spectralJetEval A (B ∘ phi) := by
    apply spectralJetEval_eq_of_iteratedDeriv_eq A
    intro a k
    have haU : (a : ℂ) ∈ U :=
      hroots _ (Multiset.mem_toFinset.mp a.2)
    have hevent : g =ᶠ[nhds (a : ℂ)] B ∘ phi := by
      filter_upwards [hUo.mem_nhds haU] with z hz
      exact hgeq hz
    exact hevent.iteratedDeriv_eq k.val
  have hgEvalNorm : ‖spectralJetEval A g‖ = 2 := by
    rw [hgeval, hcompEval]
  have hgNonconst : IsNonconstantOn U g := by
    rintro ⟨w, hw⟩
    apply hcompNonconst
    exact ⟨w, fun z hz ↦ (hgeq hz).symm.trans (hw hz)⟩
  have hboundW : ∀ z ∈ W, ‖g z‖ ≤ 1 := by
    intro z hzW
    by_cases hzU : z ∈ U
    · rw [hgeq hzU]
      exact hB.isSchur.comp_biholomorphic hphi hbij |>.norm_le hzU
    · have hzFront : z ∈ frontier W := by
        rw [frontier, hWclosed.closure_eq]
        exact ⟨hzW, hzU⟩
      rw [← hfrontier] at hzFront
      exact (hgfrontier z hzFront).le
  have hgSchur : IsSchurOn U g := by
    refine ⟨hgcl.differentiableOn, ?_⟩
    intro z hz
    rw [mem_closedBall_zero_iff]
    exact hboundW z (interior_subset hz)
  refine ⟨g, phi, B, hgcl, hgSchur, hphi, hbij, hB, hgeq,
    hgEvalNorm, hgNonconst, ?_, ?_⟩
  · intro z hz
    apply hgfrontier
    rwa [hfrontier]
  · exact hboundW

end

end DiskRigidity.Complex
