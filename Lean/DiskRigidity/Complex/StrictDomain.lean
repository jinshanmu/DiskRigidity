/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.ConvexBoundary
public import DiskRigidity.Complex.ConformalSchurInterpolation
public import DiskRigidity.Complex.ProperFiniteBlaschke

/-!
# The complex-analytic core of strict domain monotonicity

A Schur function on a larger convex domain cannot restrict to a nonconstant finite-Blaschke
composition relative to a proper smaller domain.  Properness forces modulus one at a point of the
smaller boundary lying inside the larger domain, and the maximum-modulus principle then forces
constancy.
-/

open Function Metric Set

namespace DiskRigidity.Complex

@[expose] public section

/-- If a Schur function on a larger convex domain is finite Blaschke relative to a proper smaller
domain, then it is a unimodular constant throughout the larger domain. -/
theorem eqOn_unimodular_const_of_eqOn_finiteBlaschke_comp_of_ssubset
    {U V : Set ℂ} (hUo : IsOpen U) (hUne : U.Nonempty) (hUV : U ⊂ V)
    (hVo : IsOpen V) (hVc : Convex ℝ V)
    {phi B g : ℂ → ℂ} (hphi : DifferentiableOn ℂ phi U)
    (hphibij : BijOn phi U (ball 0 1)) (hB : IsSchurFiniteBlaschke B)
    (hg : IsSchurOn V g) (hgeq : EqOn g (B ∘ phi) U) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ EqOn g (const ℂ c) V := by
  obtain ⟨xi, hxiU, hxiV⟩ := exists_mem_frontier_inter_of_convex hUo hUne hUV hVc
  have hgcont : ContinuousAt g xi :=
    (hg.differentiableOn.differentiableAt (hVo.mem_nhds hxiV)).continuousAt
  have hxinorm : ‖g xi‖ = 1 :=
    norm_eq_one_at_frontier_of_eqOn_finiteBlaschke_comp
      hUo hphi hphibij hB hgcont hgeq hxiU
  have hmax : IsMaxOn (norm ∘ g) V xi := by
    intro z hz
    change ‖g z‖ ≤ ‖g xi‖
    rw [hxinorm]
    exact hg.norm_le hz
  exact ⟨g xi, hxinorm,
    _root_.Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
      hVc.isPreconnected hVo hg.differentiableOn hxiV hmax⟩

/-- Nonconstant form of the preceding theorem. -/
theorem not_eqOn_finiteBlaschke_comp_of_schurOn_ssuperset_of_nonconstant
    {U V : Set ℂ} (hUo : IsOpen U) (hUne : U.Nonempty) (hUV : U ⊂ V)
    (hVo : IsOpen V) (hVc : Convex ℝ V)
    {phi B g : ℂ → ℂ} (hphi : DifferentiableOn ℂ phi U)
    (hphibij : BijOn phi U (ball 0 1)) (hB : IsSchurFiniteBlaschke B)
    (hg : IsSchurOn V g) (hnonconst : ∀ c : ℂ, ¬ EqOn g (const ℂ c) V) :
    ¬ EqOn g (B ∘ phi) U := by
  intro hgeq
  obtain ⟨c, -, hc⟩ := eqOn_unimodular_const_of_eqOn_finiteBlaschke_comp_of_ssubset
    hUo hUne hUV hVo hVc hphi hphibij hB hg hgeq
  exact hnonconst c hc

end

end DiskRigidity.Complex
