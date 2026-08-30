/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.ConvexRadialApproximation
public import DiskRigidity.Complex.HolomorphicExtremizer

/-!
# Extending a holomorphic calculus estimate from neighborhoods of a convex set

Radial contraction upgrades any estimate proved first for functions
holomorphic on a neighborhood of the closed convex set to the corresponding
estimate for all bounded holomorphic functions on its interior.  This is the
precise approximation step needed between a contour-integral estimate and the
finite spectral-jet extremizer.
-/

noncomputable section

open Filter Function Metric Set Topology
open scoped Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Complex

@[expose] public section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A homogeneous functional-calculus estimate for functions holomorphic on
some open neighborhood of a fixed compact set. -/
def HasNeighborhoodHolomorphicCalculusBound
    (A : Operator.SquareMatrix n) (K : Set ℂ) (C : ℝ) : Prop :=
  ∀ (g : ℂ → ℂ) (V : Set ℂ) (r : ℝ),
    IsOpen V → K ⊆ V → DifferentiableOn ℂ g V → 0 ≤ r →
      (∀ z ∈ K, ‖g z‖ ≤ r) → ‖spectralJetEval A g‖ ≤ C * r

/-- The standard increasing radial factors `m / (m + 1)`. -/
def standardRadialFactor (m : ℕ) : ℝ :=
  (m : ℝ) / (m + 1)

theorem standardRadialFactor_nonneg (m : ℕ) :
    0 ≤ standardRadialFactor m := by
  unfold standardRadialFactor
  positivity

theorem standardRadialFactor_lt_one (m : ℕ) :
    standardRadialFactor m < 1 := by
  unfold standardRadialFactor
  rw [div_lt_one]
  · norm_num
  · positivity

theorem tendsto_standardRadialFactor :
    Tendsto standardRadialFactor atTop (nhds 1) := by
  change Tendsto (fun m : ℕ ↦ (m : ℝ) / (m + 1)) atTop (nhds 1)
  exact tendsto_natCast_div_add_atTop (1 : ℝ)

/-- On an open convex domain, a neighborhood-holomorphic estimate on the
closure implies the same estimate for every bounded holomorphic function on
the domain. -/
theorem hasHolomorphicCalculusBound_of_neighborhoods_of_isOpen_convex
    (A : Operator.SquareMatrix n) {U : Set ℂ} {C : ℝ}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hUne : U.Nonempty)
    (hspec : spectrum ℂ A ⊆ U)
    (hnhd : HasNeighborhoodHolomorphicCalculusBound A (closure U) C) :
    HasHolomorphicCalculusBound A U C := by
  obtain ⟨z₀, hz₀⟩ := hUne
  intro g R hg hR hgR
  let F : ℕ → ℂ → ℂ := fun m ↦
    g ∘ radialContract z₀ (standardRadialFactor m)
  have hpackage (m : ℕ) :
      ∃ V : Set ℂ, IsOpen V ∧ closure U ⊆ V ∧
        DifferentiableOn ℂ (F m) V ∧
        ContinuousOn (F m) (closure U) ∧
        ∀ z ∈ closure U, ‖F m z‖ ≤ R := by
    simpa [F] using radial_holomorphicOnNhd_closure hUo hUc hz₀
      (standardRadialFactor_nonneg m) (standardRadialFactor_lt_one m) hg hgR
  have hFbound (m : ℕ) : ‖spectralJetEval A (F m)‖ ≤ C * R := by
    obtain ⟨V, hVo, hclV, hFdV, -, hFR⟩ := hpackage m
    exact hnhd (F m) V R hVo hclV hFdV hR hFR
  have hFd (m : ℕ) : DifferentiableOn ℂ (F m) U := by
    obtain ⟨V, -, hclV, hFdV, -, -⟩ := hpackage m
    exact hFdV.mono (subset_closure.trans hclV)
  have hconv : TendstoLocallyUniformlyOn F g atTop U := by
    simpa [F] using tendstoLocallyUniformlyOn_comp_radialContract z₀ hUo
      hg.continuousOn tendsto_standardRadialFactor
  have heval : Tendsto (fun m ↦ spectralJetEval A (F m)) atTop
      (nhds (spectralJetEval A g)) :=
    spectralJetEval_tendsto_of_tendstoLocallyUniformlyOn A hUo hFd
      (charpoly_roots_subset_of_spectrum_subset A hspec) hconv
  exact le_of_tendsto heval.norm (Eventually.of_forall hFbound)

end

end DiskRigidity.Complex
