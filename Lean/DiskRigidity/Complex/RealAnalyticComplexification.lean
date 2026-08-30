/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Complex.Basic

/-!
# Complexification of one-variable real-analytic complex-valued functions

A convergent real power series with complex coefficients has the same
positive convergence radius when its real variable is replaced by a complex
variable.  This gives the elementary one-variable complexification needed to
flatten a real-analytic planar arc.
-/

noncomputable section

open Filter Metric Set Topology

namespace DiskRigidity.Complex

@[expose] public section

/-- A complex-valued real-analytic function of one real variable agrees near
the base point with a holomorphic function of one complex variable. -/
theorem exists_complexification_of_analyticAt
    {f : ℝ → ℂ} {x : ℝ} (hf : AnalyticAt ℝ f x) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F (x : ℂ) ∧
      ∀ᶠ y : ℝ in nhds x, F (y : ℂ) = f y := by
  obtain ⟨p, hp⟩ := hf
  let q : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ p.coeff
  have hnorm (n : ℕ) : ‖q n‖ = ‖p n‖ := by
    simp [q, FormalMultilinearSeries.norm_apply_eq_norm_coef]
  have hqradius : q.radius = p.radius := by
    apply le_antisymm
    · exact FormalMultilinearSeries.radius_le_of_le fun n ↦ (hnorm n).ge
    · exact FormalMultilinearSeries.radius_le_of_le fun n ↦ (hnorm n).le
  have hqpos : 0 < q.radius := by
    rw [hqradius]
    exact hp.radius_pos
  let F : ℂ → ℂ := fun z ↦ q.sum (z - (x : ℂ))
  have hFanalytic : AnalyticAt ℂ F (x : ℂ) := by
    have hq := (q.hasFPowerSeriesOnBall hqpos).comp_sub (x : ℂ)
    simpa [F] using hq.analyticAt
  refine ⟨F, hFanalytic, ?_⟩
  filter_upwards [hp.eventually_hasSum_sub] with y hy
  have hqsum :
      HasSum (fun n : ℕ ↦ q n (fun _ : Fin n ↦ (y : ℂ) - (x : ℂ))) (f y) := by
    have hterms :
        (fun n : ℕ ↦ q n (fun _ : Fin n ↦ (y : ℂ) - (x : ℂ))) =
          fun n : ℕ ↦ p n (fun _ : Fin n ↦ y - x) := by
      funext n
      simp only [q, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
        FormalMultilinearSeries.coeff_ofScalars,
        Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_pow]
      ring
    rw [hterms]
    exact hy
  exact hqsum.tsum_eq

end

end DiskRigidity.Complex
