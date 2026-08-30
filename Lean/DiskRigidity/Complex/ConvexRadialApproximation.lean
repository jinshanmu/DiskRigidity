/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module


public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Radial approximation on an open convex domain

Contracting the closure of an open convex set toward an interior point lands
strictly inside the set.  Consequently, a bounded holomorphic function on the
open set becomes holomorphic on a neighborhood of the closure after radial
contraction, without increasing its bound.  This is the elementary convex
replacement for the Riemann-map radial approximation used in the manuscript's
passage from `A(K)` to `H∞`.
-/

noncomputable section

open Filter Function Metric Set Topology

namespace DiskRigidity.Complex

@[expose] public section

/-- Affine contraction toward `z₀` by the real factor `r`. -/
def radialContract (z₀ : ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  (1 - r) • z₀ + r • z

theorem continuous_radialContract (z₀ : ℂ) (r : ℝ) :
    Continuous (radialContract z₀ r) := by
  unfold radialContract
  fun_prop

theorem differentiable_radialContract (z₀ : ℂ) (r : ℝ) :
    Differentiable ℂ (radialContract z₀ r) := by
  exact (differentiable_const ((1 - r) • z₀)).add
    (differentiable_id.const_smul r)

theorem dist_radialContract (z₀ z : ℂ) (r : ℝ) :
    dist z (radialContract z₀ r z) = |1 - r| * dist z z₀ := by
  rw [dist_eq_norm, dist_eq_norm]
  have hsub : z - radialContract z₀ r z = (1 - r) • (z - z₀) := by
    unfold radialContract
    module
  rw [hsub, norm_smul, Real.norm_eq_abs]

/-- Every point of the closure contracts strictly into an open convex set. -/
theorem radialContract_mem_of_mem_closure {U : Set ℂ} {z₀ : ℂ} {r : ℝ}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hz₀ : z₀ ∈ U)
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) {z : ℂ} (hz : z ∈ closure U) :
    radialContract z₀ r z ∈ U := by
  rw [← hUo.interior_eq] at hz₀ ⊢
  exact hUc.combo_interior_closure_mem_interior hz₀ hz
    (sub_pos.mpr hr₁) hr₀ (by ring)

/-- The maximal open set on which the contracted argument lies in `U`. -/
def radialAnalyticDomain (U : Set ℂ) (z₀ : ℂ) (r : ℝ) : Set ℂ :=
  radialContract z₀ r ⁻¹' U

theorem isOpen_radialAnalyticDomain {U : Set ℂ} (hU : IsOpen U)
    (z₀ : ℂ) (r : ℝ) :
    IsOpen (radialAnalyticDomain U z₀ r) :=
  hU.preimage (continuous_radialContract z₀ r)

theorem closure_subset_radialAnalyticDomain {U : Set ℂ} {z₀ : ℂ} {r : ℝ}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hz₀ : z₀ ∈ U)
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    closure U ⊆ radialAnalyticDomain U z₀ r := by
  intro z hz
  exact radialContract_mem_of_mem_closure hUo hUc hz₀ hr₀ hr₁ hz

/-- A holomorphic function becomes holomorphic on a neighborhood of the
closed convex set after radial contraction. -/
theorem differentiableOn_radialAnalyticDomain {U : Set ℂ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (z₀ : ℂ) (r : ℝ) :
    DifferentiableOn ℂ (f ∘ radialContract z₀ r)
      (radialAnalyticDomain U z₀ r) := by
  exact hf.comp (differentiable_radialContract z₀ r).differentiableOn
    (fun _ hz ↦ hz)

/-- Radial contraction preserves every uniform bound on the original domain,
including on the closure of the contracted domain. -/
theorem norm_radialContract_le_on_closure {U : Set ℂ} {f : ℂ → ℂ}
    {z₀ : ℂ} {r R : ℝ}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hz₀ : z₀ ∈ U)
    (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (hfR : ∀ z ∈ U, ‖f z‖ ≤ R) :
    ∀ z ∈ closure U, ‖(f ∘ radialContract z₀ r) z‖ ≤ R := by
  intro z hz
  exact hfR _ (radialContract_mem_of_mem_closure hUo hUc hz₀ hr₀ hr₁ hz)

/-- Complete radial-approximation package: the contracted function is
holomorphic on an explicit open neighborhood of the closure, continuous on
the closure, and obeys the original bound there. -/
theorem radial_holomorphicOnNhd_closure {U : Set ℂ} {f : ℂ → ℂ}
    {z₀ : ℂ} {r R : ℝ}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hz₀ : z₀ ∈ U)
    (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (hf : DifferentiableOn ℂ f U) (hfR : ∀ z ∈ U, ‖f z‖ ≤ R) :
    ∃ V : Set ℂ, IsOpen V ∧ closure U ⊆ V ∧
      DifferentiableOn ℂ (f ∘ radialContract z₀ r) V ∧
      ContinuousOn (f ∘ radialContract z₀ r) (closure U) ∧
      ∀ z ∈ closure U, ‖(f ∘ radialContract z₀ r) z‖ ≤ R := by
  refine ⟨radialAnalyticDomain U z₀ r, isOpen_radialAnalyticDomain hUo z₀ r,
    closure_subset_radialAnalyticDomain hUo hUc hz₀ hr₀ hr₁,
    differentiableOn_radialAnalyticDomain hf z₀ r, ?_,
    norm_radialContract_le_on_closure hUo hUc hz₀ hr₀ hr₁ hfR⟩
  exact (differentiableOn_radialAnalyticDomain hf z₀ r).continuousOn.mono
    (closure_subset_radialAnalyticDomain hUo hUc hz₀ hr₀ hr₁)

/-- As the contraction factor tends to one, radial contractions of a
continuous function converge locally uniformly on its open domain. -/
theorem tendstoLocallyUniformlyOn_comp_radialContract
    {ι : Type*} {l : Filter ι} {r : ι → ℝ} {U : Set ℂ}
    {f : ℂ → ℂ} (z₀ : ℂ) (hUo : IsOpen U)
    (hf : ContinuousOn f U) (hr : Tendsto r l (nhds 1)) :
    TendstoLocallyUniformlyOn
      (fun i ↦ f ∘ radialContract z₀ (r i)) f l U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hUo]
  intro K hKU hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_cases hKne : K.Nonempty
  · obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hUo hKU
    have hfuc : UniformContinuousOn f L :=
      hL.uniformContinuousOn_of_continuous (hf.mono hLU)
    obtain ⟨η, hη, hfη⟩ := Metric.uniformContinuousOn_iff.mp hfuc ε hε
    obtain ⟨δ, hδ, hδL⟩ :=
      hK.exists_cthickening_subset_open isOpen_interior hKL
    obtain ⟨w, hwK, hwmax⟩ := hK.exists_isMaxOn hKne
      (continuous_id.dist (continuous_const : Continuous fun _ : ℂ ↦ z₀)).continuousOn
    have hcoef : Tendsto (fun i ↦ |1 - r i| * dist w z₀) l (nhds 0) := by
      simpa only [sub_self, abs_zero, zero_mul] using
        (((tendsto_const_nhds :
          Tendsto (fun _ : ι ↦ (1 : ℝ)) l (nhds 1)).sub hr).abs.mul
          (tendsto_const_nhds :
            Tendsto (fun _ : ι ↦ dist w z₀) l (nhds (dist w z₀))))
    filter_upwards [hcoef (Iio_mem_nhds (lt_min hδ hη))] with i hi
    intro z hzK
    have hdist : dist z (radialContract z₀ (r i) z) < min δ η := by
      rw [dist_radialContract]
      exact (mul_le_mul_of_nonneg_left (hwmax hzK) (abs_nonneg _)).trans_lt hi
    have hradL : radialContract z₀ (r i) z ∈ L := by
      apply interior_subset
      apply hδL
      apply mem_cthickening_of_dist_le (radialContract z₀ (r i) z) z δ K hzK
      rw [dist_comm]
      exact hdist.le.trans (min_le_left δ η)
    have hzL : z ∈ L := interior_subset (hKL hzK)
    exact hfη z hzL (radialContract z₀ (r i) z) hradL
      (hdist.trans_le (min_le_right δ η))
  · have hKempty : K = ∅ := not_nonempty_iff_eq_empty.mp hKne
    subst K
    exact Eventually.of_forall fun _ z hz ↦ hz.elim

end

end DiskRigidity.Complex
