/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Analysis.TransferZeros
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Polynomial.Basic

/-!
# The full rational lemniscate

This file formalizes Proposition 6.3.  Rational sublevel and level sets carry
an explicit nonvanishing condition on the denominator; this records poles
correctly, rather than using the field convention `a / 0 = 0`.
-/

@[expose] public section

noncomputable section

open Bornology Filter Metric Polynomial Set
open scoped Topology

namespace DiskRigidity.Analysis

/-- The finite part of `{|U/V| < 1}`. -/
def rationalSublevel (U V : ℂ[X]) : Set ℂ :=
  {z | V.eval z ≠ 0 ∧ ‖U.eval z / V.eval z‖ < 1}

/-- The finite part of `{|U/V| = 1}`. -/
def rationalLevel (U V : ℂ[X]) : Set ℂ :=
  {z | V.eval z ≠ 0 ∧ ‖U.eval z / V.eval z‖ = 1}

/-- Outside a compact convex set, the reciprocal reduced rational function
has modulus at most one.  This is the maximum-modulus argument at infinity
used implicitly in the component proof of Proposition 6.3. -/
theorem norm_denominator_div_numerator_le_one_off_convex
    {K : Set ℂ} (hKcompact : IsCompact K) {U V : ℂ[X]}
    (hdeg : V.natDegree < U.natDegree)
    (hzeros : ∀ z, U.eval z = 0 → z ∈ interior K)
    (hlevel : ∀ z ∈ frontier K, ‖U.eval z‖ = ‖V.eval z‖)
    {z : ℂ} (hz : z ∉ K) : ‖V.eval z / U.eval z‖ ≤ 1 := by
  have hU : U ≠ 0 := by
    intro h
    simp [h] at hdeg
  have hdegree : V.degree < U.degree := Polynomial.degree_lt_degree hdeg
  have heventually : ∀ᶠ w : ℂ in cobounded ℂ,
      ‖V.eval w‖ ≤ ‖U.eval w‖ :=
    (Polynomial.isLittleO_cobounded_of_degree_lt hdegree).eventuallyLE
  obtain ⟨R₀, -, hR₀⟩ :=
    Filter.hasBasis_cobounded_norm.eventually_iff.mp heventually
  obtain ⟨R₁, hKR₁⟩ := hKcompact.isBounded.subset_ball (0 : ℂ)
  let R : ℝ := max R₀ (max R₁ ‖z‖) + 1
  have hR₀R : R₀ < R := by
    dsimp only [R]
    linarith [le_max_left R₀ (max R₁ ‖z‖)]
  have hR₁R : R₁ < R := by
    dsimp only [R]
    linarith [le_max_left R₁ ‖z‖,
      le_max_right R₀ (max R₁ ‖z‖)]
  have hzR : ‖z‖ < R := by
    dsimp only [R]
    linarith [le_max_right R₁ ‖z‖,
      le_max_right R₀ (max R₁ ‖z‖)]
  let O : Set ℂ := ball 0 R ∩ Kᶜ
  let g : ℂ → ℂ := fun w ↦ V.eval w / U.eval w
  have hOsub : O ⊆ (interior K)ᶜ := by
    rintro w ⟨-, hwK⟩ hwint
    exact hwK (interior_subset hwint)
  have hclosureOsub : closure O ⊆ (interior K)ᶜ :=
    closure_minimal hOsub (isClosed_compl_iff.mpr isOpen_interior)
  have hUne : ∀ w ∈ closure O, U.eval w ≠ 0 := by
    intro w hw hUw
    exact hclosureOsub hw (hzeros w hUw)
  have hgdiff : DiffContOnCl ℂ g O := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    exact (V.differentiableAt.div U.differentiableAt (hUne w hw)).differentiableWithinAt
  have hObounded : IsBounded O := isBounded_ball.subset inter_subset_left
  have hfrontier : ∀ w ∈ frontier O, ‖g w‖ ≤ 1 := by
    intro w hw
    have hwcases := frontier_inter_subset (ball (0 : ℂ) R) Kᶜ hw
    rcases hwcases with hwball | hwK
    · have hwnorm : ‖w‖ = R := by
        exact mem_sphere_zero_iff_norm.mp
          (frontier_ball_subset_sphere hwball.1)
      have hwoutside : w ∉ K := by
        intro hwmem
        have hwlt := hKR₁ hwmem
        rw [mem_ball_zero_iff, hwnorm] at hwlt
        linarith
      have hUw : U.eval w ≠ 0 := by
        intro hzero
        exact hwoutside (interior_subset (hzeros w hzero))
      have hVU : ‖V.eval w‖ ≤ ‖U.eval w‖ :=
        hR₀ (by
          change R₀ ≤ ‖w‖
          rw [hwnorm]
          exact hR₀R.le)
      simp only [g, norm_div]
      exact (div_le_one (norm_pos_iff.mpr hUw)).mpr hVU
    · have hwfrontier : w ∈ frontier K := by
        simpa only [frontier_compl] using hwK.2
      have hUw : U.eval w ≠ 0 := by
        intro hzero
        exact (mem_interior_iff_notMem_frontier
          (interior_subset (hzeros w hzero))).mp (hzeros w hzero) hwfrontier
      simp only [g, norm_div]
      rw [← hlevel w hwfrontier]
      exact div_self (norm_ne_zero_iff.mpr hUw) ▸ le_rfl
  have hzO : z ∈ O := by
    exact ⟨by simpa [mem_ball_zero_iff] using hzR, hz⟩
  exact Complex.norm_le_of_forall_mem_frontier_norm_le hObounded hgdiff hfrontier
    (subset_closure hzO)

/-- The exterior estimate is strict.  Equality would be a local maximum of
the reciprocal quotient; the strong maximum-modulus principle would make a
polynomial of smaller degree a scalar multiple of the numerator. -/
theorem norm_denominator_div_numerator_lt_one_off_convex
    {K : Set ℂ} (hKcompact : IsCompact K) {U V : ℂ[X]}
    (hdeg : V.natDegree < U.natDegree)
    (hzeros : ∀ z, U.eval z = 0 → z ∈ interior K)
    (hlevel : ∀ z ∈ frontier K, ‖U.eval z‖ = ‖V.eval z‖)
    {z : ℂ} (hz : z ∉ K) : ‖V.eval z / U.eval z‖ < 1 := by
  let g : ℂ → ℂ := fun w ↦ V.eval w / U.eval w
  have hle : ‖g z‖ ≤ 1 :=
    norm_denominator_div_numerator_le_one_off_convex hKcompact hdeg hzeros hlevel hz
  by_contra hnlt
  have heq : ‖g z‖ = 1 := le_antisymm hle (le_of_not_gt hnlt)
  have hcompl : Kᶜ ∈ 𝓝 z := hKcompact.isClosed.isOpen_compl.mem_nhds hz
  have hlocal : IsLocalMax (norm ∘ g) z := by
    filter_upwards [hcompl] with w hw
    change ‖g w‖ ≤ ‖g z‖
    rw [heq]
    exact norm_denominator_div_numerator_le_one_off_convex
      hKcompact hdeg hzeros hlevel hw
  have hdiff : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ g w := by
    filter_upwards [hcompl] with w hw
    have hUw : U.eval w ≠ 0 := by
      intro hzero
      exact hw (interior_subset (hzeros w hzero))
    exact V.differentiableAt.div U.differentiableAt hUw
  have hgeq : g =ᶠ[𝓝 z] fun _ ↦ g z :=
    Complex.eventually_eq_of_isLocalMax_norm hdiff hlocal
  have hcross : (fun w ↦ V.eval w) =ᶠ[𝓝 z]
      fun w ↦ g z * U.eval w := by
    filter_upwards [hgeq, hcompl] with w hgw hw
    have hUw : U.eval w ≠ 0 := by
      intro hzero
      exact hw (interior_subset (hzeros w hzero))
    exact (div_eq_iff hUw).mp hgw
  have hVanalytic : AnalyticOnNhd ℂ (fun w ↦ V.eval w) univ :=
    AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) V
  have hUanalytic : AnalyticOnNhd ℂ (fun w ↦ g z * U.eval w) univ :=
    analyticOnNhd_const.mul (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) U)
  have hfun : (fun w ↦ V.eval w) = (fun w ↦ g z * U.eval w) :=
    hVanalytic.eq_of_eventuallyEq hUanalytic hcross
  have hpoly : V = Polynomial.C (g z) * U := by
    apply Polynomial.funext
    intro w
    simpa using congrFun hfun w
  have hgz : g z ≠ 0 := by
    exact norm_ne_zero_iff.mp (by rw [heq]; exact one_ne_zero)
  have hU : U ≠ 0 := by
    intro hzero
    simp [hzero] at hdeg
  have hdegreeEq : V.natDegree = U.natDegree := by
    rw [hpoly, Polynomial.natDegree_mul]
    · simp
    · exact Polynomial.C_ne_zero.mpr hgz
    · exact hU
  exact (Nat.ne_of_lt hdeg) hdegreeEq

/-- Equivalently, the original reduced rational function has modulus greater
than one at every finite exterior point which is not a pole. -/
theorem one_lt_norm_numerator_div_denominator_off_convex
    {K : Set ℂ} (hKcompact : IsCompact K) {U V : ℂ[X]}
    (hdeg : V.natDegree < U.natDegree)
    (hzeros : ∀ z, U.eval z = 0 → z ∈ interior K)
    (hlevel : ∀ z ∈ frontier K, ‖U.eval z‖ = ‖V.eval z‖)
    {z : ℂ} (hz : z ∉ K) (hVz : V.eval z ≠ 0) :
    1 < ‖U.eval z / V.eval z‖ := by
  have hUz : U.eval z ≠ 0 := by
    intro hzero
    exact hz (interior_subset (hzeros z hzero))
  have hrec := norm_denominator_div_numerator_lt_one_off_convex
    hKcompact hdeg hzeros hlevel hz
  have hVU : ‖V.eval z‖ < ‖U.eval z‖ := by
    apply (div_lt_one (norm_pos_iff.mpr hUz)).mp
    simpa only [norm_div] using hrec
  rw [norm_div]
  exact (one_lt_div (norm_pos_iff.mpr hVz)).mpr hVU

/-- Proposition 6.3's two set identities. -/
theorem full_level_identity
    {K : Set ℂ} (hKcompact : IsCompact K) {U V : ℂ[X]}
    (hdeg : V.natDegree < U.natDegree)
    (hzeros : ∀ z, U.eval z = 0 → z ∈ interior K)
    (hpoles : ∀ z, V.eval z = 0 → z ∉ K)
    (hinner : ∀ z ∈ interior K,
      V.eval z ≠ 0 ∧ ‖U.eval z / V.eval z‖ < 1)
    (hlevel : ∀ z ∈ frontier K, ‖U.eval z‖ = ‖V.eval z‖) :
    rationalSublevel U V = interior K ∧
      rationalLevel U V = frontier K := by
  have hclosed : IsClosed K := hKcompact.isClosed
  constructor
  · ext z
    constructor
    · rintro ⟨hVz, hzlt⟩
      by_cases hzK : z ∈ K
      · apply (mem_interior_iff_notMem_frontier hzK).mpr
        intro hzfrontier
        have hnormeq : ‖U.eval z / V.eval z‖ = 1 := by
          rw [norm_div, hlevel z hzfrontier]
          exact div_self (norm_ne_zero_iff.mpr hVz)
        linarith
      · have hzgt := one_lt_norm_numerator_div_denominator_off_convex
          hKcompact hdeg hzeros hlevel hzK hVz
        linarith
    · intro hzint
      exact hinner z hzint
  · ext z
    constructor
    · rintro ⟨hVz, hzone⟩
      have hzK : z ∈ K := by
        by_contra hzK
        have hzgt := one_lt_norm_numerator_div_denominator_off_convex
          hKcompact hdeg hzeros hlevel hzK hVz
        linarith
      apply (mem_frontier_iff_notMem_interior hzK).mpr
      intro hzint
      have hzlt := (hinner z hzint).2
      linarith
    · intro hzfrontier
      have hzK : z ∈ K := by
        rw [← hclosed.closure_eq]
        exact frontier_subset_closure hzfrontier
      have hVz : V.eval z ≠ 0 := by
        intro hzero
        exact hpoles z hzero hzK
      refine ⟨hVz, ?_⟩
      rw [norm_div, hlevel z hzfrontier]
      exact div_self (norm_ne_zero_iff.mpr hVz)

end DiskRigidity.Analysis
