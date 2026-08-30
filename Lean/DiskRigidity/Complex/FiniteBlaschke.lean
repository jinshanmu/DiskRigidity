/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.AbsMax

/-!
# Finite Blaschke products

This file supplies the rational-inner functions used by finite Schur interpolation.  Roots are
indexed by a finite set, so repetitions encode multiplicity without a separate polynomial layer.
-/

open Metric Set
open scoped ComplexConjugate BigOperators

namespace DiskRigidity.Complex

@[expose] public section

/-- The elementary Blaschke factor with zero `a`. -/
noncomputable def blaschkeFactor (a z : ℂ) : ℂ :=
  (z - a) / (1 - conj a * z)

theorem blaschkeFactor_apply (a z : ℂ) :
    blaschkeFactor a z = (z - a) / (1 - conj a * z) :=
  rfl

/-- The denominator of a Blaschke factor does not vanish on the closed disc when its zero is in
the open disc. -/
theorem blaschkeFactor_den_ne_zero {a z : ℂ} (ha : a ∈ ball 0 1)
    (hz : z ∈ closedBall 0 1) : 1 - conj a * z ≠ 0 := by
  have ha' : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  have hz' : ‖z‖ ≤ 1 := by simpa [mem_closedBall_zero_iff] using hz
  have hprod : ‖conj a * z‖ < 1 := by
    rw [norm_mul, _root_.Complex.norm_conj]
    exact (mul_le_mul_of_nonneg_left hz' (norm_nonneg a)).trans_lt (by simpa using ha')
  intro hzero
  have hone : conj a * z = 1 := (sub_eq_zero.mp hzero).symm
  have := congrArg norm hone
  simp only [norm_one] at this
  exact (ne_of_lt hprod) this

/-- A Blaschke factor is holomorphic in a neighbourhood of the closed unit disc. -/
theorem analyticOnNhd_blaschkeFactor {a : ℂ} (ha : a ∈ ball 0 1) :
    AnalyticOnNhd ℂ (blaschkeFactor a) (closedBall 0 1) := by
  intro z hz
  change AnalyticAt ℂ (fun w ↦ (w - a) / (1 - conj a * w)) z
  fun_prop (disch := exact blaschkeFactor_den_ne_zero ha hz)

/-- The only zero of an elementary factor in the open unit disc is its prescribed zero. -/
theorem blaschkeFactor_eq_zero_iff {a z : ℂ} (ha : a ∈ ball 0 1)
    (hz : z ∈ ball 0 1) : blaschkeFactor a z = 0 ↔ z = a := by
  rw [blaschkeFactor_apply, div_eq_zero_iff]
  rw [or_iff_left (blaschkeFactor_den_ne_zero ha (ball_subset_closedBall hz))]
  exact sub_eq_zero

/-- An elementary Blaschke factor has modulus one on the unit circle. -/
theorem norm_blaschkeFactor_eq_one {a z : ℂ} (ha : a ∈ ball 0 1)
    (hz : z ∈ sphere 0 1) : ‖blaschkeFactor a z‖ = 1 := by
  have hza : z - a ≠ 0 := by
    intro h
    have hza' : z = a := sub_eq_zero.mp h
    have hz' : ‖z‖ = 1 := by simpa [mem_sphere_zero_iff_norm] using hz
    have ha' : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
    rw [hza'] at hz'
    exact ha'.ne hz'
  have hden : 1 - conj a * z ≠ 0 :=
    blaschkeFactor_den_ne_zero ha (sphere_subset_closedBall hz)
  have hcanonical := _root_.Complex.norm_canonicalFactor_eval_circle_eq_one ha hz
  norm_num [_root_.Complex.canonicalFactor_apply] at hcanonical
  rw [div_eq_one_iff_eq (norm_ne_zero_iff.mpr hza)] at hcanonical
  rw [blaschkeFactor_apply, norm_div,
    div_eq_one_iff_eq (norm_ne_zero_iff.mpr hden)]
  exact hcanonical.symm

/-- A finite Blaschke product with zero family `a` and unimodular leading coefficient `c`. -/
noncomputable def finiteBlaschkeProduct {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (c : ℂ) (z : ℂ) : ℂ :=
  c * ∏ i ∈ s, blaschkeFactor (a i) z

theorem finiteBlaschkeProduct_apply {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (c z : ℂ) :
    finiteBlaschkeProduct s a c z = c * ∏ i ∈ s, blaschkeFactor (a i) z :=
  rfl

/-- A finite Blaschke product is holomorphic in a neighbourhood of the closed unit disc. -/
theorem analyticOnNhd_finiteBlaschkeProduct {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (c : ℂ) (ha : ∀ i ∈ s, a i ∈ ball 0 1) :
    AnalyticOnNhd ℂ (finiteBlaschkeProduct s a c) (closedBall 0 1) := by
  intro z hz
  unfold finiteBlaschkeProduct
  have hprod := Finset.analyticAt_prod s fun i hi ↦
    (analyticOnNhd_blaschkeFactor (ha i hi)) z hz
  have hc : AnalyticAt ℂ (fun _ : ℂ ↦ c) z := analyticAt_const
  exact (hc.mul hprod).congr <| .of_forall fun w ↦ by
    simp only [Pi.mul_apply, Finset.prod_apply]

/-- Every finite Blaschke product has modulus one on the unit circle. -/
theorem norm_finiteBlaschkeProduct_eq_one {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (c z : ℂ) (hc : ‖c‖ = 1) (ha : ∀ i ∈ s, a i ∈ ball 0 1)
    (hz : z ∈ sphere 0 1) : ‖finiteBlaschkeProduct s a c z‖ = 1 := by
  rw [finiteBlaschkeProduct_apply, norm_mul, norm_prod, hc]
  simp only [one_mul]
  exact Finset.prod_eq_one fun i hi ↦ norm_blaschkeFactor_eq_one (ha i hi) hz

/-- A finite Blaschke product maps the closed unit disc to itself. -/
theorem mapsTo_closedBall_finiteBlaschkeProduct {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (c : ℂ) (hc : ‖c‖ = 1) (ha : ∀ i ∈ s, a i ∈ ball 0 1) :
    MapsTo (finiteBlaschkeProduct s a c) (closedBall 0 1) (closedBall 0 1) := by
  have han := analyticOnNhd_finiteBlaschkeProduct s a c ha
  have hdiff : DiffContOnCl ℂ (finiteBlaschkeProduct s a c) (ball 0 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact han.differentiableOn
  intro z hz
  rw [mem_closedBall_zero_iff]
  apply _root_.Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdiff
  · intro w hw
    have hws : w ∈ sphere (0 : ℂ) 1 := by
      rwa [frontier_ball (0 : ℂ) one_ne_zero] at hw
    exact (norm_finiteBlaschkeProduct_eq_one s a c w hc ha hws).le
  · simpa [closure_ball (0 : ℂ) one_ne_zero] using hz

/-- A finite Blaschke product maps the open unit disc to the closed unit disc. -/
theorem mapsTo_ball_closedBall_finiteBlaschkeProduct {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (c : ℂ) (hc : ‖c‖ = 1) (ha : ∀ i ∈ s, a i ∈ ball 0 1) :
    MapsTo (finiteBlaschkeProduct s a c) (ball 0 1) (closedBall 0 1) :=
  (mapsTo_closedBall_finiteBlaschkeProduct s a c hc ha).mono ball_subset_closedBall subset_rfl

end

end DiskRigidity.Complex
