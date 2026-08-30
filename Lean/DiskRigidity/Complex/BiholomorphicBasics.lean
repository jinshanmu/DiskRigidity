/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.LocalInjectivity
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Elementary packaging of planar biholomorphisms
-/

open Function Metric Set

namespace DiskRigidity.Complex

@[expose] public section

/-- The image of an open subset of the plane under an injective holomorphic map is open. -/
theorem isOpen_image_of_differentiableOn_of_injOn {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) : IsOpen (f '' U) := by
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z hz
  have hz' : z ∈ ball z ε := mem_ball_self hε
  have hana : AnalyticOnNhd ℂ f (ball z ε) :=
    ((hf.mono hball).analyticOnNhd isOpen_ball)
  have hnc : ¬ ∃ w, ∀ y ∈ ball z ε, f y = w := by
    rintro ⟨w, hw⟩
    have hshift : z + ((ε / 2 : ℝ) : ℂ) ∈ ball z ε := by
      have hdist : dist (z + ((ε / 2 : ℝ) : ℂ)) z = ε / 2 := by
        simpa [dist_eq_norm] using hε.le
      rw [mem_ball, hdist]
      linarith
    have hne : ((ε / 2 : ℝ) : ℂ) ≠ 0 := _root_.Complex.ofReal_ne_zero.mpr (by positivity)
    have heq := hinj (hball hz') (hball hshift) ((hw z hz').trans (hw _ hshift).symm)
    exact hne (by simpa using heq)
  rcases hana.is_constant_or_isOpen (convex_ball z ε).isPreconnected with hconst | hopen
  · exact absurd hconst hnc
  · exact ⟨f '' ball z ε, image_mono hball, hopen _ subset_rfl isOpen_ball,
      ⟨z, hz', rfl⟩⟩

/-- Restricted to its open domain, an injective holomorphic map is open. -/
theorem isOpenMap_domRestrict_of_differentiableOn_of_injOn {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) :
    IsOpenMap (U.domRestrict f) := by
  intro V hV
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.mp hV
  rw [Set.image_domRestrict]
  exact isOpen_image_of_differentiableOn_of_injOn (hW.inter hU)
    (hf.mono inter_subset_right) (hinj.mono inter_subset_right)

/-- A holomorphic bijection between planar open sets, packaged as a homeomorphism of subtypes. -/
noncomputable def homeomorphOfDifferentiableOnBijOn {U V : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U V) : U ≃ₜ V :=
  let e := hbij.equiv f
  e.toHomeomorphOfContinuousOpen
    (by
      change Continuous (V.codRestrict (U.domRestrict f) fun z => hbij.mapsTo z.2)
      exact (continuousOn_iff_continuous_domRestrict.mp hf.continuousOn).subtype_mk _)
    (by
      change IsOpenMap (V.codRestrict (U.domRestrict f) fun z => hbij.mapsTo z.2)
      exact (isOpenMap_domRestrict_of_differentiableOn_of_injOn hU hf hbij.injOn).codRestrict _)

@[simp]
theorem homeomorphOfDifferentiableOnBijOn_apply {U V : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U V) (z : U) :
    ((homeomorphOfDifferentiableOnBijOn hU hf hbij z : V) : ℂ) = f z :=
  rfl

/-- An injective holomorphic map on an open set has nonzero derivative there. -/
theorem deriv_ne_zero_of_differentiableOn_of_injOn {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    {z : ℂ} (hz : z ∈ U) : deriv f z ≠ 0 := by
  have hfz : AnalyticAt ℂ f z := hf.analyticAt (hU.mem_nhds hz)
  exact (exists_injOn_nhds_iff_deriv_ne_zero hfz).mp ⟨U, hU.mem_nhds hz, hinj⟩

/-- The set-theoretic inverse of an injective holomorphic map on an open set is holomorphic on its
image. -/
theorem differentiableOn_invFunOn {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) :
    DifferentiableOn ℂ (Function.invFunOn f U) (f '' U) := by
  rintro _ ⟨z, hz, rfl⟩
  have hfz : AnalyticAt ℂ f z := hf.analyticAt (hU.mem_nhds hz)
  have hderiv : deriv f z ≠ 0 :=
    deriv_ne_zero_of_differentiableOn_of_injOn hU hf hinj hz
  have hleft : (Function.invFunOn f U ∘ f) =ᶠ[nhds z] id := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hinj.leftInvOn_invFunOn hw
  have hcomp : AnalyticAt ℂ (Function.invFunOn f U ∘ f) z :=
    analyticAt_id.congr hleft.symm
  exact ((analyticAt_comp_iff_of_deriv_ne_zero hfz hderiv).mp hcomp).differentiableAt
    |>.differentiableWithinAt

/-- Inverse holomorphy with the image identified by a bijection hypothesis. -/
theorem differentiableOn_invFunOn_of_bijOn {U V : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U V) :
    DifferentiableOn ℂ (Function.invFunOn f U) V := by
  rw [← hbij.image_eq]
  exact differentiableOn_invFunOn hU hf hbij.injOn

end

end DiskRigidity.Complex
