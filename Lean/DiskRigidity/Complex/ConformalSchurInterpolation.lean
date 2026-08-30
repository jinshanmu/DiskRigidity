/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.BiholomorphicBasics
public import DiskRigidity.Complex.ExtremalSchur

/-!
# Finite Schur interpolation on a biholomorphic domain

This file transports finite confluent Schur interpolation and its extremal uniqueness statement
between an arbitrary planar domain and the unit disc. Repetition in the node list encodes higher
jets, exactly as in `DiskRigidity.Complex.FiniteSchurInterpolation`.
-/

open Filter Function Metric Set
open scoped Topology

namespace DiskRigidity.Complex

@[expose] public section

/-- The Schur class on an arbitrary planar domain. -/
def IsSchurOn (U : Set ℂ) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f U ∧ MapsTo f U (closedBall 0 1)

theorem IsSchurOn.differentiableOn {U : Set ℂ} {f : ℂ → ℂ} (hf : IsSchurOn U f) :
    DifferentiableOn ℂ f U :=
  hf.1

theorem IsSchurOn.norm_le {U : Set ℂ} {f : ℂ → ℂ} (hf : IsSchurOn U f)
    {z : ℂ} (hz : z ∈ U) : ‖f z‖ ≤ 1 := by
  simpa [mem_closedBall_zero_iff] using hf.2 hz

/-- A strict uniform bound on an arbitrary domain. -/
def HasStrictBoundOn (U : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ z ∈ U, ‖f z‖ ≤ r

/-- A feasible jet datum has minimal norm one on `U` when no Schur interpolant has a strict
uniform bound below one. -/
def HasMinimalNormOneJetsOn (U : Set ℂ) (nodes : List ℂ) (f : ℂ → ℂ) : Prop :=
  ¬ ∃ g : ℂ → ℂ, IsSchurOn U g ∧ JetEq nodes g f ∧ HasStrictBoundOn U g

/-- A bijection preserves the multiplicity of every node in a list. -/
theorem jetMultiplicity_map_of_injOn {U : Set ℂ} {phi : ℂ → ℂ}
    (hinj : InjOn phi U) {nodes : List ℂ} (hnodes : ∀ z ∈ nodes, z ∈ U)
    {z : ℂ} (hz : z ∈ U) :
    jetMultiplicity (nodes.map phi) (phi z) = jetMultiplicity nodes z := by
  induction nodes with
  | nil => simp [jetMultiplicity_nil]
  | cons a nodes ih =>
      have ha : a ∈ U := hnodes a (by simp)
      have htail : ∀ w ∈ nodes, w ∈ U := fun w hw ↦ hnodes w (by simp [hw])
      have heq : phi a = phi z ↔ a = z := ⟨hinj ha hz, congrArg phi⟩
      simp only [List.map_cons]
      rw [jetMultiplicity_cons, jetMultiplicity_cons, ih htail]
      simp only [heq]

/-- Pull a domain Schur function back to the unit disc through the set-theoretic inverse of a
biholomorphism. -/
theorem IsSchurOn.comp_invFunOn {U : Set ℂ} {phi f : ℂ → ℂ}
    (hU : IsOpen U) (hphi : DifferentiableOn ℂ phi U)
    (hbij : BijOn phi U (ball 0 1)) (hf : IsSchurOn U f) :
    IsSchur (f ∘ Function.invFunOn phi U) := by
  let psi := Function.invFunOn phi U
  have hpsi : DifferentiableOn ℂ psi (ball 0 1) :=
    differentiableOn_invFunOn_of_bijOn hU hphi hbij
  have hpsimaps : MapsTo psi (ball 0 1) U :=
    hbij.invOn_invFunOn.1.mapsTo hbij.surjOn
  exact ⟨hf.differentiableOn.comp hpsi hpsimaps, hf.2.comp hpsimaps⟩

/-- Push a disc Schur function forward along a biholomorphism. -/
theorem IsSchur.comp_biholomorphic {U : Set ℂ} {phi B : ℂ → ℂ}
    (hphi : DifferentiableOn ℂ phi U) (hbij : BijOn phi U (ball 0 1))
    (hB : IsSchur B) : IsSchurOn U (B ∘ phi) :=
  ⟨hB.differentiableOn.comp hphi hbij.mapsTo, hB.2.comp hbij.mapsTo⟩

/-- A strict disc bound pushes forward to the source domain. -/
theorem HasStrictDiscBound.comp_biholomorphic {U : Set ℂ} {phi B : ℂ → ℂ}
    (hbij : BijOn phi U (ball 0 1)) (hB : HasStrictDiscBound B) :
    HasStrictBoundOn U (B ∘ phi) := by
  obtain ⟨r, hr0, hr1, hr⟩ := hB
  exact ⟨r, hr0, hr1, fun z hz ↦ hr (phi z) (hbij.mapsTo hz)⟩

/-- A strict domain bound pulls back to the disc. -/
theorem HasStrictBoundOn.comp_invFunOn {U : Set ℂ} {phi f : ℂ → ℂ}
    (hbij : BijOn phi U (ball 0 1)) (hf : HasStrictBoundOn U f) :
    HasStrictDiscBound (f ∘ Function.invFunOn phi U) := by
  obtain ⟨r, hr0, hr1, hr⟩ := hf
  have hpsimaps : MapsTo (Function.invFunOn phi U) (ball 0 1) U :=
    hbij.invOn_invFunOn.1.mapsTo hbij.surjOn
  exact ⟨r, hr0, hr1, fun z hz ↦ hr _ (hpsimaps hz)⟩

/-- A jet identity on the disc pushes forward along a biholomorphism. -/
theorem JetEq.comp_biholomorphic {U : Set ℂ} {phi B f : ℂ → ℂ}
    (hU : IsOpen U) (hphi : DifferentiableOn ℂ phi U)
    (hbij : BijOn phi U (ball 0 1)) {nodes : List ℂ}
    (hnodes : ∀ z ∈ nodes, z ∈ U)
    (hjet : JetEq (nodes.map phi) B (f ∘ Function.invFunOn phi U)) :
    JetEq nodes (B ∘ phi) f := by
  intro z
  by_cases hzmem : z ∈ nodes
  · have hzU : z ∈ U := hnodes z hzmem
    have hphia : AnalyticAt ℂ phi z := hphi.analyticAt (hU.mem_nhds hzU)
    have hphid : deriv phi z ≠ 0 :=
      deriv_ne_zero_of_differentiableOn_of_injOn hU hphi hbij.injOn hzU
    have hleft := hbij.invOn_invFunOn.1
    have heq : ((B ∘ phi) - f) =ᶠ[𝓝 z]
        ((B - (f ∘ Function.invFunOn phi U)) ∘ phi) := by
      filter_upwards [hU.mem_nhds hzU] with w hw
      simp [hleft hw]
    have horder := hjet (phi z)
    rw [jetMultiplicity_map_of_injOn hbij.injOn hnodes hzU] at horder
    rw [analyticOrderAt_congr heq,
      analyticOrderAt_comp_of_deriv_ne_zero hphia hphid]
    exact horder
  · have hcount : jetMultiplicity nodes z = 0 := by
      classical
      exact List.count_eq_zero.mpr hzmem
    simp [hcount]

/-- A jet identity on the domain pulls back through the inverse biholomorphism. -/
theorem JetEq.comp_invFunOn {U : Set ℂ} {phi f g : ℂ → ℂ}
    (hU : IsOpen U) (hphi : DifferentiableOn ℂ phi U)
    (hbij : BijOn phi U (ball 0 1)) {nodes : List ℂ}
    (hnodes : ∀ z ∈ nodes, z ∈ U) (hjet : JetEq nodes f g) :
    JetEq (nodes.map phi) (f ∘ Function.invFunOn phi U)
      (g ∘ Function.invFunOn phi U) := by
  let psi := Function.invFunOn phi U
  have hpsidiff : DifferentiableOn ℂ psi (ball 0 1) :=
    differentiableOn_invFunOn_of_bijOn hU hphi hbij
  have hpsibij : BijOn psi (ball 0 1) U :=
    Set.BijOn.symm hbij.invOn_invFunOn.symm hbij
  intro w
  by_cases hwmem : w ∈ nodes.map phi
  · obtain ⟨z, hzmem, hzw⟩ := List.mem_map.mp hwmem
    subst w
    have hzU : z ∈ U := hnodes z hzmem
    have hphiD : phi z ∈ ball (0 : ℂ) 1 := hbij.mapsTo hzU
    have hpsia : AnalyticAt ℂ psi (phi z) :=
      hpsidiff.analyticAt (isOpen_ball.mem_nhds hphiD)
    have hpsid : deriv psi (phi z) ≠ 0 :=
      deriv_ne_zero_of_differentiableOn_of_injOn isOpen_ball hpsidiff hpsibij.injOn hphiD
    have hleft : psi (phi z) = z := hbij.invOn_invFunOn.1 hzU
    have heq : ((f ∘ psi) - (g ∘ psi)) = (f - g) ∘ psi := by
      funext y
      rfl
    rw [jetMultiplicity_map_of_injOn hbij.injOn hnodes hzU, heq,
      analyticOrderAt_comp_of_deriv_ne_zero hpsia hpsid, hleft]
    exact hjet z
  · have hcount : jetMultiplicity (nodes.map phi) w = 0 := by
      classical
      exact List.count_eq_zero.mpr hwmem
    simp [hcount]

/-- Finite confluent Schur interpolation on a biholomorphic planar domain. -/
theorem exists_schurFiniteBlaschke_comp_jetEq {U : Set ℂ} {phi f : ℂ → ℂ}
    (hU : IsOpen U) (hphi : DifferentiableOn ℂ phi U)
    (hbij : BijOn phi U (ball 0 1)) (nodes : List ℂ)
    (hnodes : ∀ z ∈ nodes, z ∈ U) (hf : IsSchurOn U f) :
    ∃ B : ℂ → ℂ, IsSchurFiniteBlaschke B ∧ JetEq nodes (B ∘ phi) f := by
  have hnodesD : ∀ w ∈ nodes.map phi, w ∈ ball (0 : ℂ) 1 := by
    intro w hw
    obtain ⟨z, hz, hzw⟩ := List.mem_map.mp hw
    rw [← hzw]
    exact hbij.mapsTo (hnodes z hz)
  have hF : IsSchur (f ∘ Function.invFunOn phi U) :=
    hf.comp_invFunOn hU hphi hbij
  obtain ⟨B, hB, hBjet⟩ :=
    exists_schurFiniteBlaschke_jetEq (nodes.map phi) hnodesD hF
  exact ⟨B, hB, hBjet.comp_biholomorphic hU hphi hbij hnodes⟩

/-- Derivative-facing form of finite confluent Schur interpolation on a biholomorphic domain. -/
theorem exists_schurFiniteBlaschke_comp_iteratedDeriv_eq
    {U : Set ℂ} {phi f : ℂ → ℂ}
    (hU : IsOpen U) (hphi : DifferentiableOn ℂ phi U)
    (hbij : BijOn phi U (ball 0 1)) (nodes : List ℂ)
    (hnodes : ∀ z ∈ nodes, z ∈ U) (hf : IsSchurOn U f) :
    ∃ B : ℂ → ℂ, IsSchurFiniteBlaschke B ∧
      ∀ z ∈ nodes, ∀ k < jetMultiplicity nodes z,
        iteratedDeriv k (B ∘ phi) z = iteratedDeriv k f z := by
  obtain ⟨B, hB, hjet⟩ :=
    exists_schurFiniteBlaschke_comp_jetEq hU hphi hbij nodes hnodes hf
  have hBU : IsSchurOn U (B ∘ phi) := hB.isSchur.comp_biholomorphic hphi hbij
  refine ⟨B, hB, fun z hz k hk ↦ ?_⟩
  exact hjet.iteratedDeriv_eq
    (hBU.differentiableOn.analyticAt (hU.mem_nhds (hnodes z hz)))
    (hf.differentiableOn.analyticAt (hU.mem_nhds (hnodes z hz))) hk

/-- Minimal norm one is preserved when a domain interpolation problem is pulled back to the unit
disc. -/
theorem HasMinimalNormOneJetsOn.comp_invFunOn {U : Set ℂ} {phi f : ℂ → ℂ}
    (hU : IsOpen U) (hphi : DifferentiableOn ℂ phi U)
    (hbij : BijOn phi U (ball 0 1)) {nodes : List ℂ}
    (hnodes : ∀ z ∈ nodes, z ∈ U) (hmin : HasMinimalNormOneJetsOn U nodes f) :
    HasMinimalNormOneJets (nodes.map phi) (f ∘ Function.invFunOn phi U) := by
  rintro ⟨G, hG, hGjet, hGbound⟩
  apply hmin
  exact ⟨G ∘ phi, hG.comp_biholomorphic hphi hbij,
    hGjet.comp_biholomorphic hU hphi hbij hnodes,
    hGbound.comp_biholomorphic hbij⟩

/-- Uniqueness of an extremal finite confluent Schur interpolation problem on a biholomorphic
domain. -/
theorem eqOn_of_hasMinimalNormOneJetsOn {U : Set ℂ} {phi f g : ℂ → ℂ}
    (hU : IsOpen U) (hphi : DifferentiableOn ℂ phi U)
    (hbij : BijOn phi U (ball 0 1)) (nodes : List ℂ)
    (hnodes : ∀ z ∈ nodes, z ∈ U) (hf : IsSchurOn U f) (hg : IsSchurOn U g)
    (hmin : HasMinimalNormOneJetsOn U nodes f) (hjet : JetEq nodes g f) :
    EqOn g f U := by
  let psi := Function.invFunOn phi U
  have hF : IsSchur (f ∘ psi) := hf.comp_invFunOn hU hphi hbij
  have hG : IsSchur (g ∘ psi) := hg.comp_invFunOn hU hphi hbij
  have hminD : HasMinimalNormOneJets (nodes.map phi) (f ∘ psi) :=
    hmin.comp_invFunOn hU hphi hbij hnodes
  have hjetD : JetEq (nodes.map phi) (g ∘ psi) (f ∘ psi) :=
    hjet.comp_invFunOn hU hphi hbij hnodes
  have heqD : EqOn (g ∘ psi) (f ∘ psi) (ball 0 1) :=
    eqOn_of_hasMinimalNormOneJets (nodes.map phi)
      (fun w hw ↦ by
        obtain ⟨z, hz, hzw⟩ := List.mem_map.mp hw
        rw [← hzw]
        exact hbij.mapsTo (hnodes z hz))
      hF hG hminD hjetD
  intro z hz
  have hphiD : phi z ∈ ball (0 : ℂ) 1 := hbij.mapsTo hz
  simpa [psi, hbij.invOn_invFunOn.1 hz] using heqD hphiD

/-- Existence of a finite Blaschke interpolant and uniqueness of every norm-one interpolant for an
extremal finite confluent problem on a biholomorphic planar domain. -/
theorem exists_schurFiniteBlaschke_comp_unique_of_hasMinimalNormOneJetsOn
    {U : Set ℂ} {phi f : ℂ → ℂ}
    (hU : IsOpen U) (hphi : DifferentiableOn ℂ phi U)
    (hbij : BijOn phi U (ball 0 1)) (nodes : List ℂ)
    (hnodes : ∀ z ∈ nodes, z ∈ U) (hf : IsSchurOn U f)
    (hmin : HasMinimalNormOneJetsOn U nodes f) :
    ∃ B : ℂ → ℂ, IsSchurFiniteBlaschke B ∧ JetEq nodes (B ∘ phi) f ∧
      ∀ g : ℂ → ℂ, IsSchurOn U g → JetEq nodes g f → EqOn g (B ∘ phi) U := by
  obtain ⟨B, hB, hBjet⟩ :=
    exists_schurFiniteBlaschke_comp_jetEq hU hphi hbij nodes hnodes hf
  have hBschur : IsSchurOn U (B ∘ phi) := hB.isSchur.comp_biholomorphic hphi hbij
  have hBf : EqOn (B ∘ phi) f U :=
    eqOn_of_hasMinimalNormOneJetsOn hU hphi hbij nodes hnodes hf hBschur hmin hBjet
  refine ⟨B, hB, hBjet, fun g hg hgjet z hz ↦ ?_⟩
  calc
    g z = f z := eqOn_of_hasMinimalNormOneJetsOn
      hU hphi hbij nodes hnodes hf hg hmin hgjet hz
    _ = (B ∘ phi) z := (hBf hz).symm

end

end DiskRigidity.Complex
