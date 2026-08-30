/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.ConformalSchurInterpolation
public import DiskRigidity.Complex.ConvexRiemannMap

/-!
# Finite Schur interpolation on bounded convex domains

These are the domain-facing existence and extremal-uniqueness forms: the Riemann map is produced
from bounded convexity rather than supplied as a hypothesis.
-/

open Function Metric Set

namespace DiskRigidity.Complex

@[expose] public section

/-- Every finite feasible family of jets on a bounded convex domain is realized by a finite
Schur--Blaschke function composed with a Riemann map. -/
theorem exists_riemannMap_schurFiniteBlaschke_comp_jetEq
    {U : Set ℂ} (hUo : IsOpen U) (hUc : Convex ℝ U) (hUne : U.Nonempty)
    (hUb : Bornology.IsBounded U) (nodes : List ℂ)
    (hnodes : ∀ z ∈ nodes, z ∈ U) {f : ℂ → ℂ} (hf : IsSchurOn U f) :
    ∃ phi B : ℂ → ℂ,
      DifferentiableOn ℂ phi U ∧ BijOn phi U (ball 0 1) ∧
        IsSchurFiniteBlaschke B ∧ JetEq nodes (B ∘ phi) f := by
  obtain ⟨z₀, hz₀⟩ := hUne
  obtain ⟨phi⟩ := exists_riemannMap_of_convex hUo hUc ⟨z₀, hz₀⟩ hUb hz₀
  obtain ⟨B, hB, hjet⟩ := exists_schurFiniteBlaschke_comp_jetEq
    hUo phi.differentiableOn phi.bijOn nodes hnodes hf
  exact ⟨phi.toFun, B, phi.differentiableOn, phi.bijOn, hB, hjet⟩

/-- Derivative-facing form of finite confluent interpolation on a bounded convex domain. -/
theorem exists_riemannMap_schurFiniteBlaschke_comp_iteratedDeriv_eq
    {U : Set ℂ} (hUo : IsOpen U) (hUc : Convex ℝ U) (hUne : U.Nonempty)
    (hUb : Bornology.IsBounded U) (nodes : List ℂ)
    (hnodes : ∀ z ∈ nodes, z ∈ U) {f : ℂ → ℂ} (hf : IsSchurOn U f) :
    ∃ phi B : ℂ → ℂ,
      DifferentiableOn ℂ phi U ∧ BijOn phi U (ball 0 1) ∧ IsSchurFiniteBlaschke B ∧
        ∀ z ∈ nodes, ∀ k < jetMultiplicity nodes z,
          iteratedDeriv k (B ∘ phi) z = iteratedDeriv k f z := by
  obtain ⟨z₀, hz₀⟩ := hUne
  obtain ⟨phi⟩ := exists_riemannMap_of_convex hUo hUc ⟨z₀, hz₀⟩ hUb hz₀
  obtain ⟨B, hB, hderiv⟩ := exists_schurFiniteBlaschke_comp_iteratedDeriv_eq
    hUo phi.differentiableOn phi.bijOn nodes hnodes hf
  exact ⟨phi.toFun, B, phi.differentiableOn, phi.bijOn, hB, hderiv⟩

/-- Extremal finite feasible jet data of minimal norm one on a bounded convex domain have a unique
Schur interpolant, and it is a finite Schur--Blaschke function composed with a Riemann map. -/
theorem exists_riemannMap_schurFiniteBlaschke_comp_unique_of_hasMinimalNormOneJetsOn
    {U : Set ℂ} (hUo : IsOpen U) (hUc : Convex ℝ U) (hUne : U.Nonempty)
    (hUb : Bornology.IsBounded U) (nodes : List ℂ)
    (hnodes : ∀ z ∈ nodes, z ∈ U) {f : ℂ → ℂ} (hf : IsSchurOn U f)
    (hmin : HasMinimalNormOneJetsOn U nodes f) :
    ∃ phi B : ℂ → ℂ,
      DifferentiableOn ℂ phi U ∧ BijOn phi U (ball 0 1) ∧
        IsSchurFiniteBlaschke B ∧ JetEq nodes (B ∘ phi) f ∧
          ∀ g : ℂ → ℂ, IsSchurOn U g → JetEq nodes g f → EqOn g (B ∘ phi) U := by
  obtain ⟨z₀, hz₀⟩ := hUne
  obtain ⟨phi⟩ := exists_riemannMap_of_convex hUo hUc ⟨z₀, hz₀⟩ hUb hz₀
  obtain ⟨B, hB, hjet, hunique⟩ :=
    exists_schurFiniteBlaschke_comp_unique_of_hasMinimalNormOneJetsOn
      hUo phi.differentiableOn phi.bijOn nodes hnodes hf hmin
  exact ⟨phi.toFun, B, phi.differentiableOn, phi.bijOn, hB, hjet, hunique⟩

end

end DiskRigidity.Complex
