/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.ConvexSchurInterpolation
public import DiskRigidity.Complex.SchurMontel
public import DiskRigidity.Complex.SpectralJets

/-!
# Holomorphic matrix extremizers

Montel selection and the finite characteristic spectral jet turn a maximizing
sequence in the Schur class into an attained matrix norm.  The finite Schur
algorithm then replaces the maximizer by a finite Blaschke product composed
with a Riemann map, without changing its matrix value.
-/

noncomputable section

open Filter Function Metric Set Topology
open scoped Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Complex

@[expose] public section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrix norms obtained from the Schur class on a domain. -/
def schurSpectralEvalNorms (A : Operator.SquareMatrix n) (U : Set ℂ) : Set ℝ :=
  {r | ∃ f : ℂ → ℂ, IsSchurOn U f ∧ ‖spectralJetEval A f‖ = r}

/-- The norm of the finite spectral-jet functional calculus on the Schur class. -/
def holomorphicCalculusNorm (A : Operator.SquareMatrix n) (U : Set ℂ) : ℝ :=
  sSup (schurSpectralEvalNorms A U)

theorem schurSpectralEvalNorms_nonempty (A : Operator.SquareMatrix n) (U : Set ℂ) :
    (schurSpectralEvalNorms A U).Nonempty := by
  refine ⟨‖spectralJetEval A (fun _ ↦ 0)‖, fun _ ↦ 0, ?_, rfl⟩
  exact ⟨differentiableOn_const (c := 0), fun _ _ ↦ by simp⟩

theorem charpoly_roots_subset_of_spectrum_subset
    (A : Operator.SquareMatrix n) {U : Set ℂ}
    (hspec : spectrum ℂ A ⊆ U) : ∀ z ∈ A.charpoly.roots, z ∈ U := by
  intro z hz
  apply hspec
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  exact (Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero).mp hz

theorem spectralJetNodes_subset_of_spectrum_subset
    (A : Operator.SquareMatrix n) {U : Set ℂ}
    (hspec : spectrum ℂ A ⊆ U) : ∀ z ∈ spectralJetNodes A, z ∈ U := by
  intro z hz
  apply charpoly_roots_subset_of_spectrum_subset A hspec z
  exact Multiset.mem_toList.mp hz

/-- Montel attainment for the finite-matrix holomorphic functional calculus. -/
theorem exists_schurOn_spectralJetEval_norm_eq_of_tendsto
    (A : Operator.SquareMatrix n) {U : Set ℂ} (hU : IsOpen U)
    (hspec : spectrum ℂ A ⊆ U) {F : ℕ → ℂ → ℂ} {c : ℝ}
    (hF : ∀ m, IsSchurOn U (F m))
    (hmax : Tendsto (fun m ↦ ‖spectralJetEval A (F m)‖) atTop (nhds c)) :
    ∃ f : ℂ → ℂ, IsSchurOn U f ∧ ‖spectralJetEval A f‖ = c := by
  obtain ⟨φ, f, hφ, hfd, hconv⟩ := schurMontel hU
    (fun m ↦ (hF m).differentiableOn) (fun m z hz ↦ (hF m).norm_le hz)
  have hfbound : ∀ z ∈ U, ‖f z‖ ≤ 1 := by
    intro z hz
    exact le_of_tendsto ((hconv.tendsto_at hz).norm)
      (Eventually.of_forall fun m ↦ (hF (φ m)).norm_le hz)
  have hf : IsSchurOn U f := ⟨hfd, fun z hz ↦ by
    simpa [mem_closedBall_zero_iff] using hfbound z hz⟩
  have heval := spectralJetEval_tendsto_of_tendstoLocallyUniformlyOn A hU
    (fun m ↦ (hF (φ m)).differentiableOn)
    (charpoly_roots_subset_of_spectrum_subset A hspec) hconv
  have hnormEval : Tendsto (fun m ↦ ‖spectralJetEval A (F (φ m))‖) atTop
      (nhds ‖spectralJetEval A f‖) := heval.norm
  have hnormC : Tendsto (fun m ↦ ‖spectralJetEval A (F (φ m))‖) atTop (nhds c) :=
    hmax.comp hφ.tendsto_atTop
  exact ⟨f, hf, tendsto_nhds_unique hnormEval hnormC⟩

/-- A bound for the holomorphic functional calculus, uniform in the sup norm. -/
def HasHolomorphicCalculusBound (A : Operator.SquareMatrix n) (U : Set ℂ) (C : ℝ) : Prop :=
  ∀ (g : ℂ → ℂ) (r : ℝ), DifferentiableOn ℂ g U → 0 ≤ r →
    (∀ z ∈ U, ‖g z‖ ≤ r) → ‖spectralJetEval A g‖ ≤ C * r

theorem bddAbove_schurSpectralEvalNorms_of_bound
    (A : Operator.SquareMatrix n) {U : Set ℂ} {C : ℝ}
    (hcalc : HasHolomorphicCalculusBound A U C) :
    BddAbove (schurSpectralEvalNorms A U) := by
  refine ⟨C, ?_⟩
  rintro r ⟨f, hf, rfl⟩
  simpa using hcalc f 1 hf.differentiableOn zero_le_one
    (fun z hz ↦ hf.norm_le hz)

theorem holomorphicCalculusNorm_le_of_bound
    (A : Operator.SquareMatrix n) {U : Set ℂ} {C : ℝ}
    (hcalc : HasHolomorphicCalculusBound A U C) :
    holomorphicCalculusNorm A U ≤ C := by
  apply csSup_le (schurSpectralEvalNorms_nonempty A U)
  rintro r ⟨f, hf, rfl⟩
  simpa using hcalc f 1 hf.differentiableOn zero_le_one
    (fun z hz ↦ hf.norm_le hz)

/-- The supremal Schur-class matrix norm is approached by an actual sequence
of Schur functions whenever the functional calculus has a finite bound. -/
theorem exists_schurOn_sequence_tendsto_holomorphicCalculusNorm
    (A : Operator.SquareMatrix n) {U : Set ℂ} {C : ℝ}
    (hcalc : HasHolomorphicCalculusBound A U C) :
    ∃ F : ℕ → ℂ → ℂ, (∀ m, IsSchurOn U (F m)) ∧
      Tendsto (fun m ↦ ‖spectralJetEval A (F m)‖) atTop
        (nhds (holomorphicCalculusNorm A U)) := by
  obtain ⟨u, -, hu, humem⟩ := exists_seq_tendsto_sSup
    (schurSpectralEvalNorms_nonempty A U)
    (bddAbove_schurSpectralEvalNorms_of_bound A hcalc)
  choose F hF hnorm using fun m ↦ humem m
  refine ⟨F, hF, ?_⟩
  simpa [holomorphicCalculusNorm, hnorm] using hu

/-- Saturating a positive functional-calculus bound forces the determining
spectral-jet interpolation problem to have least norm one. -/
theorem hasMinimalNormOneJetsOn_spectralJetNodes_of_saturates_bound
    (A : Operator.SquareMatrix n) {U : Set ℂ} (hU : IsOpen U)
    (hspec : spectrum ℂ A ⊆ U) {C : ℝ} (hC : 0 < C)
    {f : ℂ → ℂ} (hf : IsSchurOn U f)
    (heq : ‖spectralJetEval A f‖ = C)
    (hcalc : HasHolomorphicCalculusBound A U C) :
    HasMinimalNormOneJetsOn U (spectralJetNodes A) f := by
  rintro ⟨g, hg, hjet, r, hr0, hr1, hgr⟩
  have hroots := charpoly_roots_subset_of_spectrum_subset A hspec
  have heval : spectralJetEval A g = spectralJetEval A f :=
    spectralJetEval_eq_of_jetEq A
      (fun a ↦ hg.differentiableOn.analyticAt (hU.mem_nhds (hroots _
        (Multiset.mem_toFinset.mp a.2))))
      (fun a ↦ hf.differentiableOn.analyticAt (hU.mem_nhds (hroots _
        (Multiset.mem_toFinset.mp a.2)))) hjet
  have hle : ‖spectralJetEval A g‖ ≤ C * r := hcalc g r hg.differentiableOn hr0 hgr
  have hlt : C * r < C := (mul_lt_iff_lt_one_right hC).2 hr1
  rw [heval, heq] at hle
  exact (not_lt_of_ge hle) hlt

/-- A function is nonconstant on a set. -/
def IsNonconstantOn (U : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ¬ ∃ w : ℂ, EqOn f (fun _ ↦ w) U

/-- End-to-end attained finite-Blaschke extremizer.  The hypotheses isolate
exactly the Montel maximizing sequence and the sharp functional-calculus
bound used in the manuscript. -/
theorem exists_attained_finiteBlaschke_extremizer
    [Nonempty n] (A : Operator.SquareMatrix n) {U : Set ℂ}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hUne : U.Nonempty)
    (hUb : Bornology.IsBounded U) (hspec : spectrum ℂ A ⊆ U)
    {F : ℕ → ℂ → ℂ} {c : ℝ} (hc : 1 < c)
    (hF : ∀ m, IsSchurOn U (F m))
    (hmax : Tendsto (fun m ↦ ‖spectralJetEval A (F m)‖) atTop (nhds c))
    (hcalc : HasHolomorphicCalculusBound A U c) :
    ∃ f phi B : ℂ → ℂ,
      IsSchurOn U f ∧
      ‖spectralJetEval A f‖ = c ∧
      HasMinimalNormOneJetsOn U (spectralJetNodes A) f ∧
      DifferentiableOn ℂ phi U ∧
      BijOn phi U (ball 0 1) ∧
      IsSchurFiniteBlaschke B ∧
      JetEq (spectralJetNodes A) (B ∘ phi) f ∧
      spectralJetEval A (B ∘ phi) = spectralJetEval A f ∧
      ‖spectralJetEval A (B ∘ phi)‖ = c ∧
      IsNonconstantOn U (B ∘ phi) ∧
      ∀ g : ℂ → ℂ, IsSchurOn U g →
        JetEq (spectralJetNodes A) g f → EqOn g (B ∘ phi) U := by
  obtain ⟨f, hf, hfeval⟩ :=
    exists_schurOn_spectralJetEval_norm_eq_of_tendsto A hUo hspec hF hmax
  have hmin : HasMinimalNormOneJetsOn U (spectralJetNodes A) f :=
    hasMinimalNormOneJetsOn_spectralJetNodes_of_saturates_bound A hUo hspec
      (lt_trans zero_lt_one hc) hf hfeval hcalc
  have hnodes := spectralJetNodes_subset_of_spectrum_subset A hspec
  obtain ⟨phi, B, hphi, hbij, hB, hjet, hunique⟩ :=
    exists_riemannMap_schurFiniteBlaschke_comp_unique_of_hasMinimalNormOneJetsOn
      hUo hUc hUne hUb (spectralJetNodes A) hnodes hf hmin
  have hcomp : IsSchurOn U (B ∘ phi) := hB.isSchur.comp_biholomorphic hphi hbij
  have hroots := charpoly_roots_subset_of_spectrum_subset A hspec
  have heval : spectralJetEval A (B ∘ phi) = spectralJetEval A f :=
    spectralJetEval_eq_of_jetEq A
      (fun a ↦ hcomp.differentiableOn.analyticAt (hUo.mem_nhds (hroots _
        (Multiset.mem_toFinset.mp a.2))))
      (fun a ↦ hf.differentiableOn.analyticAt (hUo.mem_nhds (hroots _
        (Multiset.mem_toFinset.mp a.2)))) hjet
  have hcompEval : ‖spectralJetEval A (B ∘ phi)‖ = c := by rw [heval, hfeval]
  have hnonconst : IsNonconstantOn U (B ∘ phi) := by
    rintro ⟨w, hw⟩
    obtain ⟨z₀, hz₀⟩ := hUne
    have hwNorm : ‖w‖ ≤ 1 := by
      have hval : (B ∘ phi) z₀ = w := hw hz₀
      calc
        ‖w‖ = ‖(B ∘ phi) z₀‖ := congrArg norm hval |>.symm
        _ ≤ 1 := hcomp.norm_le hz₀
    have hconstEval : spectralJetEval A (B ∘ phi) =
        spectralJetEval A (fun _ ↦ w) := by
      apply spectralJetEval_eq_of_iteratedDeriv_eq A
      intro a k
      have haU : (a : ℂ) ∈ U := hroots _ (Multiset.mem_toFinset.mp a.2)
      have hevent : (B ∘ phi) =ᶠ[nhds (a : ℂ)] fun _ ↦ w := by
        filter_upwards [hUo.mem_nhds haU] with z hz
        exact hw hz
      exact hevent.iteratedDeriv_eq k.val
    have hconstPoly : spectralJetEval A (fun _ ↦ w) =
        Operator.polynomialEval (Polynomial.C w) A := by
      simpa using spectralJetEval_polynomial A (Polynomial.C w)
    have hconstNorm : ‖spectralJetEval A (fun _ ↦ w)‖ ≤ 1 := by
      rw [hconstPoly]
      calc
        ‖Operator.polynomialEval (Polynomial.C w) A‖ = ‖w‖ := by
          simp [Operator.polynomialEval, norm_algebraMap']
        _ ≤ 1 := hwNorm
    have : c ≤ 1 := by
      rw [← hcompEval, hconstEval]
      exact hconstNorm
    exact (not_lt_of_ge this) hc
  exact ⟨f, phi, B, hf, hfeval, hmin, hphi, hbij, hB, hjet, heval,
    hcompEval, hnonconst, hunique⟩

/-- Supremum-facing form of `exists_attained_finiteBlaschke_extremizer`.
No maximizing sequence is part of the interface: it is extracted from the
definition of the holomorphic functional-calculus norm and then attained by
Montel compactness. -/
theorem exists_attained_finiteBlaschke_extremizer_at_holomorphicCalculusNorm
    [Nonempty n] (A : Operator.SquareMatrix n) {U : Set ℂ}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hUne : U.Nonempty)
    (hUb : Bornology.IsBounded U) (hspec : spectrum ℂ A ⊆ U)
    (hc : 1 < holomorphicCalculusNorm A U)
    (hcalc : HasHolomorphicCalculusBound A U (holomorphicCalculusNorm A U)) :
    ∃ f phi B : ℂ → ℂ,
      IsSchurOn U f ∧
      ‖spectralJetEval A f‖ = holomorphicCalculusNorm A U ∧
      HasMinimalNormOneJetsOn U (spectralJetNodes A) f ∧
      DifferentiableOn ℂ phi U ∧
      BijOn phi U (ball 0 1) ∧
      IsSchurFiniteBlaschke B ∧
      JetEq (spectralJetNodes A) (B ∘ phi) f ∧
      spectralJetEval A (B ∘ phi) = spectralJetEval A f ∧
      ‖spectralJetEval A (B ∘ phi)‖ = holomorphicCalculusNorm A U ∧
      IsNonconstantOn U (B ∘ phi) ∧
      ∀ g : ℂ → ℂ, IsSchurOn U g →
        JetEq (spectralJetNodes A) g f → EqOn g (B ∘ phi) U := by
  obtain ⟨F, hF, hmax⟩ :=
    exists_schurOn_sequence_tendsto_holomorphicCalculusNorm A hcalc
  exact exists_attained_finiteBlaschke_extremizer A hUo hUc hUne hUb hspec hc hF hmax hcalc

end

end DiskRigidity.Complex
