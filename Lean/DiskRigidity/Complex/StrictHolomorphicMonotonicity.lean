/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.StrictDomain
public import DiskRigidity.Complex.HolomorphicExtremizer
public import DiskRigidity.Complex.SpectralJetAlgebra
public import Mathlib.Analysis.Complex.Liouville

/-!
# Strict monotonicity of finite-jet holomorphic-calculus norms

For a finite matrix the Schur-class calculus norm is finite on every open
neighborhood of its spectrum.  On a proper inclusion of bounded convex
domains it strictly decreases, unless the norm on the smaller domain is the
scalar value one.
-/

noncomputable section

open Function Metric Set
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Complex

@[expose] public section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The finite spectral-jet calculus is bounded on the Schur class of every
open neighborhood of the spectrum. -/
theorem bddAbove_schurSpectralEvalNorms_of_isOpen_spectrum
    (A : Operator.SquareMatrix n) {U : Set ℂ} (hUo : IsOpen U)
    (hspec : spectrum ℂ A ⊆ U) :
    BddAbove (schurSpectralEvalNorms A U) := by
  classical
  have hroot (a : HermiteRoot A.charpoly) : (a : ℂ) ∈ U :=
    charpoly_roots_subset_of_spectrum_subset A hspec _
      (Multiset.mem_toFinset.mp a.2)
  have hex (a : HermiteRoot A.charpoly) :
      ∃ R : ℝ, 0 < R ∧ closedBall (a : ℂ) R ⊆ U := by
    obtain ⟨ε, hε, hεU⟩ := (Metric.isOpen_iff.mp hUo) (a : ℂ) (hroot a)
    exact ⟨ε / 2, half_pos hε,
      (closedBall_subset_ball (half_lt_self hε)).trans hεU⟩
  choose R hR hRU using hex
  let C : ℝ :=
    ∑ a : HermiteRoot A.charpoly,
      ∑ k : Fin (A.charpoly.rootMultiplicity (a : ℂ)),
        (((k.val.factorial : ℝ) / R a ^ k.val) / k.val.factorial) *
          ‖Operator.polynomialEval (hermiteBasis A.charpoly a k) A‖
  refine ⟨C, ?_⟩
  rintro x ⟨f, hf, rfl⟩
  rw [spectralJetEval_eq_sum]
  calc
    ‖∑ a : HermiteRoot A.charpoly,
        ∑ k : Fin (A.charpoly.rootMultiplicity (a : ℂ)),
          holomorphicHermiteData A.charpoly f a k •
            Operator.polynomialEval (hermiteBasis A.charpoly a k) A‖
        ≤ ∑ a : HermiteRoot A.charpoly,
            ‖∑ k : Fin (A.charpoly.rootMultiplicity (a : ℂ)),
              holomorphicHermiteData A.charpoly f a k •
                Operator.polynomialEval (hermiteBasis A.charpoly a k) A‖ := by
          simpa using norm_sum_le Finset.univ (fun a : HermiteRoot A.charpoly ↦
            ∑ k : Fin (A.charpoly.rootMultiplicity (a : ℂ)),
              holomorphicHermiteData A.charpoly f a k •
                Operator.polynomialEval (hermiteBasis A.charpoly a k) A)
    _ ≤ ∑ a : HermiteRoot A.charpoly,
          ∑ k : Fin (A.charpoly.rootMultiplicity (a : ℂ)),
            ‖holomorphicHermiteData A.charpoly f a k •
              Operator.polynomialEval (hermiteBasis A.charpoly a k) A‖ := by
      apply Finset.sum_le_sum
      intro a _
      simpa using norm_sum_le Finset.univ (fun k :
        Fin (A.charpoly.rootMultiplicity (a : ℂ)) ↦
          holomorphicHermiteData A.charpoly f a k •
            Operator.polynomialEval (hermiteBasis A.charpoly a k) A)
    _ ≤ C := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro k _
      have hdiff : DiffContOnCl ℂ f (ball (a : ℂ) (R a)) :=
        hf.differentiableOn.diffContOnCl_ball (hRU a)
      have hderiv : ‖iteratedDeriv k.val f (a : ℂ)‖ ≤
          k.val.factorial * 1 / R a ^ k.val :=
        _root_.Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
          k.val (hR a) hdiff (fun z hz ↦ hf.norm_le (hRU a (sphere_subset_closedBall hz)))
      have hfac : (0 : ℝ) < k.val.factorial := by positivity
      have hdata : ‖holomorphicHermiteData A.charpoly f a k‖ ≤
          ((k.val.factorial : ℝ) / R a ^ k.val) / k.val.factorial := by
        rw [holomorphicHermiteData, norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_right (by simpa using hderiv) hfac.le
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right hdata (norm_nonneg _)

/-- Inclusion reverses the Schur-class finite-jet calculus norm. -/
theorem holomorphicCalculusNorm_anti_mono_of_subset
    (A : Operator.SquareMatrix n) {U V : Set ℂ} (hUo : IsOpen U)
    (hspec : spectrum ℂ A ⊆ U) (hUV : U ⊆ V) :
    holomorphicCalculusNorm A V ≤ holomorphicCalculusNorm A U := by
  have hb := bddAbove_schurSpectralEvalNorms_of_isOpen_spectrum A hUo hspec
  apply csSup_le (schurSpectralEvalNorms_nonempty A V)
  rintro x ⟨f, hf, rfl⟩
  apply le_csSup hb
  exact ⟨f, ⟨hf.differentiableOn.mono hUV, hf.2.mono_left hUV⟩, rfl⟩

/-- The supremal finite-jet norm itself is the sharp homogeneous calculus
bound on every open spectral neighborhood. -/
theorem hasHolomorphicCalculusBound_holomorphicCalculusNorm
    (A : Operator.SquareMatrix n) {U : Set ℂ} (hUo : IsOpen U)
    (hspec : spectrum ℂ A ⊆ U) :
    HasHolomorphicCalculusBound A U (holomorphicCalculusNorm A U) := by
  have hb := bddAbove_schurSpectralEvalNorms_of_isOpen_spectrum A hUo hspec
  intro g r hg hr hgR
  rcases hr.eq_or_lt with rfl | hr
  · have heval : spectralJetEval A g = 0 := by
      calc
        spectralJetEval A g = spectralJetEval A (fun _ ↦ 0) := by
          apply spectralJetEval_eq_of_iteratedDeriv_eq A
          intro a k
          have haU : (a : ℂ) ∈ U := charpoly_roots_subset_of_spectrum_subset A hspec _
            (Multiset.mem_toFinset.mp a.2)
          have hevent : g =ᶠ[nhds (a : ℂ)] fun _ ↦ 0 := by
            filter_upwards [hUo.mem_nhds haU] with z hz
            exact norm_eq_zero.mp (le_antisymm (hgR z hz) (norm_nonneg _))
          simpa using hevent.iteratedDeriv_eq k.val
        _ = 0 := by
          rw [show spectralJetEval A (fun _ ↦ 0) =
            Operator.polynomialEval (0 : Polynomial ℂ) A by
              simpa using spectralJetEval_polynomial A (0 : Polynomial ℂ)]
          simp [Operator.polynomialEval]
    simp [heval]
  · let c : ℂ := (r : ℂ)⁻¹
    have hcnorm : ‖c‖ = r⁻¹ := by simp [c, abs_of_pos hr]
    have hnormalized : IsSchurOn U (fun z ↦ c * g z) := by
      refine ⟨(differentiableOn_const (c := c)).mul hg, fun z hz ↦ ?_⟩
      rw [mem_closedBall_zero_iff, norm_mul, hcnorm]
      exact (mul_le_mul_of_nonneg_left (hgR z hz) (inv_nonneg.mpr hr.le)).trans
        (le_of_eq (inv_mul_cancel₀ hr.ne'))
    have hmem : ‖spectralJetEval A (fun z ↦ c * g z)‖ ∈
        schurSpectralEvalNorms A U := ⟨_, hnormalized, rfl⟩
    have hle := le_csSup hb hmem
    rw [spectralJetEval_const_mul, norm_smul, hcnorm] at hle
    calc
      ‖spectralJetEval A g‖ = r * (r⁻¹ * ‖spectralJetEval A g‖) := by field_simp
      _ ≤ r * holomorphicCalculusNorm A U := mul_le_mul_of_nonneg_left hle hr.le
      _ = holomorphicCalculusNorm A U * r := mul_comm _ _

/-- Exact strict-domain monotonicity for the finite spectral-jet holomorphic
calculus.  If the smaller norm exceeds the scalar value one, enlarging a
bounded convex domain strictly lowers it. -/
theorem holomorphicCalculusNorm_strict_anti_of_ssubset
    [Nonempty n] (A : Operator.SquareMatrix n) {U V : Set ℂ}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hUne : U.Nonempty)
    (hUb : Bornology.IsBounded U) (hVo : IsOpen V) (hVc : Convex ℝ V)
    (_hVne : V.Nonempty) (_hVb : Bornology.IsBounded V)
    (hUV : U ⊂ V) (hspec : spectrum ℂ A ⊆ U)
    (hgt : 1 < holomorphicCalculusNorm A U) :
    holomorphicCalculusNorm A V < holomorphicCalculusNorm A U := by
  let CU := holomorphicCalculusNorm A U
  let CV := holomorphicCalculusNorm A V
  have hVU : spectrum ℂ A ⊆ V := hspec.trans hUV.subset
  have hcalcU : HasHolomorphicCalculusBound A U CU :=
    hasHolomorphicCalculusBound_holomorphicCalculusNorm A hUo hspec
  have hcalcV : HasHolomorphicCalculusBound A V CV :=
    hasHolomorphicCalculusBound_holomorphicCalculusNorm A hVo hVU
  have hle : CV ≤ CU := holomorphicCalculusNorm_anti_mono_of_subset
    A hUo hspec hUV.subset
  by_contra hnot
  have heq : CV = CU := le_antisymm hle (not_lt.mp hnot)
  obtain ⟨F, hF, hFmax⟩ :=
    exists_schurOn_sequence_tendsto_holomorphicCalculusNorm A hcalcV
  obtain ⟨g, hgV, hgeval⟩ :=
    exists_schurOn_spectralJetEval_norm_eq_of_tendsto A hVo hVU hF hFmax
  have hgU : IsSchurOn U g :=
    ⟨hgV.differentiableOn.mono hUV.subset, hgV.2.mono_left hUV.subset⟩
  have hgevalU : ‖spectralJetEval A g‖ = CU := hgeval.trans heq
  have hmin : HasMinimalNormOneJetsOn U (spectralJetNodes A) g :=
    hasMinimalNormOneJetsOn_spectralJetNodes_of_saturates_bound A hUo hspec
      (lt_trans zero_lt_one hgt) hgU hgevalU hcalcU
  have hnodes := spectralJetNodes_subset_of_spectrum_subset A hspec
  obtain ⟨phi, B, hphi, hphibij, hB, hjet, -⟩ :=
    exists_riemannMap_schurFiniteBlaschke_comp_unique_of_hasMinimalNormOneJetsOn
      hUo hUc hUne hUb (spectralJetNodes A) hnodes hgU hmin
  have hcomp : IsSchurOn U (B ∘ phi) :=
    hB.isSchur.comp_biholomorphic hphi hphibij
  have hgeq : EqOn g (B ∘ phi) U := by
    intro z hz
    exact (eqOn_of_hasMinimalNormOneJetsOn hUo hphi hphibij
      (spectralJetNodes A) hnodes hgU hcomp hmin hjet hz).symm
  obtain ⟨c, hcnorm, hconst⟩ :=
    eqOn_unimodular_const_of_eqOn_finiteBlaschke_comp_of_ssubset
      hUo hUne hUV hVo hVc hphi hphibij hB hgV hgeq
  have hevalConst : spectralJetEval A g = spectralJetEval A (fun _ ↦ c) := by
    apply spectralJetEval_eq_of_iteratedDeriv_eq A
    intro a k
    have haV : (a : ℂ) ∈ V := charpoly_roots_subset_of_spectrum_subset A hVU _
      (Multiset.mem_toFinset.mp a.2)
    have hevent : g =ᶠ[nhds (a : ℂ)] fun _ ↦ c := by
      filter_upwards [hVo.mem_nhds haV] with z hz
      exact hconst hz
    exact hevent.iteratedDeriv_eq k.val
  have hconstNorm : ‖spectralJetEval A (fun _ ↦ c)‖ = 1 := by
    rw [show spectralJetEval A (fun _ ↦ c) =
      Operator.polynomialEval (Polynomial.C c) A by
        simpa using spectralJetEval_polynomial A (Polynomial.C c)]
    simpa [Operator.polynomialEval, norm_algebraMap'] using hcnorm
  have hCUone : CU = 1 := by rw [← hgevalU, hevalConst, hconstNorm]
  exact (ne_of_gt hgt) hCUone

/-- Exact manuscript-facing strict-domain monotonicity.  If the calculus norm
on the larger bounded convex domain exceeds one, then restriction to a proper
smaller domain strictly increases the norm. -/
theorem holomorphicCalculusNorm_strict_anti_of_ssubset_of_larger_gt_one
    [Nonempty n] (A : Operator.SquareMatrix n) {U V : Set ℂ}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hUne : U.Nonempty)
    (hUb : Bornology.IsBounded U) (hVo : IsOpen V) (hVc : Convex ℝ V)
    (hVne : V.Nonempty) (hVb : Bornology.IsBounded V)
    (hUV : U ⊂ V) (hspec : spectrum ℂ A ⊆ U)
    (hgt : 1 < holomorphicCalculusNorm A V) :
    holomorphicCalculusNorm A V < holomorphicCalculusNorm A U := by
  apply holomorphicCalculusNorm_strict_anti_of_ssubset
    A hUo hUc hUne hUb hVo hVc hVne hVb hUV hspec
  exact hgt.trans_le
    (holomorphicCalculusNorm_anti_mono_of_subset A hUo hspec hUV.subset)

end

end DiskRigidity.Complex
