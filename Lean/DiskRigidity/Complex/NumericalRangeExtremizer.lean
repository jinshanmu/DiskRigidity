/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.ConvexHolomorphicBound
public import DiskRigidity.Complex.HolomorphicDoubleLayer
public import DiskRigidity.Operator.NumericalRangeConvexity

/-!
# From the polynomial Crouzeix constant to a holomorphic extremizer

Normalized polynomials on the numerical range form a subfamily of the Schur
class on its interior.  This identifies the manuscript's polynomial
functional-calculus constant with the finite-jet holomorphic calculus norm as
soon as the sharp holomorphic bound is available.
-/

noncomputable section

open Filter Function Metric Set Topology
open scoped Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Complex

@[expose] public section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The normalized polynomial family defining `crouzeixConstant` is nonempty. -/
theorem normalizedPolynomialValues_nonempty [Nonempty n]
    (A : Operator.SquareMatrix n) :
    (Operator.normalizedPolynomialValues A).Nonempty := by
  have hzero : Operator.maxPolynomialModulus A 0 = 0 := by
    obtain ⟨z, -, hz⟩ := Operator.exists_norm_eval_eq_maxPolynomialModulus A 0
    simpa using hz.symm
  exact ⟨0, 0, by simp [hzero], by simp [Operator.polynomialEval]⟩

/-- A uniform normalized polynomial bound makes the defining family bounded. -/
theorem bddAbove_normalizedPolynomialValues_of_bound
    (A : Operator.SquareMatrix n) {C : ℝ}
    (hbound : ∀ p : Polynomial ℂ,
      Operator.maxPolynomialModulus A p ≤ 1 →
        ‖Operator.polynomialEval p A‖ ≤ C) :
    BddAbove (Operator.normalizedPolynomialValues A) := by
  refine ⟨C, ?_⟩
  rintro r ⟨p, hp, rfl⟩
  exact hbound p hp

/-- Every polynomial normalized on the numerical range is a Schur function
on its interior, with the same finite spectral-jet matrix value. -/
theorem normalizedPolynomialValues_subset_schurSpectralEvalNorms
    [Nonempty n] (A : Operator.SquareMatrix n) :
    Operator.normalizedPolynomialValues A ⊆
      schurSpectralEvalNorms A (interior (Operator.numericalRange A)) := by
  rintro r ⟨p, hp, rfl⟩
  refine ⟨fun z ↦ p.eval z, ?_, congrArg norm (spectralJetEval_polynomial A p)⟩
  refine ⟨p.differentiable.differentiableOn, fun z hz ↦ ?_⟩
  rw [mem_closedBall_zero_iff]
  exact (Operator.norm_eval_le_maxPolynomialModulus A p (interior_subset hz)).trans hp

/-- Equality of the polynomial functional-calculus constant with two already
forces the normalized polynomial values to be bounded.  This uses only the
definition of the real supremum: an unbounded set has `sSup = 0`. -/
theorem bddAbove_normalizedPolynomialValues_of_crouzeixConstant_eq_two
    (A : Operator.SquareMatrix n)
    (hpsi : Operator.crouzeixConstant A = 2) :
    BddAbove (Operator.normalizedPolynomialValues A) := by
  by_contra hbounded
  have hzero : Operator.crouzeixConstant A = 0 := by
    rw [Operator.crouzeixConstant, Real.sSup_of_not_bddAbove hbounded]
  norm_num [hzero] at hpsi

/-- At `crouzeixConstant A = 2`, normalized polynomials themselves form a
maximizing sequence.  No holomorphic functional-calculus estimate is needed
to extract this sequence. -/
theorem exists_normalizedPolynomial_sequence_tendsto_two
    [Nonempty n] (A : Operator.SquareMatrix n)
    (hpsi : Operator.crouzeixConstant A = 2) :
    ∃ P : ℕ → Polynomial ℂ,
      (∀ m, Operator.maxPolynomialModulus A (P m) ≤ 1) ∧
      Tendsto (fun m ↦ ‖Operator.polynomialEval (P m) A‖) atTop (nhds 2) := by
  obtain ⟨u, -, hu, humem⟩ := exists_seq_tendsto_sSup
    (normalizedPolynomialValues_nonempty A)
    (bddAbove_normalizedPolynomialValues_of_crouzeixConstant_eq_two A hpsi)
  choose P hP hnorm using fun m ↦ humem m
  refine ⟨P, hP, ?_⟩
  have hutwo : Tendsto u atTop (nhds 2) := by
    change Tendsto u atTop (nhds (Operator.crouzeixConstant A)) at hu
    rwa [hpsi] at hu
  simpa [hnorm] using hutwo

/-- The polynomial Crouzeix constant is bounded by the holomorphic calculus
norm on the interior numerical range. -/
theorem crouzeixConstant_le_holomorphicCalculusNorm [Nonempty n]
    (A : Operator.SquareMatrix n)
    (hcalc : HasHolomorphicCalculusBound A
      (interior (Operator.numericalRange A)) 2) :
    Operator.crouzeixConstant A ≤
      holomorphicCalculusNorm A (interior (Operator.numericalRange A)) := by
  apply csSup_le (normalizedPolynomialValues_nonempty A)
  intro r hr
  exact le_csSup (bddAbove_schurSpectralEvalNorms_of_bound A hcalc)
    (normalizedPolynomialValues_subset_schurSpectralEvalNorms A hr)

/-- At polynomial constant two, the polynomial and holomorphic calculus norms
on the interior numerical range are both exactly two. -/
theorem holomorphicCalculusNorm_interior_numericalRange_eq_two
    [Nonempty n] (A : Operator.SquareMatrix n)
    (hpsi : Operator.crouzeixConstant A = 2)
    (hcalc : HasHolomorphicCalculusBound A
      (interior (Operator.numericalRange A)) 2) :
    holomorphicCalculusNorm A (interior (Operator.numericalRange A)) = 2 := by
  apply le_antisymm (holomorphicCalculusNorm_le_of_bound A hcalc)
  rw [← hpsi]
  exact crouzeixConstant_le_holomorphicCalculusNorm A hcalc

/-- A sharp estimate proved first for functions holomorphic near the numerical
range automatically holds for all bounded holomorphic functions on its
interior.  The closure identification is a consequence of compact convexity
and the assumed nonempty interior. -/
theorem hasHolomorphicCalculusBound_interior_numericalRange_of_neighborhoods
    (A : Operator.SquareMatrix n)
    (hInt : (interior (Operator.numericalRange A)).Nonempty)
    (hspec : spectrum ℂ A ⊆ interior (Operator.numericalRange A))
    {C : ℝ}
    (hnhd : HasNeighborhoodHolomorphicCalculusBound A
      (Operator.numericalRange A) C) :
    HasHolomorphicCalculusBound A
      (interior (Operator.numericalRange A)) C := by
  let W := Operator.numericalRange A
  let U := interior W
  have hWc : Convex ℝ W := Operator.numericalRange_convex A
  have hWclosed : IsClosed W := (Operator.isCompact_numericalRange A).isClosed
  have hclosure : closure U = W := by
    rw [show U = interior W from rfl,
      hWc.closure_interior_eq_closure_of_nonempty_interior hInt,
      hWclosed.closure_eq]
  apply hasHolomorphicCalculusBound_of_neighborhoods_of_isOpen_convex
    A isOpen_interior hWc.interior hInt hspec
  change HasNeighborhoodHolomorphicCalculusBound A (closure U) C
  rw [hclosure]
  simpa [W] using hnhd

/-- Direct polynomial-to-Blaschke extremizer at `crouzeixConstant A = 2`.

This is the extremizer construction actually needed in the manuscript.  A
maximizing sequence is taken directly from the normalized polynomials in the
definition of `crouzeixConstant`; Montel selection attains its finite spectral
jet, and finite confluent Schur interpolation replaces the limit by a finite
Blaschke product composed with a Riemann map.  In particular, neither a
supporting-boundary Cauchy package nor a prior sharp estimate for every
bounded holomorphic function is an input. -/
theorem exists_finiteBlaschke_extremizer_direct_of_crouzeixConstant_eq_two
    [Nonempty n] (A : Operator.SquareMatrix n)
    (hInt : (interior (Operator.numericalRange A)).Nonempty)
    (hspec : spectrum ℂ A ⊆ interior (Operator.numericalRange A))
    (hpsi : Operator.crouzeixConstant A = 2) :
    ∃ f phi B : ℂ → ℂ,
      IsSchurOn (interior (Operator.numericalRange A)) f ∧
      ‖spectralJetEval A f‖ = 2 ∧
      DifferentiableOn ℂ phi (interior (Operator.numericalRange A)) ∧
      BijOn phi (interior (Operator.numericalRange A)) (ball 0 1) ∧
      IsSchurFiniteBlaschke B ∧
      JetEq (spectralJetNodes A) (B ∘ phi) f ∧
      spectralJetEval A (B ∘ phi) = spectralJetEval A f ∧
      ‖spectralJetEval A (B ∘ phi)‖ = 2 ∧
      IsNonconstantOn (interior (Operator.numericalRange A)) (B ∘ phi) := by
  let U := interior (Operator.numericalRange A)
  obtain ⟨P, hP, hPmax⟩ :=
    exists_normalizedPolynomial_sequence_tendsto_two A hpsi
  let F : ℕ → ℂ → ℂ := fun m z ↦ (P m).eval z
  have hF : ∀ m, IsSchurOn U (F m) := by
    intro m
    refine ⟨(P m).differentiable.differentiableOn, fun z hz ↦ ?_⟩
    rw [mem_closedBall_zero_iff]
    exact (Operator.norm_eval_le_maxPolynomialModulus A (P m)
      (interior_subset hz)).trans (hP m)
  have hFmax : Tendsto (fun m ↦ ‖spectralJetEval A (F m)‖) atTop (nhds 2) := by
    simpa [F, spectralJetEval_polynomial] using hPmax
  obtain ⟨f, hf, hfeval⟩ :=
    exists_schurOn_spectralJetEval_norm_eq_of_tendsto A isOpen_interior
      hspec hF hFmax
  have hUb : Bornology.IsBounded U :=
    (Operator.isCompact_numericalRange A).isBounded.subset interior_subset
  have hUc : Convex ℝ U := (Operator.numericalRange_convex A).interior
  have hnodes := spectralJetNodes_subset_of_spectrum_subset A hspec
  obtain ⟨phi, B, hphi, hbij, hB, hjet⟩ :=
    exists_riemannMap_schurFiniteBlaschke_comp_jetEq
      isOpen_interior hUc hInt hUb (spectralJetNodes A) hnodes hf
  have hcomp : IsSchurOn U (B ∘ phi) :=
    hB.isSchur.comp_biholomorphic hphi hbij
  have hroots := charpoly_roots_subset_of_spectrum_subset A hspec
  have heval : spectralJetEval A (B ∘ phi) = spectralJetEval A f :=
    spectralJetEval_eq_of_jetEq A
      (fun a ↦ hcomp.differentiableOn.analyticAt
        (isOpen_interior.mem_nhds (hroots _
          (Multiset.mem_toFinset.mp a.2))))
      (fun a ↦ hf.differentiableOn.analyticAt
        (isOpen_interior.mem_nhds (hroots _
          (Multiset.mem_toFinset.mp a.2)))) hjet
  have hcompEval : ‖spectralJetEval A (B ∘ phi)‖ = 2 := by
    rw [heval, hfeval]
  have hnonconst : IsNonconstantOn U (B ∘ phi) := by
    rintro ⟨w, hw⟩
    obtain ⟨z₀, hz₀⟩ := hInt
    have hwNorm : ‖w‖ ≤ 1 := by
      have hval : (B ∘ phi) z₀ = w := hw hz₀
      calc
        ‖w‖ = ‖(B ∘ phi) z₀‖ := congrArg norm hval |>.symm
        _ ≤ 1 := hcomp.norm_le hz₀
    have hconstEval : spectralJetEval A (B ∘ phi) =
        spectralJetEval A (fun _ ↦ w) := by
      apply spectralJetEval_eq_of_iteratedDeriv_eq A
      intro a k
      have haU : (a : ℂ) ∈ U :=
        hroots _ (Multiset.mem_toFinset.mp a.2)
      have hevent : (B ∘ phi) =ᶠ[nhds (a : ℂ)] fun _ ↦ w := by
        filter_upwards [isOpen_interior.mem_nhds haU] with z hz
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
    have : (2 : ℝ) ≤ 1 := by
      rw [← hcompEval, hconstEval]
      exact hconstNorm
    norm_num at this
  exact ⟨f, phi, B, hf, hfeval, hphi, hbij, hB, hjet, heval,
    hcompEval, hnonconst⟩

/-- Raw numerical-range form of the attained finite-Blaschke extremizer.
The only analytic estimate requested is the sharp homogeneous `H∞` calculus
bound; all domain geometry is discharged from the numerical range itself. -/
theorem exists_finiteBlaschke_extremizer_of_crouzeixConstant_eq_two
    [Nonempty n] (A : Operator.SquareMatrix n)
    (hInt : (interior (Operator.numericalRange A)).Nonempty)
    (hspec : spectrum ℂ A ⊆ interior (Operator.numericalRange A))
    (hpsi : Operator.crouzeixConstant A = 2)
    (hcalc : HasHolomorphicCalculusBound A
      (interior (Operator.numericalRange A)) 2) :
    ∃ f phi B : ℂ → ℂ,
      IsSchurOn (interior (Operator.numericalRange A)) f ∧
      ‖spectralJetEval A f‖ = 2 ∧
      HasMinimalNormOneJetsOn (interior (Operator.numericalRange A))
        (spectralJetNodes A) f ∧
      DifferentiableOn ℂ phi (interior (Operator.numericalRange A)) ∧
      BijOn phi (interior (Operator.numericalRange A)) (ball 0 1) ∧
      IsSchurFiniteBlaschke B ∧
      JetEq (spectralJetNodes A) (B ∘ phi) f ∧
      spectralJetEval A (B ∘ phi) = spectralJetEval A f ∧
      ‖spectralJetEval A (B ∘ phi)‖ = 2 ∧
      IsNonconstantOn (interior (Operator.numericalRange A)) (B ∘ phi) ∧
      ∀ g : ℂ → ℂ,
        IsSchurOn (interior (Operator.numericalRange A)) g →
        JetEq (spectralJetNodes A) g f →
        EqOn g (B ∘ phi) (interior (Operator.numericalRange A)) := by
  let U := interior (Operator.numericalRange A)
  have hnorm : holomorphicCalculusNorm A U = 2 :=
    holomorphicCalculusNorm_interior_numericalRange_eq_two A hpsi hcalc
  have hcalcNorm : HasHolomorphicCalculusBound A U (holomorphicCalculusNorm A U) := by
    rwa [hnorm]
  have hUb : Bornology.IsBounded U :=
    (Operator.isCompact_numericalRange A).isBounded.subset interior_subset
  have hUc : Convex ℝ U := (Operator.numericalRange_convex A).interior
  have h := exists_attained_finiteBlaschke_extremizer_at_holomorphicCalculusNorm
    A isOpen_interior hUc hInt hUb hspec (by rw [hnorm]; norm_num) hcalcNorm
  simpa [U, hnorm] using h

/-- Numerical-range extremizer from the sharp neighborhood-holomorphic
estimate.  The `H∞` functional-calculus estimate is derived internally by
convex radial approximation. -/
theorem exists_finiteBlaschke_extremizer_of_crouzeixConstant_eq_two_of_neighborhoods
    [Nonempty n] (A : Operator.SquareMatrix n)
    (hInt : (interior (Operator.numericalRange A)).Nonempty)
    (hspec : spectrum ℂ A ⊆ interior (Operator.numericalRange A))
    (hpsi : Operator.crouzeixConstant A = 2)
    (hnhd : HasNeighborhoodHolomorphicCalculusBound A
      (Operator.numericalRange A) 2) :
    ∃ f phi B : ℂ → ℂ,
      IsSchurOn (interior (Operator.numericalRange A)) f ∧
      ‖spectralJetEval A f‖ = 2 ∧
      HasMinimalNormOneJetsOn (interior (Operator.numericalRange A))
        (spectralJetNodes A) f ∧
      DifferentiableOn ℂ phi (interior (Operator.numericalRange A)) ∧
      BijOn phi (interior (Operator.numericalRange A)) (ball 0 1) ∧
      IsSchurFiniteBlaschke B ∧
      JetEq (spectralJetNodes A) (B ∘ phi) f ∧
      spectralJetEval A (B ∘ phi) = spectralJetEval A f ∧
      ‖spectralJetEval A (B ∘ phi)‖ = 2 ∧
      IsNonconstantOn (interior (Operator.numericalRange A)) (B ∘ phi) ∧
      ∀ g : ℂ → ℂ,
        IsSchurOn (interior (Operator.numericalRange A)) g →
        JetEq (spectralJetNodes A) g f →
        EqOn g (B ∘ phi) (interior (Operator.numericalRange A)) := by
  apply exists_finiteBlaschke_extremizer_of_crouzeixConstant_eq_two
    A hInt hspec hpsi
  exact hasHolomorphicCalculusBound_interior_numericalRange_of_neighborhoods
    A hInt hspec hnhd

/-- End-to-end analytic extremizer from a raw supporting Cauchy boundary.
The boundary package constructs the sharp neighborhood-holomorphic estimate;
convex radial approximation then constructs the full `H∞` estimate. -/
theorem exists_finiteBlaschke_extremizer_of_crouzeixConstant_eq_two_of_cauchyBoundary
    {i : Type*} [TopologicalSpace i] [MeasurableSpace i]
    [OpensMeasurableSpace i] {mu : MeasureTheory.Measure i}
    [BorelSpace i] [MeasureTheory.IsFiniteMeasure mu]
    [Nonempty n] (A : Operator.SquareMatrix n)
    (hInt : (interior (Operator.numericalRange A)).Nonempty)
    (hspec : spectrum ℂ A ⊆ interior (Operator.numericalRange A))
    (hpsi : Operator.crouzeixConstant A = 2)
    (B : NeighborhoodHolomorphicCauchyBoundary A
      (Operator.numericalRange A) mu) :
    ∃ f phi Bl : ℂ → ℂ,
      IsSchurOn (interior (Operator.numericalRange A)) f ∧
      ‖spectralJetEval A f‖ = 2 ∧
      HasMinimalNormOneJetsOn (interior (Operator.numericalRange A))
        (spectralJetNodes A) f ∧
      DifferentiableOn ℂ phi (interior (Operator.numericalRange A)) ∧
      BijOn phi (interior (Operator.numericalRange A)) (ball 0 1) ∧
      IsSchurFiniteBlaschke Bl ∧
      JetEq (spectralJetNodes A) (Bl ∘ phi) f ∧
      spectralJetEval A (Bl ∘ phi) = spectralJetEval A f ∧
      ‖spectralJetEval A (Bl ∘ phi)‖ = 2 ∧
      IsNonconstantOn (interior (Operator.numericalRange A)) (Bl ∘ phi) ∧
      ∀ g : ℂ → ℂ,
        IsSchurOn (interior (Operator.numericalRange A)) g →
        JetEq (spectralJetNodes A) g f →
        EqOn g (Bl ∘ phi) (interior (Operator.numericalRange A)) := by
  apply
    exists_finiteBlaschke_extremizer_of_crouzeixConstant_eq_two_of_neighborhoods
      A hInt hspec hpsi
  apply B.hasNeighborhoodHolomorphicCalculusBound
  exact charpoly_roots_subset_of_spectrum_subset A
    (hspec.trans interior_subset)

end

end DiskRigidity.Complex
