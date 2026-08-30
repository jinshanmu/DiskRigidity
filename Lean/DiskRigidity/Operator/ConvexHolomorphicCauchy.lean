/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.HolomorphicDoubleLayer
public import DiskRigidity.Complex.RemovablePolynomialQuotient
public import DiskRigidity.Operator.ConvexPolynomialCauchy
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# The ordinary holomorphic Cauchy formula on a convex boundary

The radial boundary is only Lipschitz.  We combine the Poincare primitive
theorem with the Banach-valued Lipschitz fundamental theorem, then remove the
finitely many poles of the matrix resolvent by Hermite-jet cancellation.
-/

@[expose] public section

noncomputable section

open Bornology Filter Function MeasureTheory Metric Set Topology
open scoped BoundedContinuousFunction InnerProductSpace Matrix
  Matrix.Norms.L2Operator NNReal Pointwise Topology

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n]

/-- A complex-differentiable Banach-valued one-form has zero integral around
the rectifiable radial boundary of a compact convex body. -/
theorem integral_normal_smul_eq_zero_of_differentiableOn
    (K : Set ℂ) (c : ℂ)
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (S : Set ℂ) (hSo : IsOpen S) (hSconv : Convex ℝ S) (hKS : K ⊆ S)
    (F : ℂ → EuclideanEndomorphism n) (hF : DifferentiableOn ℂ F S) :
    ∫ t, radialOutwardUnitNormal K c t •
        F (radialBoundaryParametrization K c t)
      ∂radialBoundaryArcLengthMeasure K c = 0 := by
  let sigma := radialBoundaryParametrization K c
  obtain ⟨P, hP⟩ := hSconv.exists_forall_hasDerivWithinAt hF
  have hPdiff : DifferentiableOn ℂ P S := fun z hz ↦
    (hP z hz).differentiableWithinAt
  have hPcontDiffK : ContDiffOn ℝ 1 P K :=
    ((hPdiff.contDiffOn hSo : ContDiffOn ℂ 1 P S).restrict_scalars ℝ).mono hKS
  obtain ⟨CP, hPlip⟩ := hPcontDiffK.exists_lipschitzOnWith
    (by norm_num) hconv hcompact
  obtain ⟨Csigma, hsigma⟩ :=
    exists_lipschitzWith_radialBoundaryParametrization hconv hc hcompact
  have hsigmaK : ∀ t : ℝ, sigma t ∈ K := by
    intro t
    have ht := radialBoundaryParametrization_mem_frontier hconv hc hcompact t
    exact hcompact.isClosed.closure_eq ▸ frontier_subset_closure ht
  have hcompLip : LipschitzWith (CP * Csigma) (P ∘ sigma) := by
    exact lipschitzOnWith_univ.mp <|
      hPlip.comp hsigma.lipschitzOnWith fun t _ ↦ hsigmaK t
  have hFTC := intervalIntegral_deriv_eq_sub_of_lipschitzWith
    hcompLip 0 (2 * Real.pi)
  have hclose : sigma (2 * Real.pi) = sigma 0 := by
    simpa [sigma] using radialBoundaryParametrization_periodic K c 0
  have hPclose : P (sigma (2 * Real.pi)) = P (sigma 0) := by rw [hclose]
  change ∫ x in (0 : ℝ)..(2 * Real.pi), deriv (P ∘ sigma) x =
    P (sigma (2 * Real.pi)) - P (sigma 0) at hFTC
  rw [hPclose, sub_self] at hFTC
  have hderivInt := intervalIntegrable_deriv_of_lipschitzWith
    hcompLip 0 (2 * Real.pi)
  rw [integral_radialBoundaryArcLengthMeasure_eq]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  let L : EuclideanEndomorphism n →L[ℂ] EuclideanEndomorphism n :=
    (ContinuousLinearMap.lsmul ℂ ℂ) Complex.I⁻¹
  calc
    ∫ t in (0 : ℝ)..(2 * Real.pi),
        radialBoundarySpeed K c t •
          (radialOutwardUnitNormal K c t • F (sigma t)) =
      ∫ t in (0 : ℝ)..(2 * Real.pi), L (deriv (P ∘ sigma) t) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards
          [hsigma.ae_differentiableAt_real,
            ae_deriv_eq_I_mul_normal_mul_speed hconv hc hcompact]
          with t ht hnormal _
        have hchain := ((hP (sigma t) (hKS (hsigmaK t))).hasDerivAt
          (hSo.mem_nhds (hKS (hsigmaK t)))).scomp t ht.hasDerivAt
        rw [hchain.deriv, hnormal]
        dsimp only [L, sigma, ContinuousLinearMap.lsmul_apply]
        rw [← IsScalarTower.smul_assoc, Complex.real_smul, smul_smul]
        congr 1
        field_simp
    _ = L (∫ t in (0 : ℝ)..(2 * Real.pi), deriv (P ∘ sigma) t) :=
      L.intervalIntegral_comp_comm hderivInt
    _ = 0 := by rw [hFTC]; simp

/-- Boundary restriction of an arbitrary continuous function on the compact
convex body. -/
def radialContinuousBoundaryFunction
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (g : ℂ → ℂ) (hg : ContinuousOn g K) : ℝ →ᵇ ℂ where
  toFun t := g (radialBoundaryParametrization K c t)
  continuous_toFun := by
    obtain ⟨C, hC⟩ :=
      exists_lipschitzWith_radialBoundaryParametrization hconv hc hcompact
    exact hg.comp_continuous hC.continuous fun t ↦ by
      have ht := radialBoundaryParametrization_mem_frontier hconv hc hcompact t
      have ht' := frontier_subset_closure ht
      simpa only [hcompact.isClosed.closure_eq] using ht'
  map_bounded' := by
    rw [← isBounded_range_iff]
    apply (hcompact.image_of_continuousOn hg).isBounded.subset
    rintro _ ⟨t, rfl⟩
    refine ⟨radialBoundaryParametrization K c t, ?_, rfl⟩
    have ht := radialBoundaryParametrization_mem_frontier hconv hc hcompact t
    have ht' := frontier_subset_closure ht
    simpa only [hcompact.isClosed.closure_eq] using ht'

@[simp]
theorem radialContinuousBoundaryFunction_apply
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (g : ℂ → ℂ) (hg : ContinuousOn g K) (t : ℝ) :
    radialContinuousBoundaryFunction hconv hc hcompact g hg t =
      g (radialBoundaryParametrization K c t) := rfl

/-- A uniform bound on the convex body controls the norm of its boundary
trace. -/
theorem norm_radialContinuousBoundaryFunction_le
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (g : ℂ → ℂ) (hg : ContinuousOn g K) {r : ℝ}
    (hr : 0 ≤ r) (hgr : ∀ z ∈ K, ‖g z‖ ≤ r) :
    ‖radialContinuousBoundaryFunction hconv hc hcompact g hg‖ ≤ r := by
  rw [BoundedContinuousFunction.norm_le hr]
  intro t
  apply hgr
  have ht := radialBoundaryParametrization_mem_frontier hconv hc hcompact t
  have ht' := frontier_subset_closure ht
  simpa only [hcompact.isClosed.closure_eq] using ht'

/-- Total boundary-trace operator.  For a function that is not continuous on
`K` its value is irrelevant and is set to zero; the Cauchy package only uses
this trace under a continuity hypothesis. -/
def radialBoundaryTrace
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (g : ℂ → ℂ) : ℝ →ᵇ ℂ := by
  classical
  exact if hg : ContinuousOn g K then
      radialContinuousBoundaryFunction hconv hc hcompact g hg
    else 0

theorem radialBoundaryTrace_eq
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (g : ℂ → ℂ) (hg : ContinuousOn g K) :
    radialBoundaryTrace hconv hc hcompact g =
      radialContinuousBoundaryFunction hconv hc hcompact g hg := by
  classical
  simp [radialBoundaryTrace, hg]

variable [DecidableEq n]

/-- The adjugate of the characteristic matrix, regarded as a Euclidean
operator. -/
def characteristicAdjugate (A : SquareMatrix n) (z : ℂ) :
    EuclideanEndomorphism n :=
  euclideanOperator ((z • (1 : SquareMatrix n) - A).adjugate)

/-- The characteristic adjugate is a polynomial, hence entire. -/
theorem differentiable_characteristicAdjugate (A : SquareMatrix n) :
    Differentiable ℂ (characteristicAdjugate A) := by
  have hadj : Differentiable ℂ
      (fun z : ℂ ↦ (z • (1 : SquareMatrix n) - A).adjugate) := by
    change Differentiable ℂ
      (fun z : ℂ ↦ fun i j ↦ (z • (1 : SquareMatrix n) - A).adjugate i j)
    rw [differentiable_pi]
    intro i
    rw [differentiable_pi]
    intro j
    simp only [Matrix.adjugate_apply, Matrix.det_apply', Matrix.updateRow_apply]
    apply Differentiable.fun_sum
    intro s _
    apply Differentiable.const_mul
    classical
    induction (Finset.univ : Finset n) using Finset.induction_on with
    | empty => simp
    | @insert k u hk ih =>
        simp only [Finset.prod_insert hk]
        apply Differentiable.mul
        · split_ifs <;> fun_prop
        · exact ih
  let eLin : SquareMatrix n →ₗ[ℂ] EuclideanEndomorphism n :=
    (euclideanOperator (n := n)).toAlgEquiv.toLinearEquiv.toLinearMap
  let eCLM : SquareMatrix n →L[ℂ] EuclideanEndomorphism n :=
    LinearMap.toContinuousLinearMap eLin
  exact eCLM.differentiable.comp hadj

/-- Cramer's formula for the concrete convex-boundary resolvent. -/
theorem convexBoundaryResolvent_eq_charpoly_inv_smul_adjugate
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hspectrum : spectrum ℂ A ⊆ interior K) (t : ℝ) :
    convexBoundaryResolvent A K c t =
      (A.charpoly.eval (radialBoundaryParametrization K c t))⁻¹ •
        ((radialBoundaryParametrization K c t) •
          (1 : SquareMatrix n) - A).adjugate := by
  have hR := radialBoundaryParametrization_mem_resolventSet
    A hconv hc hcompact hspectrum t
  rw [convexBoundaryResolvent, spectrum.resolvent_eq hR, Matrix.coe_units_inv]
  rw [hR.unit_spec, Matrix.inv_def, Matrix.eval_charpoly]
  simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_one_eq_diagonal,
    Matrix.scalar_apply, Ring.inverse_eq_inv]

/-- A continuous scalar boundary trace times the concrete resolvent density
is Bochner integrable. -/
theorem integrable_continuousBoundary_rightResolvent
    (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hspectrum : spectrum ℂ A ⊆ interior K)
    (g : ℂ → ℂ) (hg : ContinuousOn g K) :
    Integrable
      (fun t ↦ g (radialBoundaryParametrization K c t) •
        rightResolventBoundaryTerm
          (convexBoundaryResolvent A K c t)
          (radialOutwardUnitNormal K c t))
      (radialBoundaryArcLengthMeasure K c) := by
  let f := radialContinuousBoundaryFunction hconv hc hcompact g hg
  have hbase := integrable_rightResolventBoundaryTerm_convexBoundary
    A hconv hc hcompact hspectrum
  have hbounded : ∀ᵐ t ∂radialBoundaryArcLengthMeasure K c,
      ‖f t‖ ≤ ‖f‖ := Filter.Eventually.of_forall f.norm_coe_le_norm
  have h := hbase.bdd_smul ‖f‖ f.continuous.aestronglyMeasurable hbounded
  change Integrable
    (fun t ↦ f t • rightResolventBoundaryTerm
      (convexBoundaryResolvent A K c t)
      (radialOutwardUnitNormal K c t))
    (radialBoundaryArcLengthMeasure K c) at h
  simpa only [f, radialContinuousBoundaryFunction_apply] using h

/-- The ordinary Cauchy formula for every function holomorphic on a
neighborhood of a compact convex body.  No contour formula is assumed: the
polynomial formula, Hermite cancellation, and Poincare primitive theorem
prove it. -/
theorem holomorphicRightResolventIntegral_convexBoundary_eq
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K)
    (g : ℂ → ℂ) (V : Set ℂ)
    (hVo : IsOpen V) (hKV : K ⊆ V) (hg : DifferentiableOn ℂ g V) :
    DiskRigidity.Complex.holomorphicRightResolventIntegral
        (polynomialCauchyResolventBoundaryOfConvexBodyConcrete
          A hconv hc hcompact hWA hspectrum).toCauchyResolventBoundary g =
      ((2 * Real.pi : ℝ) : ℂ) •
        euclideanOperator (DiskRigidity.Complex.spectralJetEval A g) := by
  obtain ⟨delta, hdelta, hthickV⟩ :=
    hcompact.exists_thickening_subset_open hVo hKV
  let S : Set ℂ := Metric.thickening delta K
  have hSo : IsOpen S := Metric.isOpen_thickening
  have hSconv : Convex ℝ S := hconv.thickening delta
  have hKS : K ⊆ S := Metric.self_subset_thickening hdelta K
  have hSV : S ⊆ V := by simpa only [S] using hthickV
  have hgS : DifferentiableOn ℂ g S := hg.mono hSV
  let p : Polynomial ℂ := DiskRigidity.Complex.spectralJetPolynomial A g
  let h : ℂ → ℂ := fun z ↦ g z - p.eval z
  let Q : ℂ → ℂ :=
    DiskRigidity.Complex.removablePolynomialQuotient h A.charpoly
  let F : ℂ → EuclideanEndomorphism n := fun z ↦
    Q z • characteristicAdjugate A z
  have hhS : DifferentiableOn ℂ h S := by
    exact hgS.sub p.differentiable.differentiableOn
  have hQ : DifferentiableOn ℂ Q S := by
    apply DiskRigidity.Complex.differentiableOn_removablePolynomialQuotient
      (Matrix.charpoly_monic A).ne_zero hSo hhS
    intro a haS hroot k hk
    have hrootMem : a ∈ A.charpoly.roots :=
      (Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero).2 hroot
    let ar : DiskRigidity.Complex.HermiteRoot A.charpoly :=
      ⟨a, Multiset.mem_toFinset.mpr hrootMem⟩
    have hga : AnalyticAt ℂ g a := hgS.analyticAt (hSo.mem_nhds haS)
    dsimp only [h]
    rw [iteratedDeriv_fun_sub hga.contDiffAt
      (p.differentiable.analyticAt a).contDiffAt]
    exact sub_eq_zero.mpr
      (DiskRigidity.Complex.iteratedDeriv_spectralJetPolynomial_eval
        (f := g) A ar hk).symm
  have hF : DifferentiableOn ℂ F S := by
    intro z hz
    exact (hQ z hz).smul
      ((differentiable_characteristicAdjugate A).differentiableAt.differentiableWithinAt)
  have hFboundary (t : ℝ) :
      F (radialBoundaryParametrization K c t) =
        h (radialBoundaryParametrization K c t) •
          euclideanOperator (convexBoundaryResolvent A K c t) := by
    let z := radialBoundaryParametrization K c t
    have hzfront := radialBoundaryParametrization_mem_frontier
      hconv hc hcompact t
    have hznotSpec : z ∉ spectrum ℂ A := by
      intro hz
      exact hzfront.2 (hspectrum hz)
    have hchar : A.charpoly.eval z ≠ 0 := by
      intro hz
      apply hznotSpec
      exact Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hz
    rw [show F z = Q z • characteristicAdjugate A z from rfl,
      show Q z = h z / A.charpoly.eval z by
        exact DiskRigidity.Complex.removablePolynomialQuotient_eq_of_eval_ne_zero
          h A.charpoly hchar,
      convexBoundaryResolvent_eq_charpoly_inv_smul_adjugate
        A hconv hc hcompact hspectrum t]
    simp only [characteristicAdjugate, map_smul, div_eq_mul_inv]
    module
  have hzeroForm := integral_normal_smul_eq_zero_of_differentiableOn
    K c hconv hc hcompact S hSo hSconv hKS F hF
  have hzeroBoundary :
      ∫ t, h (radialBoundaryParametrization K c t) •
          rightResolventBoundaryTerm
            (convexBoundaryResolvent A K c t)
            (radialOutwardUnitNormal K c t)
        ∂radialBoundaryArcLengthMeasure K c = 0 := by
    calc
      ∫ t, h (radialBoundaryParametrization K c t) •
          rightResolventBoundaryTerm
            (convexBoundaryResolvent A K c t)
            (radialOutwardUnitNormal K c t)
        ∂radialBoundaryArcLengthMeasure K c =
        ∫ t, radialOutwardUnitNormal K c t •
            F (radialBoundaryParametrization K c t)
          ∂radialBoundaryArcLengthMeasure K c := by
            apply integral_congr_ae
            filter_upwards with t
            rw [hFboundary]
            simp only [rightResolventBoundaryTerm]
            module
      _ = 0 := hzeroForm
  have hgK : ContinuousOn g K := hg.continuousOn.mono hKV
  have hpK : ContinuousOn (fun z ↦ p.eval z) K :=
    p.continuous.continuousOn
  have hgInt := integrable_continuousBoundary_rightResolvent
    A hconv hc hcompact hspectrum g hgK
  have hpInt := integrable_continuousBoundary_rightResolvent
    A hconv hc hcompact hspectrum (fun z ↦ p.eval z) hpK
  rw [DiskRigidity.Complex.holomorphicRightResolventIntegral]
  change (∫ t, g (radialBoundaryParametrization K c t) •
      rightResolventBoundaryTerm
        (convexBoundaryResolvent A K c t)
        (radialOutwardUnitNormal K c t)
      ∂radialBoundaryArcLengthMeasure K c) = _
  have heqIntegral :
      (∫ t, g (radialBoundaryParametrization K c t) •
          rightResolventBoundaryTerm
            (convexBoundaryResolvent A K c t)
            (radialOutwardUnitNormal K c t)
        ∂radialBoundaryArcLengthMeasure K c) =
      ∫ t, p.eval (radialBoundaryParametrization K c t) •
          rightResolventBoundaryTerm
            (convexBoundaryResolvent A K c t)
            (radialOutwardUnitNormal K c t)
        ∂radialBoundaryArcLengthMeasure K c := by
    apply sub_eq_zero.mp
    rw [← integral_sub hgInt hpInt]
    calc
      ∫ t, g (radialBoundaryParametrization K c t) •
            rightResolventBoundaryTerm
              (convexBoundaryResolvent A K c t)
              (radialOutwardUnitNormal K c t) -
          p.eval (radialBoundaryParametrization K c t) •
            rightResolventBoundaryTerm
              (convexBoundaryResolvent A K c t)
              (radialOutwardUnitNormal K c t)
        ∂radialBoundaryArcLengthMeasure K c =
        ∫ t, h (radialBoundaryParametrization K c t) •
            rightResolventBoundaryTerm
              (convexBoundaryResolvent A K c t)
              (radialOutwardUnitNormal K c t)
          ∂radialBoundaryArcLengthMeasure K c := by
            apply integral_congr_ae
            filter_upwards with t
            dsimp only [h]
            module
      _ = 0 := hzeroBoundary
  rw [heqIntegral]
  simpa only [p, polynomialRightResolventIntegral,
    DiskRigidity.Complex.spectralJetEval_eq_polynomialEval] using
      polynomialRightResolventIntegral_convexBoundary_eq
        A hconv hc hcompact hWA hspectrum p

/-- The fully concrete neighborhood-holomorphic Cauchy boundary attached to
a compact convex body containing the numerical range and containing the
spectrum in its interior. -/
def neighborhoodHolomorphicCauchyBoundaryOfConvexBody
    [Nonempty n] (A : SquareMatrix n) {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K) :
    DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary A K
      (radialBoundaryArcLengthMeasure K c) where
  toCauchyResolventBoundary :=
    (polynomialCauchyResolventBoundaryOfConvexBodyConcrete
      A hconv hc hcompact hWA hspectrum).toCauchyResolventBoundary
  boundaryPoint_mem := Filter.Eventually.of_forall fun t ↦ by
    change radialBoundaryParametrization K c t ∈ K
    have ht := radialBoundaryParametrization_mem_frontier hconv hc hcompact t
    have ht' := frontier_subset_closure ht
    simpa only [hcompact.isClosed.closure_eq] using ht'
  boundaryTrace := radialBoundaryTrace hconv hc hcompact
  boundaryTrace_eq := by
    intro g hg
    filter_upwards with t
    rw [radialBoundaryTrace_eq hconv hc hcompact g hg]
    rfl
  boundaryTrace_norm_le := by
    intro g r hg hr
    rw [radialBoundaryTrace_eq hconv hc hcompact g hg]
    have hr0 : 0 ≤ r :=
      (norm_nonneg (g c)).trans (hr c (interior_subset hc))
    exact norm_radialContinuousBoundaryFunction_le
      hconv hc hcompact g hg hr0 hr
  holomorphic_cauchy := by
    intro g V hVo hKV hg
    exact holomorphicRightResolventIntegral_convexBoundary_eq
      A hconv hc hcompact hWA hspectrum g V hVo hKV hg

end DiskRigidity.Operator
