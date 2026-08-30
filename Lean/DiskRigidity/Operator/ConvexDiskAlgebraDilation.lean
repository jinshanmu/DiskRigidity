/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.ConvexRadialApproximation
public import DiskRigidity.Operator.HolomorphicEqualityData

/-!
# Disk-algebra dilations by convex radial contraction

A function continuous on a compact convex body and holomorphic in its
interior is contracted toward an interior point.  Each contraction is
holomorphic on a neighborhood of the whole body, so a neighborhood Cauchy
boundary evaluates it.  Uniform convergence on the compact body and local
uniform convergence in the interior then give the original function's
Cauchy formula and exact double-layer dilation.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Metric Set Topology
open scoped BoundedContinuousFunction InnerProductSpace Matrix
  Matrix.Norms.L2Operator NNReal Pointwise

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Standard radial contractions converge uniformly on a compact convex body
for every function continuous on that body. -/
theorem tendstoUniformlyOn_comp_standardRadialContract_compactConvex
    {K : Set ℂ} {c : ℂ} (hconv : Convex ℝ K)
    (hc : c ∈ interior K) (hcompact : IsCompact K)
    (g : ℂ → ℂ) (hgK : ContinuousOn g K) :
    TendstoUniformlyOn
      (fun m ↦ g ∘ DiskRigidity.Complex.radialContract c
        (DiskRigidity.Complex.standardRadialFactor m))
      g atTop K := by
  have hKne : K.Nonempty := ⟨c, interior_subset hc⟩
  have hguc : UniformContinuousOn g K :=
    hcompact.uniformContinuousOn_of_continuous hgK
  obtain ⟨w, hwK, hwmax⟩ := hcompact.exists_isMaxOn hKne
    (continuous_id.dist (continuous_const : Continuous fun _ : ℂ ↦ c)).continuousOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨η, hη, hgη⟩ := Metric.uniformContinuousOn_iff.mp hguc ε hε
  have hcoef : Tendsto
      (fun m ↦ |1 - DiskRigidity.Complex.standardRadialFactor m| * dist w c)
      atTop (nhds 0) := by
    simpa only [sub_self, abs_zero, zero_mul] using
      (((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub
        DiskRigidity.Complex.tendsto_standardRadialFactor).abs.mul
          (tendsto_const_nhds :
            Tendsto (fun _ : ℕ ↦ dist w c) atTop (nhds (dist w c))))
  filter_upwards [hcoef (Iio_mem_nhds hη)] with m hm
  intro z hzK
  have hradK : DiskRigidity.Complex.radialContract c
      (DiskRigidity.Complex.standardRadialFactor m) z ∈ K := by
    exact hconv (interior_subset hc) hzK
      (sub_nonneg.mpr
        (DiskRigidity.Complex.standardRadialFactor_lt_one m).le)
      (DiskRigidity.Complex.standardRadialFactor_nonneg m) (by ring)
  apply hgη z hzK _ hradK
  rw [DiskRigidity.Complex.dist_radialContract]
  exact (mul_le_mul_of_nonneg_left (hwmax hzK) (abs_nonneg _)).trans_lt hm

variable {i : Type*} [TopologicalSpace i] [MeasurableSpace i]
  [OpensMeasurableSpace i] {mu : Measure i}
  [BorelSpace i] [IsFiniteMeasure mu]

omit [BorelSpace i] [IsFiniteMeasure mu] in
/-- The ordinary Cauchy formula extends from neighborhood-holomorphic
functions to every function in the disk algebra of a compact convex body. -/
theorem holomorphic_cauchy_of_convex_radial_contraction
    {A : SquareMatrix n} {K : Set ℂ} {c : ℂ}
    (B : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary A K mu)
    (hconv : Convex ℝ K) (hc : c ∈ interior K)
    (hcompact : IsCompact K)
    (g : ℂ → ℂ) (hgK : ContinuousOn g K)
    (hg : DifferentiableOn ℂ g (interior K))
    (hroots : ∀ z ∈ A.charpoly.roots, z ∈ interior K) :
    DiskRigidity.Complex.holomorphicRightResolventIntegral
        B.toCauchyResolventBoundary g =
      ((2 * Real.pi : ℝ) : ℂ) •
        euclideanOperator (DiskRigidity.Complex.spectralJetEval A g) := by
  let r : ℕ → ℝ := DiskRigidity.Complex.standardRadialFactor
  let Fscalar : ℕ → ℂ → ℂ := fun m ↦
    g ∘ DiskRigidity.Complex.radialContract c (r m)
  let base : i → EuclideanEndomorphism n := fun t ↦
    rightResolventBoundaryTerm (B.resolvent t) (B.outwardNormal t)
  let F : ℕ → i → EuclideanEndomorphism n := fun m t ↦
    Fscalar m (B.boundaryPoint t) • base t
  let G : i → EuclideanEndomorphism n := fun t ↦
    g (B.boundaryPoint t) • base t
  have hclosure : closure (interior K) = K := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior ⟨c, hc⟩,
      hcompact.isClosed.closure_eq]
  have hradK (m : ℕ) : MapsTo
      (DiskRigidity.Complex.radialContract c (r m)) K K := by
    intro z hzK
    exact hconv (interior_subset hc) hzK
      (sub_nonneg.mpr
        (DiskRigidity.Complex.standardRadialFactor_lt_one m).le)
      (DiskRigidity.Complex.standardRadialFactor_nonneg m) (by ring)
  have hFscalarK (m : ℕ) : ContinuousOn (Fscalar m) K :=
    hgK.comp (DiskRigidity.Complex.continuous_radialContract c (r m)).continuousOn
      (hradK m)
  have huniform : TendstoUniformlyOn Fscalar g atTop K := by
    simpa only [Fscalar, r] using
      tendstoUniformlyOn_comp_standardRadialContract_compactConvex
        hconv hc hcompact g hgK
  have hFint (m : ℕ) : Integrable (F m) mu := by
    let fm := B.boundaryTrace (Fscalar m)
    have hfm : Integrable (fun t ↦ fm t • base t) mu :=
      B.integrable_right.bdd_smul ‖fm‖
        fm.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fm.norm_coe_le_norm)
    exact hfm.congr <| (B.boundaryTrace_eq (Fscalar m) (hFscalarK m)).mono
      fun t ht ↦ by simp only [F, fm, ht]
  have hclose : ∀ᶠ m in atTop, ∀ z ∈ K,
      dist (g z) (Fscalar m z) < 1 :=
    (Metric.tendstoUniformlyOn_iff.mp huniform) 1 zero_lt_one
  let R := ‖B.boundaryTrace g‖
  have hbound : ∀ᶠ m in atTop, ∀ᵐ t ∂mu,
      ‖F m t‖ ≤ (R + 1) * ‖base t‖ := by
    filter_upwards [hclose] with m hm
    filter_upwards [B.boundaryPoint_mem,
      B.boundaryTrace_eq g hgK] with t htK httrace
    simp only [F, norm_smul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖Fscalar m (B.boundaryPoint t)‖ ≤
          ‖g (B.boundaryPoint t)‖ +
            ‖g (B.boundaryPoint t) - Fscalar m (B.boundaryPoint t)‖ :=
        norm_le_norm_add_norm_sub _ _
      _ ≤ ‖g (B.boundaryPoint t)‖ + 1 := by
        rw [← dist_eq_norm]
        gcongr
        exact (hm _ htK).le
      _ ≤ R + 1 := by
        gcongr
        rw [← httrace]
        exact (B.boundaryTrace g).norm_coe_le_norm t
  have hboundInt : Integrable (fun t ↦ (R + 1) * ‖base t‖) mu :=
    B.integrable_right.norm.const_mul (R + 1)
  have hpoint : ∀ᵐ t ∂mu,
      Tendsto (fun m ↦ F m t) atTop (nhds (G t)) := by
    filter_upwards [B.boundaryPoint_mem] with t ht
    exact (huniform.tendsto_at ht).smul_const (base t)
  have hintegral : Tendsto (fun m ↦ ∫ t, F m t ∂mu) atTop
      (nhds (∫ t, G t ∂mu)) :=
    tendsto_integral_filter_of_dominated_convergence
      (fun t ↦ (R + 1) * ‖base t‖)
      (Filter.Eventually.of_forall fun m ↦ (hFint m).aestronglyMeasurable)
      hbound hboundInt hpoint
  have hpackage (m : ℕ) :
      ∃ V : Set ℂ, IsOpen V ∧ K ⊆ V ∧
        DifferentiableOn ℂ (Fscalar m) V := by
    let V := DiskRigidity.Complex.radialAnalyticDomain
      (interior K) c (r m)
    refine ⟨V,
      DiskRigidity.Complex.isOpen_radialAnalyticDomain isOpen_interior c (r m),
      ?_, ?_⟩
    · rw [← hclosure]
      exact DiskRigidity.Complex.closure_subset_radialAnalyticDomain
        isOpen_interior hconv.interior hc
          (DiskRigidity.Complex.standardRadialFactor_nonneg m)
          (DiskRigidity.Complex.standardRadialFactor_lt_one m)
    · exact DiskRigidity.Complex.differentiableOn_radialAnalyticDomain hg c (r m)
  have hFd (m : ℕ) : DifferentiableOn ℂ (Fscalar m) (interior K) := by
    obtain ⟨V, _hVo, hKV, hFV⟩ := hpackage m
    exact hFV.mono (interior_subset.trans hKV)
  have hloc : TendstoLocallyUniformlyOn Fscalar g atTop (interior K) :=
    huniform.tendstoLocallyUniformlyOn.mono interior_subset
  have heval :=
    DiskRigidity.Complex.spectralJetEval_tendsto_of_tendstoLocallyUniformlyOn
      A isOpen_interior hFd hroots hloc
  have hop : Tendsto
      (fun m ↦ euclideanOperator
        (DiskRigidity.Complex.spectralJetEval A (Fscalar m))) atTop
      (nhds (euclideanOperator
        (DiskRigidity.Complex.spectralJetEval A g))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    rw [tendsto_iff_norm_sub_tendsto_zero] at heval
    simpa only [← map_sub, ← matrix_norm_eq_operator_norm] using heval
  have hright : Tendsto
      (fun m ↦ ((2 * Real.pi : ℝ) : ℂ) • euclideanOperator
        (DiskRigidity.Complex.spectralJetEval A (Fscalar m))) atTop
      (nhds (((2 * Real.pi : ℝ) : ℂ) •
        euclideanOperator (DiskRigidity.Complex.spectralJetEval A g))) :=
    hop.const_smul _
  have hcauchy (m : ℕ) :
      ∫ t, F m t ∂mu =
        ((2 * Real.pi : ℝ) : ℂ) • euclideanOperator
          (DiskRigidity.Complex.spectralJetEval A (Fscalar m)) := by
    obtain ⟨V, hVo, hKV, hFV⟩ := hpackage m
    simpa only [F, base,
      DiskRigidity.Complex.holomorphicRightResolventIntegral] using
      B.holomorphic_cauchy (Fscalar m) V hVo hKV hFV
  have hintegral' : Tendsto (fun m ↦ ∫ t, F m t ∂mu) atTop
      (nhds (((2 * Real.pi : ℝ) : ℂ) •
        euclideanOperator (DiskRigidity.Complex.spectralJetEval A g))) :=
    (tendsto_congr' (Filter.Eventually.of_forall hcauchy)).mpr hright
  have hlimit := tendsto_nhds_unique hintegral hintegral'
  simpa only [G, base,
    DiskRigidity.Complex.holomorphicRightResolventIntegral] using hlimit

/-- A neighborhood Cauchy boundary on a compact convex body constructs the
complete disk-algebra double-layer dilation, with no approximation
hypothesis. -/
def convexDiskAlgebraDilationData
    {A : SquareMatrix n} {K : Set ℂ} {c : ℂ}
    (B : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary A K mu)
    (hconv : Convex ℝ K) (hc : c ∈ interior K)
    (hcompact : IsCompact K)
    (g : ℂ → ℂ) (hgK : ContinuousOn g K)
    (hg : DifferentiableOn ℂ g (interior K))
    (hroots : ∀ z ∈ A.charpoly.roots, z ∈ interior K)
    (hgOne : ∀ z ∈ K, ‖g z‖ ≤ 1) :
    HolomorphicResolventDilationData B.toCauchyResolventBoundary g where
  analyticAt_roots := fun a ↦ hg.analyticAt
    (isOpen_interior.mem_nhds
      (hroots (a : ℂ) (Multiset.mem_toFinset.mp a.2)))
  boundaryFunction := B.boundaryTrace g
  boundaryFunction_eq := B.boundaryTrace_eq g hgK
  boundaryFunction_norm_le_one :=
    B.boundaryTrace_norm_le g 1 hgK hgOne
  cauchy_pow := fun k _hk ↦
    holomorphic_cauchy_of_convex_radial_contraction
      B hconv hc hcompact (fun z ↦ g z ^ k)
        (hgK.pow k) (hg.pow k) hroots

/-- The unconditional factor-two estimate for a disk-algebra function once
the concrete neighborhood Cauchy boundary has been constructed. -/
theorem norm_spectralJetEval_le_two_of_convex_diskAlgebra
    [Nonempty n] {A : SquareMatrix n} {K : Set ℂ} {c : ℂ}
    (B : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary A K mu)
    (hconv : Convex ℝ K) (hc : c ∈ interior K)
    (hcompact : IsCompact K)
    (g : ℂ → ℂ) (hgK : ContinuousOn g K)
    (hg : DifferentiableOn ℂ g (interior K))
    (hroots : ∀ z ∈ A.charpoly.roots, z ∈ interior K)
    (hgOne : ∀ z ∈ K, ‖g z‖ ≤ 1) :
    ‖DiskRigidity.Complex.spectralJetEval A g‖ ≤ 2 := by
  let P := convexDiskAlgebraDilationData B
    hconv hc hcompact g hgK hg hroots hgOne
  rw [matrix_norm_eq_operator_norm]
  exact P.witness.norm_le_two

end DiskRigidity.Operator
