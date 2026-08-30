/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.HolomorphicDoubleLayer
public import DiskRigidity.Operator.ConcreteEqualityData
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Holomorphic equality data from a concrete Cauchy boundary

This file packages the double-layer construction for a genuine holomorphic
boundary function.  Unlike the polynomial package, its matrix value is the
finite spectral-jet calculus.  The construction still derives the positive
square root, all adjoint-weighted formulas, the bounded commuting dilation
errors, and the almost-everywhere kernel identity.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory
open scoped BoundedContinuousFunction InnerProductSpace Matrix
  Matrix.Norms.L2Operator ComplexConjugate

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {i : Type*} [TopologicalSpace i] [MeasurableSpace i]
  [OpensMeasurableSpace i] {mu : Measure i}

/-- Reflection of a scalar holomorphic function across the real axis, used
for the adjoint equality run. -/
def reflectedHolomorphicFunction (g : ℂ → ℂ) : ℂ → ℂ :=
  star ∘ g ∘ conj

/-- Every iterated complex derivative commutes with simultaneous conjugation
of the argument and value. -/
theorem iteratedDeriv_reflectedHolomorphicFunction
    (g : ℂ → ℂ) (k : ℕ) :
    iteratedDeriv k (reflectedHolomorphicFunction g) =
      reflectedHolomorphicFunction (iteratedDeriv k g) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [iteratedDeriv_succ, ih]
      unfold reflectedHolomorphicFunction
      exact deriv_star_conj (𝕜 := ℂ) (F := ℂ)

/-- The characteristic polynomial of the adjoint is obtained by conjugating
all coefficients. -/
theorem charpoly_conjTranspose (A : SquareMatrix n) :
    Aᴴ.charpoly = A.charpoly.map (starRingEnd ℂ) := by
  rw [Matrix.conjTranspose]
  change (Aᵀ.map (starRingEnd ℂ)).charpoly = _
  rw [Matrix.charpoly_map, Matrix.charpoly_transpose]

/-- Spectral-jet evaluation intertwines reflected functions and matrix
adjoints.  This is proved directly from the finite Hermite jets, including
all algebraic multiplicities. -/
theorem spectralJetEval_reflected_conjTranspose
    (A : SquareMatrix n) (g : ℂ → ℂ) :
    DiskRigidity.Complex.spectralJetEval Aᴴ
        (reflectedHolomorphicFunction g) =
      (DiskRigidity.Complex.spectralJetEval A g)ᴴ := by
  let p := DiskRigidity.Complex.spectralJetPolynomial A g
  let q := conjugatePolynomial p
  have hjet : DiskRigidity.Complex.spectralJetEval Aᴴ
      (reflectedHolomorphicFunction g) =
      DiskRigidity.Complex.spectralJetEval Aᴴ (fun z ↦ q.eval z) := by
    apply DiskRigidity.Complex.spectralJetEval_eq_of_iteratedDeriv_eq Aᴴ
    intro a k
    have haRoot : Polynomial.IsRoot Aᴴ.charpoly (a : ℂ) := by
      exact (Polynomial.mem_roots (Matrix.charpoly_monic Aᴴ).ne_zero).mp
        (Multiset.mem_toFinset.mp a.2)
    have haSpec : (a : ℂ) ∈ spectrum ℂ Aᴴ :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.mpr haRoot
    have hbSpec : starRingEnd ℂ (a : ℂ) ∈ spectrum ℂ A := by
      rw [spectrum_conjTranspose A] at haSpec
      obtain ⟨w, hw, hwa⟩ := haSpec
      have hw_eq : w = starRingEnd ℂ (a : ℂ) := by
        calc
          w = starRingEnd ℂ (starRingEnd ℂ w) := by simp
          _ = starRingEnd ℂ (a : ℂ) :=
            congrArg (starRingEnd ℂ) hwa
      rwa [← hw_eq]
    have hbRoot : Polynomial.IsRoot A.charpoly
        (starRingEnd ℂ (a : ℂ)) :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.mp hbSpec
    let b : DiskRigidity.Complex.HermiteRoot A.charpoly :=
      ⟨starRingEnd ℂ (a : ℂ),
        Multiset.mem_toFinset.mpr
          ((Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero).mpr hbRoot)⟩
    have hmult : A.charpoly.rootMultiplicity (b : ℂ) =
        Aᴴ.charpoly.rootMultiplicity (a : ℂ) := by
      calc
        A.charpoly.rootMultiplicity (b : ℂ) =
            (A.charpoly.map (starRingEnd ℂ)).rootMultiplicity
              (starRingEnd ℂ (b : ℂ)) :=
          Polynomial.eq_rootMultiplicity_map
            (f := starRingEnd ℂ) (starRingEnd ℂ).injective (b : ℂ)
        _ = (A.charpoly.map (starRingEnd ℂ)).rootMultiplicity (a : ℂ) := by
          simp [b]
        _ = Aᴴ.charpoly.rootMultiplicity (a : ℂ) := by
          exact congrArg (fun r : Polynomial ℂ ↦
            r.rootMultiplicity (a : ℂ)) (charpoly_conjTranspose A).symm
    have hkA : k.val < A.charpoly.rootMultiplicity (b : ℂ) := by
      rw [hmult]
      exact k.isLt
    have hpjet :=
      DiskRigidity.Complex.iteratedDeriv_spectralJetPolynomial_eval
        (f := g) A b hkA
    have hreflg := congrFun
      (iteratedDeriv_reflectedHolomorphicFunction g k.val) (a : ℂ)
    have hreflp := congrFun
      (iteratedDeriv_reflectedHolomorphicFunction
        (fun z ↦ p.eval z) k.val) (a : ℂ)
    have hqfun : (fun z ↦ q.eval z) =
        reflectedHolomorphicFunction (fun z ↦ p.eval z) := by
      funext z
      simp [q, p, reflectedHolomorphicFunction, conjugatePolynomial_eval]
    rw [hqfun, hreflg, hreflp]
    change star (iteratedDeriv k.val g (b : ℂ)) =
      star (iteratedDeriv k.val (fun z ↦ p.eval z) (b : ℂ))
    rw [hpjet]
  rw [hjet, DiskRigidity.Complex.spectralJetEval_polynomial,
    show q = conjugatePolynomial p from rfl,
    polynomialEval_conjugate_conjTranspose,
    show polynomialEval p A =
      DiskRigidity.Complex.spectralJetEval A g from rfl]

/-- Operator form of `spectralJetEval_reflected_conjTranspose`. -/
theorem euclideanOperator_spectralJetEval_reflected_conjTranspose
    (A : SquareMatrix n) (g : ℂ → ℂ) :
    euclideanOperator (DiskRigidity.Complex.spectralJetEval Aᴴ
      (reflectedHolomorphicFunction g)) =
      ContinuousLinearMap.adjoint
        (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g)) := by
  rw [spectralJetEval_reflected_conjTranspose,
    euclideanOperator_conjTranspose]

/-- Function-specific data needed for the holomorphic double-layer
dilation.  The Cauchy input is only the ordinary holomorphic formula for
positive powers of the boundary function. -/
structure HolomorphicResolventDilationData
    {A : SquareMatrix n} (B : CauchyResolventBoundary A mu)
    (g : ℂ → ℂ) where
  analyticAt_roots : ∀ a : DiskRigidity.Complex.HermiteRoot A.charpoly,
    AnalyticAt ℂ g (a : ℂ)
  /-- The bounded boundary trace used as the multiplication symbol in the
  dilation. -/
  boundaryFunction : i →ᵇ ℂ
  boundaryFunction_eq : ∀ᵐ t ∂mu,
    boundaryFunction t = g (B.boundaryPoint t)
  boundaryFunction_norm_le_one : ‖boundaryFunction‖ ≤ 1
  cauchy_pow : ∀ k : ℕ, 1 ≤ k →
    DiskRigidity.Complex.holomorphicRightResolventIntegral B
        (fun z ↦ g z ^ k) =
      ((2 * Real.pi : ℝ) : ℂ) •
        euclideanOperator
          (DiskRigidity.Complex.spectralJetEval A (fun z ↦ g z ^ k))

variable [BorelSpace i] [IsFiniteMeasure mu]

/-- The canonical square root of the concrete positive double layer. -/
def HolomorphicResolventDilationData.squareRoot
    {A : SquareMatrix n} {B : CauchyResolventBoundary A mu}
    {g : ℂ → ℂ} (_P : HolomorphicResolventDilationData B g) :
    PositiveBoundarySquareRoot B.positiveDensity :=
  B.positiveDensity.canonicalSquareRoot

omit [OpensMeasurableSpace i] [BorelSpace i] [IsFiniteMeasure mu] in
/-- Ordinary holomorphic Cauchy formulas give the conjugate-weighted
adjoint identities used by the dilation. -/
theorem HolomorphicResolventDilationData.weighted_adjoint_cauchy
    {A : SquareMatrix n} {B : CauchyResolventBoundary A mu}
    {g : ℂ → ℂ} (P : HolomorphicResolventDilationData B g)
    (k : ℕ) (hk : 1 ≤ k) :
    weightedAdjointResolventIntegral (mu := mu)
        B.outwardNormal B.resolvent P.boundaryFunction k =
      ((2 * Real.pi : ℝ) : ℂ) •
        (ContinuousLinearMap.adjoint
          (euclideanOperator
            (DiskRigidity.Complex.spectralJetEval A g))) ^ k := by
  have hright :
      ∫ t, ((P.boundaryFunction ^ k : i →ᵇ ℂ) t) •
          rightResolventBoundaryTerm
            (B.resolvent t) (B.outwardNormal t) ∂mu =
        DiskRigidity.Complex.holomorphicRightResolventIntegral B
          (fun z ↦ g z ^ k) := by
    rw [DiskRigidity.Complex.holomorphicRightResolventIntegral]
    apply integral_congr_ae
    filter_upwards [P.boundaryFunction_eq] with t ht
    simp [ht]
  rw [weightedAdjointResolventIntegral,
    integral_conjugateBoundary_adjointResolvent_eq_star,
    hright, P.cauchy_pow k hk,
    DiskRigidity.Complex.spectralJetEval_pow A P.analyticAt_roots k]
  simp [ContinuousLinearMap.star_eq_adjoint]

/-- Exact error formula for the holomorphic dilation. -/
theorem HolomorphicResolventDilationData.error_eq
    {A : SquareMatrix n} {B : CauchyResolventBoundary A mu}
    {g : ℂ → ℂ} (P : HolomorphicResolventDilationData B g)
    (k : ℕ) (hk : 1 ≤ k) :
    dilationError
        (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g))
        (boundaryMultiplier (E := EuclideanVector n) (mu := mu)
          P.boundaryFunction)
        P.squareRoot.boundaryIsometry k =
      normalizedRightResolventIntegral (mu := mu)
        B.outwardNormal B.resolvent P.boundaryFunction k := by
  exact dilationError_eq_normalizedRightResolventIntegral P.squareRoot
    (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g))
    B.outwardNormal B.resolvent P.boundaryFunction k
    (Filter.Eventually.of_forall fun t ↦ by
      simp [CauchyResolventBoundary.positiveDensity_apply])
    B.integrable_right B.integrable_adjoint
      (P.weighted_adjoint_cauchy k hk)

/-- The holomorphic dilation errors are uniformly bounded. -/
theorem HolomorphicResolventDilationData.errors_bounded
    {A : SquareMatrix n} {B : CauchyResolventBoundary A mu}
    {g : ℂ → ℂ} (P : HolomorphicResolventDilationData B g) :
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k →
      ‖dilationError
        (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g))
        (boundaryMultiplier (E := EuclideanVector n) (mu := mu)
          P.boundaryFunction)
        P.squareRoot.boundaryIsometry k‖ ≤ C := by
  refine ⟨(2 * Real.pi)⁻¹ *
    ∫ t, ‖rightResolventBoundaryTerm
      (B.resolvent t) (B.outwardNormal t)‖ ∂mu, ?_⟩
  intro k hk
  rw [P.error_eq k hk]
  exact norm_normalizedRightResolventIntegral_le B.outwardNormal
    B.resolvent P.boundaryFunction P.boundaryFunction_norm_le_one
    B.integrable_right k

/-- Every error commutes with the spectral-jet matrix value. -/
theorem HolomorphicResolventDilationData.errors_commute
    {A : SquareMatrix n} {B : CauchyResolventBoundary A mu}
    {g : ℂ → ℂ} (P : HolomorphicResolventDilationData B g) :
    ∀ k : ℕ, 1 ≤ k →
      Commute
        (dilationError
          (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g))
          (boundaryMultiplier (E := EuclideanVector n) (mu := mu)
            P.boundaryFunction)
          P.squareRoot.boundaryIsometry k)
        (euclideanOperator
          (DiskRigidity.Complex.spectralJetEval A g)) := by
  intro k hk
  rw [P.error_eq k hk]
  simpa only [DiskRigidity.Complex.spectralJetEval_eq_polynomialEval] using
    normalizedRightResolventIntegral_commutes_polynomialEval
      A B.boundaryPoint B.outwardNormal B.resolvent P.boundaryFunction
      (DiskRigidity.Complex.spectralJetPolynomial A g) k
      B.resolvent_ae B.integrable_right

/-- The exact dilation witness for a holomorphic boundary function. -/
def HolomorphicResolventDilationData.witness
    {A : SquareMatrix n} {B : CauchyResolventBoundary A mu}
    {g : ℂ → ℂ} (P : HolomorphicResolventDilationData B g) :
    DilationWitness (K := Lp (EuclideanVector n) 2 mu)
      (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g)) :=
  boundaryDilationWitness
    (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g))
    P.squareRoot P.boundaryFunction P.boundaryFunction_norm_le_one
    P.errors_bounded P.errors_commute

/-- A neighborhood-holomorphic Cauchy package constructs the complete
holomorphic dilation record. -/
def _root_.DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary.dilationData
    {A : SquareMatrix n} {K : Set ℂ}
    (B : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary A K mu)
    (hroots : ∀ z ∈ A.charpoly.roots, z ∈ K)
    (g : ℂ → ℂ) (V : Set ℂ)
    (hVo : IsOpen V) (hKV : K ⊆ V) (hg : DifferentiableOn ℂ g V)
    (hgOne : ∀ z ∈ K, ‖g z‖ ≤ 1) :
    HolomorphicResolventDilationData B.toCauchyResolventBoundary g where
  analyticAt_roots := fun a ↦ hg.analyticAt
    (hVo.mem_nhds (hKV (hroots (a : ℂ) (Multiset.mem_toFinset.mp a.2))))
  boundaryFunction := B.boundaryTrace g
  boundaryFunction_eq := B.boundaryTrace_eq g
    (hg.continuousOn.mono hKV)
  boundaryFunction_norm_le_one := B.boundaryTrace_norm_le g 1
    (hg.continuousOn.mono hKV) hgOne
  cauchy_pow := fun k _hk ↦
    B.holomorphic_cauchy (fun z ↦ g z ^ k) V hVo hKV (hg.pow k)

/-- Uniform polynomial approximation on a compact set, in the exact form
consumed by the boundary Cauchy limit. -/
def HasUniformPolynomialApproximationOn (K : Set ℂ) (g : ℂ → ℂ) : Prop :=
  ∃ P : ℕ → Polynomial ℂ,
    TendstoUniformlyOn (fun m z ↦ (P m).eval z) g atTop K

omit [BorelSpace i] [IsFiniteMeasure mu] in
/-- The ordinary Cauchy formula passes from uniformly approximating
polynomials to a function holomorphic in the interior.  This is the precise
analytic limit used for disk-algebra functions in Proposition 3.2. -/
theorem holomorphic_cauchy_of_tendstoUniformlyOn_polynomial
    {A : SquareMatrix n} {K : Set ℂ}
    (B : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary A K mu)
    (g : ℂ → ℂ) (hgK : ContinuousOn g K)
    (_hg : DifferentiableOn ℂ g (interior K))
    (hroots : ∀ z ∈ A.charpoly.roots, z ∈ interior K)
    (P : ℕ → Polynomial ℂ)
    (hP : TendstoUniformlyOn (fun m z ↦ (P m).eval z) g atTop K) :
    DiskRigidity.Complex.holomorphicRightResolventIntegral
        B.toCauchyResolventBoundary g =
      ((2 * Real.pi : ℝ) : ℂ) •
        euclideanOperator (DiskRigidity.Complex.spectralJetEval A g) := by
  let base : i → EuclideanEndomorphism n := fun t ↦
    rightResolventBoundaryTerm
      (B.resolvent t) (B.outwardNormal t)
  let F : ℕ → i → EuclideanEndomorphism n := fun m t ↦
    (P m).eval (B.boundaryPoint t) • base t
  let G : i → EuclideanEndomorphism n := fun t ↦
    g (B.boundaryPoint t) • base t
  have hFint (m : ℕ) : Integrable (F m) mu := by
    let fm := B.boundaryTrace (fun z ↦ (P m).eval z)
    have hfm : Integrable (fun t ↦ fm t • base t) mu :=
      B.integrable_right.bdd_smul ‖fm‖
        fm.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fm.norm_coe_le_norm)
    exact hfm.congr <|
      (B.boundaryTrace_eq (fun z ↦ (P m).eval z)
        (P m).continuous.continuousOn).mono fun t ht ↦ by
          simp only [F, fm, ht]
  have hclose : ∀ᶠ m in atTop, ∀ z ∈ K,
      dist (g z) ((P m).eval z) < 1 :=
    (Metric.tendstoUniformlyOn_iff.mp hP) 1 zero_lt_one
  let R := ‖B.boundaryTrace g‖
  have hbound : ∀ᶠ m in atTop, ∀ᵐ t ∂mu,
      ‖F m t‖ ≤ (R + 1) * ‖base t‖ := by
    filter_upwards [hclose] with m hm
    filter_upwards [B.boundaryPoint_mem,
      B.boundaryTrace_eq g hgK] with t htK httrace
    simp only [F, norm_smul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖(P m).eval (B.boundaryPoint t)‖ ≤
          ‖g (B.boundaryPoint t)‖ +
            ‖g (B.boundaryPoint t) - (P m).eval (B.boundaryPoint t)‖ :=
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
    exact (hP.tendsto_at ht).smul_const (base t)
  have hintegral : Tendsto (fun m ↦ ∫ t, F m t ∂mu) atTop
      (nhds (∫ t, G t ∂mu)) :=
    tendsto_integral_filter_of_dominated_convergence
      (fun t ↦ (R + 1) * ‖base t‖)
      (Filter.Eventually.of_forall fun m ↦ (hFint m).aestronglyMeasurable)
      hbound hboundInt hpoint
  have hloc : TendstoLocallyUniformlyOn
      (fun m z ↦ (P m).eval z) g atTop (interior K) :=
    hP.tendstoLocallyUniformlyOn.mono interior_subset
  have heval :=
    DiskRigidity.Complex.spectralJetEval_tendsto_of_tendstoLocallyUniformlyOn
      A isOpen_interior
      (fun m ↦ (P m).differentiable.differentiableOn)
      hroots hloc
  have hop : Tendsto
      (fun m ↦ euclideanOperator
        (DiskRigidity.Complex.spectralJetEval A
          (fun z ↦ (P m).eval z))) atTop
      (nhds (euclideanOperator
        (DiskRigidity.Complex.spectralJetEval A g))) :=
    by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      rw [tendsto_iff_norm_sub_tendsto_zero] at heval
      simpa only [← map_sub, ← matrix_norm_eq_operator_norm] using heval
  have hright : Tendsto
      (fun m ↦ ((2 * Real.pi : ℝ) : ℂ) •
        euclideanOperator
          (DiskRigidity.Complex.spectralJetEval A
            (fun z ↦ (P m).eval z))) atTop
      (nhds (((2 * Real.pi : ℝ) : ℂ) •
        euclideanOperator (DiskRigidity.Complex.spectralJetEval A g))) :=
    hop.const_smul _
  have hcauchy (m : ℕ) :
      ∫ t, F m t ∂mu =
        ((2 * Real.pi : ℝ) : ℂ) •
          euclideanOperator
            (DiskRigidity.Complex.spectralJetEval A
              (fun z ↦ (P m).eval z)) := by
    simpa only [F, base,
      DiskRigidity.Complex.holomorphicRightResolventIntegral] using
      B.holomorphic_cauchy (fun z ↦ (P m).eval z) Set.univ
        isOpen_univ (Set.subset_univ K)
        (P m).differentiable.differentiableOn
  have hintegral' : Tendsto
      (fun m ↦ ∫ t, F m t ∂mu) atTop
      (nhds (((2 * Real.pi : ℝ) : ℂ) •
        euclideanOperator (DiskRigidity.Complex.spectralJetEval A g))) :=
    (tendsto_congr' (Filter.Eventually.of_forall hcauchy)).mpr hright
  have hlimit := tendsto_nhds_unique hintegral hintegral'
  simpa only [G, base,
    DiskRigidity.Complex.holomorphicRightResolventIntegral] using hlimit

/-- Equality and boundary-kernel data for two independently constructed
holomorphic dilations.  In applications the second function is the reflected
inner function on the adjoint numerical range. -/
theorem exists_sharpEqualityData_and_holomorphicBoundaryKernel
    [Nonempty n]
    {j : Type*} [TopologicalSpace j] [MeasurableSpace j]
    [OpensMeasurableSpace j] {nu : Measure j}
    [BorelSpace j] [IsFiniteMeasure nu]
    {A Aadj : SquareMatrix n}
    {Badj : CauchyResolventBoundary Aadj nu}
    {B : CauchyResolventBoundary A mu}
    {g gadj : ℂ → ℂ}
    (P : HolomorphicResolventDilationData B g)
    (Padj : HolomorphicResolventDilationData Badj gadj)
    (hadj : euclideanOperator
        (DiskRigidity.Complex.spectralJetEval Aadj gadj) =
      ContinuousLinearMap.adjoint
        (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g)))
    (hnorm : ‖DiskRigidity.Complex.spectralJetEval A g‖ = 2)
    (hradius : spectralRadius ℂ
      (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g)) < 1) :
    ∃ x y : EuclideanVector n,
      SharpEqualityData
        (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g)) x y ∧
        ∀ᵐ t ∂mu, P.squareRoot.factor t
          (y - P.boundaryFunction t • x) = 0 := by
  let T := euclideanOperator (DiskRigidity.Complex.spectralJetEval A g)
  let D := P.witness
  let Dadj : DilationWitness (K := Lp (EuclideanVector n) 2 nu)
      (ContinuousLinearMap.adjoint T) := by
    rw [← hadj]
    exact Padj.witness
  let realization : BoundaryMultiplicationRealization D mu :=
    BoundaryMultiplicationRealization.ofLp D P.boundaryFunction
      P.squareRoot.factor rfl P.squareRoot.boundaryIsometry_coe_ae
  have hoperatorNorm : ‖T‖ = 2 := by
    simpa only [T, ← matrix_norm_eq_operator_norm] using hnorm
  simpa only [T, realization, BoundaryMultiplicationRealization.ofLp] using
    (exists_sharpEqualityData_and_boundaryKernel T D Dadj realization
      hoperatorNorm hradius)

/-- Reflected-function specialization of the preceding theorem.  The exact
adjoint matrix identity is discharged by the spectral-jet reflection law. -/
theorem exists_sharpEqualityData_and_reflectedHolomorphicBoundaryKernel
    [Nonempty n]
    {j : Type*} [TopologicalSpace j] [MeasurableSpace j]
    [OpensMeasurableSpace j] {nu : Measure j}
    [BorelSpace j] [IsFiniteMeasure nu]
    {A : SquareMatrix n}
    {Badj : CauchyResolventBoundary Aᴴ nu}
    {B : CauchyResolventBoundary A mu}
    {g : ℂ → ℂ}
    (P : HolomorphicResolventDilationData B g)
    (Padj : HolomorphicResolventDilationData Badj
      (reflectedHolomorphicFunction g))
    (hnorm : ‖DiskRigidity.Complex.spectralJetEval A g‖ = 2)
    (hradius : spectralRadius ℂ
      (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g)) < 1) :
    ∃ x y : EuclideanVector n,
      SharpEqualityData
        (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g)) x y ∧
        ∀ᵐ t ∂mu, P.squareRoot.factor t
          (y - P.boundaryFunction t • x) = 0 := by
  exact exists_sharpEqualityData_and_holomorphicBoundaryKernel P Padj
    (euclideanOperator_spectralJetEval_reflected_conjTranspose A g)
    hnorm hradius

end DiskRigidity.Operator
