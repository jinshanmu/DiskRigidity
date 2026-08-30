/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Analysis.ExtremalStateMeasure
public import DiskRigidity.Operator.ConvexDiskAlgebraDilation
public import DiskRigidity.Operator.ConvexHolomorphicCauchy
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# The concrete extremal state on a convex disk algebra

This file instantiates the abstract Hahn--Banach--Riesz package from
`ExtremalStateMeasure` with the finite spectral-jet functional calculus.
It is the concrete form of Lemma 6.1: equality in the sharp factor-two
estimate produces a probability measure representing every function in the
disk algebra of the convex numerical range.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The disk algebra of a planar compact set, presented as continuous
functions on the set that have a total representative holomorphic in its
interior.  The total representative is used only to feed the finite
spectral-jet calculus; its value is independent of the representative. -/
def convexDiskAlgebra (K : Set ℂ) : Subalgebra ℂ C(K, ℂ) where
  carrier := {f | ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (interior K) ∧
    ∀ z : K, g z = f z}
  mul_mem' := by
    rintro f g ⟨F, hF, hFeq⟩ ⟨G, hG, hGeq⟩
    refine ⟨F * G, hF.mul hG, ?_⟩
    intro z
    simp only [Pi.mul_apply, ContinuousMap.mul_apply, hFeq z, hGeq z]
  add_mem' := by
    rintro f g ⟨F, hF, hFeq⟩ ⟨G, hG, hGeq⟩
    refine ⟨F + G, hF.add hG, ?_⟩
    intro z
    simp only [Pi.add_apply, ContinuousMap.add_apply, hFeq z, hGeq z]
  algebraMap_mem' := by
    intro c
    refine ⟨fun _ ↦ c, differentiableOn_const c, ?_⟩
    intro z
    simp

theorem one_mem_convexDiskAlgebra (K : Set ℂ) :
    (1 : C(K, ℂ)) ∈ convexDiskAlgebra K :=
  (convexDiskAlgebra K).one_mem

/-- A chosen total holomorphic-interior representative of a disk-algebra
function. -/
noncomputable def convexDiskAlgebraExtension {K : Set ℂ}
    (f : convexDiskAlgebra K) : ℂ → ℂ :=
  Classical.choose f.2

theorem convexDiskAlgebraExtension_differentiableOn {K : Set ℂ}
    (f : convexDiskAlgebra K) :
    DifferentiableOn ℂ (convexDiskAlgebraExtension f) (interior K) :=
  (Classical.choose_spec f.2).1

theorem convexDiskAlgebraExtension_eq {K : Set ℂ}
    (f : convexDiskAlgebra K) (z : K) :
    convexDiskAlgebraExtension f z = f.1 z :=
  (Classical.choose_spec f.2).2 z

/-- Spectral-jet evaluation is independent of a representative whenever all
characteristic roots lie in the interior. -/
theorem spectralJetEval_eq_of_eqOn_convexBody
    (A : SquareMatrix n) {K : Set ℂ} {f g : ℂ → ℂ}
    (hfg : EqOn f g K)
    (hroots : ∀ z ∈ A.charpoly.roots, z ∈ interior K) :
    DiskRigidity.Complex.spectralJetEval A f =
      DiskRigidity.Complex.spectralJetEval A g := by
  apply DiskRigidity.Complex.spectralJetEval_eq_of_iteratedDeriv_eq A
  intro a k
  apply Filter.EventuallyEq.iteratedDeriv_eq k
  apply (hfg.mono interior_subset).eventuallyEq_of_mem
  exact isOpen_interior.mem_nhds
    (hroots (a : ℂ) (Multiset.mem_toFinset.mp a.2))

/-- Additivity of spectral-jet evaluation for functions analytic at every
characteristic root. -/
theorem spectralJetEval_add_of_analyticAt
    (A : SquareMatrix n) {f g : ℂ → ℂ}
    (hf : ∀ a : DiskRigidity.Complex.HermiteRoot A.charpoly,
      AnalyticAt ℂ f (a : ℂ))
    (hg : ∀ a : DiskRigidity.Complex.HermiteRoot A.charpoly,
      AnalyticAt ℂ g (a : ℂ)) :
    DiskRigidity.Complex.spectralJetEval A (f + g) =
      DiskRigidity.Complex.spectralJetEval A f +
        DiskRigidity.Complex.spectralJetEval A g := by
  simp only [DiskRigidity.Complex.spectralJetEval_eq_sum,
    DiskRigidity.Complex.holomorphicHermiteData]
  simp_rw [iteratedDeriv_add (hf _).contDiffAt (hg _).contDiffAt,
    add_div, add_smul, Finset.sum_add_distrib]

/-- The finite spectral-jet functional calculus on the convex disk algebra,
as a bounded linear map into Euclidean operators. -/
noncomputable def convexDiskAlgebraCalculus
    [Nonempty n] {A : SquareMatrix n} {K : Set ℂ} {c : ℂ}
    {i : Type*} [TopologicalSpace i] [MeasurableSpace i]
    [OpensMeasurableSpace i] [BorelSpace i] {mu : Measure i}
    [IsFiniteMeasure mu]
    (B : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary A K mu)
    (hconv : Convex ℝ K) (hc : c ∈ interior K)
    (hcompact : IsCompact K)
    (hroots : ∀ z ∈ A.charpoly.roots, z ∈ interior K) :
    (convexDiskAlgebra K).toSubmodule →L[ℂ] EuclideanEndomorphism n := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  let L : (convexDiskAlgebra K).toSubmodule →ₗ[ℂ] EuclideanEndomorphism n :=
    { toFun := fun f ↦ euclideanOperator
        (DiskRigidity.Complex.spectralJetEval A
          (convexDiskAlgebraExtension f))
      map_add' := by
        intro f g
        have hfanalytic : ∀ a : DiskRigidity.Complex.HermiteRoot A.charpoly,
            AnalyticAt ℂ (convexDiskAlgebraExtension f) (a : ℂ) := by
          intro a
          exact (convexDiskAlgebraExtension_differentiableOn f).analyticAt
            (isOpen_interior.mem_nhds
              (hroots (a : ℂ) (Multiset.mem_toFinset.mp a.2)))
        have hganalytic : ∀ a : DiskRigidity.Complex.HermiteRoot A.charpoly,
            AnalyticAt ℂ (convexDiskAlgebraExtension g) (a : ℂ) := by
          intro a
          exact (convexDiskAlgebraExtension_differentiableOn g).analyticAt
            (isOpen_interior.mem_nhds
              (hroots (a : ℂ) (Multiset.mem_toFinset.mp a.2)))
        have hext : DiskRigidity.Complex.spectralJetEval A
              (convexDiskAlgebraExtension (f + g)) =
            DiskRigidity.Complex.spectralJetEval A
              (convexDiskAlgebraExtension f + convexDiskAlgebraExtension g) := by
          apply spectralJetEval_eq_of_eqOn_convexBody A _ hroots
          intro z hz
          calc
            convexDiskAlgebraExtension (f + g) z =
                (f + g).1 ⟨z, hz⟩ :=
              convexDiskAlgebraExtension_eq (f + g) ⟨z, hz⟩
            _ = f.1 ⟨z, hz⟩ + g.1 ⟨z, hz⟩ := rfl
            _ = convexDiskAlgebraExtension f z +
                convexDiskAlgebraExtension g z := by
              have hfz := convexDiskAlgebraExtension_eq f ⟨z, hz⟩
              have hgz := convexDiskAlgebraExtension_eq g ⟨z, hz⟩
              exact congrArg₂ (fun a b : ℂ ↦ a + b) hfz.symm hgz.symm
        rw [hext, spectralJetEval_add_of_analyticAt A hfanalytic hganalytic,
          map_add]
      map_smul' := by
        intro r f
        have hext : DiskRigidity.Complex.spectralJetEval A
              (convexDiskAlgebraExtension (r • f)) =
            DiskRigidity.Complex.spectralJetEval A
              (fun z ↦ r * convexDiskAlgebraExtension f z) := by
          apply spectralJetEval_eq_of_eqOn_convexBody A _ hroots
          intro z hz
          calc
            convexDiskAlgebraExtension (r • f) z =
                (r • f).1 ⟨z, hz⟩ :=
              convexDiskAlgebraExtension_eq (r • f) ⟨z, hz⟩
            _ = r * f.1 ⟨z, hz⟩ := rfl
            _ = r * convexDiskAlgebraExtension f z := by
              have hfz := convexDiskAlgebraExtension_eq f ⟨z, hz⟩
              exact congrArg (fun a : ℂ ↦ r * a) hfz.symm
        rw [hext, DiskRigidity.Complex.spectralJetEval_const_mul]
        exact map_smul euclideanOperator r
          (DiskRigidity.Complex.spectralJetEval A
            (convexDiskAlgebraExtension f)) }
  exact LinearMap.mkContinuous L 2 (by
    intro f
    by_cases hfzero : ‖f‖ = 0
    · have hzero : f = 0 := norm_eq_zero.mp hfzero
      rw [hzero, map_zero]
      norm_num
    · let r : ℂ := (‖f‖ : ℂ)⁻¹
      have hrnorm : ‖r‖ = ‖f‖⁻¹ := by
        dsimp only [r]
        rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg f)]
      let q : ℂ → ℂ := fun z ↦ r * convexDiskAlgebraExtension f z
      have hqK : ContinuousOn q K := by
        apply ContinuousOn.const_mul
        rw [continuousOn_iff_continuous_domRestrict]
        exact f.1.continuous.congr fun z ↦
          (convexDiskAlgebraExtension_eq f z).symm
      have hqd : DifferentiableOn ℂ q (interior K) :=
        (convexDiskAlgebraExtension_differentiableOn f).const_mul r
      have hqOne : ∀ z ∈ K, ‖q z‖ ≤ 1 := by
        intro z hz
        have hfnormpos : 0 < ‖f‖ :=
          lt_of_le_of_ne (norm_nonneg f) (Ne.symm hfzero)
        change ‖r * convexDiskAlgebraExtension f z‖ ≤ 1
        rw [norm_mul, hrnorm]
        apply (inv_mul_le_one₀ hfnormpos).mpr
        have hfz := convexDiskAlgebraExtension_eq f ⟨z, hz⟩
        calc
          ‖convexDiskAlgebraExtension f z‖ = ‖f.1 ⟨z, hz⟩‖ :=
            congrArg norm hfz
          _ ≤ ‖f.1‖ := ContinuousMap.norm_coe_le_norm f.1 ⟨z, hz⟩
          _ = ‖f‖ := rfl
      have hqbound := norm_spectralJetEval_le_two_of_convex_diskAlgebra
        B hconv hc hcompact q hqK hqd hroots hqOne
      have heval : DiskRigidity.Complex.spectralJetEval A q =
          r • DiskRigidity.Complex.spectralJetEval A
            (convexDiskAlgebraExtension f) :=
        DiskRigidity.Complex.spectralJetEval_const_mul A r _
      rw [heval, norm_smul, hrnorm] at hqbound
      change ‖euclideanOperator (DiskRigidity.Complex.spectralJetEval A
        (convexDiskAlgebraExtension f))‖ ≤ 2 * ‖f‖
      rw [← matrix_norm_eq_operator_norm]
      have hfnormpos : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg f) (Ne.symm hfzero)
      apply (div_le_iff₀ hfnormpos).mp
      rw [div_eq_mul_inv, mul_comm]
      exact hqbound)

@[simp]
theorem convexDiskAlgebraCalculus_apply
    [Nonempty n] {A : SquareMatrix n} {K : Set ℂ} {c : ℂ}
    {i : Type*} [TopologicalSpace i] [MeasurableSpace i]
    [OpensMeasurableSpace i] [BorelSpace i] {mu : Measure i}
    [IsFiniteMeasure mu]
    (B : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary A K mu)
    (hconv : Convex ℝ K) (hc : c ∈ interior K)
    (hcompact : IsCompact K)
    (hroots : ∀ z ∈ A.charpoly.roots, z ∈ interior K)
    (f : (convexDiskAlgebra K).toSubmodule) :
    convexDiskAlgebraCalculus B hconv hc hcompact hroots f =
      euclideanOperator (DiskRigidity.Complex.spectralJetEval A
        (convexDiskAlgebraExtension f)) :=
  rfl

/-- The calculus sends the disk-algebra unit to the identity operator. -/
theorem convexDiskAlgebraCalculus_one
    [Nonempty n] {A : SquareMatrix n} {K : Set ℂ} {c : ℂ}
    {i : Type*} [TopologicalSpace i] [MeasurableSpace i]
    [OpensMeasurableSpace i] [BorelSpace i] {mu : Measure i}
    [IsFiniteMeasure mu]
    (B : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary A K mu)
    (hconv : Convex ℝ K) (hc : c ∈ interior K)
    (hcompact : IsCompact K)
    (hroots : ∀ z ∈ A.charpoly.roots, z ∈ interior K) :
    convexDiskAlgebraCalculus B hconv hc hcompact hroots
        ⟨1, one_mem_convexDiskAlgebra K⟩ = 1 := by
  rw [convexDiskAlgebraCalculus_apply]
  have hext : DiskRigidity.Complex.spectralJetEval A
        (convexDiskAlgebraExtension
          (⟨1, one_mem_convexDiskAlgebra K⟩ : convexDiskAlgebra K)) =
      DiskRigidity.Complex.spectralJetEval A (fun _ ↦ 1) := by
    apply spectralJetEval_eq_of_eqOn_convexBody A _ hroots
    intro z hz
    have hzext := convexDiskAlgebraExtension_eq
      (⟨1, one_mem_convexDiskAlgebra K⟩ : convexDiskAlgebra K) ⟨z, hz⟩
    exact hzext.trans (by rfl)
  rw [hext, DiskRigidity.Complex.spectralJetEval_one, map_one]

/-- Multiplicativity of the concrete disk-algebra calculus. -/
theorem convexDiskAlgebraCalculus_mul
    [Nonempty n] {A : SquareMatrix n} {K : Set ℂ} {c : ℂ}
    {i : Type*} [TopologicalSpace i] [MeasurableSpace i]
    [OpensMeasurableSpace i] [BorelSpace i] {mu : Measure i}
    [IsFiniteMeasure mu]
    (B : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary A K mu)
    (hconv : Convex ℝ K) (hc : c ∈ interior K)
    (hcompact : IsCompact K)
    (hroots : ∀ z ∈ A.charpoly.roots, z ∈ interior K)
    (f g : convexDiskAlgebra K) :
    convexDiskAlgebraCalculus B hconv hc hcompact hroots (f * g) =
      convexDiskAlgebraCalculus B hconv hc hcompact hroots f *
        convexDiskAlgebraCalculus B hconv hc hcompact hroots g := by
  simp only [convexDiskAlgebraCalculus_apply]
  let F := convexDiskAlgebraExtension f
  let G := convexDiskAlgebraExtension g
  have hext : DiskRigidity.Complex.spectralJetEval A
        (convexDiskAlgebraExtension (f * g)) =
      DiskRigidity.Complex.spectralJetEval A (F * G) := by
    apply spectralJetEval_eq_of_eqOn_convexBody A _ hroots
    intro z hz
    have hfgz := convexDiskAlgebraExtension_eq (f * g) ⟨z, hz⟩
    have hfz := convexDiskAlgebraExtension_eq f ⟨z, hz⟩
    have hgz := convexDiskAlgebraExtension_eq g ⟨z, hz⟩
    change convexDiskAlgebraExtension (f * g) z = F z * G z
    calc
      convexDiskAlgebraExtension (f * g) z = (f * g).1 ⟨z, hz⟩ := hfgz
      _ = f.1 ⟨z, hz⟩ * g.1 ⟨z, hz⟩ := rfl
      _ = F z * G z := congrArg₂ (fun a b : ℂ ↦ a * b) hfz.symm hgz.symm
  have hFanalytic : ∀ a : DiskRigidity.Complex.HermiteRoot A.charpoly,
      AnalyticAt ℂ F (a : ℂ) := by
    intro a
    exact (convexDiskAlgebraExtension_differentiableOn f).analyticAt
      (isOpen_interior.mem_nhds
        (hroots (a : ℂ) (Multiset.mem_toFinset.mp a.2)))
  have hGanalytic : ∀ a : DiskRigidity.Complex.HermiteRoot A.charpoly,
      AnalyticAt ℂ G (a : ℂ) := by
    intro a
    exact (convexDiskAlgebraExtension_differentiableOn g).analyticAt
      (isOpen_interior.mem_nhds
        (hroots (a : ℂ) (Multiset.mem_toFinset.mp a.2)))
  rw [hext, DiskRigidity.Complex.spectralJetEval_mul A hFanalytic hGanalytic,
    map_mul]

/-- Power preservation for the concrete disk-algebra calculus. -/
theorem convexDiskAlgebraCalculus_pow
    [Nonempty n] {A : SquareMatrix n} {K : Set ℂ} {c : ℂ}
    {i : Type*} [TopologicalSpace i] [MeasurableSpace i]
    [OpensMeasurableSpace i] [BorelSpace i] {mu : Measure i}
    [IsFiniteMeasure mu]
    (B : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary A K mu)
    (hconv : Convex ℝ K) (hc : c ∈ interior K)
    (hcompact : IsCompact K)
    (hroots : ∀ z ∈ A.charpoly.roots, z ∈ interior K)
    (f : convexDiskAlgebra K) (k : ℕ) :
    convexDiskAlgebraCalculus B hconv hc hcompact hroots (f ^ k) =
      (convexDiskAlgebraCalculus B hconv hc hcompact hroots f) ^ k := by
  induction k with
  | zero => exact convexDiskAlgebraCalculus_one B hconv hc hcompact hroots
  | succ k ih =>
      rw [pow_succ, convexDiskAlgebraCalculus_mul, ih, pow_succ]

/-- Pointwise exponential stays in the convex disk algebra. -/
noncomputable def convexDiskAlgebraExp {K : Set ℂ}
    (f : convexDiskAlgebra K) : convexDiskAlgebra K :=
  ⟨⟨fun z ↦ Complex.exp (f.1 z),
      Complex.continuous_exp.comp f.1.continuous⟩,
    ⟨fun z ↦ Complex.exp (convexDiskAlgebraExtension f z),
      (convexDiskAlgebraExtension_differentiableOn f).cexp,
      fun z ↦ congrArg Complex.exp (convexDiskAlgebraExtension_eq f z)⟩⟩

@[simp]
theorem convexDiskAlgebraExp_apply {K : Set ℂ}
    (f : convexDiskAlgebra K) (z : K) :
    (convexDiskAlgebraExp f).1 z = Complex.exp (f.1 z) :=
  rfl

/-- The exponential series converges inside the disk-algebra subtype. -/
theorem convexDiskAlgebra_exp_series_hasSum
    {K : Set ℂ} (hcompact : IsCompact K)
    (f : convexDiskAlgebra K) :
    HasSum (fun k : ℕ ↦ ((k.factorial : ℂ)⁻¹ • f ^ k))
      (convexDiskAlgebraExp f) := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  have hnorm : Summable
      (fun k : ℕ ↦ ‖((k.factorial : ℂ)⁻¹ • f ^ k)‖) := by
    apply (NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) f.1).congr
    intro k
    rfl
  apply (hasSum_iff_tendsto_nat_of_summable_norm hnorm).2
  rw [tendsto_subtype_rng]
  have htarget : (convexDiskAlgebraExp f).1 =
      NormedSpace.exp f.1 := by
    rw [NormedSpace.exp_continuousMap_eq]
    apply ContinuousMap.ext
    intro z
    simp only [convexDiskAlgebraExp]
    exact congrFun Complex.exp_eq_exp_ℂ (f.1 z)
  rw [htarget]
  have hsum :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) f.1).tendsto_sum_nat
  convert hsum using 1
  funext m
  change ((↑(∑ i ∈ Finset.range m,
      (i.factorial : ℂ)⁻¹ • f ^ i) : C(K, ℂ))) = _
  calc
    (↑(∑ i ∈ Finset.range m,
        (i.factorial : ℂ)⁻¹ • f ^ i) : C(K, ℂ)) =
        ∑ i ∈ Finset.range m,
          ↑((i.factorial : ℂ)⁻¹ • f ^ i) :=
      Submodule.coe_sum (convexDiskAlgebra K).toSubmodule
        (fun i ↦ (i.factorial : ℂ)⁻¹ • f ^ i) (Finset.range m)
    _ = ∑ i ∈ Finset.range m, (i.factorial : ℂ)⁻¹ • f.1 ^ i := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Subalgebra.coe_smul, Subalgebra.coe_pow]

/-- Spectral-jet evaluation intertwines pointwise and operator
exponentials. -/
theorem convexDiskAlgebraCalculus_exp
    [Nonempty n] {A : SquareMatrix n} {K : Set ℂ} {c : ℂ}
    {i : Type*} [TopologicalSpace i] [MeasurableSpace i]
    [OpensMeasurableSpace i] [BorelSpace i] {mu : Measure i}
    [IsFiniteMeasure mu]
    (B : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary A K mu)
    (hconv : Convex ℝ K) (hc : c ∈ interior K)
    (hcompact : IsCompact K)
    (hroots : ∀ z ∈ A.charpoly.roots, z ∈ interior K)
    (f : convexDiskAlgebra K) :
    convexDiskAlgebraCalculus B hconv hc hcompact hroots
        (convexDiskAlgebraExp f) =
      NormedSpace.exp
        (convexDiskAlgebraCalculus B hconv hc hcompact hroots f) := by
  let Phi := convexDiskAlgebraCalculus B hconv hc hcompact hroots
  have hmapped := Phi.hasSum (convexDiskAlgebra_exp_series_hasSum hcompact f)
  have hmapped' : HasSum
      (fun k : ℕ ↦ ((k.factorial : ℂ)⁻¹ • (Phi f) ^ k))
      (Phi (convexDiskAlgebraExp f)) := by
    have hterm :
        (fun k : ℕ ↦ Phi ((k.factorial : ℂ)⁻¹ • f ^ k)) =
          (fun k : ℕ ↦ (k.factorial : ℂ)⁻¹ • (Phi f) ^ k) := by
      funext k
      rw [map_smul]
      change ((k.factorial : ℂ)⁻¹ •
          convexDiskAlgebraCalculus B hconv hc hcompact hroots (f ^ k)) = _
      rw [convexDiskAlgebraCalculus_pow]
    exact hterm ▸ hmapped
  change Phi (convexDiskAlgebraExp f) = NormedSpace.exp (Phi f)
  exact hmapped'.unique
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (Phi f))

/-- The sharp factor-two bound on the concrete calculus unit ball. -/
theorem convexDiskAlgebraCalculus_norm_le_two
    [Nonempty n] {A : SquareMatrix n} {K : Set ℂ} {c : ℂ}
    {i : Type*} [TopologicalSpace i] [MeasurableSpace i]
    [OpensMeasurableSpace i] [BorelSpace i] {mu : Measure i}
    [IsFiniteMeasure mu]
    (B : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary A K mu)
    (hconv : Convex ℝ K) (hc : c ∈ interior K)
    (hcompact : IsCompact K)
    (hroots : ∀ z ∈ A.charpoly.roots, z ∈ interior K)
    (f : convexDiskAlgebra K) (hf : ∀ z : K, ‖f.1 z‖ ≤ 1) :
    ‖convexDiskAlgebraCalculus B hconv hc hcompact hroots f‖ ≤ 2 := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  rw [convexDiskAlgebraCalculus_apply, ← matrix_norm_eq_operator_norm]
  apply norm_spectralJetEval_le_two_of_convex_diskAlgebra B hconv hc hcompact
    (convexDiskAlgebraExtension f)
  · rw [continuousOn_iff_continuous_domRestrict]
    exact f.1.continuous.congr fun z ↦
      (convexDiskAlgebraExtension_eq f z).symm
  · exact convexDiskAlgebraExtension_differentiableOn f
  · exact hroots
  · intro z hz
    have hfz := convexDiskAlgebraExtension_eq f ⟨z, hz⟩
    rw [hfz]
    exact hf ⟨z, hz⟩

/-- The concrete form of Lemma 6.1 for a convex disk algebra equipped with
its spectral-jet calculus.  No positivity or variation hypothesis remains:
the variation is the actual disk-algebra function `g * exp (-t h)`, and its
bound is supplied by the convex double-layer theorem. -/
theorem exists_probabilityMeasure_of_convexDiskAlgebra_extremizer
    [Nonempty n] {A : SquareMatrix n} {K : Set ℂ} {c : ℂ}
    {i : Type*} [TopologicalSpace i] [MeasurableSpace i]
    [OpensMeasurableSpace i] [BorelSpace i] {mu : Measure i}
    [IsFiniteMeasure mu]
    (B : DiskRigidity.Complex.NeighborhoodHolomorphicCauchyBoundary A K mu)
    (hconv : Convex ℝ K) (hc : c ∈ interior K)
    (hcompact : IsCompact K)
    (hroots : ∀ z ∈ A.charpoly.roots, z ∈ interior K)
    (g : convexDiskAlgebra K)
    (hgOne : ∀ z : K, ‖g.1 z‖ ≤ 1)
    (x y : EuclideanVector n)
    (hxy : SharpEqualityData
      (convexDiskAlgebraCalculus B hconv hc hcompact hroots g) x y) :
    ∃ nu : Measure K, IsProbabilityMeasure nu ∧
      ∀ f : (convexDiskAlgebra K).toSubmodule,
        ∫ z, f.1 z ∂nu =
          ⟪x, convexDiskAlgebraCalculus B hconv hc hcompact hroots f x⟫_ℂ := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  let _ : Nonempty K := ⟨⟨c, interior_subset hc⟩⟩
  let P := (convexDiskAlgebra K).toSubmodule
  let Phi : P →L[ℂ] EuclideanEndomorphism n :=
    convexDiskAlgebraCalculus B hconv hc hcompact hroots
  let T : EuclideanEndomorphism n := Phi g
  have hcomm : ∀ f : P, ∀ z, Phi f (T z) = T (Phi f z) := by
    intro f z
    have hfg := convexDiskAlgebraCalculus_mul
      B hconv hc hcompact hroots f g
    have hgf := convexDiskAlgebraCalculus_mul
      B hconv hc hcompact hroots g f
    have hmul : Phi f * T = T * Phi f := by
      rw [← hfg, ← hgf]
      congr 1
      apply Subtype.ext
      apply ContinuousMap.ext
      intro q
      exact mul_comm _ _
    calc
      Phi f (T z) = (Phi f * T) z :=
        (mul_apply_eq_comp (Phi f) T z).symm
      _ = (T * Phi f) z := congrArg (fun S : EuclideanEndomorphism n ↦ S z) hmul
      _ = T (Phi f z) := mul_apply_eq_comp T (Phi f) z
  have hvariation : ∀ f : P, (∀ q, 0 ≤ (f.1 q).re) →
      ∀ t : ℝ, 0 ≤ t →
        ‖T (NormedSpace.exp (t • (-(Phi f))) x)‖ ≤ 2 := by
    intro f hf t ht
    let e : convexDiskAlgebra K := convexDiskAlgebraExp (t • (-f))
    let q : convexDiskAlgebra K := g * e
    have hqOne : ∀ z : K, ‖q.1 z‖ ≤ 1 := by
      intro z
      change ‖g.1 z * Complex.exp ((t : ℂ) * (-f.1 z))‖ ≤ 1
      rw [norm_mul, Complex.norm_exp]
      have hre : (((t : ℂ) * (-f.1 z)).re) ≤ 0 := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, Complex.neg_re]
        exact mul_nonpos_of_nonneg_of_nonpos ht (neg_nonpos.mpr (hf z))
      calc
        ‖g.1 z‖ * Real.exp (((t : ℂ) * (-f.1 z)).re) ≤
            1 * 1 := mul_le_mul (hgOne z)
          (Real.exp_le_one_iff.mpr hre) (Real.exp_pos _).le zero_le_one
        _ = 1 := one_mul 1
    have hqbound := convexDiskAlgebraCalculus_norm_le_two
      B hconv hc hcompact hroots q hqOne
    have hPhiE : Phi e = NormedSpace.exp (t • (-(Phi f))) := by
      change Phi (convexDiskAlgebraExp (t • (-f))) = _
      rw [convexDiskAlgebraCalculus_exp]
      congr 1
      rw [ContinuousLinearMap.map_smul_of_tower, map_neg]
    have hPhiq : Phi q = T * NormedSpace.exp (t • (-(Phi f))) := by
      change Phi (g * e) = _
      rw [convexDiskAlgebraCalculus_mul, hPhiE]
    calc
      ‖T (NormedSpace.exp (t • (-(Phi f))) x)‖ =
          ‖(Phi q) x‖ := by
        rw [hPhiq, mul_apply_eq_comp]
      _ ≤ ‖Phi q‖ * ‖x‖ := (Phi q).le_opNorm x
      _ ≤ 2 * 1 := mul_le_mul hqbound hxy.norm_x.le
        (norm_nonneg x) (by norm_num)
      _ = 2 := mul_one 2
  exact DiskRigidity.Analysis.exists_probabilityMeasure_of_extremalVariation
    P Phi (one_mem_convexDiskAlgebra K)
      (convexDiskAlgebraCalculus_one B hconv hc hcompact hroots)
      T x y hxy.toDilationEqualityPair hxy.norm_x hxy.norm_y
      hcomm hvariation

/-- Lemma 6.1 on the actual numerical range.  Starting only from an
interior-spectrum matrix, a disk-algebra extremizer, and its sharp equality
vectors, this constructs the representing probability measure for every
continuous-on-the-range, holomorphic-in-the-interior function. -/
theorem exists_probabilityMeasure_numericalRange_of_extremal_spectralJet
    [Nonempty n] (A : SquareMatrix n) {c : ℂ}
    (hc : c ∈ interior (numericalRange A))
    (hspectrum : spectrum ℂ A ⊆ interior (numericalRange A))
    (g : ℂ → ℂ) (hgK : ContinuousOn g (numericalRange A))
    (hg : DifferentiableOn ℂ g (interior (numericalRange A)))
    (hgOne : ∀ z ∈ numericalRange A, ‖g z‖ ≤ 1)
    (x y : EuclideanVector n)
    (hxy : SharpEqualityData
      (euclideanOperator (DiskRigidity.Complex.spectralJetEval A g)) x y) :
    ∃ nu : Measure (numericalRange A), IsProbabilityMeasure nu ∧
      ∀ h : ℂ → ℂ, ContinuousOn h (numericalRange A) →
        DifferentiableOn ℂ h (interior (numericalRange A)) →
        ∫ z, h z ∂nu =
          ⟪x, euclideanOperator
            (DiskRigidity.Complex.spectralJetEval A h) x⟫_ℂ := by
  let K := numericalRange A
  let hconv : Convex ℝ K := numericalRange_convex A
  let hcompact : IsCompact K := isCompact_numericalRange A
  let hroots : ∀ z ∈ A.charpoly.roots, z ∈ interior K :=
    DiskRigidity.Complex.charpoly_roots_subset_of_spectrum_subset A hspectrum
  let _ : IsFiniteMeasure (radialBoundaryArcLengthMeasure K c) :=
    isFiniteMeasure_radialBoundaryArcLengthMeasure hconv hc hcompact
  let B := neighborhoodHolomorphicCauchyBoundaryOfConvexBody
    A hconv hc hcompact (Subset.rfl) hspectrum
  let gK : C(K, ℂ) := ⟨fun z ↦ g z, hgK.domRestrict⟩
  let gp : convexDiskAlgebra K :=
    ⟨gK, ⟨g, hg, fun z ↦ rfl⟩⟩
  have hcalculusG :
      convexDiskAlgebraCalculus B hconv hc hcompact hroots gp =
        euclideanOperator (DiskRigidity.Complex.spectralJetEval A g) := by
    rw [convexDiskAlgebraCalculus_apply]
    apply congrArg euclideanOperator
    apply spectralJetEval_eq_of_eqOn_convexBody A _ hroots
    intro z hz
    exact (convexDiskAlgebraExtension_eq gp ⟨z, hz⟩).trans rfl
  have hxy' : SharpEqualityData
      (convexDiskAlgebraCalculus B hconv hc hcompact hroots gp) x y := by
    rw [hcalculusG]
    exact hxy
  obtain ⟨nu, hnu, hrepr⟩ :=
    exists_probabilityMeasure_of_convexDiskAlgebra_extremizer
      B hconv hc hcompact hroots gp
        (fun z ↦ hgOne z z.2) x y hxy'
  refine ⟨nu, hnu, ?_⟩
  intro h hhK hh
  let hK : C(K, ℂ) := ⟨fun z ↦ h z, hhK.domRestrict⟩
  let hp : convexDiskAlgebra K :=
    ⟨hK, ⟨h, hh, fun z ↦ rfl⟩⟩
  have heval : DiskRigidity.Complex.spectralJetEval A
        (convexDiskAlgebraExtension hp) =
      DiskRigidity.Complex.spectralJetEval A h := by
    apply spectralJetEval_eq_of_eqOn_convexBody A _ hroots
    intro z hz
    exact (convexDiskAlgebraExtension_eq hp ⟨z, hz⟩).trans rfl
  have hpRepr := hrepr hp
  change (∫ z, h z ∂nu) = _
  change (∫ z, hp.1 z ∂nu) = _
  rw [hpRepr, convexDiskAlgebraCalculus_apply, heval]

/-- The coefficient identities (3.10)--(3.11), specialized to two
disk-algebra spectral-jet values.  Their commutation is proved by the
multiplicativity of the finite jet calculus rather than required from the
caller. -/
theorem spectralJet_coefficient_identities_of_sharpEqualityData
    (A : SquareMatrix n)
    (hspectrum : spectrum ℂ A ⊆ interior (numericalRange A))
    {f h : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (interior (numericalRange A)))
    (hh : DifferentiableOn ℂ h (interior (numericalRange A)))
    (x y : EuclideanVector n)
    (hxy : SharpEqualityData
      (euclideanOperator (DiskRigidity.Complex.spectralJetEval A f)) x y) :
    let T := euclideanOperator (DiskRigidity.Complex.spectralJetEval A f)
    let S := euclideanOperator (DiskRigidity.Complex.spectralJetEval A h)
    ⟪x, S (T x)⟫_ℂ = 0 ∧
      ⟪y, S (T x)⟫_ℂ = (2 : ℂ) * ⟪x, S x⟫_ℂ ∧
      ⟪x, S y⟫_ℂ = 0 ∧
      ⟪y, S y⟫_ℂ = ⟪x, S x⟫_ℂ := by
  let T := euclideanOperator (DiskRigidity.Complex.spectralJetEval A f)
  let S := euclideanOperator (DiskRigidity.Complex.spectralJetEval A h)
  have hfanalytic : ∀ a : DiskRigidity.Complex.HermiteRoot A.charpoly,
      AnalyticAt ℂ f (a : ℂ) := by
    intro a
    exact hf.analyticAt (isOpen_interior.mem_nhds
      (DiskRigidity.Complex.charpoly_roots_subset_of_spectrum_subset
        A hspectrum (a : ℂ) (Multiset.mem_toFinset.mp a.2)))
  have hhanalytic : ∀ a : DiskRigidity.Complex.HermiteRoot A.charpoly,
      AnalyticAt ℂ h (a : ℂ) := by
    intro a
    exact hh.analyticAt (isOpen_interior.mem_nhds
      (DiskRigidity.Complex.charpoly_roots_subset_of_spectrum_subset
        A hspectrum (a : ℂ) (Multiset.mem_toFinset.mp a.2)))
  have hmatrix :
      DiskRigidity.Complex.spectralJetEval A h *
          DiskRigidity.Complex.spectralJetEval A f =
        DiskRigidity.Complex.spectralJetEval A f *
          DiskRigidity.Complex.spectralJetEval A h := by
    calc
      DiskRigidity.Complex.spectralJetEval A h *
          DiskRigidity.Complex.spectralJetEval A f =
          DiskRigidity.Complex.spectralJetEval A (h * f) :=
        (DiskRigidity.Complex.spectralJetEval_mul
          A hhanalytic hfanalytic).symm
      _ = DiskRigidity.Complex.spectralJetEval A (f * h) := by
        congr 1
        funext z
        exact mul_comm _ _
      _ = DiskRigidity.Complex.spectralJetEval A f *
          DiskRigidity.Complex.spectralJetEval A h :=
        DiskRigidity.Complex.spectralJetEval_mul A hfanalytic hhanalytic
  have hcommOp : S * T = T * S := by
    dsimp only [S, T]
    rw [← map_mul, ← map_mul, hmatrix]
  have hcomm : ∀ z, S (T z) = T (S z) := by
    intro z
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, hcommOp]
  exact hxy.coefficient_identities hcomm

end DiskRigidity.Operator
