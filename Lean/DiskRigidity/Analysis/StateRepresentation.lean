/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.RCLike.ContinuousMap
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Norm-one states and their representing probability measures

This file supplies the Hahn--Banach and Riesz--Markov part of Lemma 6.1.
In particular, it proves rather than assumes the elementary fact used in the
manuscript: a norm-one complex functional taking the unit to one is real on
self-adjoint elements and positive on nonnegative elements.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported ComplexConjugate ComplexOrder

namespace DiskRigidity.Analysis

/-- Multiplication by the conjugate phase rotates a nonzero complex number
onto the positive real axis. -/
theorem norm_inv_mul_star_norm_and_re (z : ℂ) (hz : z ≠ 0) :
    ‖(‖z‖ : ℂ)⁻¹ * star z‖ = 1 ∧
      (((‖z‖ : ℂ)⁻¹ * star z) * z).re = ‖z‖ := by
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  constructor
  · rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hnorm, norm_star, inv_mul_cancel₀ hnorm.ne']
  · change ((((‖z‖ : ℂ)⁻¹ * conj z) * z)).re = ‖z‖
    rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
    simp only [Complex.ofReal_pow]
    field_simp
    rfl

/-- The elementary phase-rotation argument used to pass from real-part
inequalities to a modulus bound. -/
theorem norm_le_one_of_rotated_re_nonneg (z : ℂ)
    (h : ∀ c : ℂ, ‖c‖ = 1 → 0 ≤ (1 - c * z).re) : ‖z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  let c : ℂ := (‖z‖ : ℂ)⁻¹ * star z
  have hc := norm_inv_mul_star_norm_and_re z hz
  have hzbound := h c hc.1
  rw [Complex.sub_re, Complex.one_re, hc.2] at hzbound
  linarith

/-- The squared norm estimate behind the standard norm-one-state argument. -/
theorem norm_one_add_I_smul_sq_le {A : Type*} [CStarAlgebra A] [NormOneClass A]
    (g : A) (hg : IsSelfAdjoint g) (t : ℝ) :
    ‖1 + ((t : ℂ) * Complex.I) • g‖ ^ 2 ≤ 1 + t ^ 2 * ‖g‖ ^ 2 := by
  rw [pow_two, ← CStarRing.norm_star_mul_self]
  have halg :
      star (1 + ((t : ℂ) * Complex.I) • g) *
          (1 + ((t : ℂ) * Complex.I) • g) =
        1 + ((t ^ 2 : ℝ) : ℂ) • (g * g) := by
    have hc : star ((t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by
      simp
    have hscalar :
        (-((t : ℂ) * Complex.I)) * ((t : ℂ) * Complex.I) =
          ((t ^ 2 : ℝ) : ℂ) := by
      ring_nf
      simp
    rw [star_add, star_one, star_smul, hg.star_eq, hc]
    calc
      (1 + (-((t : ℂ) * Complex.I)) • g) *
          (1 + ((t : ℂ) * Complex.I) • g) =
          1 + ((-((t : ℂ) * Complex.I)) *
            ((t : ℂ) * Complex.I)) • (g * g) := by
        simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul]
        module
      _ = 1 + ((t ^ 2 : ℝ) : ℂ) • (g * g) := by rw [hscalar]
  rw [halg]
  calc
    ‖1 + ((t ^ 2 : ℝ) : ℂ) • (g * g)‖
        ≤ ‖(1 : A)‖ + ‖((t ^ 2 : ℝ) : ℂ) • (g * g)‖ := norm_add_le _ _
    _ ≤ 1 + t ^ 2 * ‖g‖ ^ 2 := by
      rw [norm_one, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg t)]
      gcongr
      simpa [pow_two] using norm_mul_le g g

/-- A norm-one unital functional is real on every self-adjoint element. -/
theorem map_selfAdjoint_im_eq_zero {A : Type*} [CStarAlgebra A] [NormOneClass A]
    (F : A →L[ℂ] ℂ) (hFnorm : ‖F‖ ≤ 1) (hFone : F 1 = 1)
    (g : A) (hg : IsSelfAdjoint g) : (F g).im = 0 := by
  have hvariation (t : ℝ) :
      ‖F (1 + ((t : ℂ) * Complex.I) • g)‖ ^ 2 ≤
        1 + t ^ 2 * ‖g‖ ^ 2 := by
    have hmap :
        ‖F (1 + ((t : ℂ) * Complex.I) • g)‖ ≤
          ‖1 + ((t : ℂ) * Complex.I) • g‖ := by
      calc
        _ ≤ ‖F‖ * ‖1 + ((t : ℂ) * Complex.I) • g‖ := F.le_opNorm _
        _ ≤ 1 * ‖1 + ((t : ℂ) * Complex.I) • g‖ := by gcongr
        _ = _ := one_mul _
    exact le_trans ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hmap)
      (norm_one_add_I_smul_sq_le g hg t)
  have hformula (t : ℝ) :
      (1 - t * (F g).im) ^ 2 + (t * (F g).re) ^ 2 ≤
        1 + t ^ 2 * ‖g‖ ^ 2 := by
    have h := hvariation t
    rw [map_add, map_smul, hFone, Complex.sq_norm,
      Complex.normSq_apply] at h
    simpa [Complex.mul_re, Complex.mul_im, pow_two, sub_eq_add_neg] using h
  let b : ℝ := (F g).im
  let D : ℝ := ‖g‖ ^ 2 + 1
  have hD : 0 < D := by positivity
  have htest := hformula (-b / D)
  have hreSq : 0 ≤ (F g).re ^ 2 := sq_nonneg _
  have hb : b = 0 := by
    by_contra hbne
    have hbSq : 0 < b ^ 2 := sq_pos_of_ne_zero hbne
    dsimp [D] at htest hD
    dsimp [b] at htest ⊢
    field_simp at htest
    nlinarith [sq_nonneg ‖g‖, hreSq]
  exact hb

/-- A norm-one unital functional has nonnegative real value on every
nonnegative element. -/
theorem map_nonneg_re_nonneg {A : Type*} [CStarAlgebra A] [NormOneClass A]
    [PartialOrder A] [StarOrderedRing A]
    (F : A →L[ℂ] ℂ) (hFnorm : ‖F‖ ≤ 1) (hFone : F 1 = 1)
    (g : A) (hg : 0 ≤ g) : 0 ≤ (F g).re := by
  by_cases hgzero : g = 0
  · simp [hgzero]
  have hgnorm : 0 < ‖g‖ := norm_pos_iff.mpr hgzero
  let q : A := (‖g‖⁻¹ : ℝ) • g
  have hqnonneg : 0 ≤ q := smul_nonneg (inv_nonneg.mpr (norm_nonneg g)) hg
  have hqnorm : ‖q‖ ≤ 1 := by
    simp [q, norm_smul, hgnorm.ne']
  have hqle : q ≤ 1 :=
    ((CStarAlgebra.mem_Icc_iff_norm_le_one (A := A)).2
      ⟨hqnonneg, hqnorm⟩).2
  have hsubnonneg : 0 ≤ 1 - q := sub_nonneg.mpr hqle
  have hsuble : 1 - q ≤ 1 := sub_le_self 1 hqnonneg
  have hsubnorm : ‖1 - q‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg (1 - q) hsubnonneg).2 hsuble
  have hFsub : ‖F (1 - q)‖ ≤ 1 := by
    calc
      _ ≤ ‖F‖ * ‖1 - q‖ := F.le_opNorm _
      _ ≤ 1 * 1 := mul_le_mul hFnorm hsubnorm (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hqself : IsSelfAdjoint q := IsSelfAdjoint.of_nonneg hqnonneg
  have hqreal := map_selfAdjoint_im_eq_zero F hFnorm hFone q hqself
  rw [map_sub, hFone] at hFsub
  have hsq : ‖1 - F q‖ ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ (norm_nonneg _) zero_le_one).mpr hFsub
  rw [Complex.sq_norm, Complex.normSq_apply] at hsq
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
    hqreal, sub_zero, zero_mul, add_zero] at hsq
  have hqre : 0 ≤ (F q).re := by nlinarith [sq_nonneg (1 - (F q).re)]
  have hgq : (‖g‖ : ℂ) • q = g := by
    simp [q, smul_smul, hgnorm.ne']
  have hFg : F g = (‖g‖ : ℂ) • F q := by
    calc
      F g = F ((‖g‖ : ℂ) • q) := congrArg F hgq.symm
      _ = (‖g‖ : ℂ) • F q := map_smul F _ _
  rw [hFg]
  simpa using mul_nonneg hgnorm.le hqre

/-- Regard a compactly supported real continuous function as complex-valued. -/
noncomputable def compactRealToComplex {X : Type*} [TopologicalSpace X]
    (f : X →C_c ℝ) : C(X, ℂ) :=
  f.toContinuousMap.realToRCLike ℂ

/-- On a compact space every real continuous function has compact support. -/
noncomputable def continuousRealToCompact {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (f : C(X, ℝ)) : X →C_c ℝ :=
  ⟨f, HasCompactSupport.of_compactSpace f⟩

/-- The positive real functional associated to a complex norm-one unital
functional on `C(X, ℂ)`. -/
noncomputable def realPartPositiveMap {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [Nonempty X]
    (G : C(X, ℂ) →L[ℂ] ℂ) (hGnorm : ‖G‖ ≤ 1) (hGone : G 1 = 1) :
    (X →C_c ℝ) →ₚ[ℝ] ℝ where
  toFun f := (G (compactRealToComplex f)).re
  map_add' f g := by
    have hadd : compactRealToComplex (f + g) =
        compactRealToComplex f + compactRealToComplex g := by
      ext x
      simp [compactRealToComplex]
    rw [hadd, map_add]
    exact Complex.add_re _ _
  map_smul' r f := by
    have hsmul : compactRealToComplex (r • f) =
        (r : ℂ) • compactRealToComplex f := by
      ext x
      simp [compactRealToComplex]
    rw [hsmul, map_smul]
    simp [Complex.mul_re]
  monotone' f g hfg := by
    have hnonneg : 0 ≤ compactRealToComplex (g - f) := by
      intro x
      simpa [compactRealToComplex] using sub_nonneg.mpr (hfg x)
    have hpos := map_nonneg_re_nonneg G hGnorm hGone _ hnonneg
    have hsub : compactRealToComplex (g - f) =
        compactRealToComplex g - compactRealToComplex f := by
      ext x
      simp [compactRealToComplex]
    rw [hsub, map_sub, Complex.sub_re] at hpos
    exact sub_nonneg.mp hpos

/-- Riesz--Markov represents the real part of a norm-one unital functional. -/
theorem integral_realPartPositiveMap {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (G : C(X, ℂ) →L[ℂ] ℂ) (hGnorm : ‖G‖ ≤ 1) (hGone : G 1 = 1)
    (f : C(X, ℝ)) :
    ∫ x, f x ∂(RealRMK.rieszMeasure (realPartPositiveMap G hGnorm hGone)) =
      (G (f.realToRCLike ℂ)).re := by
  let fc := continuousRealToCompact f
  have h := RealRMK.integral_rieszMeasure
    (realPartPositiveMap G hGnorm hGone) fc
  change (∫ x, f x ∂(RealRMK.rieszMeasure
      (realPartPositiveMap G hGnorm hGone))) =
    (G (compactRealToComplex fc)).re at h
  have hfc : compactRealToComplex fc = f.realToRCLike ℂ := by
    ext x
    rfl
  rw [hfc] at h
  exact h

/-- The representing Riesz measure has total mass one. -/
theorem realPartPositiveMap_isProbability {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (G : C(X, ℂ) →L[ℂ] ℂ) (hGnorm : ‖G‖ ≤ 1) (hGone : G 1 = 1) :
    IsProbabilityMeasure
      (RealRMK.rieszMeasure (realPartPositiveMap G hGnorm hGone)) := by
  constructor
  have h := integral_realPartPositiveMap G hGnorm hGone (1 : C(X, ℝ))
  change (∫ _ : X, (1 : ℝ) ∂(RealRMK.rieszMeasure
      (realPartPositiveMap G hGnorm hGone))) = _ at h
  rw [integral_const] at h
  have honeComplex : (1 : C(X, ℝ)).realToRCLike ℂ = (1 : C(X, ℂ)) := by
    ext x
    simp
  rw [honeComplex, hGone] at h
  have hreal :
      (RealRMK.rieszMeasure (realPartPositiveMap G hGnorm hGone)).real Set.univ = 1 := by
    simpa using h
  exact (ENNReal.toReal_eq_one_iff _).mp hreal

/-- The same Riesz measure represents the full complex functional. -/
theorem integral_rieszState_eq {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (G : C(X, ℂ) →L[ℂ] ℂ) (hGnorm : ‖G‖ ≤ 1) (hGone : G 1 = 1)
    (h : C(X, ℂ)) :
    ∫ x, h x ∂(RealRMK.rieszMeasure (realPartPositiveMap G hGnorm hGone)) = G h := by
  let fr : C(X, ℝ) := h.rclikeToReal
  let fi : C(X, ℝ) := ((-(Complex.I)) • h).rclikeToReal
  let hr : C(X, ℂ) := fr.realToRCLike ℂ
  let hi : C(X, ℂ) := fi.realToRCLike ℂ
  have hfi (x : X) : fi x = (h x).im := by
    simp [fi, ContinuousMap.rclikeToReal_apply, Complex.mul_re]
  have hdecomp : h = hr + Complex.I • hi := by
    ext x
    apply Complex.ext <;>
      simp [hr, hi, fr, hfi, ContinuousMap.realToRCLike_apply,
        ContinuousMap.rclikeToReal_apply]
  have hrself : IsSelfAdjoint hr := by
    simp [hr]
  have hiself : IsSelfAdjoint hi := by
    simp [hi]
  have hGrim : (G hr).im = 0 :=
    map_selfAdjoint_im_eq_zero G hGnorm hGone hr hrself
  have hGiim : (G hi).im = 0 :=
    map_selfAdjoint_im_eq_zero G hGnorm hGone hi hiself
  have hre := integral_realPartPositiveMap G hGnorm hGone fr
  have him := integral_realPartPositiveMap G hGnorm hGone fi
  have hintegrable : Integrable h
      (RealRMK.rieszMeasure (realPartPositiveMap G hGnorm hGone)) :=
    (map_continuous h).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace h)
  have hGre : (G h).re = (G hr).re := by
    rw [hdecomp, map_add, map_smul]
    simp [hGiim, Complex.mul_re]
  have hGim : (G h).im = (G hi).re := by
    rw [hdecomp, map_add, map_smul]
    simp [hGrim, hGiim, Complex.mul_im]
  have hIntRe := integral_re hintegrable
  have hIntIm := integral_im hintegrable
  change (∫ x, (h x).re ∂(RealRMK.rieszMeasure
    (realPartPositiveMap G hGnorm hGone))) =
      (∫ x, h x ∂(RealRMK.rieszMeasure
        (realPartPositiveMap G hGnorm hGone))).re at hIntRe
  change (∫ x, (h x).im ∂(RealRMK.rieszMeasure
    (realPartPositiveMap G hGnorm hGone))) =
      (∫ x, h x ∂(RealRMK.rieszMeasure
        (realPartPositiveMap G hGnorm hGone))).im at hIntIm
  apply Complex.ext
  · calc
      _ = ∫ x, (h x).re ∂(RealRMK.rieszMeasure
          (realPartPositiveMap G hGnorm hGone)) := hIntRe.symm
      _ = ∫ x, fr x ∂(RealRMK.rieszMeasure
          (realPartPositiveMap G hGnorm hGone)) := by rfl
      _ = (G hr).re := by simpa [hr] using hre
      _ = (G h).re := hGre.symm
  · calc
      _ = ∫ x, (h x).im ∂(RealRMK.rieszMeasure
          (realPartPositiveMap G hGnorm hGone)) := hIntIm.symm
      _ = ∫ x, fi x ∂(RealRMK.rieszMeasure
          (realPartPositiveMap G hGnorm hGone)) := by
            apply integral_congr_ae
            filter_upwards [] with x
            exact (hfi x).symm
      _ = (G hi).re := by simpa [hi] using him
      _ = (G h).im := hGim.symm

/-- Hahn--Banach followed by Riesz--Markov: a norm-one unital functional on
a complex subspace of `C(X, ℂ)` is integration against a probability measure. -/
theorem exists_probabilityMeasure_extension {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (P : Subspace ℂ C(X, ℂ)) (L : StrongDual ℂ P)
    (honeMem : (1 : C(X, ℂ)) ∈ P) (hLnorm : ‖L‖ = 1)
    (hLone : L ⟨1, honeMem⟩ = 1) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧
      ∀ f : P, ∫ x, f.1 x ∂μ = L f := by
  obtain ⟨G, hGext, hGnorm⟩ := exists_extension_norm_eq P L
  have hGnorm' : ‖G‖ ≤ 1 := by rw [hGnorm, hLnorm]
  have hGone : G 1 = 1 := by
    calc
      G 1 = G (⟨1, honeMem⟩ : P) := rfl
      _ = L ⟨1, honeMem⟩ := hGext ⟨1, honeMem⟩
      _ = 1 := hLone
  let μ : Measure X := RealRMK.rieszMeasure (realPartPositiveMap G hGnorm' hGone)
  have hμprob : IsProbabilityMeasure μ := by
    exact realPartPositiveMap_isProbability G hGnorm' hGone
  refine ⟨μ, hμprob, fun f ↦ ?_⟩
  calc
    ∫ x, f.1 x ∂μ = G f.1 := integral_rieszState_eq G hGnorm' hGone f.1
    _ = L f := hGext f

/-- Positivity on real parts gives the unit-ball estimate used in Lemma 6.1.
This is the manuscript's rotation argument with `1 - c f`. -/
theorem subspace_state_apply_norm_le_one
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (P : Subspace ℂ C(X, ℂ)) (L : StrongDual ℂ P)
    (honeMem : (1 : C(X, ℂ)) ∈ P)
    (hLone : L ⟨1, honeMem⟩ = 1)
    (hpositive : ∀ f : P, (∀ x, 0 ≤ (f.1 x).re) → 0 ≤ (L f).re)
    (f : P) (hf : ‖f‖ ≤ 1) : ‖L f‖ ≤ 1 := by
  apply norm_le_one_of_rotated_re_nonneg
  intro c hc
  have hmem : (1 : C(X, ℂ)) - c • f.1 ∈ P :=
    P.sub_mem honeMem (P.smul_mem c f.2)
  let g : P := ⟨(1 : C(X, ℂ)) - c • f.1, hmem⟩
  have hgpos : ∀ x, 0 ≤ (g.1 x).re := by
    intro x
    have hfx : ‖f.1 x‖ ≤ 1 := by
      exact (ContinuousMap.norm_coe_le_norm f.1 x).trans hf
    have hcfx : ‖c * f.1 x‖ ≤ 1 := by
      rw [norm_mul, hc, one_mul]
      exact hfx
    have hre : (c * f.1 x).re ≤ 1 :=
      (Complex.re_le_norm _).trans hcfx
    change 0 ≤ (1 - c * f.1 x).re
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hLg := hpositive g hgpos
  have hLgeq : L g = 1 - c * L f := by
    let oneP : P := ⟨1, honeMem⟩
    have hgsub : g = oneP - c • f := by
      apply Subtype.ext
      rfl
    rw [hgsub, map_sub, map_smul]
    change L ⟨1, honeMem⟩ - c * L f = 1 - c * L f
    rw [hLone]
  rw [hLgeq] at hLg
  exact hLg

/-- A unital functional positive on real parts has norm exactly one. -/
theorem subspace_state_norm_eq_one
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (P : Subspace ℂ C(X, ℂ)) (L : StrongDual ℂ P)
    (honeMem : (1 : C(X, ℂ)) ∈ P)
    (hLone : L ⟨1, honeMem⟩ = 1)
    (hpositive : ∀ f : P, (∀ x, 0 ≤ (f.1 x).re) → 0 ≤ (L f).re) :
    ‖L‖ = 1 := by
  have hupper : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound L zero_le_one
    intro f
    by_cases hfzero : f = 0
    · simp [hfzero]
    have hfnorm : 0 < ‖f‖ := norm_pos_iff.mpr hfzero
    let q : P := (‖f‖ : ℂ)⁻¹ • f
    have hqnorm : ‖q‖ ≤ 1 := by
      change ‖(‖f‖ : ℂ)⁻¹ • f‖ ≤ 1
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hfnorm, inv_mul_cancel₀ hfnorm.ne']
    have hLq := subspace_state_apply_norm_le_one
      P L honeMem hLone hpositive q hqnorm
    have hfq : (‖f‖ : ℂ) • q = f := by
      dsimp only [q]
      rw [smul_smul, mul_inv_cancel₀]
      · exact one_smul ℂ f
      · exact_mod_cast hfnorm.ne'
    calc
      ‖L f‖ = ‖L ((‖f‖ : ℂ) • q)‖ := by rw [hfq]
      _ = ‖f‖ * ‖L q‖ := by
        rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hfnorm]
      _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left hLq hfnorm.le
      _ = 1 * ‖f‖ := by ring
  have hlower : 1 ≤ ‖L‖ := by
    let oneP : P := ⟨1, honeMem⟩
    have honePnorm : ‖oneP‖ = 1 := by
      change ‖(1 : C(X, ℂ))‖ = 1
      exact norm_one
    calc
      1 = ‖L oneP‖ := by rw [hLone, norm_one]
      _ ≤ ‖L‖ * ‖oneP‖ := L.le_opNorm oneP
      _ = ‖L‖ := by rw [honePnorm, mul_one]
  exact le_antisymm hupper hlower

/-- The extremal-state conclusion in the exact form needed downstream:
positivity obtained from the exponential variation yields a representing
probability measure on the compact set. -/
theorem exists_probabilityMeasure_of_subspace_state
    {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (P : Subspace ℂ C(X, ℂ)) (L : StrongDual ℂ P)
    (honeMem : (1 : C(X, ℂ)) ∈ P)
    (hLone : L ⟨1, honeMem⟩ = 1)
    (hpositive : ∀ f : P, (∀ x, 0 ≤ (f.1 x).re) → 0 ≤ (L f).re) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧
      ∀ f : P, ∫ x, f.1 x ∂μ = L f := by
  exact exists_probabilityMeasure_extension P L honeMem
    (subspace_state_norm_eq_one P L honeMem hLone hpositive) hLone

end DiskRigidity.Analysis
