/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Noncritical full analytic levels of convex domains

The local branching argument in Proposition 6.1 can be made without a
separate Jordan-curve theorem.  If an analytic unit-level point had order
`k ≥ 2`, a complete orbit under the standard primitive `k`th root of
unity would lie in the strict sublevel for all sufficiently small positive
radii.  Its barycenter is the original boundary point, contradicting
convexity of the interior.
-/

@[expose] public section

noncomputable section

namespace DiskRigidity.Algebraic

namespace ConvexNoncriticalLevel

open Complex Filter Finset Metric Polynomial Set
open scoped Topology ComplexConjugate

/-- Polarization of `normSq`, used to read the sign of the leading analytic
term. -/
theorem normSq_add_sub_normSq (w a : ℂ) :
    Complex.normSq (w + a) - Complex.normSq w =
      2 * (conj w * a).re + Complex.normSq a := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The polarization identity with a real scalar separated out. -/
theorem normSq_add_real_mul_sub_normSq (w b : ℂ) (r : ℝ) :
    Complex.normSq (w + (r : ℂ) * b) - Complex.normSq w =
      r * (2 * (conj w * b).re + r * Complex.normSq b) := by
  rw [normSq_add_sub_normSq]
  simp only [map_mul, Complex.normSq_ofReal, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero]
  ring

/-- The standard primitive `k`th root of unity. -/
def standardRoot (k : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / k)

theorem standardRoot_isPrimitiveRoot {k : ℕ} (hk : k ≠ 0) :
    IsPrimitiveRoot (standardRoot k) k := by
  exact Complex.isPrimitiveRoot_exp k hk

theorem sum_standardRoot_powers {k : ℕ} (hk : 1 < k) :
    ∑ j ∈ Finset.range k, standardRoot k ^ j = 0 := by
  have hroot := standardRoot_isPrimitiveRoot (Nat.ne_zero_of_lt hk)
  have hgeom := geom_sum_mul (standardRoot k) k
  rw [hroot.pow_eq_one, sub_self] at hgeom
  exact (mul_eq_zero.mp hgeom).resolve_right
    (sub_ne_zero.mpr (hroot.ne_one hk))

/-- A full strict sublevel which is the interior of a convex set has no
critical point on its unit frontier.  This is the analytic `2k`-ray
argument, formalized by a root-of-unity barycenter. -/
theorem deriv_ne_zero_of_convex_full_sublevel
    {f : ℂ → ℂ} {K : Set ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀)
    (hnonconstant : ¬ f =ᶠ[nhds z₀] fun _ ↦ f z₀)
    (hnorm : ‖f z₀‖ = 1)
    (hconvex : Convex ℝ K)
    (hz₀ : z₀ ∈ frontier K)
    (hsublevel : ∀ᶠ z in nhds z₀, ‖f z‖ < 1 → z ∈ interior K) :
    deriv f z₀ ≠ 0 := by
  intro hcritical
  let A : ℂ → ℂ := fun z ↦ f z - f z₀
  have hA : AnalyticAt ℂ A z₀ := hf.sub analyticAt_const
  have horderFinite : analyticOrderAt A z₀ ≠ ⊤ := by
    intro htop
    have hzero : ∀ᶠ z in nhds z₀, A z = 0 :=
      analyticOrderAt_eq_top.mp htop
    apply hnonconstant
    filter_upwards [hzero] with z hz
    exact sub_eq_zero.mp hz
  let k : ℕ := analyticOrderNatAt A z₀
  have horderTwo : ((2 : ℕ) : ℕ∞) ≤ analyticOrderAt A z₀ := by
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hA).2
    intro i hi
    interval_cases i
    · simp [A]
    · simpa [A, iteratedDeriv_one, deriv_sub_const] using hcritical
  have hkcast : (k : ℕ∞) = analyticOrderAt A z₀ := by
    exact Nat.cast_analyticOrderNatAt horderFinite
  have hk : 2 ≤ k := by
    rw [← hkcast] at horderTwo
    exact_mod_cast horderTwo
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_two hk
  obtain ⟨q, hqAnalytic, hqNonzero, hfactor⟩ :=
    (hA.analyticOrderNatAt_eq_iff horderFinite).mp (show
      analyticOrderNatAt A z₀ = k from rfl)
  let ζ : ℂ := standardRoot k
  have hζroot : IsPrimitiveRoot ζ k :=
    standardRoot_isPrimitiveRoot hkpos.ne'
  have hζpow : ζ ^ k = 1 := hζroot.pow_eq_one
  have hζsum : ∑ j ∈ Finset.range k, ζ ^ j = 0 :=
    sum_standardRoot_powers (lt_of_lt_of_le one_lt_two hk)
  have hfz₀ : f z₀ ≠ 0 := by
    exact norm_ne_zero_iff.mp (by rw [hnorm]; exact one_ne_zero)
  let c : ℂ := conj (f z₀) * q z₀
  have hc : c ≠ 0 := by
    exact mul_ne_zero ((_root_.map_ne_zero (starRingEnd ℂ)).2 hfz₀) hqNonzero
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (-c⁻¹) hkpos
  have hlead : conj (f z₀) * α ^ k * q z₀ = -1 := by
    calc
      conj (f z₀) * α ^ k * q z₀ =
          conj (f z₀) * (-c⁻¹) * q z₀ := by rw [hα]
      _ = -(c * c⁻¹) := by simp only [c]; ring
      _ = -1 := by rw [mul_inv_cancel₀ hc]
  let direction : ℕ → ℂ := fun j ↦ α * ζ ^ j
  have hdirectionPow : ∀ j, direction j ^ k = α ^ k := by
    intro j
    change (α * ζ ^ j) ^ k = α ^ k
    rw [mul_pow]
    have hj : (ζ ^ j) ^ k = 1 := by
      calc
        (ζ ^ j) ^ k = (ζ ^ k) ^ j := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ = 1 := by rw [hζpow, one_pow]
    rw [hj, mul_one]
  let point : ℕ → ℝ → ℂ := fun j t ↦
    z₀ + (t : ℂ) * direction j
  have hpointZero : ∀ j, point j 0 = z₀ := by
    intro j
    simp [point]
  let normalizedDifference : ℕ → ℝ → ℝ := fun j t ↦
    2 * (conj (f z₀) * direction j ^ k * q (point j t)).re +
      t ^ k * Complex.normSq (direction j ^ k * q (point j t))
  have hnormalizedZero : ∀ j, normalizedDifference j 0 = -2 := by
    intro j
    change 2 * (conj (f z₀) * direction j ^ k * q (point j 0)).re +
      0 ^ k * Complex.normSq (direction j ^ k * q (point j 0)) = -2
    rw [hpointZero, hdirectionPow, hlead]
    simp [hkpos.ne']
  have hpointContinuous : ∀ j, ContinuousAt (point j) 0 := by
    intro j
    dsimp only [point]
    fun_prop
  have hpointTendsto : ∀ j, Tendsto (point j) (nhds 0) (nhds z₀) := by
    intro j
    rw [← hpointZero j]
    exact hpointContinuous j
  have hnormalizedContinuous : ∀ j,
      ContinuousAt (normalizedDifference j) 0 := by
    intro j
    have hqContinuous : ContinuousAt (fun t ↦ q (point j t)) 0 :=
      by
        change ContinuousAt (q ∘ point j) 0
        exact hqAnalytic.continuousAt.comp_of_eq
          (hpointContinuous j) (hpointZero j)
    dsimp only [normalizedDifference]
    have hcore : ContinuousAt
        (fun t ↦ conj (f z₀) * direction j ^ k * q (point j t)) 0 :=
      continuousAt_const.mul hqContinuous
    have hre : ContinuousAt
        (fun t ↦ (conj (f z₀) * direction j ^ k * q (point j t)).re) 0 :=
      Complex.continuous_re.continuousAt.comp hcore
    have hnormSq : ContinuousAt
        (fun t ↦ Complex.normSq (direction j ^ k * q (point j t))) 0 :=
      Complex.continuous_normSq.continuousAt.comp
        (continuousAt_const.mul hqContinuous)
    exact (hre.const_mul 2).add (continuousAt_id.pow k |>.mul hnormSq)
  have horbitInterior : ∀ j ∈ Finset.range k, ∀ᶠ t in nhds 0,
      0 < t → point j t ∈ interior K := by
    intro j hj
    have hnegative : ∀ᶠ t in nhds 0, normalizedDifference j t < 0 := by
      apply (hnormalizedContinuous j).eventually_lt continuousAt_const
      rw [hnormalizedZero j]
      norm_num
    have hfactorPath : ∀ᶠ t in nhds 0,
        A (point j t) = (point j t - z₀) ^ k * q (point j t) := by
      exact (hpointTendsto j).eventually hfactor
    have hsublevelPath : ∀ᶠ t in nhds 0,
        ‖f (point j t)‖ < 1 → point j t ∈ interior K :=
      (hpointTendsto j).eventually hsublevel
    filter_upwards [hnegative, hfactorPath, hsublevelPath] with
      t htNegative htFactor htSublevel ht
    have htPow : 0 < t ^ k := pow_pos ht k
    have hdelta : f (point j t) = f z₀ +
        ((t : ℂ) ^ k) * (direction j ^ k * q (point j t)) := by
      calc
        f (point j t) = f z₀ + A (point j t) := by simp [A]
        _ = f z₀ + (point j t - z₀) ^ k * q (point j t) := by rw [htFactor]
        _ = f z₀ + ((t : ℂ) ^ k) *
            (direction j ^ k * q (point j t)) := by
          simp only [point, add_sub_cancel_left, mul_pow]
          ring
    have hnormz₀ : Complex.normSq (f z₀) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hnorm, one_pow]
    have hnormIdentity : Complex.normSq (f (point j t)) - 1 =
        t ^ k * normalizedDifference j t := by
      have hrealPow : ((t : ℂ) ^ k) = (t ^ k : ℝ) := by norm_cast
      rw [hdelta, ← hnormz₀, hrealPow,
        normSq_add_real_mul_sub_normSq]
      simp only [normalizedDifference, mul_assoc]
    have hnormSqLt : Complex.normSq (f (point j t)) < 1 := by
      rw [← sub_neg]
      rw [hnormIdentity]
      exact mul_neg_of_pos_of_neg htPow htNegative
    have hnormLt : ‖f (point j t)‖ < 1 := by
      rw [Complex.normSq_eq_norm_sq] at hnormSqLt
      nlinarith [norm_nonneg (f (point j t))]
    exact htSublevel hnormLt
  have hall : ∀ᶠ t in nhds 0, ∀ j ∈ Finset.range k,
      0 < t → point j t ∈ interior K :=
    (eventually_all_finset (Finset.range k)).mpr horbitInterior
  have hallWithin : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      ∀ j ∈ Finset.range k, 0 < t → point j t ∈ interior K :=
    hall.filter_mono nhdsWithin_le_nhds
  have hpositive : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < t :=
    self_mem_nhdsWithin
  obtain ⟨t, htAll, ht⟩ := (hallWithin.and hpositive).exists
  have horbit : ∀ j ∈ Finset.range k, point j t ∈ interior K := by
    intro j hj
    exact htAll j hj ht
  have hweights : ∑ _j ∈ Finset.range k, (k : ℝ)⁻¹ = 1 := by
    simp [hkpos.ne']
  have havg : (∑ j ∈ Finset.range k, (k : ℝ)⁻¹ • point j t) ∈
      interior K := by
    apply hconvex.interior.sum_mem
    · intro j hj
      positivity
    · exact hweights
    · exact horbit
  have hsumDirection : ∑ j ∈ Finset.range k, direction j = 0 := by
    simp only [direction]
    rw [← mul_sum, hζsum, mul_zero]
  have hsumPoint : ∑ j ∈ Finset.range k, point j t = k • z₀ := by
    simp only [point, sum_add_distrib, sum_const, card_range]
    rw [← mul_sum, hsumDirection, mul_zero, add_zero]
  have havgEq : ∑ j ∈ Finset.range k, (k : ℝ)⁻¹ • point j t = z₀ := by
    rw [← Finset.smul_sum, hsumPoint]
    rw [nsmul_eq_mul, Complex.real_smul]
    simp [hkpos.ne']
  rw [havgEq] at havg
  exact (Set.disjoint_left.mp disjoint_interior_frontier) havg hz₀

/-- Polynomial-quotient form of the root-of-unity barycenter argument.
The strict sublevel is stated with the explicit nonpole condition, so it
matches the usual finite rational sublevel exactly. -/
theorem quotient_deriv_ne_zero_of_coprime_convex_full_sublevel
    (U V : ℂ[X]) (hcoprime : IsCoprime U V)
    (hdegree : V.natDegree < U.natDegree)
    {K : Set ℂ} (hconvex : Convex ℝ K)
    (hsublevel : ∀ z,
      (V.eval z ≠ 0 ∧ ‖U.eval z / V.eval z‖ < 1) ↔ z ∈ interior K)
    {z₀ : ℂ} (hz₀ : z₀ ∈ frontier K)
    (hlevel : ‖U.eval z₀‖ = ‖V.eval z₀‖) :
    deriv (fun z ↦ U.eval z / V.eval z) z₀ ≠ 0 := by
  have hvalues : U.eval z₀ ≠ 0 ∨ V.eval z₀ ≠ 0 := by
    simpa [Polynomial.aeval_def] using
      Polynomial.aeval_ne_zero_of_isCoprime hcoprime z₀
  have hVzero : V.eval z₀ ≠ 0 := by
    intro hV
    have hU : U.eval z₀ = 0 := by
      apply norm_eq_zero.mp
      rw [hlevel, hV, norm_zero]
    exact hvalues.elim (fun h ↦ h hU) (fun h ↦ h hV)
  have hanalytic : AnalyticAt ℂ (fun z ↦ U.eval z / V.eval z) z₀ := by
    have hUanalytic : AnalyticAt ℂ (fun z ↦ U.eval z) z₀ :=
      AnalyticOnNhd.eval_polynomial U z₀ (mem_univ z₀)
    have hVanalytic : AnalyticAt ℂ (fun z ↦ V.eval z) z₀ :=
      AnalyticOnNhd.eval_polynomial V z₀ (mem_univ z₀)
    apply (hUanalytic.div hVanalytic hVzero).congr
    filter_upwards [] with z
    simp only [Pi.div_apply]
  have hnonconstant : ¬ (fun z ↦ U.eval z / V.eval z) =ᶠ[nhds z₀]
      fun _ ↦ U.eval z₀ / V.eval z₀ := by
    intro hconstant
    let c : ℂ := U.eval z₀ / V.eval z₀
    let P : ℂ[X] := U - Polynomial.C c * V
    have hVevent : ∀ᶠ z in nhds z₀, V.eval z ≠ 0 :=
      V.continuous.continuousAt.eventually_ne hVzero
    have hPevent : (fun z ↦ P.eval z) =ᶠ[nhds z₀] 0 := by
      filter_upwards [hconstant, hVevent] with z hz hVz
      change P.eval z = (0 : ℂ)
      have hquotient : U.eval z / V.eval z = c := by
        simpa only [c] using hz
      have hcross : U.eval z = c * V.eval z :=
        (div_eq_iff hVz).mp hquotient
      simpa only [P, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C, sub_eq_zero] using hcross
    have hPfun : (fun z : ℂ ↦ P.eval z) = (fun _ : ℂ ↦ (0 : ℂ)) := by
      apply AnalyticOnNhd.eq_of_eventuallyEq
        (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) P) analyticOnNhd_const
      exact hPevent
    have hPzero : P = 0 := by
      apply Polynomial.funext
      intro z
      simpa using congrFun hPfun z
    have hUeq : U = Polynomial.C c * V := by
      exact sub_eq_zero.mp hPzero
    have hdegreeLe : U.natDegree ≤ V.natDegree := by
      rw [hUeq]
      exact Polynomial.natDegree_C_mul_le c V
    exact (Nat.not_lt_of_ge hdegreeLe) hdegree
  have hnorm : ‖U.eval z₀ / V.eval z₀‖ = 1 := by
    rw [norm_div, hlevel, div_self]
    exact norm_ne_zero_iff.mpr hVzero
  have hlocalSublevel : ∀ᶠ z in nhds z₀,
      ‖U.eval z / V.eval z‖ < 1 → z ∈ interior K := by
    have hVevent : ∀ᶠ z in nhds z₀, V.eval z ≠ 0 :=
      V.continuous.continuousAt.eventually_ne hVzero
    filter_upwards [hVevent] with z hVz hz
    exact (hsublevel z).mp ⟨hVz, hz⟩
  exact deriv_ne_zero_of_convex_full_sublevel hanalytic hnonconstant
    hnorm hconvex hz₀ hlocalSublevel

/-- Setwise form: every point of a full reduced rational level is
noncritical once its finite strict sublevel is the interior of a convex
body. -/
theorem quotient_deriv_ne_zero_on_frontier_of_coprime_convex_full_sublevel
    (U V : ℂ[X]) (hcoprime : IsCoprime U V)
    (hdegree : V.natDegree < U.natDegree)
    {K : Set ℂ} (hconvex : Convex ℝ K)
    (hsublevel : ∀ z,
      (V.eval z ≠ 0 ∧ ‖U.eval z / V.eval z‖ < 1) ↔ z ∈ interior K)
    (hlevel : ∀ z ∈ frontier K, ‖U.eval z‖ = ‖V.eval z‖) :
    ∀ z ∈ frontier K,
      deriv (fun w ↦ U.eval w / V.eval w) z ≠ 0 := by
  intro z hz
  exact quotient_deriv_ne_zero_of_coprime_convex_full_sublevel
    U V hcoprime hdegree hconvex hsublevel hz (hlevel z hz)

end ConvexNoncriticalLevel

end DiskRigidity.Algebraic
