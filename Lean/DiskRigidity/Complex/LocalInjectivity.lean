/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

module

public import DiskRigidity.Complex.Rouche
public import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Local injectivity of holomorphic functions

The local mapping-degree argument proves that an analytic function is locally injective exactly
where its derivative is nonzero.  This is the one-variable ingredient needed to show that the
inverse of a biholomorphism is holomorphic.
-/

open Complex Metric Filter Topology

namespace DiskRigidity.Complex

@[expose] public section

/-- A continuous zero-free function on a sphere has a positive uniform lower bound there. -/
theorem exists_pos_le_norm_of_mem_sphere {E F : Type*} [PseudoMetricSpace E] [ProperSpace E]
    [NormedAddCommGroup F] {f : E → F} {a : E} {ρ : ℝ}
    (hcont : ContinuousOn f (sphere a ρ)) (hne : ∀ z ∈ sphere a ρ, f z ≠ 0) :
    ∃ δ > 0, ∀ z ∈ sphere a ρ, δ ≤ ‖f z‖ :=
  (isCompact_sphere a ρ).exists_forall_le' hcont.norm fun z hz ↦ norm_pos_iff.mpr (hne z hz)

/-- A function nonzero off the centre of a positive-radius ball has finite analytic order there. -/
theorem analyticOrderAt_ne_top_of_forall_ne_zero {f : ℂ → ℂ} {a : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hzf : ∀ z ∈ ball a ρ, z ≠ a → f z ≠ 0) :
    analyticOrderAt f a ≠ ⊤ := by
  intro hev
  rw [analyticOrderAt_eq_top] at hev
  obtain ⟨ε, hε, hbl⟩ := Metric.eventually_nhds_iff.mp hev
  set t : ℝ := min ε ρ / 2 with ht_def
  have ht0 : 0 < t := by rw [ht_def]; exact half_pos (lt_min hε hρ)
  have htε : t < ε := by
    have h := min_le_left ε ρ
    rw [ht_def]
    linarith
  have htρ : t < ρ := by
    have h := min_le_right ε ρ
    rw [ht_def] at ht0 ⊢
    linarith
  have hdist : dist (a + (t : ℂ)) a = t := by simp [dist_eq_norm, abs_of_pos ht0]
  refine hzf (a + (t : ℂ)) ?_ ?_ (hbl ?_)
  · simpa [mem_ball, hdist]
  · simp only [ne_eq, add_eq_left, Complex.ofReal_eq_zero]
    exact ht0.ne'
  · rwa [hdist]

private lemma count_eq_single {f : ℂ → ℂ} {c z₀ : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hz₀ : z₀ ∈ ball c R)
    (hone : ∀ z ∈ ball c R, z ≠ z₀ → f z ≠ 0) :
    (∑ᶠ z ∈ ball c R, analyticOrderNatAt f z) = analyticOrderNatAt f z₀ := by
  classical
  have hsub : ((({z₀} : Finset ℂ) : Set ℂ)) ⊆ ball c R := by simpa using hz₀
  have h1 : ball c R ∩ Function.support (fun z ↦ analyticOrderNatAt f z) ⊆
      ((({z₀} : Finset ℂ) : Set ℂ)) := by
    rintro z ⟨hzb, hzs⟩
    simp only [Function.mem_support, ne_eq] at hzs
    by_contra hne
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hne
    exact hzs (by
      simp [analyticOrderNatAt,
        (hf z (ball_subset_closedBall hzb)).analyticOrderAt_eq_zero.2 (hone z hzb hne)])
  rw [finsum_mem_eq_sum_of_subset _ h1 hsub, Finset.sum_singleton]

/-- The local mapping-degree theorem, counting zeros with multiplicity. -/
theorem localDegree {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall z₀ r))
    (hisol : ∀ z ∈ closedBall z₀ r, z ≠ z₀ → f z ≠ f z₀) :
    ∃ δ > 0, ∀ w : ℂ, ‖w - f z₀‖ < δ →
      (∑ᶠ z ∈ ball z₀ r, analyticOrderNatAt (fun ζ ↦ f ζ - w) z) =
        analyticOrderNatAt (fun ζ ↦ f ζ - f z₀) z₀ := by
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_norm_of_mem_sphere
    (f := fun ζ ↦ f ζ - f z₀)
    ((hf.continuousOn.mono sphere_subset_closedBall).sub continuousOn_const)
    fun z hz ↦ sub_ne_zero.mpr
      (hisol z (sphere_subset_closedBall hz) (Metric.ne_of_mem_sphere hz hr.ne'))
  refine ⟨δ, hδ, fun w hw ↦ ?_⟩
  have hA0 : AnalyticOnNhd ℂ (fun ζ ↦ f ζ - f z₀) (closedBall z₀ r) :=
    hf.sub analyticOnNhd_const
  have hAw : AnalyticOnNhd ℂ (fun ζ ↦ f ζ - w) (closedBall z₀ r) :=
    hf.sub analyticOnNhd_const
  have hs : ∀ z ∈ sphere z₀ r, ‖(f z - f z₀) - (f z - w)‖ < ‖f z - f z₀‖ := by
    intro z hz
    have he : (f z - f z₀) - (f z - w) = w - f z₀ := by ring
    rw [he]
    exact lt_of_lt_of_le hw (hδle z hz)
  refine (rouche hr hA0 hAw hs).symm.trans
    (count_eq_single hA0 (mem_ball_self hr) (fun z hz hzn ↦ ?_))
  exact sub_ne_zero.mpr (hisol z (ball_subset_closedBall hz) hzn)

private lemma count_eq_ncard {A : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hA : AnalyticOnNhd ℂ A (closedBall c R))
    (hsimple : ∀ z ∈ ball c R, A z = 0 → analyticOrderNatAt A z = 1) :
    (∑ᶠ z ∈ ball c R, analyticOrderNatAt A z) = {z ∈ ball c R | A z = 0}.ncard := by
  have hAb : AnalyticOnNhd ℂ A (ball c R) := hA.mono ball_subset_closedBall
  have hsupp : ball c R ∩ Function.support (fun z ↦ analyticOrderNatAt A z) =
      {z ∈ ball c R | A z = 0} := by
    ext z
    constructor
    · rintro ⟨hzb, hzs⟩
      refine ⟨hzb, ?_⟩
      by_contra h
      exact hzs (by
        simp [analyticOrderNatAt, (hAb z hzb).analyticOrderAt_eq_zero.2 h])
    · rintro ⟨hzb, hz0⟩
      exact ⟨hzb, by simp [Function.mem_support, hsimple z hzb hz0]⟩
  rw [← finsum_mem_inter_support, hsupp,
    finsum_mem_congr rfl
      (fun z (hz : z ∈ {z ∈ ball c R | A z = 0}) ↦ hsimple z hz.1 hz.2)]
  exact finsum_one

private lemma zeros_finite {A : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hA : AnalyticOnNhd ℂ A (closedBall c R))
    (hsimple : ∀ z ∈ ball c R, A z = 0 → analyticOrderNatAt A z = 1) :
    {z ∈ ball c R | A z = 0}.Finite := by
  refine Set.Finite.subset (MeromorphicOn.divisor_ball_support_finite hA.meromorphicOn)
    (fun z hz ↦ ?_)
  obtain ⟨hzb, hz0⟩ := hz
  have hAb : AnalyticOnNhd ℂ A (ball c R) := hA.mono ball_subset_closedBall
  have h1 : analyticOrderNatAt A z = 1 := hsimple z hzb hz0
  have hord : analyticOrderAt A z = 1 := by
    cases h : analyticOrderAt A z with
    | top => simp [analyticOrderNatAt, h] at h1
    | coe n =>
        simp only [analyticOrderNatAt, h, ENat.toNat_natCast] at h1
        simp [h1]
  simp [Function.mem_support, MeromorphicOn.AnalyticOnNhd.divisor_apply hAb hzb, hord]

/-- Local degree in the form that counts distinct simple preimages. -/
theorem localDegree_card {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall z₀ r))
    (hisol : ∀ z ∈ closedBall z₀ r, z ≠ z₀ → f z ≠ f z₀)
    (hderiv : ∀ z ∈ ball z₀ r, z ≠ z₀ → deriv f z ≠ 0) :
    ∃ δ > 0, ∀ w : ℂ, w ≠ f z₀ → ‖w - f z₀‖ < δ →
      {z ∈ ball z₀ r | f z = w}.Finite ∧
        {z ∈ ball z₀ r | f z = w}.ncard =
          analyticOrderNatAt (fun ζ ↦ f ζ - f z₀) z₀ ∧
        ∀ z ∈ ball z₀ r, f z = w → analyticOrderNatAt (fun ζ ↦ f ζ - w) z = 1 := by
  obtain ⟨δ, hδ, hcount⟩ := localDegree hr hf hisol
  refine ⟨δ, hδ, fun w hw hwδ ↦ ?_⟩
  have hA : AnalyticOnNhd ℂ (fun ζ ↦ f ζ - w) (closedBall z₀ r) :=
    hf.sub analyticOnNhd_const
  have hsimple : ∀ z ∈ ball z₀ r, f z - w = 0 →
      analyticOrderNatAt (fun ζ ↦ f ζ - w) z = 1 := by
    intro z hz hz0
    have hzne : z ≠ z₀ := by
      rintro rfl
      exact hw (sub_eq_zero.mp hz0).symm
    have hd : deriv (fun ζ ↦ f ζ - w) z ≠ 0 := by
      rw [deriv_sub_const]
      exact hderiv z hz hzne
    simp [analyticOrderNatAt,
      (hA z (ball_subset_closedBall hz)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz0 hd]
  have hset : {z ∈ ball z₀ r | (fun ζ ↦ f ζ - w) z = 0} =
      {z ∈ ball z₀ r | f z = w} := by
    ext z
    simp [sub_eq_zero]
  refine ⟨hset ▸ zeros_finite hA hsimple, ?_,
    fun z hz hfz ↦ hsimple z hz (by rw [hfz, sub_self])⟩
  rw [← hcount w hwδ, count_eq_ncard hA hsimple, hset]

private lemma not_injOn_ball_of_deriv_eq_zero {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall z₀ r))
    (hisol : ∀ z ∈ closedBall z₀ r, z ≠ z₀ → f z ≠ f z₀)
    (hderiv : ∀ z ∈ ball z₀ r, z ≠ z₀ → deriv f z ≠ 0)
    (hd₀ : deriv f z₀ = 0) : ¬ Set.InjOn f (ball z₀ r) := by
  obtain ⟨δ, hδ, hcard⟩ := localDegree_card hr hf hisol hderiv
  have hA : AnalyticAt ℂ (fun ζ ↦ f ζ - f z₀) z₀ :=
    (hf.sub analyticOnNhd_const) z₀ (mem_closedBall_self hr.le)
  have htop : analyticOrderAt (fun ζ ↦ f ζ - f z₀) z₀ ≠ ⊤ :=
    analyticOrderAt_ne_top_of_forall_ne_zero hr fun z hz hzn ↦
      sub_ne_zero.mpr (hisol z (ball_subset_closedBall hz) hzn)
  have h2 : 2 ≤ analyticOrderNatAt (fun ζ ↦ f ζ - f z₀) z₀ := by
    have hle : ((2 : ℕ) : ℕ∞) ≤ analyticOrderAt (fun ζ ↦ f ζ - f z₀) z₀ := by
      rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hA]
      intro i hi
      interval_cases i
      · simp
      · simpa [iteratedDeriv_one, deriv_sub_const] using hd₀
    simpa [analyticOrderNatAt] using (ENat.toNat_le_toNat hle htop)
  set w : ℂ := f z₀ + (δ / 2 : ℝ) with hw_def
  have hwne : w ≠ f z₀ := by
    simp [hw_def, ne_eq, add_eq_left, Complex.ofReal_eq_zero]
    linarith
  have hwlt : ‖w - f z₀‖ < δ := by
    simp only [hw_def, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < δ / 2)]
    linarith
  obtain ⟨hfin, hncard, _⟩ := hcard w hwne hwlt
  have hnontriv : {z ∈ ball z₀ r | f z = w}.Nontrivial := by
    have hgt : 1 < {z ∈ ball z₀ r | f z = w}.ncard := by rw [hncard]; omega
    have := hfin.to_subtype
    exact Set.one_lt_ncard_iff_nontrivial.mp hgt
  obtain ⟨a, ha, b, hb, hab⟩ := hnontriv
  exact fun hinj ↦ hab (hinj ha.1 hb.1 (ha.2.trans hb.2.symm))

private theorem eventually_deriv_ne_zero_of_eventually_ne {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hne : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ f z₀) :
    ∀ᶠ z in 𝓝[≠] z₀, deriv f z ≠ 0 := by
  rcases hf.deriv.eventually_eq_zero_or_eventually_ne_zero with hz | hz
  · exfalso
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hz.and hf.eventually_analyticAt)
    have hfd : Set.EqOn (deriv f) 0 (ball z₀ ε) := fun x hx ↦ (hball (mem_ball.mp hx)).1
    have hdiff : DifferentiableOn ℂ f (ball z₀ ε) := fun x hx ↦
      ((hball (mem_ball.mp hx)).2.differentiableAt).differentiableWithinAt
    have hpunct : ∀ᶠ z in 𝓝[≠] z₀, z ∈ ball z₀ ε ∧ f z ≠ f z₀ := by
      filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds z₀ hε), hne] with z h1 h2
      exact ⟨h1, h2⟩
    obtain ⟨b, hbball, hbne⟩ := hpunct.exists
    exact hbne (isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball z₀ ε).isPreconnected hdiff hfd hbball (mem_ball_self hε))
  · exact hz

/-- An analytic function with vanishing derivative is not injective on any neighbourhood. -/
theorem not_injOn_of_deriv_eq_zero {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hd₀ : deriv f z₀ = 0)
    {V : Set ℂ} (hV : V ∈ 𝓝 z₀) : ¬ Set.InjOn f V := by
  intro hinj
  have hz₀V : z₀ ∈ V := mem_of_mem_nhds hV
  rcases (hf.sub analyticAt_const).eventually_eq_zero_or_eventually_ne_zero with hconst | hisol
  · have hpunct : ∀ᶠ z in 𝓝[≠] z₀, z ∈ V ∧ z ≠ z₀ ∧ f z = f z₀ := by
      filter_upwards [nhdsWithin_le_nhds hV, self_mem_nhdsWithin, nhdsWithin_le_nhds hconst]
        with z h1 h2 h3
      exact ⟨h1, by simpa using h2, by simpa [sub_eq_zero] using h3⟩
    obtain ⟨a, haV, hane, haeq⟩ := hpunct.exists
    exact hane (hinj haV hz₀V haeq)
  · have hderiv : ∀ᶠ z in 𝓝[≠] z₀, deriv f z ≠ 0 :=
      eventually_deriv_ne_zero_of_eventually_ne hf
        (hisol.mono fun _ h ↦ sub_ne_zero.mp h)
    have hall : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ f z ∧ z ∈ V ∧
        (z ≠ z₀ → f z ≠ f z₀) ∧ (z ≠ z₀ → deriv f z ≠ 0) := by
      filter_upwards [hf.eventually_analyticAt, hV, eventually_nhdsWithin_iff.mp hisol,
        eventually_nhdsWithin_iff.mp hderiv] with z h1 h2 h3 h4
      exact ⟨h1, h2, fun hz ↦ sub_ne_zero.mp (h3 (by simpa using hz)),
        fun hz ↦ h4 (by simpa using hz)⟩
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hall
    have hr : 0 < ε / 2 := by linarith
    have hsub : ∀ z ∈ closedBall z₀ (ε / 2), dist z z₀ < ε := fun z hz ↦
      lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith)
    refine absurd
      (hinj.mono (fun z hz ↦ (hball (hsub z (ball_subset_closedBall hz))).2.1))
      (not_injOn_ball_of_deriv_eq_zero hr (fun z hz ↦ (hball (hsub z hz)).1)
        (fun z hz hzn ↦ (hball (hsub z hz)).2.2.1 hzn)
        (fun z hz hzn ↦ (hball (hsub z (ball_subset_closedBall hz))).2.2.2 hzn) hd₀)

/-- An analytic function is locally injective exactly when its derivative is nonzero. -/
theorem exists_injOn_nhds_iff_deriv_ne_zero {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) :
    (∃ V ∈ 𝓝 z₀, Set.InjOn f V) ↔ deriv f z₀ ≠ 0 := by
  constructor
  · rintro ⟨V, hV, hinj⟩ hd₀
    exact not_injOn_of_deriv_eq_zero hf hd₀ hV hinj
  · intro hd₀
    obtain ⟨W, hW, hWeq⟩ :=
      Filter.eventually_iff_exists_mem.mp (hf.hasStrictDerivAt.eventually_left_inverse hd₀)
    exact ⟨W, hW, fun a ha b hb hab ↦ by rw [← hWeq a ha, ← hWeq b hb, hab]⟩

end

end DiskRigidity.Complex
