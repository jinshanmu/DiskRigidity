/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.AnalyticImplicitCurve
public import DiskRigidity.Algebraic.ConvexSupport

/-!
# Analytic tangent charts on a strictly convex algebraic oval

Regularity gives a local analytic coordinate graph.  Strict convexity then
rules out an open arc whose tangent normals all lie in the vertical chart at
infinity: only two support lines have a fixed unoriented normal.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace ConvexAnalyticArc

open Matrix Metric MvPolynomial Set
open ProjectiveDual
open Filter
open scoped Topology

/-- A point of every ambient-open boundary arc has nonzero `Y` component in
its tangent covector.  This is the chart-selection fact needed to normalize
the tangent line to `[s:u:1]`. -/
theorem exists_gradient_two_ne_zero_on_open_boundary_arc
    {P : MvPolynomial (Fin 3) ℝ} {d : ℕ}
    (hP : P.IsHomogeneous d)
    {K : Set ConvexSupport.Point}
    (hcompact : IsCompact K) (hinterior : (interior K).Nonempty)
    (hstrict : StrictConvex ℝ K)
    (hregular : ∀ x ∈ frontier K,
      RegularAt P ![1, x 0, x 1])
    (hlocus : frontier K =
      {x | MvPolynomial.eval ![1, x 0, x 1] P = 0})
    (htangentSupport : ∀ {x : ConvexSupport.Point}
      {ell : Fin 3 → ℝ}, x ∈ frontier K →
      (∃ a : ℝ, gradient P ![1, x 0, x 1] = a • ell) →
      ConvexSupport.IsSupportOffset K ![ell 1, ell 2] (-ell 0))
    {W : Set ConvexSupport.Point} (hWopen : IsOpen W)
    (hWarc : (W ∩ frontier K).Nonempty) :
    ∃ x ∈ W ∩ frontier K, gradient P ![1, x 0, x 1] 2 ≠ 0 := by
  obtain ⟨x₀, hx₀W, hx₀boundary⟩ := hWarc
  have hx₀repr : (![x₀ 0, x₀ 1] : ConvexSupport.Point) = x₀ := by
    funext i
    fin_cases i <;> rfl
  rcases AnalyticImplicitCurve.exists_connected_analytic_coordinate_graph_in_open
      hP (hregular x₀ hx₀boundary) hWopen (hx₀repr.symm ▸ hx₀W) with hYX | hXY
  · obtain ⟨U, p, hUopen, hUne, _hUpre, hp, hgraph⟩ := hYX
    by_contra hnone
    have hgrad₂ : ∀ t ∈ U, gradient P ![1, p t, t] 2 = 0 := by
      intro t ht
      by_contra hne
      apply hnone
      refine ⟨![p t, t], ⟨(hgraph t ht).1, ?_⟩, hne⟩
      rw [hlocus]
      exact (hgraph t ht).2.1
    let n : ConvexSupport.Point := ![1, 0]
    have hn : n ≠ 0 := by
      intro h
      have := congrFun h (0 : Fin 2)
      norm_num [n] at this
    obtain ⟨rmin, rmax, _hrne, hsupportClass⟩ :=
      ConvexSupport.supportOffset_iff_eq_two hcompact hinterior hn
    let offset : ℝ → ℝ := fun t ↦
      -(gradient P ![1, p t, t] 0 / gradient P ![1, p t, t] 1)
    have hboundary : ∀ t ∈ U, ![p t, t] ∈ frontier K := by
      intro t ht
      rw [hlocus]
      exact (hgraph t ht).2.1
    have hsupport : ∀ t ∈ U,
        ConvexSupport.IsSupportOffset K n (offset t) := by
      intro t ht
      let ell : Fin 3 → ℝ := ![-offset t, 1, 0]
      have hscale : gradient P ![1, p t, t] =
          gradient P ![1, p t, t] 1 • ell := by
        have h₁ := (hgraph t ht).2.2
        have h₂ := hgrad₂ t ht
        funext i
        fin_cases i
        · simp only [ell, offset, Pi.smul_apply, smul_eq_mul, neg_neg]
          change gradient P ![1, p t, t] 0 =
            gradient P ![1, p t, t] 1 *
              (gradient P ![1, p t, t] 0 /
                gradient P ![1, p t, t] 1)
          field_simp
        · simp [ell]
        · simp [ell, h₂]
      have hs := htangentSupport (hboundary t ht)
        ⟨gradient P ![1, p t, t] 1, hscale⟩
      simpa [ell, n] using hs
    have hclass : ∀ t ∈ U, offset t = rmin ∨ offset t = rmax := by
      intro t ht
      exact (hsupportClass (offset t)).mp (hsupport t ht)
    have hUinf : U.Infinite := by
      obtain ⟨t, ht⟩ := hUne
      exact infinite_of_mem_nhds t (hUopen.mem_nhds ht)
    let color : {t // t ∈ U} → Bool := fun t ↦ decide (offset t = rmin)
    have hninj : ¬Function.Injective color :=
      @not_injective_infinite_finite {t // t ∈ U} Bool
        hUinf.to_subtype inferInstance color
    simp only [Function.Injective, not_forall] at hninj
    obtain ⟨a, b, habColor, hab⟩ := hninj
    have hoffset : offset a = offset b := by
      by_cases ha : offset a = rmin
      · have hb : offset b = rmin := by
          simpa [color, ha] using habColor
        exact ha.trans hb.symm
      · have haMax : offset a = rmax := (hclass a a.property).resolve_left ha
        have hbNot : offset b ≠ rmin := by
          intro hb
          have : color a ≠ color b := by simp [color, ha, hb]
          exact this habColor
        have hbMax : offset b = rmax :=
          (hclass b b.property).resolve_left hbNot
        exact haMax.trans hbMax.symm
    have hKmem : ∀ t ∈ U, ![p t, t] ∈ K := by
      intro t ht
      have hcl := frontier_subset_closure (hboundary t ht)
      simpa [hcompact.isClosed.closure_eq] using hcl
    have hline : ∀ t ∈ U,
        ConvexSupport.linearValue n ![p t, t] = offset t := by
      intro t ht
      have hdot := dot_gradient_eq_zero hP (hgraph t ht).2.1
      have h₁ := (hgraph t ht).2.2
      have h₂ := hgrad₂ t ht
      have hdot' : gradient P ![1, p t, t] 0 +
          p t * gradient P ![1, p t, t] 1 = 0 := by
        simpa [dotProduct, Fin.sum_univ_three, h₂] using hdot
      have hpEq : p t =
          -(gradient P ![1, p t, t] 0 /
            gradient P ![1, p t, t] 1) := by
        calc
          p t = (-gradient P ![1, p t, t] 0) /
              gradient P ![1, p t, t] 1 := by
            apply (eq_div_iff h₁).2
            nlinarith [hdot']
          _ = -(gradient P ![1, p t, t] 0 /
              gradient P ![1, p t, t] 1) := by ring
      simpa [ConvexSupport.linearValue, n, dotProduct, Fin.sum_univ_two]
        using hpEq
    have hzEq : (![p a, (a : ℝ)] : ConvexSupport.Point) = ![p b, (b : ℝ)] := by
      apply ConvexSupport.eq_of_mem_support_of_strictConvex hstrict hn
        (hsupport a a.property)
        (hKmem a a.property) (hKmem b b.property)
      · exact hline a a.property
      · calc
          ConvexSupport.linearValue n ![p b, (b : ℝ)] = offset b :=
            hline b b.property
          _ = offset a := hoffset.symm
    apply hab
    have := congrFun hzEq (1 : Fin 2)
    apply Subtype.ext
    simpa using this
  · obtain ⟨U, p, _hUopen, hUne, _hUpre, _hp, hgraph⟩ := hXY
    obtain ⟨t, ht⟩ := hUne
    refine ⟨![t, p t], ?_, (hgraph t ht).2.2⟩
    exact ⟨(hgraph t ht).1, by
      rw [hlocus]
      exact (hgraph t ht).2.1⟩

/-- The preceding chart-selection theorem followed by the analytic implicit
function theorem gives a connected graph `[1,t,p(t)]` throughout which the
last tangent coordinate is nonzero. -/
theorem exists_connected_graph_with_gradient_two_ne_zero
    {P : MvPolynomial (Fin 3) ℝ} {d : ℕ}
    (hP : P.IsHomogeneous d)
    {K : Set ConvexSupport.Point}
    (hcompact : IsCompact K) (hinterior : (interior K).Nonempty)
    (hstrict : StrictConvex ℝ K)
    (hregular : ∀ x ∈ frontier K,
      RegularAt P ![1, x 0, x 1])
    (hlocus : frontier K =
      {x | MvPolynomial.eval ![1, x 0, x 1] P = 0})
    (htangentSupport : ∀ {x : ConvexSupport.Point}
      {ell : Fin 3 → ℝ}, x ∈ frontier K →
      (∃ a : ℝ, gradient P ![1, x 0, x 1] = a • ell) →
      ConvexSupport.IsSupportOffset K ![ell 1, ell 2] (-ell 0))
    {W : Set ConvexSupport.Point} (hWopen : IsOpen W)
    (hWarc : (W ∩ frontier K).Nonempty) :
    ∃ (U : Set ℝ) (p : ℝ → ℝ),
      IsOpen U ∧ U.Nonempty ∧ IsPreconnected U ∧
      AnalyticOnNhd ℝ p U ∧
      ∀ t ∈ U, ![t, p t] ∈ W ∩ frontier K ∧
        gradient P ![1, t, p t] 2 ≠ 0 := by
  obtain ⟨x, ⟨hxW, hxboundary⟩, hx₂⟩ :=
    exists_gradient_two_ne_zero_on_open_boundary_arc hP hcompact hinterior
      hstrict hregular hlocus htangentSupport hWopen hWarc
  obtain ⟨U₀, p, hU₀open, hx₀, hp, hp₀, hzero⟩ :=
    AnalyticImplicitCurve.exists_open_analytic_graph_of_pderiv_two_ne_zero
      P (x 0) (x 1) (by
        have hxzero : MvPolynomial.eval ![1, x 0, x 1] P = 0 := by
          have : x ∈ {y | MvPolynomial.eval ![1, y 0, y 1] P = 0} := by
            rwa [← hlocus]
          exact this
        exact hxzero) hx₂
  have hzAt : ContinuousAt (fun t : ℝ ↦ ![t, p t]) (x 0) := by
    rw [continuousAt_pi]
    intro i
    fin_cases i
    · exact continuousAt_id
    · exact (hp (x 0) hx₀).continuousAt
  have hz₀ : (fun t : ℝ ↦ ![t, p t]) (x 0) = x := by
    funext i
    fin_cases i
    · rfl
    · exact hp₀
  have hgAt : ContinuousAt
      (fun t : ℝ ↦ gradient P ![1, t, p t] 2) (x 0) := by
    have hg : AnalyticAt ℝ
        (fun t : ℝ ↦ ProjectiveDual.gradient P ![1, t, p t] 2) (x 0) := by
      unfold ProjectiveDual.gradient
      apply AnalyticAt.aeval_mvPolynomial
      intro i
      fin_cases i
      · exact analyticAt_const
      · exact analyticAt_id
      · exact hp (x 0) hx₀
    exact hg.continuousAt
  have hg₀ : gradient P ![1, x 0, p (x 0)] 2 ≠ 0 := by
    simpa [hp₀] using hx₂
  have hgood :
      (U₀ ∩ (fun t : ℝ ↦ ![t, p t]) ⁻¹' W) ∩
        {t | gradient P ![1, t, p t] 2 ≠ 0} ∈ 𝓝 (x 0) := by
    apply inter_mem
    · apply inter_mem (hU₀open.mem_nhds hx₀)
      apply hzAt
      rw [hz₀]
      exact hWopen.mem_nhds hxW
    · exact hgAt.eventually_ne hg₀
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨Metric.ball (x 0) ε, p, Metric.isOpen_ball,
    ⟨x 0, Metric.mem_ball_self hε⟩, Metric.isPreconnected_ball,
    hp.mono (hball.trans (inter_subset_left.trans inter_subset_left)), ?_⟩
  intro t ht
  have htg := hball ht
  refine ⟨⟨htg.1.2, ?_⟩, htg.2⟩
  rw [hlocus]
  exact hzero t htg.1.1

/-- Normalized offset coordinate of the tangent line along `[1,t,p(t)]`. -/
noncomputable def tangentOffset
    (P : MvPolynomial (Fin 3) ℝ) (p : ℝ → ℝ) (t : ℝ) : ℝ :=
  gradient P ![1, t, p t] 0 / gradient P ![1, t, p t] 2

/-- Normalized `X`-normal coordinate of the tangent line. -/
noncomputable def tangentSlope
    (P : MvPolynomial (Fin 3) ℝ) (p : ℝ → ℝ) (t : ℝ) : ℝ :=
  gradient P ![1, t, p t] 1 / gradient P ![1, t, p t] 2

theorem analyticOnNhd_gradient_graph
    (P : MvPolynomial (Fin 3) ℝ) {U : Set ℝ} {p : ℝ → ℝ}
    (hp : AnalyticOnNhd ℝ p U) (i : Fin 3) :
    AnalyticOnNhd ℝ (fun t ↦ gradient P ![1, t, p t] i) U := by
  intro t ht
  unfold ProjectiveDual.gradient
  apply AnalyticAt.aeval_mvPolynomial
  intro j
  fin_cases j
  · exact analyticAt_const
  · exact analyticAt_id
  · exact hp t ht

theorem analyticOnNhd_tangentOffset
    (P : MvPolynomial (Fin 3) ℝ) {U : Set ℝ} {p : ℝ → ℝ}
    (hp : AnalyticOnNhd ℝ p U)
    (h₂ : ∀ t ∈ U, gradient P ![1, t, p t] 2 ≠ 0) :
    AnalyticOnNhd ℝ (tangentOffset P p) U := by
  exact (analyticOnNhd_gradient_graph P hp 0).div
    (analyticOnNhd_gradient_graph P hp 2) h₂

theorem analyticOnNhd_tangentSlope
    (P : MvPolynomial (Fin 3) ℝ) {U : Set ℝ} {p : ℝ → ℝ}
    (hp : AnalyticOnNhd ℝ p U)
    (h₂ : ∀ t ∈ U, gradient P ![1, t, p t] 2 ≠ 0) :
    AnalyticOnNhd ℝ (tangentSlope P p) U := by
  exact (analyticOnNhd_gradient_graph P hp 1).div
    (analyticOnNhd_gradient_graph P hp 2) h₂

/-- Strict convexity forces the normalized tangent slope to move somewhere
on every connected analytic boundary graph. -/
theorem exists_deriv_tangentSlope_ne_zero
    {P : MvPolynomial (Fin 3) ℝ} {d : ℕ}
    (hP : P.IsHomogeneous d)
    {K : Set ConvexSupport.Point}
    (hcompact : IsCompact K) (hinterior : (interior K).Nonempty)
    (hstrict : StrictConvex ℝ K)
    {U : Set ℝ} (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hUpre : IsPreconnected U) {p : ℝ → ℝ}
    (hp : AnalyticOnNhd ℝ p U)
    (hboundary : ∀ t ∈ U, ![t, p t] ∈ frontier K)
    (hzero : ∀ t ∈ U, MvPolynomial.eval ![1, t, p t] P = 0)
    (h₂ : ∀ t ∈ U, gradient P ![1, t, p t] 2 ≠ 0)
    (htangentSupport : ∀ {x : ConvexSupport.Point}
      {ell : Fin 3 → ℝ}, x ∈ frontier K →
      (∃ a : ℝ, gradient P ![1, x 0, x 1] = a • ell) →
      ConvexSupport.IsSupportOffset K ![ell 1, ell 2] (-ell 0)) :
    ∃ t ∈ U, deriv (tangentSlope P p) t ≠ 0 := by
  by_contra hnone
  have hderivZero : ∀ t ∈ U, deriv (tangentSlope P p) t = 0 := by
    intro t ht
    by_contra hne
    exact hnone ⟨t, ht, hne⟩
  have hu := analyticOnNhd_tangentSlope P hp h₂
  obtain ⟨t₀, ht₀⟩ := hUne
  have huconst : ∀ t ∈ U, tangentSlope P p t = tangentSlope P p t₀ := by
    intro t ht
    exact hUopen.is_const_of_deriv_eq_zero hUpre hu.differentiableOn
      (fun x hx ↦ hderivZero x hx) ht ht₀
  let n : ConvexSupport.Point := ![tangentSlope P p t₀, 1]
  have hn : n ≠ 0 := by
    intro h
    have := congrFun h (1 : Fin 2)
    norm_num [n] at this
  let offset : ℝ → ℝ := fun t ↦ -tangentOffset P p t
  have hsupport : ∀ t ∈ U,
      ConvexSupport.IsSupportOffset K n (offset t) := by
    intro t ht
    let ell : Fin 3 → ℝ :=
      ![tangentOffset P p t, tangentSlope P p t, 1]
    have hscale : gradient P ![1, t, p t] =
        gradient P ![1, t, p t] 2 • ell := by
      have hne := h₂ t ht
      funext i
      fin_cases i
      · simp only [ell, tangentOffset, Pi.smul_apply, smul_eq_mul]
        change gradient P ![1, t, p t] 0 =
          gradient P ![1, t, p t] 2 *
            (gradient P ![1, t, p t] 0 /
              gradient P ![1, t, p t] 2)
        field_simp
      · simp only [ell, tangentSlope, Pi.smul_apply, smul_eq_mul]
        change gradient P ![1, t, p t] 1 =
          gradient P ![1, t, p t] 2 *
            (gradient P ![1, t, p t] 1 /
              gradient P ![1, t, p t] 2)
        field_simp
      · simp [ell]
    have hs := htangentSupport (hboundary t ht)
      ⟨gradient P ![1, t, p t] 2, hscale⟩
    simpa [ell, n, offset, huconst t ht] using hs
  obtain ⟨rmin, rmax, _hrne, hsupportClass⟩ :=
    ConvexSupport.supportOffset_iff_eq_two hcompact hinterior hn
  have hclass : ∀ t ∈ U, offset t = rmin ∨ offset t = rmax := by
    intro t ht
    exact (hsupportClass (offset t)).mp (hsupport t ht)
  have hUinf : U.Infinite :=
    infinite_of_mem_nhds t₀ (hUopen.mem_nhds ht₀)
  let color : {t // t ∈ U} → Bool := fun t ↦ decide (offset t = rmin)
  have hninj : ¬Function.Injective color :=
    @not_injective_infinite_finite {t // t ∈ U} Bool
      hUinf.to_subtype inferInstance color
  simp only [Function.Injective, not_forall] at hninj
  obtain ⟨a, b, habColor, hab⟩ := hninj
  have hoffset : offset a = offset b := by
    by_cases ha : offset a = rmin
    · have hb : offset b = rmin := by
        simpa [color, ha] using habColor
      exact ha.trans hb.symm
    · have haMax : offset a = rmax := (hclass a a.property).resolve_left ha
      have hbNot : offset b ≠ rmin := by
        intro hb
        have : color a ≠ color b := by simp [color, ha, hb]
        exact this habColor
      have hbMax : offset b = rmax :=
        (hclass b b.property).resolve_left hbNot
      exact haMax.trans hbMax.symm
  have hKmem : ∀ t ∈ U, ![t, p t] ∈ K := by
    intro t ht
    have hcl := frontier_subset_closure (hboundary t ht)
    simpa [hcompact.isClosed.closure_eq] using hcl
  have hline : ∀ t ∈ U,
      ConvexSupport.linearValue n ![t, p t] = offset t := by
    intro t ht
    have hdot := dot_gradient_eq_zero hP (hzero t ht)
    have hdot' : gradient P ![1, t, p t] 0 +
        t * gradient P ![1, t, p t] 1 +
        p t * gradient P ![1, t, p t] 2 = 0 := by
      simpa [dotProduct, Fin.sum_univ_three] using hdot
    have hnorm :
        tangentSlope P p t₀ * t + p t = -tangentOffset P p t := by
      rw [← huconst t ht]
      unfold tangentSlope tangentOffset
      field_simp [h₂ t ht]
      nlinarith [hdot']
    simpa [ConvexSupport.linearValue, n, offset, dotProduct,
      Fin.sum_univ_two] using hnorm
  have hzEq :
      (![(a : ℝ), p (a : ℝ)] : ConvexSupport.Point) =
        ![(b : ℝ), p (b : ℝ)] := by
    apply ConvexSupport.eq_of_mem_support_of_strictConvex hstrict hn
      (hsupport a a.property)
      (hKmem a a.property) (hKmem b b.property)
    · exact hline a a.property
    · calc
        ConvexSupport.linearValue n
            (![(b : ℝ), p (b : ℝ)] : ConvexSupport.Point) = offset b :=
          hline b b.property
        _ = offset a := hoffset.symm
  apply hab
  apply Subtype.ext
  have := congrFun hzEq (0 : Fin 2)
  simpa using this

/-- A noncritical point of a real-analytic function admits connected open
source and target intervals on which Mathlib's canonical local inverse is
analytic, has nonzero derivative, and satisfies both inverse identities.
The two intervals are recorded separately because the primal arc is
parameterized on the source whereas the normalized dual arc is parameterized
on the target. -/
theorem exists_connected_local_analytic_inverse
    {U : Set ℝ} (hUopen : IsOpen U) {u : ℝ → ℝ}
    (hu : AnalyticOnNhd ℝ u U) {t₀ : ℝ} (ht₀ : t₀ ∈ U)
    (hu' : deriv u t₀ ≠ 0) :
    ∃ (S R : Set ℝ) (psi : ℝ → ℝ),
      IsOpen S ∧ S.Nonempty ∧ IsPreconnected S ∧
      IsOpen R ∧ R.Nonempty ∧ IsPreconnected R ∧
      AnalyticOnNhd ℝ psi R ∧
      (∀ r ∈ R, psi r ∈ U ∧ u (psi r) = r ∧ deriv psi r ≠ 0) ∧
      (∀ t ∈ S, t ∈ U ∧ u t ∈ R ∧ psi (u t) = t) := by
  let hu₀ : AnalyticAt ℝ u t₀ := hu t₀ ht₀
  let psi : ℝ → ℝ :=
    hu₀.hasStrictDerivAt.localInverse u (deriv u t₀) t₀ hu'
  have hpsi₀ : psi (u t₀) = t₀ := by
    exact HasStrictFDerivAt.localInverse_apply_image _
  have hpsiAnalytic : AnalyticAt ℝ psi (u t₀) := by
    exact hu₀.analyticAt_localInverse hu'
  have hpsiDeriv : deriv psi (u t₀) = (deriv u t₀)⁻¹ := by
    exact (HasStrictDerivAt.to_localInverse hu₀.hasStrictDerivAt hu').hasDerivAt.deriv
  have hpsiDerivNe : deriv psi (u t₀) ≠ 0 := by
    rw [hpsiDeriv]
    exact inv_ne_zero hu'
  have hpsiU : ∀ᶠ r in 𝓝 (u t₀), psi r ∈ U := by
    apply hpsiAnalytic.continuousAt
    rw [hpsi₀]
    exact hUopen.mem_nhds ht₀
  have hright : ∀ᶠ r in 𝓝 (u t₀), u (psi r) = r := by
    exact HasStrictDerivAt.eventually_right_inverse hu₀.hasStrictDerivAt hu'
  have hpsiAnalyticNhd : ∀ᶠ r in 𝓝 (u t₀), AnalyticAt ℝ psi r :=
    hpsiAnalytic.eventually_analyticAt
  have hpsiDerivNhd : ∀ᶠ r in 𝓝 (u t₀), deriv psi r ≠ 0 :=
    hpsiAnalytic.deriv.continuousAt.eventually_ne hpsiDerivNe
  have hgoodR :
      {r | AnalyticAt ℝ psi r ∧ psi r ∈ U ∧
        u (psi r) = r ∧ deriv psi r ≠ 0} ∈ 𝓝 (u t₀) := by
    filter_upwards [hpsiAnalyticNhd, hpsiU, hright, hpsiDerivNhd] with r
      hrAnalytic hrU hrRight hrDeriv
    exact ⟨hrAnalytic, hrU, hrRight, hrDeriv⟩
  obtain ⟨ε, hε, hballR⟩ := Metric.mem_nhds_iff.mp hgoodR
  let R : Set ℝ := Metric.ball (u t₀) ε
  have huContinuous : ContinuousAt u t₀ := hu₀.continuousAt
  have huR : ∀ᶠ t in 𝓝 t₀, u t ∈ R := by
    apply huContinuous
    exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)
  have hleft : ∀ᶠ t in 𝓝 t₀, psi (u t) = t := by
    exact HasStrictDerivAt.eventually_left_inverse hu₀.hasStrictDerivAt hu'
  have hgoodS : {t | t ∈ U ∧ u t ∈ R ∧ psi (u t) = t} ∈ 𝓝 t₀ := by
    filter_upwards [hUopen.mem_nhds ht₀, huR, hleft] with t htU htR htLeft
    exact ⟨htU, htR, htLeft⟩
  obtain ⟨δ, hδ, hballS⟩ := Metric.mem_nhds_iff.mp hgoodS
  let S : Set ℝ := Metric.ball t₀ δ
  refine ⟨S, R, psi, Metric.isOpen_ball,
    ⟨t₀, Metric.mem_ball_self hδ⟩, Metric.isPreconnected_ball,
    Metric.isOpen_ball, ⟨u t₀, Metric.mem_ball_self hε⟩,
    Metric.isPreconnected_ball, ?_, ?_, ?_⟩
  · intro r hr
    exact (hballR hr).1
  · intro r hr
    exact ⟨(hballR hr).2.1, (hballR hr).2.2.1,
      (hballR hr).2.2.2⟩
  · intro t ht
    exact hballS ht

end ConvexAnalyticArc

end DiskRigidity.Algebraic
