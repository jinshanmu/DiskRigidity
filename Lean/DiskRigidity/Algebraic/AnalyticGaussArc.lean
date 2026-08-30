/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.ConvexAnalyticArc

/-!
# A normalized analytic Gauss arc of a strictly convex algebraic oval

Starting with an ambient-open boundary arc, this file selects the affine
chart in which the last tangent coordinate is nonzero, proves that the
normalized tangent slope moves, and applies the analytic inverse-function
theorem.  The result is a dual graph `[s(r):r:1]` together with its genuine
moving contact point.  Incidence, first-order tangency, and projective
nonstationarity are all derived rather than assumed.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace AnalyticGaussArc

open Filter Matrix Metric MvPolynomial Set
open ProjectiveDual
open scoped Topology

/-- All local data produced from a curved boundary arc.  This is output data
of `exists_normalizedTangentContactArc`; none of its fields is a hypothesis
of the final circle theorem. -/
structure NormalizedTangentContactArc
    (P : MvPolynomial (Fin 3) ℝ)
    (K W : Set ConvexSupport.Point)
    (D : MvPolynomial (Fin 3) ℂ) where
  /-- Parameter domain for the primal boundary graph. -/
  graphDomain : Set ℝ
  /-- Parameter domain for the normalized primal arc. -/
  primalDomain : Set ℝ
  /-- Parameter domain for the corresponding dual arc. -/
  dualDomain : Set ℝ
  /-- Real-analytic graph function for the primal arc. -/
  graph : ℝ → ℝ
  /-- Inverse of the slope coordinate along the dual arc. -/
  inverseSlope : ℝ → ℝ
  /-- Offset coordinate of the normalized dual tangent line. -/
  dualOffset : ℝ → ℝ
  graphDomain_open : IsOpen graphDomain
  graphDomain_nonempty : graphDomain.Nonempty
  graphDomain_preconnected : IsPreconnected graphDomain
  primalDomain_open : IsOpen primalDomain
  primalDomain_nonempty : primalDomain.Nonempty
  primalDomain_preconnected : IsPreconnected primalDomain
  dualDomain_open : IsOpen dualDomain
  dualDomain_nonempty : dualDomain.Nonempty
  dualDomain_preconnected : IsPreconnected dualDomain
  graph_analytic : AnalyticOnNhd ℝ graph graphDomain
  inverseSlope_analytic : AnalyticOnNhd ℝ inverseSlope dualDomain
  dualOffset_analytic : AnalyticOnNhd ℝ dualOffset dualDomain
  graph_mem : ∀ t ∈ graphDomain,
    ![t, graph t] ∈ W ∩ frontier K ∧
      gradient P ![1, t, graph t] 2 ≠ 0
  inverseSlope_spec : ∀ r ∈ dualDomain,
    inverseSlope r ∈ graphDomain ∧
      ConvexAnalyticArc.tangentSlope P graph (inverseSlope r) = r ∧
      deriv inverseSlope r ≠ 0
  primalDomain_spec : ∀ t ∈ primalDomain,
    t ∈ graphDomain ∧
      ConvexAnalyticArc.tangentSlope P graph t ∈ dualDomain ∧
      inverseSlope (ConvexAnalyticArc.tangentSlope P graph t) = t
  dualOffset_eq : ∀ r ∈ dualDomain,
    dualOffset r =
      ConvexAnalyticArc.tangentOffset P graph (inverseSlope r)
  determinant_zero : ∀ r ∈ dualDomain,
    MvPolynomial.eval ![(dualOffset r : ℂ), (r : ℂ), 1] D = 0
  contact_boundary : ∀ r ∈ dualDomain,
    ![inverseSlope r, graph (inverseSlope r)] ∈ W ∩ frontier K
  incidence : ∀ r ∈ dualDomain,
    ![dualOffset r, r, 1] ⬝ᵥ
      ![1, inverseSlope r, graph (inverseSlope r)] = 0
  tangent_contact : ∀ r ∈ dualDomain,
    ![dualOffset r, r, 1] ⬝ᵥ
      (fun i ↦ deriv
        (fun u ↦ ![1, inverseSlope u, graph (inverseSlope u)] i) r) = 0
  contact_motion : ∀ r ∈ dualDomain,
    LinearIndependent ℝ
      ![![1, inverseSlope r, graph (inverseSlope r)],
        fun i ↦ deriv
          (fun u ↦ ![1, inverseSlope u, graph (inverseSlope u)] i) r]

/-- The gradient equals its last coordinate times the normalized tangent
line on the selected graph chart. -/
theorem gradient_eq_smul_normalizedTangent
    (P : MvPolynomial (Fin 3) ℝ) (p : ℝ → ℝ) {t : ℝ}
    (h₂ : gradient P ![1, t, p t] 2 ≠ 0) :
    gradient P ![1, t, p t] =
      gradient P ![1, t, p t] 2 •
        ![ConvexAnalyticArc.tangentOffset P p t,
          ConvexAnalyticArc.tangentSlope P p t, 1] := by
  funext i
  fin_cases i
  · change gradient P ![1, t, p t] 0 =
      gradient P ![1, t, p t] 2 *
        (gradient P ![1, t, p t] 0 / gradient P ![1, t, p t] 2)
    field_simp
  · change gradient P ![1, t, p t] 1 =
      gradient P ![1, t, p t] 2 *
        (gradient P ![1, t, p t] 1 / gradient P ![1, t, p t] 2)
    field_simp
  · simp

/-- A first-chart contact point with moving first affine coordinate has a
nonradial projective velocity. -/
theorem linearIndependent_firstChart_contact_motion
    (psi p : ℝ → ℝ) {r : ℝ} (hpsi : deriv psi r ≠ 0) :
    LinearIndependent ℝ
      ![![1, psi r, p (psi r)],
        fun i ↦ deriv (fun u ↦ ![1, psi u, p (psi u)] i) r] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have ha : a = 0 := by
    have hzero := congrFun hab (0 : Fin 3)
    simpa using hzero
  have hbmul : b * deriv psi r = 0 := by
    have hone := congrFun hab (1 : Fin 3)
    simpa [ha] using hone
  have hb : b = 0 := (mul_eq_zero.mp hbmul).resolve_right hpsi
  exact ⟨ha, hb⟩

/-- Construct the normalized dual graph and its moving contact point from an
ambient-open arc of a regular strictly convex algebraic oval.  The final
hypothesis only says that the *unnormalized gradient tangent* lies in the
homogeneous complex curve `D`; homogeneity proves the displayed normalized
determinant equation internally. -/
theorem exists_normalizedTangentContactArc
    {P : MvPolynomial (Fin 3) ℝ} {d : ℕ}
    (hP : P.IsHomogeneous d)
    {K : Set ConvexSupport.Point}
    (hcompact : IsCompact K) (hinterior : (interior K).Nonempty)
    (hstrict : StrictConvex ℝ K)
    (hregular : ∀ x ∈ frontier K, RegularAt P ![1, x 0, x 1])
    (hlocus : frontier K =
      {x | MvPolynomial.eval ![1, x 0, x 1] P = 0})
    (htangentSupport : ∀ {x : ConvexSupport.Point}
      {ell : Fin 3 → ℝ}, x ∈ frontier K →
      (∃ a : ℝ, gradient P ![1, x 0, x 1] = a • ell) →
      ConvexSupport.IsSupportOffset K ![ell 1, ell 2] (-ell 0))
    {W : Set ConvexSupport.Point} (hWopen : IsOpen W)
    (hWarc : (W ∩ frontier K).Nonempty)
    {D : MvPolynomial (Fin 3) ℂ} {e : ℕ}
    (hD : D.IsHomogeneous e)
    (hdetGradient : ∀ x ∈ W ∩ frontier K,
      MvPolynomial.eval
        (fun i ↦ Complex.ofReal (ProjectiveDual.gradient P
          (![1, x 0, x 1] : Fin 3 → ℝ) i)) D = 0) :
    Nonempty (NormalizedTangentContactArc P K W D) := by
  obtain ⟨U, p, hUopen, hUne, hUpre, hp, hgraph⟩ :=
    ConvexAnalyticArc.exists_connected_graph_with_gradient_two_ne_zero
      hP hcompact hinterior hstrict hregular hlocus htangentSupport
      hWopen hWarc
  have hboundary : ∀ t ∈ U, ![t, p t] ∈ frontier K := by
    intro t ht
    exact (hgraph t ht).1.2
  have hzero : ∀ t ∈ U, MvPolynomial.eval ![1, t, p t] P = 0 := by
    intro t ht
    have : (![t, p t] : ConvexSupport.Point) ∈
        {x | MvPolynomial.eval ![1, x 0, x 1] P = 0} := by
      rw [← hlocus]
      exact hboundary t ht
    exact this
  have h₂ : ∀ t ∈ U, gradient P ![1, t, p t] 2 ≠ 0 := by
    intro t ht
    exact (hgraph t ht).2
  obtain ⟨t₀, ht₀, hslope₀⟩ :=
    ConvexAnalyticArc.exists_deriv_tangentSlope_ne_zero hP hcompact
      hinterior hstrict hUopen hUne hUpre hp hboundary hzero h₂
      htangentSupport
  obtain ⟨S, R, psi, hSopen, hSne, hSpre, hRopen, hRne, hRpre,
      hpsi, hpsiSpec, hSSpec⟩ :=
    ConvexAnalyticArc.exists_connected_local_analytic_inverse hUopen
      (ConvexAnalyticArc.analyticOnNhd_tangentSlope P hp h₂) ht₀
      hslope₀
  let s : ℝ → ℝ := fun r ↦
    ConvexAnalyticArc.tangentOffset P p (psi r)
  have hs : AnalyticOnNhd ℝ s R := by
    intro r hr
    exact ((ConvexAnalyticArc.analyticOnNhd_tangentOffset P hp h₂)
      (psi r) (hpsiSpec r hr).1).comp (hpsi r hr) |>.congr
        (by simp [Function.comp_def, s])
  have hdet : ∀ r ∈ R,
      MvPolynomial.eval ![(s r : ℂ), (r : ℂ), 1] D = 0 := by
    intro r hr
    let t := psi r
    have ht : t ∈ U := (hpsiSpec r hr).1
    let g : Fin 3 → ℝ := gradient P ![1, t, p t]
    have hg₂ : g 2 ≠ 0 := h₂ t ht
    have hrSlope : ConvexAnalyticArc.tangentSlope P p t = r :=
      (hpsiSpec r hr).2.1
    have hnormalizedReal :
        (![s r, r, 1] : Fin 3 → ℝ) = (g 2)⁻¹ • g := by
      funext i
      fin_cases i
      · change gradient P ![1, t, p t] 0 /
          gradient P ![1, t, p t] 2 =
            (gradient P ![1, t, p t] 2)⁻¹ *
              gradient P ![1, t, p t] 0
        field_simp
      · change r = (gradient P ![1, t, p t] 2)⁻¹ *
          gradient P ![1, t, p t] 1
        rw [← hrSlope]
        unfold ConvexAnalyticArc.tangentSlope
        field_simp
      · simp [hg₂]
    have hnormalized :
        (![(s r : ℂ), (r : ℂ), 1] : Fin 3 → ℂ) =
          ((g 2 : ℂ)⁻¹) • (fun i ↦ (g i : ℂ)) := by
      funext i
      fin_cases i
      · have hi := congrFun hnormalizedReal (0 : Fin 3)
        have hi' : s r = (g 2)⁻¹ * g 0 := by simpa using hi
        change (s r : ℂ) = ((g 2 : ℂ)⁻¹) * (g 0 : ℂ)
        exact_mod_cast hi'
      · have hi := congrFun hnormalizedReal (1 : Fin 3)
        have hi' : r = (g 2)⁻¹ * g 1 := by simpa using hi
        change (r : ℂ) = ((g 2 : ℂ)⁻¹) * (g 1 : ℂ)
        exact_mod_cast hi'
      · have hi := congrFun hnormalizedReal (2 : Fin 3)
        have hi' : (1 : ℝ) = (g 2)⁻¹ * g 2 := by simpa using hi
        change (1 : ℂ) = ((g 2 : ℂ)⁻¹) * (g 2 : ℂ)
        exact_mod_cast hi'
    have hdetg : MvPolynomial.eval (fun i ↦ (g i : ℂ)) D = 0 := by
      simpa [g, t] using hdetGradient ![t, p t] (hgraph t ht).1
    rw [hnormalized, eval_smul_of_isHomogeneous hD, hdetg, mul_zero]
  have hincidence : ∀ r ∈ R,
      ![s r, r, 1] ⬝ᵥ ![1, psi r, p (psi r)] = 0 := by
    intro r hr
    let t := psi r
    have ht : t ∈ U := (hpsiSpec r hr).1
    have hdot := dot_gradient_eq_zero hP (hzero t ht)
    have hrSlope : ConvexAnalyticArc.tangentSlope P p t = r :=
      (hpsiSpec r hr).2.1
    have hg₂ := h₂ t ht
    have hnormalized : ConvexAnalyticArc.tangentOffset P p t +
        ConvexAnalyticArc.tangentSlope P p t * t + p t = 0 := by
      unfold ConvexAnalyticArc.tangentOffset
        ConvexAnalyticArc.tangentSlope
      field_simp [hg₂]
      have hdot' : gradient P ![1, t, p t] 0 +
          t * gradient P ![1, t, p t] 1 +
          p t * gradient P ![1, t, p t] 2 = 0 := by
        simpa [dotProduct, Fin.sum_univ_three] using hdot
      nlinarith [hdot']
    simpa [dotProduct, Fin.sum_univ_three, s, t, hrSlope] using hnormalized
  have htangent : ∀ r ∈ R,
      ![s r, r, 1] ⬝ᵥ
        (fun i ↦ deriv (fun u ↦ ![1, psi u, p (psi u)] i) r) = 0 := by
    intro r hr
    let z : ℝ → Fin 3 → ℝ := fun u ↦ ![1, psi u, p (psi u)]
    have hzAnalytic : ∀ i, AnalyticAt ℝ (fun u ↦ z u i) r := by
      intro i
      fin_cases i
      · exact analyticAt_const
      · exact hpsi r hr
      · exact (hp (psi r) (hpsiSpec r hr).1).comp (hpsi r hr)
    have hformula := AnalyticContact.deriv_eval_mvPolynomial P hzAnalytic
    have hzeroNhd : (fun u ↦ MvPolynomial.eval (z u) P) =ᶠ[𝓝 r]
        (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [hRopen.mem_nhds hr] with u hu
      exact hzero (psi u) (hpsiSpec u hu).1
    have hderivZero : deriv (fun u ↦ MvPolynomial.eval (z u) P) r = 0 := by
      rw [hzeroNhd.deriv_eq]
      simp
    rw [hformula] at hderivZero
    let t := psi r
    let dz : Fin 3 → ℝ := fun i ↦ deriv (fun u ↦ z u i) r
    have hdir : directionalDerivative P ![1, t, p t] dz = 0 := by
      simpa [z, t, dz] using hderivZero
    have htU : t ∈ U := (hpsiSpec r hr).1
    have hscale := gradient_eq_smul_normalizedTangent P p (h₂ t htU)
    have hrSlope : ConvexAnalyticArc.tangentSlope P p t = r :=
      (hpsiSpec r hr).2.1
    have hg₂ := h₂ t htU
    unfold directionalDerivative at hdir
    rw [hscale] at hdir
    simp only [dotProduct, Fin.sum_univ_three, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Nat.succ_eq_add_one, Nat.reduceAdd] at hdir ⊢
    simp only [s, t, dz, z] at *
    rw [hrSlope] at hdir
    have hfactor : gradient P ![1, psi r, p (psi r)] 2 *
        (ConvexAnalyticArc.tangentOffset P p (psi r) *
            deriv (fun _u : ℝ ↦ (1 : ℝ)) r +
          r * deriv psi r + deriv (fun u ↦ p (psi u)) r) = 0 := by
      calc
        _ = deriv (fun _u : ℝ ↦ (1 : ℝ)) r *
              (gradient P ![1, psi r, p (psi r)] 2 *
                ConvexAnalyticArc.tangentOffset P p (psi r)) +
            deriv psi r *
              (gradient P ![1, psi r, p (psi r)] 2 * r) +
            deriv (fun u ↦ p (psi u)) r *
              (gradient P ![1, psi r, p (psi r)] 2 * 1) := by ring
        _ = 0 := hdir
    have hnormalized := (mul_eq_zero.mp hfactor).resolve_left hg₂
    simpa [dotProduct, Fin.sum_univ_three, s] using hnormalized
  refine ⟨⟨U, S, R, p, psi, s, hUopen, hUne, hUpre,
    hSopen, hSne, hSpre, hRopen, hRne, hRpre, hp, hpsi, hs,
    hgraph, hpsiSpec, hSSpec, ?_, hdet, ?_, hincidence, htangent, ?_⟩⟩
  · intro r _hr
    rfl
  · intro r hr
    exact (hgraph (psi r) (hpsiSpec r hr).1).1
  · intro r hr
    exact linearIndependent_firstChart_contact_motion psi p
      (hpsiSpec r hr).2.2

end AnalyticGaussArc

end DiskRigidity.Algebraic
