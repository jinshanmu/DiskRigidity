/-
Copyright (c) 2026 Jinshan Mu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinshan Mu
-/

module

public import DiskRigidity.Algebraic.AnalyticContact
public import DiskRigidity.Algebraic.AnalyticGaussArc
public import DiskRigidity.Algebraic.ConvexLevelSupport
public import DiskRigidity.Algebraic.HermitianRealFactor
public import DiskRigidity.Algebraic.LemniscateOval
public import DiskRigidity.Algebraic.LemniscateRegular
public import DiskRigidity.Algebraic.ProjectiveCircle

/-!
# End-to-end algebraic form of Proposition 7.1

This module composes the component constructions, both Gauss divisor
identities, Hermitian hyperbolicity, generic contact count, and the final
conic calculation.  The hypotheses are stated for the explicit lemniscate
level and for first-order contact parametrizations; no irreducible primal or
dual equation and no `SmoothConvexDualPair` is supplied by the caller.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace PropositionCircle

open Matrix MvPolynomial Polynomial Set
open ProjectiveDual

/-- The real affine representative `[1:x:y]` is always nonzero. -/
theorem affinePoint_ne_zero (x : Fin 2 → ℝ) :
    LemniscateOval.affinePoint x ≠ 0 := by
  intro h
  have := congrFun h (0 : Fin 3)
  norm_num [LemniscateOval.affinePoint] at this

/-- **Proposition 7.1, with all algebraic curves constructed internally.**

The level-geometry hypotheses are the direct first-order meaning of “smooth
strictly convex full level”: tangent covectors are precisely support lines.
The dual jet hypotheses say that `[s(t):t:1]` is a first-order
parametrization of the tangent-line arc and records its nonstationary contact
motion.  These inputs mention only the explicit level, determinant, and
parametrized points/lines; `F`, `Q`, their divisor identities, and the generic
degree conclusion are all produced in the proof. -/
theorem boundary_is_circle_of_full_level_and_contact_arcs
    {n : Type*} [Fintype n] [DecidableEq n]
    (U V : ℂ[X]) (hU : U ≠ 0)
    (hdeg : V.natDegree < U.natDegree)
    (H J : Matrix n n ℂ) (hH : H.IsHermitian) (hJ : J.IsHermitian)
    (K : Set (Fin 2 → ℝ))
    (hcompact : IsCompact K) (hinterior : (interior K).Nonempty)
    (hconnected : IsConnected (frontier K))
    (hfullLevel : ∀ x : Fin 2 → ℝ,
      MvPolynomial.eval (LemniscateOval.complexAffinePoint x)
        (Lemniscate.primalOrderProjectiveLevelPolynomial U V) = 0 ↔
          x ∈ frontier K)
    (hlevelRegular : ∀ x ∈ frontier K,
      RegularAt (Lemniscate.primalOrderProjectiveLevelPolynomial U V)
        (LemniscateOval.complexAffinePoint x))
    (hlevelTangentSupport : ∀ {x : Fin 2 → ℝ} {ell : Fin 3 → ℝ},
      x ∈ frontier K →
      (∃ a : ℝ, gradient (LemniscateOval.realLevelPolynomial U V)
        (LemniscateOval.affinePoint x) = a • ell) →
      ConvexSupport.IsSupportOffset K ![ell 1, ell 2] (-ell 0))
    (hsupportLevelTangent : ∀ {normal : Fin 2 → ℝ} {r : ℝ},
      ConvexSupport.IsSupportOffset K normal r → normal ≠ 0 →
      ∃ x ∈ frontier K, ∃ a : ℝ, a ≠ 0 ∧
        gradient (LemniscateOval.realLevelPolynomial U V)
          (LemniscateOval.affinePoint x) =
            a • ![-r, normal 0, normal 1])
    (T : Set ℝ) (hTopen : IsOpen T) (hTnonempty : T.Nonempty)
    (hTpreconnected : IsPreconnected T)
    (s : ℝ → ℝ) (hs : AnalyticOnNhd ℝ s T)
    (xDual : ℝ → Fin 2 → ℝ)
    (hxDual : ∀ i, AnalyticOnNhd ℝ (fun t ↦ xDual t i) T)
    (hdualBoundary : ∀ t ∈ T, xDual t ∈ frontier K)
    (hdeterminant : ∀ t ∈ T,
      MvPolynomial.eval ![(s t : ℂ), (t : ℂ), 1]
        (HermitianProjective.determinantPolynomial H J) = 0)
    (hincidence : ∀ t ∈ T,
      ![s t, t, 1] ⬝ᵥ LemniscateOval.affinePoint (xDual t) = 0)
    (hlineTangent : ∀ t ∈ T,
      ![s t, t, 1] ⬝ᵥ
        (fun i ↦ deriv
          (fun u ↦ LemniscateOval.affinePoint (xDual u) i) t) = 0)
    (hdualMotion : ∀ t ∈ T,
      LinearIndependent ℝ
        ![LemniscateOval.affinePoint (xDual t),
          fun i ↦ deriv
            (fun u ↦ LemniscateOval.affinePoint (xDual u) i) t])
    (A : Set ℝ) (hAopen : IsOpen A) (hAnonempty : A.Nonempty)
    (p ρ : ℝ → ℝ)
    (hρ : ∀ t ∈ A, ρ t ∈ T)
    (hprimalBoundary : ∀ t ∈ A, ![t, p t] ∈ frontier K)
    (hprimalLevelContact : ∀ t ∈ A, ∃ a : ℝ,
      gradient (LemniscateOval.realLevelPolynomial U V) ![1, t, p t] =
        a • ![s (ρ t), ρ t, 1]) :
    ∃ q : Conic.Form,
      0 < q.radiusSq ∧ frontier K =
        {x | (x 0 - q.centerX) ^ 2 + (x 1 - q.centerY) ^ 2 = q.radiusSq} := by
  obtain ⟨F, d, hFirr, hFcomplexIrr, hFhom, hd, hFrealDiv,
      hFcomplexDiv, hFlocus, hFnoInfinity, hFregular⟩ :=
    LemniscateOval.exists_primal_oval_component U V hU hdeg K hconnected
      hfullLevel hlevelRegular
  obtain ⟨Q, m, hQirr, hQcomplexIrr, hQhermitian, hQhom, hm, _he,
      hQzero, tregular, htregular, hQregular⟩ :=
    HermitianRealFactor.exists_dual_factor_on_open_analytic_graph
      H J hH hJ T hTopen hTnonempty hTpreconnected s hs hdeterminant
  have hrealLevelRegular : ∀ x ∈ frontier K,
      RegularAt (LemniscateOval.realLevelPolynomial U V)
        (LemniscateOval.affinePoint x) := by
    intro x hx
    exact LemniscateOval.regularAt_realLevelPolynomial_of_complex U V
      (hlevelRegular x hx)
  have hzAnalytic : ∀ i, AnalyticOnNhd ℝ
      (fun t ↦ LemniscateOval.affinePoint (xDual t) i) T := by
    intro i
    fin_cases i
    · simpa [LemniscateOval.affinePoint] using
        (analyticOnNhd_const : AnalyticOnNhd ℝ (fun _ : ℝ ↦ (1 : ℝ)) T)
    · simpa [LemniscateOval.affinePoint] using hxDual (0 : Fin 2)
    · simpa [LemniscateOval.affinePoint] using hxDual (1 : Fin 2)
  have hderivativeIncidence : ∀ t ∈ T,
      ![deriv s t, 1, 0] ⬝ᵥ LemniscateOval.affinePoint (xDual t) = 0 := by
    intro t ht
    exact AnalyticContact.derivative_incidence_of_analytic_tangent_graph
      hTopen s hs (fun u ↦ LemniscateOval.affinePoint (xDual u))
      hzAnalytic hincidence ht (hlineTangent t ht)
  have hdualContact : ∀ t ∈ T, ∃ a : ℝ,
      gradient Q ![s t, t, 1] =
        a • LemniscateOval.affinePoint (xDual t) := by
    intro t ht
    apply gradient_dual_eq_smul_contact hQhom
      (affinePoint_ne_zero (xDual t)) (hQzero t ht)
      (AnalyticContact.isTangentVector_of_analytic_graph_zero
        Q hTopen s hs hQzero ht)
      (AnalyticContact.linearIndependent_affine_graph_frame
        (s t) t (deriv s t)) (hincidence t ht)
      (hderivativeIncidence t ht)
  have hbidual : Q ∣ GaussPullback.gradientPullback F Q := by
    apply AnalyticContact.gradientPullback_dvd_of_contact_arc
      hFhom hQhom hQirr hm _he hTopen hTnonempty s
      (fun t ↦ LemniscateOval.affinePoint (xDual t)) hQzero
    · intro t ht
      have hxt := hdualBoundary t ht
      have : xDual t ∈
          {x | MvPolynomial.eval (LemniscateOval.affinePoint x) F = 0} := by
        rwa [← hFlocus]
      exact this
    · exact hdualContact
  have heF : MvPolynomial.eval ![0, 0, 1] F ≠ 0 := by
    intro hzero
    have hz : (![0, 0, 1] : Fin 3 → ℝ) ≠ 0 := by
      intro hz
      have hone : (1 : ℝ) = 0 := by
        simpa using congrFun hz (2 : Fin 3)
      exact one_ne_zero hone
    exact hFnoInfinity hz hzero rfl
  have hprimalContact : ∀ t ∈ A, ∃ a : ℝ,
      gradient F ![1, t, p t] = a • ![s (ρ t), ρ t, 1] := by
    intro t ht
    let x : Fin 2 → ℝ := ![t, p t]
    have hx : x ∈ frontier K := hprimalBoundary t ht
    have hFzero : MvPolynomial.eval ![1, t, p t] F = 0 := by
      have : x ∈
          {y | MvPolynomial.eval (LemniscateOval.affinePoint y) F = 0} := by
        rwa [← hFlocus]
      exact this
    obtain ⟨c, hc, hgradient⟩ :=
      LemniscateOval.exists_ne_zero_gradient_scale_of_factor hFrealDiv
        hFzero (hrealLevelRegular x hx)
    obtain ⟨a, ha⟩ := hprimalLevelContact t ht
    refine ⟨a / c, ?_⟩
    funext i
    have hi := congrFun (hgradient.symm.trans ha) i
    change c * gradient F ![1, t, p t] i =
      a * ![s (ρ t), ρ t, 1] i at hi
    change gradient F ![1, t, p t] i =
      (a / c) * ![s (ρ t), ρ t, 1] i
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hc).2
    rw [mul_comm]
    exact hi
  have hprimalGauss : F ∣ GaussPullback.gradientPullback Q F := by
    apply AnalyticContact.gradientPullback_dvd_of_primal_contact_second_chart
      hFhom hQhom hFirr hd heF hAopen hAnonempty p
      (fun t ↦ ![s (ρ t), ρ t, 1])
    · intro t ht
      let x : Fin 2 → ℝ := ![t, p t]
      have hx : x ∈ frontier K := hprimalBoundary t ht
      have : x ∈
          {y | MvPolynomial.eval (LemniscateOval.affinePoint y) F = 0} := by
        rwa [← hFlocus]
      exact this
    · intro t ht
      exact hQzero (ρ t) (hρ t ht)
    · exact hprimalContact
  have hpair : ProjectiveCircle.SmoothConvexDualPair F Q K := by
    apply ProjectiveCircle.smoothConvexDualPair_of_level_geometry
      hFhom hQhom hm hcompact hinterior hFregular hFnoInfinity hFlocus
      hFrealDiv hrealLevelRegular hlevelTangentSupport hsupportLevelTangent
      hprimalGauss
  obtain ⟨k, hcross⟩ :=
    AnalyticContact.exists_gaussCross_ne_zero_of_analytic_graph_contact
      Q hTopen s hs (fun t ↦ LemniscateOval.affinePoint (xDual t))
      hzAnalytic (fun t _ ↦ by simp [LemniscateOval.affinePoint]) hQzero
      hdualContact htregular hQregular (hdualMotion tregular htregular)
  have hcircle :=
    ProjectiveCircle.projective_circle_conclusion_of_unramified_contact
    U V hU hdeg H J hH hJ hFhom hQhom hFirr hQirr hm hQcomplexIrr
    hpair hFcomplexDiv hQhermitian hbidual k (s tregular) tregular
    (hQzero tregular htregular) hcross
  exact ⟨ConicEnvelope.envelopeForm Q,
    ProjectiveCircle.radiusSq_pos_of_compact_interior_boundary_circle
      (ConicEnvelope.envelopeForm Q) hcompact hinterior hcircle,
    hcircle⟩

/-- **Proposition 7.1 with the analytic tangent/contact arcs constructed
internally.**  The only local input is an ambient-open boundary arc on which
the unnormalized level gradient lies in the Hermitian determinant.  Strict
convexity, regularity, and the analytic inverse-function theorem construct
the normalized dual graph, its moving contact point, and the primal graph
used for both Gauss divisor identities. -/
theorem boundary_is_circle_of_full_level_and_open_tangent_arc
    {n : Type*} [Fintype n] [DecidableEq n]
    (U V : ℂ[X]) (hU : U ≠ 0)
    (hdeg : V.natDegree < U.natDegree)
    (H J : Matrix n n ℂ) (hH : H.IsHermitian) (hJ : J.IsHermitian)
    (K : Set (Fin 2 → ℝ))
    (hcompact : IsCompact K) (hinterior : (interior K).Nonempty)
    (hstrict : StrictConvex ℝ K)
    (hconnected : IsConnected (frontier K))
    (hfullLevel : ∀ x : Fin 2 → ℝ,
      MvPolynomial.eval (LemniscateOval.complexAffinePoint x)
        (Lemniscate.primalOrderProjectiveLevelPolynomial U V) = 0 ↔
          x ∈ frontier K)
    (hlevelRegular : ∀ x ∈ frontier K,
      RegularAt (Lemniscate.primalOrderProjectiveLevelPolynomial U V)
        (LemniscateOval.complexAffinePoint x))
    (hlevelTangentSupport : ∀ {x : Fin 2 → ℝ} {ell : Fin 3 → ℝ},
      x ∈ frontier K →
      (∃ a : ℝ, gradient (LemniscateOval.realLevelPolynomial U V)
        (LemniscateOval.affinePoint x) = a • ell) →
      ConvexSupport.IsSupportOffset K ![ell 1, ell 2] (-ell 0))
    (hsupportLevelTangent : ∀ {normal : Fin 2 → ℝ} {r : ℝ},
      ConvexSupport.IsSupportOffset K normal r → normal ≠ 0 →
      ∃ x ∈ frontier K, ∃ a : ℝ, a ≠ 0 ∧
        gradient (LemniscateOval.realLevelPolynomial U V)
          (LemniscateOval.affinePoint x) =
            a • ![-r, normal 0, normal 1])
    (W : Set (Fin 2 → ℝ)) (hWopen : IsOpen W)
    (hWarc : (W ∩ frontier K).Nonempty)
    (hdetGradient : ∀ x ∈ W ∩ frontier K,
      MvPolynomial.eval
        (fun i ↦ Complex.ofReal
          (gradient (LemniscateOval.realLevelPolynomial U V)
            (LemniscateOval.affinePoint x) i))
        (HermitianProjective.determinantPolynomial H J) = 0) :
    ∃ q : Conic.Form,
      0 < q.radiusSq ∧ frontier K =
        {x | (x 0 - q.centerX) ^ 2 + (x 1 - q.centerY) ^ 2 = q.radiusSq} := by
  let L := LemniscateOval.realLevelPolynomial U V
  have hLhom : L.IsHomogeneous (2 * U.natDegree) :=
    LemniscateOval.realLevelPolynomial_isHomogeneous U V hdeg.le
  have hLregular : ∀ x ∈ frontier K,
      RegularAt L ![1, x 0, x 1] := by
    intro x hx
    exact LemniscateOval.regularAt_realLevelPolynomial_of_complex U V
      (hlevelRegular x hx)
  have hLlocus : frontier K =
      {x | MvPolynomial.eval ![1, x 0, x 1] L = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [← hfullLevel x, ← LemniscateOval.map_realLevelPolynomial U V]
    change MvPolynomial.eval
        (fun i ↦ (LemniscateOval.affinePoint x i : ℂ))
          (MvPolynomial.map (algebraMap ℝ ℂ) L) = 0 ↔
        MvPolynomial.eval (LemniscateOval.affinePoint x) L = 0
    rw [RealComponent.eval_map_real]
    exact Complex.ofReal_eq_zero
  obtain ⟨arc⟩ := AnalyticGaussArc.exists_normalizedTangentContactArc
    hLhom hcompact hinterior hstrict hLregular hLlocus
      hlevelTangentSupport hWopen hWarc
      (HermitianProjective.determinantPolynomial_isHomogeneous H J)
      hdetGradient
  refine boundary_is_circle_of_full_level_and_contact_arcs U V hU hdeg
    H J hH hJ K hcompact hinterior hconnected hfullLevel hlevelRegular
    hlevelTangentSupport hsupportLevelTangent
    arc.dualDomain arc.dualDomain_open arc.dualDomain_nonempty
    arc.dualDomain_preconnected arc.dualOffset arc.dualOffset_analytic
    (fun r ↦ ![arc.inverseSlope r, arc.graph (arc.inverseSlope r)])
    ?_ ?_ ?_ ?_ ?_ ?_
    arc.primalDomain arc.primalDomain_open arc.primalDomain_nonempty
    arc.graph (fun t ↦ ConvexAnalyticArc.tangentSlope L arc.graph t)
    ?_ ?_ ?_
  · intro i
    fin_cases i
    · simpa using arc.inverseSlope_analytic
    · intro r hr
      exact (arc.graph_analytic (arc.inverseSlope r)
        (arc.inverseSlope_spec r hr).1).comp
          (arc.inverseSlope_analytic r hr)
  · intro r hr
    exact (arc.contact_boundary r hr).2
  · exact arc.determinant_zero
  · intro r hr
    simpa [LemniscateOval.affinePoint] using arc.incidence r hr
  · intro r hr
    simpa [LemniscateOval.affinePoint] using arc.tangent_contact r hr
  · intro r hr
    simpa [LemniscateOval.affinePoint] using arc.contact_motion r hr
  · intro t ht
    exact (arc.primalDomain_spec t ht).2.1
  · intro t ht
    exact (arc.graph_mem t (arc.primalDomain_spec t ht).1).1.2
  · intro t ht
    let r := ConvexAnalyticArc.tangentSlope L arc.graph t
    have htGraph := (arc.primalDomain_spec t ht).1
    have hr : r ∈ arc.dualDomain :=
      (arc.primalDomain_spec t ht).2.1
    have hinverse : arc.inverseSlope r = t :=
      (arc.primalDomain_spec t ht).2.2
    have hsOffset := arc.dualOffset_eq r hr
    rw [hinverse] at hsOffset
    refine ⟨gradient L ![1, t, arc.graph t] 2, ?_⟩
    rw [AnalyticGaussArc.gradient_eq_smul_normalizedTangent L arc.graph
      (arc.graph_mem t htGraph).2]
    rw [hsOffset]
    simp

/-- **Proposition 7.1 from a full regular strictly convex level and one
determinantal tangent arc.**  The tangent/support equivalence is now a
theorem, not an input: it follows from Hahn--Banach and the analytic implicit
function theorem for the regular level. -/
theorem boundary_is_circle_of_full_regular_strictly_convex_level
    {n : Type*} [Fintype n] [DecidableEq n]
    (U V : ℂ[X]) (hU : U ≠ 0)
    (hdeg : V.natDegree < U.natDegree)
    (H J : Matrix n n ℂ) (hH : H.IsHermitian) (hJ : J.IsHermitian)
    (K : Set (Fin 2 → ℝ))
    (hcompact : IsCompact K) (hinterior : (interior K).Nonempty)
    (hstrict : StrictConvex ℝ K)
    (hconnected : IsConnected (frontier K))
    (hfullLevel : ∀ x : Fin 2 → ℝ,
      MvPolynomial.eval (LemniscateOval.complexAffinePoint x)
        (Lemniscate.primalOrderProjectiveLevelPolynomial U V) = 0 ↔
          x ∈ frontier K)
    (hlevelRegular : ∀ x ∈ frontier K,
      RegularAt (Lemniscate.primalOrderProjectiveLevelPolynomial U V)
        (LemniscateOval.complexAffinePoint x))
    (W : Set (Fin 2 → ℝ)) (hWopen : IsOpen W)
    (hWarc : (W ∩ frontier K).Nonempty)
    (hdetGradient : ∀ x ∈ W ∩ frontier K,
      MvPolynomial.eval
        (fun i ↦ Complex.ofReal
          (gradient (LemniscateOval.realLevelPolynomial U V)
            (LemniscateOval.affinePoint x) i))
        (HermitianProjective.determinantPolynomial H J) = 0) :
    ∃ q : Conic.Form,
      0 < q.radiusSq ∧ frontier K =
        {x | (x 0 - q.centerX) ^ 2 + (x 1 - q.centerY) ^ 2 = q.radiusSq} := by
  let L := LemniscateOval.realLevelPolynomial U V
  have hLhom : L.IsHomogeneous (2 * U.natDegree) :=
    LemniscateOval.realLevelPolynomial_isHomogeneous U V hdeg.le
  have hLregular : ∀ x ∈ frontier K,
      RegularAt L ![1, x 0, x 1] := by
    intro x hx
    exact LemniscateOval.regularAt_realLevelPolynomial_of_complex U V
      (hlevelRegular x hx)
  have hLlocus : frontier K =
      {x | MvPolynomial.eval ![1, x 0, x 1] L = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [← hfullLevel x, ← LemniscateOval.map_realLevelPolynomial U V]
    change MvPolynomial.eval
        (fun i ↦ (LemniscateOval.affinePoint x i : ℂ))
          (MvPolynomial.map (algebraMap ℝ ℂ) L) = 0 ↔
        MvPolynomial.eval (LemniscateOval.affinePoint x) L = 0
    rw [RealComponent.eval_map_real]
    exact Complex.ofReal_eq_zero
  have htangentSupport : ∀ {x : Fin 2 → ℝ} {ell : Fin 3 → ℝ},
      x ∈ frontier K →
      (∃ a : ℝ, gradient L ![1, x 0, x 1] = a • ell) →
      ConvexSupport.IsSupportOffset K ![ell 1, ell 2] (-ell 0) := by
    exact ConvexLevelSupport.tangent_is_support_of_regular_convex_level
      hLhom hstrict.convex hcompact hinterior hLlocus hLregular
  have hsupportTangent : ∀ {normal : Fin 2 → ℝ} {r : ℝ},
      ConvexSupport.IsSupportOffset K normal r → normal ≠ 0 →
      ∃ x ∈ frontier K, ∃ a : ℝ, a ≠ 0 ∧
        gradient L ![1, x 0, x 1] =
          a • ![-r, normal 0, normal 1] := by
    exact ConvexLevelSupport.support_is_tangent_of_regular_convex_level
      hLhom hcompact hLlocus hLregular
  exact boundary_is_circle_of_full_level_and_open_tangent_arc
    U V hU hdeg H J hH hJ K hcompact hinterior hstrict hconnected
    hfullLevel hlevelRegular htangentSupport hsupportTangent
    W hWopen hWarc hdetGradient

/-- Support-line form of the preceding end-to-end theorem.  It matches the
Hermitian numerical-range pencil directly: every support line is assumed to
lie in the determinant, and the regular convex-level theorem identifies the
gradient tangent with such a support line.  No open set or analytic arc is
supplied by the caller. -/
theorem boundary_is_circle_of_full_regular_strictly_convex_level_and_support_determinant
    {n : Type*} [Fintype n] [DecidableEq n]
    (U V : ℂ[X]) (hU : U ≠ 0)
    (hdeg : V.natDegree < U.natDegree)
    (H J : Matrix n n ℂ) (hH : H.IsHermitian) (hJ : J.IsHermitian)
    (K : Set (Fin 2 → ℝ))
    (hcompact : IsCompact K) (hinterior : (interior K).Nonempty)
    (hstrict : StrictConvex ℝ K)
    (hconnected : IsConnected (frontier K))
    (hfullLevel : ∀ x : Fin 2 → ℝ,
      MvPolynomial.eval (LemniscateOval.complexAffinePoint x)
        (Lemniscate.primalOrderProjectiveLevelPolynomial U V) = 0 ↔
          x ∈ frontier K)
    (hlevelRegular : ∀ x ∈ frontier K,
      RegularAt (Lemniscate.primalOrderProjectiveLevelPolynomial U V)
        (LemniscateOval.complexAffinePoint x))
    (hdetSupport : ∀ {normal : Fin 2 → ℝ} {r : ℝ},
      ConvexSupport.IsSupportOffset K normal r →
      MvPolynomial.eval
        ![-(r : ℂ), (normal 0 : ℂ), (normal 1 : ℂ)]
        (HermitianProjective.determinantPolynomial H J) = 0) :
    ∃ q : Conic.Form,
      0 < q.radiusSq ∧ frontier K =
        {x | (x 0 - q.centerX) ^ 2 + (x 1 - q.centerY) ^ 2 = q.radiusSq} := by
  let L := LemniscateOval.realLevelPolynomial U V
  have hLhom : L.IsHomogeneous (2 * U.natDegree) :=
    LemniscateOval.realLevelPolynomial_isHomogeneous U V hdeg.le
  have hLregular : ∀ x ∈ frontier K,
      RegularAt L ![1, x 0, x 1] := by
    intro x hx
    exact LemniscateOval.regularAt_realLevelPolynomial_of_complex U V
      (hlevelRegular x hx)
  have hLlocus : frontier K =
      {x | MvPolynomial.eval ![1, x 0, x 1] L = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [← hfullLevel x, ← LemniscateOval.map_realLevelPolynomial U V]
    change MvPolynomial.eval
        (fun i ↦ (LemniscateOval.affinePoint x i : ℂ))
          (MvPolynomial.map (algebraMap ℝ ℂ) L) = 0 ↔
        MvPolynomial.eval (LemniscateOval.affinePoint x) L = 0
    rw [RealComponent.eval_map_real]
    exact Complex.ofReal_eq_zero
  have htangentSupport : ∀ {x : Fin 2 → ℝ} {ell : Fin 3 → ℝ},
      x ∈ frontier K →
      (∃ a : ℝ, gradient L ![1, x 0, x 1] = a • ell) →
      ConvexSupport.IsSupportOffset K ![ell 1, ell 2] (-ell 0) := by
    exact ConvexLevelSupport.tangent_is_support_of_regular_convex_level
      hLhom hstrict.convex hcompact hinterior hLlocus hLregular
  have hdetGradient : ∀ x ∈ (Set.univ : Set (Fin 2 → ℝ)) ∩ frontier K,
      MvPolynomial.eval
        (fun i ↦ Complex.ofReal (gradient L ![1, x 0, x 1] i))
        (HermitianProjective.determinantPolynomial H J) = 0 := by
    intro x hx
    let g : Fin 3 → ℝ := gradient L ![1, x 0, x 1]
    have hs : ConvexSupport.IsSupportOffset K ![g 1, g 2] (-g 0) := by
      apply htangentSupport hx.2
      exact ⟨1, by simp [g]⟩
    have hd := hdetSupport hs
    have hvec : (fun i ↦ Complex.ofReal (g i)) =
        (![(g 0 : ℂ), (g 1 : ℂ), (g 2 : ℂ)] : Fin 3 → ℂ) := by
      funext i
      fin_cases i <;> rfl
    rw [hvec]
    simpa using hd
  apply boundary_is_circle_of_full_regular_strictly_convex_level
    U V hU hdeg H J hH hJ K hcompact hinterior hstrict hconnected
    hfullLevel hlevelRegular Set.univ isOpen_univ
  · simpa using hconnected.nonempty
  · exact hdetGradient

/-- **Assumption-free algebraic regularity form of Proposition 7.1.**

The caller supplies the reduced rational data and the noncritical-level fact
`U'V - UV' ≠ 0` proved in the analytic full-level proposition.  Coprimality
and the explicit differential calculation in `LemniscateRegular` construct
the projective `RegularAt` hypothesis internally.  Thus no algebraic
regularity assumption remains in this end-to-end circle theorem. -/
theorem boundary_is_circle_of_full_strictly_convex_level_and_support_determinant
    {n : Type*} [Fintype n] [DecidableEq n]
    (U V : ℂ[X]) (hcoprime : IsCoprime U V) (hU : U ≠ 0)
    (hdeg : V.natDegree < U.natDegree)
    (H J : Matrix n n ℂ) (hH : H.IsHermitian) (hJ : J.IsHermitian)
    (K : Set (Fin 2 → ℝ))
    (hcompact : IsCompact K) (hinterior : (interior K).Nonempty)
    (hstrict : StrictConvex ℝ K)
    (hconnected : IsConnected (frontier K))
    (hfullLevel : ∀ x : Fin 2 → ℝ,
      MvPolynomial.eval (LemniscateOval.complexAffinePoint x)
        (Lemniscate.primalOrderProjectiveLevelPolynomial U V) = 0 ↔
          x ∈ frontier K)
    (hwronskian : ∀ x ∈ frontier K,
      (U.derivative * V - U * V.derivative).eval
        ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I) ≠ 0)
    (hdetSupport : ∀ {normal : Fin 2 → ℝ} {r : ℝ},
      ConvexSupport.IsSupportOffset K normal r →
      MvPolynomial.eval
        ![-(r : ℂ), (normal 0 : ℂ), (normal 1 : ℂ)]
        (HermitianProjective.determinantPolynomial H J) = 0) :
    ∃ q : Conic.Form,
      0 < q.radiusSq ∧ frontier K =
        {x | (x 0 - q.centerX) ^ 2 + (x 1 - q.centerY) ^ 2 = q.radiusSq} := by
  have hnormLevel : ∀ x ∈ frontier K,
      ‖U.eval ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I)‖ =
        ‖V.eval ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I)‖ := by
    intro x hx
    have hzero := (hfullLevel x).2 hx
    have hpoint : LemniscateOval.complexAffinePoint x =
        ![(1 : ℂ), (x 0 : ℂ), (x 1 : ℂ)] := by
      funext i
      fin_cases i <;> rfl
    rw [hpoint] at hzero
    exact
      (Lemniscate.eval_primalOrderProjectiveLevelPolynomial_affine_eq_zero_iff
        U V (x 0) (x 1)).1 hzero
  have hlevelRegular : ∀ x ∈ frontier K,
      RegularAt (Lemniscate.primalOrderProjectiveLevelPolynomial U V)
        (LemniscateOval.complexAffinePoint x) :=
    LemniscateRegular.regularAt_primalOrderProjectiveLevelPolynomial_on_set
      U V hcoprime (frontier K) hnormLevel hwronskian
  exact
    boundary_is_circle_of_full_regular_strictly_convex_level_and_support_determinant
      U V hU hdeg H J hH hJ K hcompact hinterior hstrict hconnected
      hfullLevel hlevelRegular hdetSupport

/-- Quotient-derivative form of the preceding theorem.  This matches the
statement `f' ≠ 0` produced by the analytic full-level argument without
requiring callers to rewrite the derivative as its polynomial numerator. -/
theorem boundary_is_circle_of_full_strictly_convex_level_and_support_determinant_of_deriv_ne_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (U V : ℂ[X]) (hcoprime : IsCoprime U V) (hU : U ≠ 0)
    (hdeg : V.natDegree < U.natDegree)
    (H J : Matrix n n ℂ) (hH : H.IsHermitian) (hJ : J.IsHermitian)
    (K : Set (Fin 2 → ℝ))
    (hcompact : IsCompact K) (hinterior : (interior K).Nonempty)
    (hstrict : StrictConvex ℝ K)
    (hconnected : IsConnected (frontier K))
    (hfullLevel : ∀ x : Fin 2 → ℝ,
      MvPolynomial.eval (LemniscateOval.complexAffinePoint x)
        (Lemniscate.primalOrderProjectiveLevelPolynomial U V) = 0 ↔
          x ∈ frontier K)
    (hderiv : ∀ x ∈ frontier K,
      deriv (fun z ↦ U.eval z / V.eval z)
        ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I) ≠ 0)
    (hdetSupport : ∀ {normal : Fin 2 → ℝ} {r : ℝ},
      ConvexSupport.IsSupportOffset K normal r →
      MvPolynomial.eval
        ![-(r : ℂ), (normal 0 : ℂ), (normal 1 : ℂ)]
        (HermitianProjective.determinantPolynomial H J) = 0) :
    ∃ q : Conic.Form,
      0 < q.radiusSq ∧ frontier K =
        {x | (x 0 - q.centerX) ^ 2 + (x 1 - q.centerY) ^ 2 = q.radiusSq} := by
  have hnormLevel : ∀ x ∈ frontier K,
      ‖U.eval ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I)‖ =
        ‖V.eval ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I)‖ := by
    intro x hx
    have hzero := (hfullLevel x).2 hx
    have hpoint : LemniscateOval.complexAffinePoint x =
        ![(1 : ℂ), (x 0 : ℂ), (x 1 : ℂ)] := by
      funext i
      fin_cases i <;> rfl
    rw [hpoint] at hzero
    exact
      (Lemniscate.eval_primalOrderProjectiveLevelPolynomial_affine_eq_zero_iff
        U V (x 0) (x 1)).1 hzero
  have hwronskian : ∀ x ∈ frontier K,
      (U.derivative * V - U * V.derivative).eval
        ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I) ≠ 0 := by
    intro x hx
    exact LemniscateRegular.wronskian_eval_ne_zero_of_deriv_quotient_ne_zero
      U V hcoprime _ (hnormLevel x hx) (hderiv x hx)
  exact boundary_is_circle_of_full_strictly_convex_level_and_support_determinant
    U V hcoprime hU hdeg H J hH hJ K hcompact hinterior hstrict hconnected
    hfullLevel hwronskian hdetSupport

end PropositionCircle

end DiskRigidity.Algebraic
