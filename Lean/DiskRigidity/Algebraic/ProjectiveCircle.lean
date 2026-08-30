/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.Conic
public import DiskRigidity.Algebraic.ContactDegree
public import DiskRigidity.Algebraic.ConvexSupport
public import DiskRigidity.Algebraic.ConicEnvelope
public import DiskRigidity.Algebraic.GaussPullback
public import DiskRigidity.Algebraic.HermitianProjective
public import DiskRigidity.Algebraic.Lemniscate
public import DiskRigidity.Algebraic.PlaneGauss

/-!
# Generic projective contact count and the circle conclusion

This file composes the algebraic genericity, bidual contact recovery, and
convex support-line count from Proposition 7.1.  The geometric interface
`SmoothConvexDualPair` records exactly that the real projective curve is a
smooth convex oval and that `Q` is its dual equation; it does not contain a
degree or conic conclusion.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace ProjectiveCircle

open Matrix MvPolynomial Polynomial Set
open ProjectiveDual GenericSpecialization PlaneCurveSpecialization
open ProjectiveHomogenization

/-- The geometric real-locus facts established before the generic-direction
paragraph of Proposition 7.1. -/
structure SmoothConvexDualPair
    (F Q : MvPolynomial (Fin 3) ℝ) (K : Set ConvexSupport.Point) : Prop where
  isCompact : IsCompact K
  interior_nonempty : (interior K).Nonempty
  real_regular : ∀ {z : Fin 3 → ℝ}, z ≠ 0 →
    MvPolynomial.eval z F = 0 → RegularAt F z
  no_real_infinity : ∀ {z : Fin 3 → ℝ}, z ≠ 0 →
    MvPolynomial.eval z F = 0 → z 0 ≠ 0
  real_affine_locus : frontier K =
    {x | MvPolynomial.eval ![1, x 0, x 1] F = 0}
  tangent_is_support : ∀ {z ell : Fin 3 → ℝ},
    RegularAt F z → z 0 ≠ 0 →
    (∃ a : ℝ, gradient F z = a • ell) →
    ConvexSupport.IsSupportOffset K ![ell 1, ell 2] (-ell 0)
  support_is_dual : ∀ {n : ConvexSupport.Point} {r : ℝ},
    ConvexSupport.IsSupportOffset K n r →
    MvPolynomial.eval ![-r, n 0, n 1] Q = 0

/-- Construct the real oval interface from separate affine smooth-boundary
facts and the *proved* primal Gauss divisor identity `F ∣ Q(∇F)`.

The two geometric hypotheses say exactly that tangents to the smooth convex
boundary are supports and, conversely, that every nonzero support line is a
tangent at a boundary point.  In particular `support_is_dual` is not assumed:
it follows algebraically from `hprimalGauss`. -/
theorem smoothConvexDualPair_of_affine_geometry
    {F Q : MvPolynomial (Fin 3) ℝ} {K : Set ConvexSupport.Point}
    {d m : ℕ}
    (hF : F.IsHomogeneous d) (hQ : Q.IsHomogeneous m) (hm : m ≠ 0)
    (hcompact : IsCompact K) (hinterior : (interior K).Nonempty)
    (hregular : ∀ {z : Fin 3 → ℝ}, z ≠ 0 →
      MvPolynomial.eval z F = 0 → RegularAt F z)
    (hnoInfinity : ∀ {z : Fin 3 → ℝ}, z ≠ 0 →
      MvPolynomial.eval z F = 0 → z 0 ≠ 0)
    (hlocus : frontier K =
      {x | MvPolynomial.eval ![1, x 0, x 1] F = 0})
    (haffineTangentSupport : ∀ {x : ConvexSupport.Point}
      {ell : Fin 3 → ℝ}, x ∈ frontier K →
      (∃ a : ℝ, gradient F ![1, x 0, x 1] = a • ell) →
      ConvexSupport.IsSupportOffset K ![ell 1, ell 2] (-ell 0))
    (hsupportTangent : ∀ {n : ConvexSupport.Point} {r : ℝ},
      ConvexSupport.IsSupportOffset K n r → n ≠ 0 →
      ∃ x ∈ frontier K, ∃ a : ℝ, a ≠ 0 ∧
        gradient F ![1, x 0, x 1] = a • ![-r, n 0, n 1])
    (hprimalGauss : F ∣ GaussPullback.gradientPullback Q F) :
    SmoothConvexDualPair F Q K := by
  refine ⟨hcompact, hinterior, hregular, hnoInfinity, hlocus, ?_, ?_⟩
  · intro z ell hzreg hz0 hparallel
    let x : ConvexSupport.Point := ![z 1 / z 0, z 2 / z 0]
    have hnormalize : ![1, x 0, x 1] = (z 0)⁻¹ • z := by
      funext i
      fin_cases i
      · simp [hz0]
      · simpa [x, div_eq_mul_inv] using (mul_comm (z 1) (z 0)⁻¹)
      · simpa [x, div_eq_mul_inv] using (mul_comm (z 2) (z 0)⁻¹)
    have hFnorm : MvPolynomial.eval ![1, x 0, x 1] F = 0 := by
      rw [hnormalize, eval_smul_of_isHomogeneous hF, hzreg.1.2, mul_zero]
    have hx : x ∈ frontier K := by
      rw [hlocus]
      exact hFnorm
    apply haffineTangentSupport hx
    obtain ⟨a, ha⟩ := hparallel
    refine ⟨(z 0)⁻¹ ^ (d - 1) * a, ?_⟩
    rw [hnormalize, gradient_smul_of_isHomogeneous hF, ha, smul_smul]
  · intro n r hsupport
    by_cases hn : n = 0
    · subst n
      have hr : r = 0 := by
        rcases hsupport with hupper | hlower
        · obtain ⟨x, _, hx, _⟩ := hupper
          simpa [ConvexSupport.linearValue] using hx.symm
        · obtain ⟨x, _, hx, _⟩ := hlower
          simpa [ConvexSupport.linearValue] using hx.symm
      subst r
      have hv : ![-0, (0 : ConvexSupport.Point) 0,
          (0 : ConvexSupport.Point) 1] =
          (0 : ℝ) • distinguishedPoint := by
        funext i
        fin_cases i <;> simp [distinguishedPoint]
      rw [hv, eval_smul_of_isHomogeneous hQ]
      simp [hm]
    · obtain ⟨x, hx, a, ha, hgradient⟩ :=
        hsupportTangent hsupport hn
      have hFzero : MvPolynomial.eval ![1, x 0, x 1] F = 0 := by
        have : x ∈ {y | MvPolynomial.eval ![1, y 0, y 1] F = 0} := by
          rwa [← hlocus]
        exact this
      have hQgradient : MvPolynomial.eval
          (gradient F ![1, x 0, x 1]) Q = 0 :=
        GaussPullback.eval_gradient_eq_zero_of_dvd hprimalGauss hFzero
      rw [hgradient, eval_smul_of_isHomogeneous hQ] at hQgradient
      exact (mul_eq_zero.mp hQgradient).resolve_left (pow_ne_zero _ ha)

/-- Version of `smoothConvexDualPair_of_affine_geometry` stated using a
fixed ambient level equation `L`.  This is the form matching the manuscript:
smooth strict convexity is asserted for the explicit full level, while the
irreducible component `F` is constructed later.  Since `F ∣ L` and the level
is regular, their gradients are nonzero scalar multiples along the boundary,
so all tangent/support facts transfer to `F`. -/
theorem smoothConvexDualPair_of_level_geometry
    {L F Q : MvPolynomial (Fin 3) ℝ}
    {K : Set ConvexSupport.Point} {d m : ℕ}
    (hF : F.IsHomogeneous d) (hQ : Q.IsHomogeneous m) (hm : m ≠ 0)
    (hcompact : IsCompact K) (hinterior : (interior K).Nonempty)
    (hregular : ∀ {z : Fin 3 → ℝ}, z ≠ 0 →
      MvPolynomial.eval z F = 0 → RegularAt F z)
    (hnoInfinity : ∀ {z : Fin 3 → ℝ}, z ≠ 0 →
      MvPolynomial.eval z F = 0 → z 0 ≠ 0)
    (hlocus : frontier K =
      {x | MvPolynomial.eval ![1, x 0, x 1] F = 0})
    (hFdivL : F ∣ L)
    (hlevelRegular : ∀ x ∈ frontier K,
      RegularAt L ![1, x 0, x 1])
    (hlevelTangentSupport : ∀ {x : ConvexSupport.Point}
      {ell : Fin 3 → ℝ}, x ∈ frontier K →
      (∃ a : ℝ, gradient L ![1, x 0, x 1] = a • ell) →
      ConvexSupport.IsSupportOffset K ![ell 1, ell 2] (-ell 0))
    (hsupportLevelTangent : ∀ {n : ConvexSupport.Point} {r : ℝ},
      ConvexSupport.IsSupportOffset K n r → n ≠ 0 →
      ∃ x ∈ frontier K, ∃ a : ℝ, a ≠ 0 ∧
        gradient L ![1, x 0, x 1] = a • ![-r, n 0, n 1])
    (hprimalGauss : F ∣ GaussPullback.gradientPullback Q F) :
    SmoothConvexDualPair F Q K := by
  obtain ⟨R, hR⟩ := hFdivL
  apply smoothConvexDualPair_of_affine_geometry hF hQ hm hcompact hinterior
    hregular hnoInfinity hlocus
  · intro x ell hx hFtangent
    have hFzero : MvPolynomial.eval ![1, x 0, x 1] F = 0 := by
      have : x ∈ {y | MvPolynomial.eval ![1, y 0, y 1] F = 0} := by
        rwa [← hlocus]
      exact this
    have hgradient : gradient L ![1, x 0, x 1] =
        MvPolynomial.eval ![1, x 0, x 1] R •
          gradient F ![1, x 0, x 1] := by
      funext i
      rw [hR]
      simp [ProjectiveDual.gradient, hFzero]
    apply hlevelTangentSupport hx
    obtain ⟨a, ha⟩ := hFtangent
    refine ⟨MvPolynomial.eval ![1, x 0, x 1] R * a, ?_⟩
    rw [hgradient, ha, smul_smul]
  · intro n r hsupport hn
    obtain ⟨x, hx, a, ha, hLtangent⟩ :=
      hsupportLevelTangent hsupport hn
    have hFzero : MvPolynomial.eval ![1, x 0, x 1] F = 0 := by
      have : x ∈ {y | MvPolynomial.eval ![1, y 0, y 1] F = 0} := by
        rwa [← hlocus]
      exact this
    let c : ℝ := MvPolynomial.eval ![1, x 0, x 1] R
    have hgradient : gradient L ![1, x 0, x 1] =
        c • gradient F ![1, x 0, x 1] := by
      funext i
      rw [hR]
      simp [ProjectiveDual.gradient, hFzero, c]
    have hc : c ≠ 0 := by
      intro hc0
      apply (hlevelRegular x hx).2
      rw [hgradient, hc0, zero_smul]
    refine ⟨x, hx, a / c, div_ne_zero ha hc, ?_⟩
    funext i
    have hi := congrFun (hgradient.symm.trans hLtangent) i
    change c * gradient F ![1, x 0, x 1] i =
      a * ![-r, n 0, n 1] i at hi
    change gradient F ![1, x 0, x 1] i =
      (a / c) * ![-r, n 0, n 1] i
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hc).2
    rw [mul_comm]
    exact hi
  · exact hprimalGauss

theorem root_is_support_of_generic
    {F Q : MvPolynomial (Fin 3) ℝ} {K : Set ConvexSupport.Point}
    {d m : ℕ} (hF : F.IsHomogeneous d) (hQ : Q.IsHomogeneous m)
    (hpair : SmoothConvexDualPair F Q K)
    (hbidual : Q ∣ GaussPullback.gradientPullback F Q)
    (k : Fin 3)
    (hlead : IsUnit (affineFamily Q).leadingCoeff)
    (hPgen : Irreducible (genericMap (affineFamily Q)))
    (hnotdvd : ¬ genericMap (affineFamily Q) ∣
      genericMap (affineFamily (PlaneGauss.gaussCrossPolynomial Q k)))
    {t s : ℝ}
    (htDisc : t ∉ exceptionalSet (affineFamily Q))
    (htGauss : t ∉ GenericAvoidance.pairExceptionalSet
      (affineFamily Q)
      (affineFamily (PlaneGauss.gaussCrossPolynomial Q k)))
    (hs : (specialize (affineFamily Q) t).eval s = 0) :
    ConvexSupport.IsSupportOffset K ![t, 1] (-s) := by
  let ell : Fin 3 → ℝ := ![s, t, 1]
  let dell : Fin 3 → ℝ := fun j ↦
    MvPolynomial.eval ell (PlaneGauss.affineTangentPolynomial Q j)
  obtain ⟨hregular, hLI⟩ :=
    PlaneGauss.regular_and_unramified_of_generic_root k hlead hPgen
      hnotdvd htDisc htGauss hs
  have hdell : IsTangentVector Q ell dell :=
    PlaneGauss.affineTangent_isTangent Q ell
  obtain ⟨a, ha⟩ := GaussPullback.gradient_primal_eq_smul_line_of_dvd
    hF hQ hbidual hregular hdell hLI
  let z := gradient Q ell
  have hFz : MvPolynomial.eval z F = 0 :=
    GaussPullback.eval_gradient_eq_zero_of_dvd hbidual hregular.1.2
  have hz0 : z ≠ 0 := hregular.2
  have hFregular : RegularAt F z := hpair.real_regular hz0 hFz
  have hzAffine : z 0 ≠ 0 := hpair.no_real_infinity hz0 hFz
  exact hpair.tangent_is_support hFregular hzAffine ⟨a, ha⟩

/-- The full generic projective contact count: an irreducible hyperbolic dual
curve of a smooth convex oval has degree two.  Hyperbolicity enters through
the `Splits` hypothesis, which is supplied by the Hermitian determinant
factor theorem. -/
theorem dual_degree_eq_two
    {F Q : MvPolynomial (Fin 3) ℝ} {K : Set ConvexSupport.Point}
    {d m : ℕ}
    (hF : F.IsHomogeneous d) (hQ : Q.IsHomogeneous m)
    (hQirr : Irreducible Q) (hm : m ≠ 0)
    (he : MvPolynomial.eval distinguishedPoint Q ≠ 0)
    (hpair : SmoothConvexDualPair F Q K)
    (hbidual : Q ∣ GaussPullback.gradientPullback F Q)
    (k : Fin 3)
    (hnotdvd : ¬ genericMap (affineFamily Q) ∣
      genericMap (affineFamily (PlaneGauss.gaussCrossPolynomial Q k)))
    (hsplits : ∀ t : ℝ, (specialize (affineFamily Q) t).Splits) :
    m = 2 := by
  let P := affineFamily Q
  let R := affineFamily (PlaneGauss.gaussCrossPolynomial Q k)
  have hPirr : Irreducible P := irreducible_affineFamily hQ hQirr hm he
  have hPdegree : P.natDegree = m := natDegree_affineFamily_eq hQ he
  have hPgen : Irreducible (genericMap P) :=
    genericMap_irreducible_of_irreducible hPirr (hPdegree.trans_ne hm)
  have hlead : IsUnit P.leadingCoeff :=
    isUnit_leadingCoeff_affineFamily hQ he
  obtain ⟨t, htDisc, htGauss, _⟩ :=
    GenericAvoidance.exists_parameter_avoiding_pair P R ∅ Set.finite_empty
  let p := specialize P t
  have hpnodup : p.roots.Nodup :=
    roots_nodup_of_not_mem_exceptional hlead hPgen htDisc
  have hpdegree : p.natDegree = m := by
    rw [natDegree_specialize_eq P hlead, hPdegree]
  have hp0 : p ≠ 0 := by
    intro hp
    rw [hp, Polynomial.natDegree_zero] at hpdegree
    exact hm hpdegree.symm
  let n : ConvexSupport.Point := ![t, 1]
  have hn : n ≠ 0 := by
    intro hnzero
    have h := congrFun hnzero (1 : Fin 2)
    change (1 : ℝ) = 0 at h
    exact one_ne_zero h
  obtain ⟨rmin, rmax, hminmax, hsupport⟩ :=
    ConvexSupport.supportOffset_iff_eq_two hpair.isCompact
      hpair.interior_nonempty hn
  have hrootSupport : ∀ x : ℝ, x ∈ p.roots →
      x = -rmin ∨ x = -rmax := by
    intro x hx
    have hxzero : p.eval x = 0 :=
      (Polynomial.isRoot_of_mem_roots hx).eq_zero
    have hsupportX : ConvexSupport.IsSupportOffset K n (-x) := by
      apply root_is_support_of_generic hF hQ hpair hbidual k hlead hPgen
        hnotdvd htDisc htGauss
      exact hxzero
    rw [hsupport] at hsupportX
    rcases hsupportX with h | h
    · left; linarith
    · right; linarith
  have hminRoot : -rmin ∈ p.roots := by
    rw [Polynomial.mem_roots hp0]
    change (specialize (affineFamily Q) t).eval (-rmin) = 0
    rw [eval_specialize_affineFamily]
    simpa [n] using
      hpair.support_is_dual ((hsupport rmin).2 (Or.inl rfl))
  have hmaxRoot : -rmax ∈ p.roots := by
    rw [Polynomial.mem_roots hp0]
    change (specialize (affineFamily Q) t).eval (-rmax) = 0
    rw [eval_specialize_affineFamily]
    simpa [n] using
      hpair.support_is_dual ((hsupport rmax).2 (Or.inr rfl))
  have hpTwo := ContactDegree.natDegree_eq_two_of_support_bound
    (hsplits t) hpnodup (fun h ↦ hminmax (neg_injective h))
    hminRoot hmaxRoot hrootSupport
  exact hpdegree.symm.trans hpTwo

/-- Set-level completion of the final conic calculation: a real conic
through a circular point, with nonzero Euclidean quadratic part, is a circle.
-/
theorem boundary_eq_circle_of_conic
    {K : Set ConvexSupport.Point} (q : Conic.Form)
    (hboundary : frontier K =
      {x | q.evalAffine (x 0) (x 1) = 0})
    (hcircular : q.evalComplex 1 Complex.I 0 = 0)
    (hxx : q.xx ≠ 0) :
    frontier K =
      {x | (x 0 - q.centerX) ^ 2 + (x 1 - q.centerY) ^ 2 = q.radiusSq} := by
  rw [hboundary]
  ext x
  change q.evalAffine (x 0) (x 1) = 0 ↔
    (x 0 - q.centerX) ^ 2 + (x 1 - q.centerY) ^ 2 = q.radiusSq
  obtain ⟨hyy, hxy⟩ := (Conic.eval_circularPoint_eq_zero_iff q).mp hcircular
  exact Conic.evalAffine_eq_zero_iff_circle q hxx hyy hxy (x 0) (x 1)

/-- A circle equation for the boundary of a compact set with nonempty
interior has strictly positive squared radius.  Compactness supplies two
opposite support points, and nonempty interior makes their offsets distinct. -/
theorem radiusSq_pos_of_compact_interior_boundary_circle
    {K : Set ConvexSupport.Point} (q : Conic.Form)
    (hcompact : IsCompact K) (hinterior : (interior K).Nonempty)
    (hboundary : frontier K =
      {x | (x 0 - q.centerX) ^ 2 + (x 1 - q.centerY) ^ 2 = q.radiusSq}) :
    0 < q.radiusSq := by
  let n : ConvexSupport.Point := ![1, 0]
  have hn : n ≠ 0 := by
    intro h
    have := congrFun h (0 : Fin 2)
    norm_num [n] at this
  have hKne : K.Nonempty := hinterior.mono interior_subset
  obtain ⟨smax, hupper⟩ :=
    ConvexSupport.exists_upperSupportOffset hcompact hKne n
  obtain ⟨smin, hlower⟩ :=
    ConvexSupport.exists_lowerSupportOffset hcompact hKne n
  have hsne : smax ≠ smin :=
    ConvexSupport.upper_ne_lower_of_interior hinterior hn hupper hlower
  obtain ⟨x, hxK, hxvalue, hxbound⟩ := hupper
  obtain ⟨y, hyK, hyvalue, hybound⟩ := hlower
  have hxfrontier : x ∈ frontier K := by
    rw [mem_frontier_iff_notMem_interior hxK]
    intro hxint
    exact ConvexSupport.linearValue_lt_of_mem_interior_of_upper_bound
      hxint hn hxbound hxvalue
  have hyfrontier : y ∈ frontier K := by
    rw [mem_frontier_iff_notMem_interior hyK]
    intro hyint
    exact ConvexSupport.linearValue_gt_of_mem_interior_of_lower_bound
      hyint hn hybound hyvalue
  have hxy : x ≠ y := by
    intro h
    apply hsne
    rw [← hxvalue, ← hyvalue, h]
  have hxcircle :
      (x 0 - q.centerX) ^ 2 + (x 1 - q.centerY) ^ 2 = q.radiusSq := by
    rw [hboundary] at hxfrontier
    exact hxfrontier
  have hycircle :
      (y 0 - q.centerX) ^ 2 + (y 1 - q.centerY) ^ 2 = q.radiusSq := by
    rw [hboundary] at hyfrontier
    exact hyfrontier
  have hrsNonneg : 0 ≤ q.radiusSq := by
    rw [← hxcircle]
    positivity
  refine lt_of_le_of_ne hrsNonneg ?_
  intro hrs
  have hrsZero : q.radiusSq = 0 := hrs.symm
  have hx₀ : x 0 = q.centerX := by
    rw [hrsZero] at hxcircle
    nlinarith [sq_nonneg (x 0 - q.centerX), sq_nonneg (x 1 - q.centerY)]
  have hx₁ : x 1 = q.centerY := by
    rw [hrsZero] at hxcircle
    nlinarith [sq_nonneg (x 0 - q.centerX), sq_nonneg (x 1 - q.centerY)]
  have hy₀ : y 0 = q.centerX := by
    rw [hrsZero] at hycircle
    nlinarith [sq_nonneg (y 0 - q.centerX), sq_nonneg (y 1 - q.centerY)]
  have hy₁ : y 1 = q.centerY := by
    rw [hrsZero] at hycircle
    nlinarith [sq_nonneg (y 0 - q.centerX), sq_nonneg (y 1 - q.centerY)]
  apply hxy
  funext i
  fin_cases i
  · exact hx₀.trans hy₀.symm
  · exact hx₁.trans hy₁.symm

/-- End-to-end algebraic/projective conclusion of Proposition 7.1.

Starting from the irreducible primal component, its irreducible dual, the
explicit bidual divisor identity, Hermitian hyperbolicity, and the real oval
interface established earlier in the proposition, this theorem derives the
degree-two statement, constructs the primal envelope by the inverse Hessian,
identifies it with the primal component, forces the circular points at
infinity, and concludes that the boundary is a circle. -/
theorem projective_circle_conclusion
    {F Q : MvPolynomial (Fin 3) ℝ} {K : Set ConvexSupport.Point}
    {d m : ℕ}
    (hF : F.IsHomogeneous d) (hQ : Q.IsHomogeneous m)
    (hFirr : Irreducible F) (hQirr : Irreducible Q) (hm : m ≠ 0)
    (hQcomplexIrr : Irreducible
      (MvPolynomial.map (algebraMap ℝ ℂ) Q))
    (he : MvPolynomial.eval distinguishedPoint Q ≠ 0)
    (hpair : SmoothConvexDualPair F Q K)
    (hbidual : Q ∣ GaussPullback.gradientPullback F Q)
    (k : Fin 3)
    (hnotdvd : ¬ genericMap (affineFamily Q) ∣
      genericMap (affineFamily (PlaneGauss.gaussCrossPolynomial Q k)))
    (hsplits : ∀ t : ℝ, (specialize (affineFamily Q) t).Splits)
    (hInfinity : ∀ X Y : ℂ,
      MvPolynomial.eval ![0, X, Y]
        (MvPolynomial.map (algebraMap ℝ ℂ) F) = 0 →
      X ^ 2 + Y ^ 2 = 0) :
    frontier K =
      {x | (x 0 - (ConicEnvelope.envelopeForm Q).centerX) ^ 2 +
        (x 1 - (ConicEnvelope.envelopeForm Q).centerY) ^ 2 =
          (ConicEnvelope.envelopeForm Q).radiusSq} := by
  have hm2 : m = 2 := dual_degree_eq_two hF hQ hQirr hm he hpair
    hbidual k hnotdvd hsplits
  subst m
  have hdet : IsUnit (ConicEnvelope.conicMatrix Q).det :=
    ConicEnvelope.isUnit_det_conicMatrix_of_map_irreducible hQ hQcomplexIrr
  have hEnvelopeDvd : ConicEnvelope.primalEnvelopePolynomial Q ∣ F :=
    ConicEnvelope.primalEnvelopePolynomial_dvd_of_gradientPullback_dvd
      hQ hdet hbidual
  have hAssociated : Associated F
      (ConicEnvelope.primalEnvelopePolynomial Q) :=
    (hFirr.dvd_iff.mp hEnvelopeDvd).resolve_left
      (ConicEnvelope.primalEnvelopePolynomial_not_isUnit Q)
  have hzero : ∀ x : ConvexSupport.Point,
      MvPolynomial.eval ![1, x 0, x 1] F = 0 ↔
      MvPolynomial.eval ![1, x 0, x 1]
        (ConicEnvelope.primalEnvelopePolynomial Q) = 0 := by
    intro x
    constructor
    · intro hFx
      obtain ⟨R, hR⟩ := hAssociated.dvd
      rw [hR, map_mul, hFx, zero_mul]
    · intro hEx
      obtain ⟨R, hR⟩ := hEnvelopeDvd
      rw [hR, map_mul, hEx, zero_mul]
  have hboundary : frontier K =
      {x | (ConicEnvelope.envelopeForm Q).evalAffine (x 0) (x 1) = 0} := by
    rw [hpair.real_affine_locus]
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [hzero, ConicEnvelope.eval_primalEnvelope_eq_evalAffine]
  have hcircular :
      (ConicEnvelope.envelopeForm Q).evalComplex 1 Complex.I 0 = 0 :=
    ConicEnvelope.envelopeForm_eval_circularPoint_eq_zero_of_infinity_control
      hEnvelopeDvd hInfinity
  have hxx : (ConicEnvelope.envelopeForm Q).xx ≠ 0 :=
    ConicEnvelope.envelopeForm_xx_ne_zero hdet hcircular
  exact boundary_eq_circle_of_conic (ConicEnvelope.envelopeForm Q)
    hboundary hcircular hxx

/-- The same conclusion with the infinity condition discharged directly from
the rational lemniscate equation (7.3).  Thus the only remaining inputs are
the irreducible primal/dual component data and the generic dual-contact data;
the final circular-point step is no longer an abstract hypothesis. -/
theorem projective_circle_conclusion_of_lemniscate
    {F Q : MvPolynomial (Fin 3) ℝ} {K : Set ConvexSupport.Point}
    {d m : ℕ}
    (U V : ℂ[X]) (hU : U ≠ 0)
    (hUVdegree : V.natDegree < U.natDegree)
    (hF : F.IsHomogeneous d) (hQ : Q.IsHomogeneous m)
    (hFirr : Irreducible F) (hQirr : Irreducible Q) (hm : m ≠ 0)
    (hQcomplexIrr : Irreducible
      (MvPolynomial.map (algebraMap ℝ ℂ) Q))
    (he : MvPolynomial.eval distinguishedPoint Q ≠ 0)
    (hpair : SmoothConvexDualPair F Q K)
    (hFlemniscate : MvPolynomial.map (algebraMap ℝ ℂ) F ∣
      Lemniscate.primalOrderProjectiveLevelPolynomial U V)
    (hbidual : Q ∣ GaussPullback.gradientPullback F Q)
    (k : Fin 3)
    (hnotdvd : ¬ genericMap (affineFamily Q) ∣
      genericMap (affineFamily (PlaneGauss.gaussCrossPolynomial Q k)))
    (hsplits : ∀ t : ℝ, (specialize (affineFamily Q) t).Splits) :
    frontier K =
      {x | (x 0 - (ConicEnvelope.envelopeForm Q).centerX) ^ 2 +
        (x 1 - (ConicEnvelope.envelopeForm Q).centerY) ^ 2 =
          (ConicEnvelope.envelopeForm Q).radiusSq} := by
  apply projective_circle_conclusion hF hQ hFirr hQirr hm hQcomplexIrr
    he hpair hbidual k hnotdvd hsplits
  exact Lemniscate.infinity_control_of_component_dvd U V hU hUVdegree F
    hFlemniscate

/-- Proposition 7.1 with both analytic polynomial inputs visible.  The
lemniscate factor controls infinity, while divisibility into the explicit
Hermitian projective determinant proves both nonvanishing at `[1,0,0]` and
all real-direction splitting. -/
theorem projective_circle_conclusion_of_lemniscate_hermitian
    {n : Type*} [Fintype n] [DecidableEq n]
    {F Q : MvPolynomial (Fin 3) ℝ} {K : Set ConvexSupport.Point}
    {d m : ℕ}
    (U V : ℂ[X]) (hU : U ≠ 0)
    (hUVdegree : V.natDegree < U.natDegree)
    (H J : Matrix n n ℂ) (hH : H.IsHermitian) (hJ : J.IsHermitian)
    (hF : F.IsHomogeneous d) (hQ : Q.IsHomogeneous m)
    (hFirr : Irreducible F) (hQirr : Irreducible Q) (hm : m ≠ 0)
    (hQcomplexIrr : Irreducible
      (MvPolynomial.map (algebraMap ℝ ℂ) Q))
    (hpair : SmoothConvexDualPair F Q K)
    (hFlemniscate : MvPolynomial.map (algebraMap ℝ ℂ) F ∣
      Lemniscate.primalOrderProjectiveLevelPolynomial U V)
    (hQhermitian : MvPolynomial.map (algebraMap ℝ ℂ) Q ∣
      HermitianProjective.determinantPolynomial H J)
    (hbidual : Q ∣ GaussPullback.gradientPullback F Q)
    (k : Fin 3)
    (hnotdvd : ¬ genericMap (affineFamily Q) ∣
      genericMap (affineFamily (PlaneGauss.gaussCrossPolynomial Q k))) :
    frontier K =
      {x | (x 0 - (ConicEnvelope.envelopeForm Q).centerX) ^ 2 +
        (x 1 - (ConicEnvelope.envelopeForm Q).centerY) ^ 2 =
          (ConicEnvelope.envelopeForm Q).radiusSq} := by
  apply projective_circle_conclusion_of_lemniscate U V hU hUVdegree hF hQ
    hFirr hQirr hm hQcomplexIrr
  · exact HermitianProjective.eval_distinguishedPoint_ne_zero_of_dvd
      H J Q hQhermitian
  · exact hpair
  · exact hFlemniscate
  · exact hbidual
  · exact hnotdvd
  · exact HermitianProjective.splits_specialize_affineFamily_of_dvd
      hH hJ Q hQhermitian

/-- A fully local form of the generic Gauss input: it is enough to exhibit
one affine point of the dual curve where one explicit Gauss cross minor is
nonzero.  Gauss's lemma then proves the required generic nondivisibility, so
no generic exceptional-set assertion remains among the hypotheses. -/
theorem projective_circle_conclusion_of_unramified_contact
    {n : Type*} [Fintype n] [DecidableEq n]
    {F Q : MvPolynomial (Fin 3) ℝ} {K : Set ConvexSupport.Point}
    {d m : ℕ}
    (U V : ℂ[X]) (hU : U ≠ 0)
    (hUVdegree : V.natDegree < U.natDegree)
    (H J : Matrix n n ℂ) (hH : H.IsHermitian) (hJ : J.IsHermitian)
    (hF : F.IsHomogeneous d) (hQ : Q.IsHomogeneous m)
    (hFirr : Irreducible F) (hQirr : Irreducible Q) (hm : m ≠ 0)
    (hQcomplexIrr : Irreducible
      (MvPolynomial.map (algebraMap ℝ ℂ) Q))
    (hpair : SmoothConvexDualPair F Q K)
    (hFlemniscate : MvPolynomial.map (algebraMap ℝ ℂ) F ∣
      Lemniscate.primalOrderProjectiveLevelPolynomial U V)
    (hQhermitian : MvPolynomial.map (algebraMap ℝ ℂ) Q ∣
      HermitianProjective.determinantPolynomial H J)
    (hbidual : Q ∣ GaussPullback.gradientPullback F Q)
    (k : Fin 3) (s t : ℝ)
    (hQell : MvPolynomial.eval ![s, t, 1] Q = 0)
    (hcross : MvPolynomial.eval ![s, t, 1]
      (PlaneGauss.gaussCrossPolynomial Q k) ≠ 0) :
    frontier K =
      {x | (x 0 - (ConicEnvelope.envelopeForm Q).centerX) ^ 2 +
        (x 1 - (ConicEnvelope.envelopeForm Q).centerY) ^ 2 =
          (ConicEnvelope.envelopeForm Q).radiusSq} := by
  have he : MvPolynomial.eval distinguishedPoint Q ≠ 0 :=
    HermitianProjective.eval_distinguishedPoint_ne_zero_of_dvd
      H J Q hQhermitian
  have hPirr : Irreducible (affineFamily Q) :=
    irreducible_affineFamily hQ hQirr hm he
  have hPdegree : (affineFamily Q).natDegree ≠ 0 := by
    rw [natDegree_affineFamily_eq hQ he]
    exact hm
  have hnotdvd := PlaneGauss.not_generic_dvd_of_affine_unramified
    hPirr hPdegree k s t hQell hcross
  exact projective_circle_conclusion_of_lemniscate_hermitian
    U V hU hUVdegree H J hH hJ hF hQ hFirr hQirr hm hQcomplexIrr
    hpair hFlemniscate hQhermitian hbidual k hnotdvd

end ProjectiveCircle

end DiskRigidity.Algebraic
