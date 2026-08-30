/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.AnalyticImplicitCurve
public import DiskRigidity.Algebraic.ConvexSupport
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Tangent lines and support lines of a regular convex level curve

For a compact convex planar body with nonempty interior whose boundary is a
regular polynomial level, the algebraic tangent lines are exactly the
support lines.  The proof uses Hahn--Banach to obtain one support covector at
each boundary point and an analytic implicit graph to identify it with the
polynomial gradient.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace ConvexLevelSupport

open Filter Matrix MvPolynomial Set
open ProjectiveDual
open scoped Topology

/-- The coordinate vector representing a continuous linear functional on
the real plane. -/
noncomputable def dualNormal
    (f : StrongDual ℝ ConvexSupport.Point) : ConvexSupport.Point :=
  ![f ![1, 0], f ![0, 1]]

theorem linearValue_dualNormal
    (f : StrongDual ℝ ConvexSupport.Point) (x : ConvexSupport.Point) :
    ConvexSupport.linearValue (dualNormal f) x = f x := by
  have hx : x = x 0 • (![1, 0] : ConvexSupport.Point) +
      x 1 • (![0, 1] : ConvexSupport.Point) := by
    funext i
    fin_cases i <;> simp
  rw [hx, map_add, map_smul, map_smul]
  simp [dualNormal, ConvexSupport.linearValue, dotProduct,
    Fin.sum_univ_two]
  ring

theorem dualNormal_ne_zero
    {f : StrongDual ℝ ConvexSupport.Point} (hf : f ≠ 0) :
    dualNormal f ≠ 0 := by
  intro hn
  apply hf
  ext x
  have hvalue := linearValue_dualNormal f x
  rw [hn] at hvalue
  simpa [ConvexSupport.linearValue] using hvalue.symm

/-- Fermat's theorem applied to a supporting functional along a graph
`t ↦ [p(t),t]`. -/
theorem support_derivative_yx
    {K : Set ConvexSupport.Point} {n : ConvexSupport.Point}
    {U : Set ℝ} (hUopen : IsOpen U) {t₀ : ℝ} (ht₀ : t₀ ∈ U)
    {p : ℝ → ℝ} (hp : DifferentiableAt ℝ p t₀)
    (hgraphK : ∀ t ∈ U, ![p t, t] ∈ K)
    (hsupportAt :
      (∀ y ∈ K, ConvexSupport.linearValue n y ≤
        ConvexSupport.linearValue n ![p t₀, t₀]) ∨
      (∀ y ∈ K, ConvexSupport.linearValue n ![p t₀, t₀] ≤
        ConvexSupport.linearValue n y)) :
    n 0 * deriv p t₀ + n 1 = 0 := by
  let f : ℝ → ℝ := fun t ↦
    ConvexSupport.linearValue n ![p t, t]
  have hlocalZero : deriv f t₀ = 0 := by
    rcases hsupportAt with hupper | hlower
    · apply (show IsLocalMax f t₀ from ?_).deriv_eq_zero
      filter_upwards [hUopen.mem_nhds ht₀] with t ht
      exact hupper _ (hgraphK t ht)
    · apply (show IsLocalMin f t₀ from ?_).deriv_eq_zero
      filter_upwards [hUopen.mem_nhds ht₀] with t ht
      exact hlower _ (hgraphK t ht)
  have hfEq : f = fun t ↦ n 0 * p t + n 1 * t := by
    funext t
    simp [f, ConvexSupport.linearValue, dotProduct, Fin.sum_univ_two]
  rw [hfEq, AnalyticContact.deriv_add_apply (by fun_prop) (by fun_prop),
    deriv_const_mul_field, deriv_const_mul_id] at hlocalZero
  exact hlocalZero

/-- Fermat's theorem in the graph chart `t ↦ [t,p(t)]`. -/
theorem support_derivative_xy
    {K : Set ConvexSupport.Point} {n : ConvexSupport.Point}
    {U : Set ℝ} (hUopen : IsOpen U) {t₀ : ℝ} (ht₀ : t₀ ∈ U)
    {p : ℝ → ℝ} (hp : DifferentiableAt ℝ p t₀)
    (hgraphK : ∀ t ∈ U, ![t, p t] ∈ K)
    (hsupportAt :
      (∀ y ∈ K, ConvexSupport.linearValue n y ≤
        ConvexSupport.linearValue n ![t₀, p t₀]) ∨
      (∀ y ∈ K, ConvexSupport.linearValue n ![t₀, p t₀] ≤
        ConvexSupport.linearValue n y)) :
    n 0 + n 1 * deriv p t₀ = 0 := by
  let f : ℝ → ℝ := fun t ↦
    ConvexSupport.linearValue n ![t, p t]
  have hlocalZero : deriv f t₀ = 0 := by
    rcases hsupportAt with hupper | hlower
    · apply (show IsLocalMax f t₀ from ?_).deriv_eq_zero
      filter_upwards [hUopen.mem_nhds ht₀] with t ht
      exact hupper _ (hgraphK t ht)
    · apply (show IsLocalMin f t₀ from ?_).deriv_eq_zero
      filter_upwards [hUopen.mem_nhds ht₀] with t ht
      exact hlower _ (hgraphK t ht)
  have hfEq : f = fun t ↦ n 0 * t + n 1 * p t := by
    funext t
    simp [f, ConvexSupport.linearValue, dotProduct, Fin.sum_univ_two]
  rw [hfEq, AnalyticContact.deriv_add_apply (by fun_prop) (by fun_prop),
    deriv_const_mul_id, deriv_const_mul_field] at hlocalZero
  exact hlocalZero

/-- Differentiating a polynomial zero graph `[1:p(t):t]`. -/
theorem gradient_tangent_yx
    (P : MvPolynomial (Fin 3) ℝ)
    {U : Set ℝ} (hUopen : IsOpen U) {p : ℝ → ℝ}
    (hp : AnalyticOnNhd ℝ p U)
    (hzero : ∀ t ∈ U, MvPolynomial.eval ![1, p t, t] P = 0)
    {t₀ : ℝ} (ht₀ : t₀ ∈ U) :
    gradient P ![1, p t₀, t₀] 1 * deriv p t₀ +
      gradient P ![1, p t₀, t₀] 2 = 0 := by
  let z : ℝ → Fin 3 → ℝ := fun t ↦ ![1, p t, t]
  have hz : ∀ i, AnalyticAt ℝ (fun t ↦ z t i) t₀ := by
    intro i
    fin_cases i
    · exact analyticAt_const
    · exact hp t₀ ht₀
    · exact analyticAt_id
  have hformula := AnalyticContact.deriv_eval_mvPolynomial P hz
  have heq : (fun t ↦ MvPolynomial.eval (z t) P) =ᶠ[𝓝 t₀]
      (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [hUopen.mem_nhds ht₀] with t ht
    exact hzero t ht
  have hderiv : deriv (fun t ↦ MvPolynomial.eval (z t) P) t₀ = 0 := by
    rw [heq.deriv_eq]
    simp
  rw [hformula] at hderiv
  simpa [z, directionalDerivative, dotProduct, Fin.sum_univ_three,
    mul_comm] using hderiv

/-- Differentiating a polynomial zero graph `[1:t:p(t)]`. -/
theorem gradient_tangent_xy
    (P : MvPolynomial (Fin 3) ℝ)
    {U : Set ℝ} (hUopen : IsOpen U) {p : ℝ → ℝ}
    (hp : AnalyticOnNhd ℝ p U)
    (hzero : ∀ t ∈ U, MvPolynomial.eval ![1, t, p t] P = 0)
    {t₀ : ℝ} (ht₀ : t₀ ∈ U) :
    gradient P ![1, t₀, p t₀] 1 +
      gradient P ![1, t₀, p t₀] 2 * deriv p t₀ = 0 := by
  let z : ℝ → Fin 3 → ℝ := fun t ↦ ![1, t, p t]
  have hz : ∀ i, AnalyticAt ℝ (fun t ↦ z t i) t₀ := by
    intro i
    fin_cases i
    · exact analyticAt_const
    · exact analyticAt_id
    · exact hp t₀ ht₀
  have hformula := AnalyticContact.deriv_eval_mvPolynomial P hz
  have heq : (fun t ↦ MvPolynomial.eval (z t) P) =ᶠ[𝓝 t₀]
      (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [hUopen.mem_nhds ht₀] with t ht
    exact hzero t ht
  have hderiv : deriv (fun t ↦ MvPolynomial.eval (z t) P) t₀ = 0 := by
    rw [heq.deriv_eq]
    simp
  rw [hformula] at hderiv
  simpa [z, directionalDerivative, dotProduct, Fin.sum_univ_three,
    mul_comm] using hderiv

/-- At a regular boundary point, every supporting covector through that
point is a nonzero scalar multiple of the homogeneous polynomial gradient.
This is the local smoothness statement that rules out corners. -/
theorem gradient_eq_smul_supportLine
    {P : MvPolynomial (Fin 3) ℝ} {d : ℕ}
    (hP : P.IsHomogeneous d)
    {K : Set ConvexSupport.Point} (hcompact : IsCompact K)
    (hlocus : frontier K =
      {x | MvPolynomial.eval ![1, x 0, x 1] P = 0})
    {x : ConvexSupport.Point} (hx : x ∈ frontier K)
    (hregular : RegularAt P ![1, x 0, x 1])
    {n : ConvexSupport.Point} {r : ℝ} (hn : n ≠ 0)
    (hsupport : ConvexSupport.IsSupportOffset K n r)
    (hxline : ConvexSupport.linearValue n x = r) :
    ∃ a : ℝ, a ≠ 0 ∧
      gradient P ![1, x 0, x 1] = a • ![-r, n 0, n 1] := by
  have hxK : x ∈ K := by
    have := frontier_subset_closure hx
    simpa [hcompact.isClosed.closure_eq] using this
  have hfrontierK : frontier K ⊆ K := by
    intro y hy
    have := frontier_subset_closure hy
    simpa [hcompact.isClosed.closure_eq] using this
  have hzero : MvPolynomial.eval ![1, x 0, x 1] P = 0 := by
    have : x ∈ {y | MvPolynomial.eval ![1, y 0, y 1] P = 0} := by
      rwa [← hlocus]
    exact this
  have hxrepr : (![x 0, x 1] : ConvexSupport.Point) = x := by
    funext i
    fin_cases i <;> rfl
  rcases AnalyticImplicitCurve.pderiv_one_ne_zero_or_pderiv_two_ne_zero
      hP hregular with hg₁ | hg₂
  · obtain ⟨U, p, hUopen, hx₁U, hp, hp₀, hgraphZero⟩ :=
      AnalyticImplicitCurve.exists_open_analytic_graph_of_pderiv_one_ne_zero
        P (x 0) (x 1) hzero hg₁
    have hgraphBoundary : ∀ t ∈ U, ![p t, t] ∈ frontier K := by
      intro t ht
      rw [hlocus]
      exact hgraphZero t ht
    have hgraphK : ∀ t ∈ U, ![p t, t] ∈ K := by
      intro t ht
      exact hfrontierK (hgraphBoundary t ht)
    have hbase : (![p (x 1), x 1] : ConvexSupport.Point) = x := by
      rw [hp₀]
      exact hxrepr
    have hsupportAt :
        (∀ y ∈ K, ConvexSupport.linearValue n y ≤
          ConvexSupport.linearValue n ![p (x 1), x 1]) ∨
        (∀ y ∈ K, ConvexSupport.linearValue n ![p (x 1), x 1] ≤
          ConvexSupport.linearValue n y) := by
      rcases hsupport with hupper | hlower
      · left
        obtain ⟨_, _, _, hbound⟩ := hupper
        intro y hy
        calc
          ConvexSupport.linearValue n y ≤ r := hbound y hy
          _ = ConvexSupport.linearValue n ![p (x 1), x 1] := by
            rw [hbase, hxline]
      · right
        obtain ⟨_, _, _, hbound⟩ := hlower
        intro y hy
        calc
          ConvexSupport.linearValue n ![p (x 1), x 1] = r := by
            rw [hbase, hxline]
          _ ≤ ConvexSupport.linearValue n y := hbound y hy
    have hnTangent : n 0 * deriv p (x 1) + n 1 = 0 :=
      support_derivative_yx hUopen hx₁U (hp (x 1) hx₁U).differentiableAt
        hgraphK hsupportAt
    have hgTangent : gradient P ![1, x 0, x 1] 1 * deriv p (x 1) +
        gradient P ![1, x 0, x 1] 2 = 0 := by
      have := gradient_tangent_yx P hUopen hp hgraphZero hx₁U
      simpa [hp₀] using this
    have hn₀ : n 0 ≠ 0 := by
      intro hn₀
      have hn₁ : n 1 = 0 := by
        rw [hn₀, zero_mul, zero_add] at hnTangent
        exact hnTangent
      apply hn
      funext i
      fin_cases i
      · exact hn₀
      · exact hn₁
    let a : ℝ := gradient P ![1, x 0, x 1] 1 / n 0
    have ha : a ≠ 0 := div_ne_zero hg₁ hn₀
    have ha₁ : gradient P ![1, x 0, x 1] 1 = a * n 0 := by
      dsimp [a]
      field_simp
    have ha₂ : gradient P ![1, x 0, x 1] 2 = a * n 1 := by
      calc
        gradient P ![1, x 0, x 1] 2 =
            -(gradient P ![1, x 0, x 1] 1 * deriv p (x 1)) := by
          linarith [hgTangent]
        _ = a * (-(n 0 * deriv p (x 1))) := by rw [ha₁]; ring
        _ = a * n 1 := by
          congr 1
          linarith [hnTangent]
    have hdot := dot_gradient_eq_zero hP hzero
    have hdot' : gradient P ![1, x 0, x 1] 0 +
        x 0 * gradient P ![1, x 0, x 1] 1 +
        x 1 * gradient P ![1, x 0, x 1] 2 = 0 := by
      simpa [dotProduct, Fin.sum_univ_three] using hdot
    have hr : n 0 * x 0 + n 1 * x 1 = r := by
      simpa [ConvexSupport.linearValue, dotProduct, Fin.sum_univ_two]
        using hxline
    have ha₀ : gradient P ![1, x 0, x 1] 0 = a * (-r) := by
      calc
        gradient P ![1, x 0, x 1] 0 =
            -(x 0 * gradient P ![1, x 0, x 1] 1 +
              x 1 * gradient P ![1, x 0, x 1] 2) := by
          linarith [hdot']
        _ = a * (-(n 0 * x 0 + n 1 * x 1)) := by
          rw [ha₁, ha₂]
          ring
        _ = a * (-r) := by rw [hr]
    refine ⟨a, ha, ?_⟩
    funext i
    fin_cases i
    · simpa using ha₀
    · simpa using ha₁
    · simpa using ha₂
  · obtain ⟨U, p, hUopen, hx₀U, hp, hp₀, hgraphZero⟩ :=
      AnalyticImplicitCurve.exists_open_analytic_graph_of_pderiv_two_ne_zero
        P (x 0) (x 1) hzero hg₂
    have hgraphBoundary : ∀ t ∈ U, ![t, p t] ∈ frontier K := by
      intro t ht
      rw [hlocus]
      exact hgraphZero t ht
    have hgraphK : ∀ t ∈ U, ![t, p t] ∈ K := by
      intro t ht
      exact hfrontierK (hgraphBoundary t ht)
    have hbase : (![x 0, p (x 0)] : ConvexSupport.Point) = x := by
      rw [hp₀]
      exact hxrepr
    have hsupportAt :
        (∀ y ∈ K, ConvexSupport.linearValue n y ≤
          ConvexSupport.linearValue n ![x 0, p (x 0)]) ∨
        (∀ y ∈ K, ConvexSupport.linearValue n ![x 0, p (x 0)] ≤
          ConvexSupport.linearValue n y) := by
      rcases hsupport with hupper | hlower
      · left
        obtain ⟨_, _, _, hbound⟩ := hupper
        intro y hy
        calc
          ConvexSupport.linearValue n y ≤ r := hbound y hy
          _ = ConvexSupport.linearValue n ![x 0, p (x 0)] := by
            rw [hbase, hxline]
      · right
        obtain ⟨_, _, _, hbound⟩ := hlower
        intro y hy
        calc
          ConvexSupport.linearValue n ![x 0, p (x 0)] = r := by
            rw [hbase, hxline]
          _ ≤ ConvexSupport.linearValue n y := hbound y hy
    have hnTangent : n 0 + n 1 * deriv p (x 0) = 0 :=
      support_derivative_xy hUopen hx₀U (hp (x 0) hx₀U).differentiableAt
        hgraphK hsupportAt
    have hgTangent : gradient P ![1, x 0, x 1] 1 +
        gradient P ![1, x 0, x 1] 2 * deriv p (x 0) = 0 := by
      have := gradient_tangent_xy P hUopen hp hgraphZero hx₀U
      simpa [hp₀] using this
    have hn₁ : n 1 ≠ 0 := by
      intro hn₁
      have hn₀ : n 0 = 0 := by
        rw [hn₁, zero_mul, add_zero] at hnTangent
        exact hnTangent
      apply hn
      funext i
      fin_cases i
      · exact hn₀
      · exact hn₁
    let a : ℝ := gradient P ![1, x 0, x 1] 2 / n 1
    have ha : a ≠ 0 := div_ne_zero hg₂ hn₁
    have ha₂ : gradient P ![1, x 0, x 1] 2 = a * n 1 := by
      dsimp [a]
      field_simp
    have ha₁ : gradient P ![1, x 0, x 1] 1 = a * n 0 := by
      calc
        gradient P ![1, x 0, x 1] 1 =
            -(gradient P ![1, x 0, x 1] 2 * deriv p (x 0)) := by
          linarith [hgTangent]
        _ = a * (-(n 1 * deriv p (x 0))) := by rw [ha₂]; ring
        _ = a * n 0 := by
          congr 1
          linarith [hnTangent]
    have hdot := dot_gradient_eq_zero hP hzero
    have hdot' : gradient P ![1, x 0, x 1] 0 +
        x 0 * gradient P ![1, x 0, x 1] 1 +
        x 1 * gradient P ![1, x 0, x 1] 2 = 0 := by
      simpa [dotProduct, Fin.sum_univ_three] using hdot
    have hr : n 0 * x 0 + n 1 * x 1 = r := by
      simpa [ConvexSupport.linearValue, dotProduct, Fin.sum_univ_two]
        using hxline
    have ha₀ : gradient P ![1, x 0, x 1] 0 = a * (-r) := by
      calc
        gradient P ![1, x 0, x 1] 0 =
            -(x 0 * gradient P ![1, x 0, x 1] 1 +
              x 1 * gradient P ![1, x 0, x 1] 2) := by
          linarith [hdot']
        _ = a * (-(n 0 * x 0 + n 1 * x 1)) := by
          rw [ha₁, ha₂]
          ring
        _ = a * (-r) := by rw [hr]
    refine ⟨a, ha, ?_⟩
    funext i
    fin_cases i
    · simpa using ha₀
    · simpa using ha₁
    · simpa using ha₂

/-- Hahn--Banach gives a nonzero supporting covector through every boundary
point of a convex body with nonempty interior. -/
theorem exists_supportLine_at_boundary
    {K : Set ConvexSupport.Point} (hconvex : Convex ℝ K)
    (hcompact : IsCompact K) (hinterior : (interior K).Nonempty)
    {x : ConvexSupport.Point} (hx : x ∈ frontier K) :
    ∃ n : ConvexSupport.Point, n ≠ 0 ∧
      ConvexSupport.IsSupportOffset K n
        (ConvexSupport.linearValue n x) := by
  have hxK : x ∈ K := by
    have := frontier_subset_closure hx
    simpa [hcompact.isClosed.closure_eq] using this
  have hxnot : x ∉ interior K :=
    (mem_frontier_iff_notMem_interior hxK).mp hx
  obtain ⟨f, hf, hbound⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point hconvex hxnot hinterior
  let n := dualNormal f
  have hn : n ≠ 0 := dualNormal_ne_zero hf
  refine ⟨n, hn, Or.inl ⟨x, hxK, rfl, ?_⟩⟩
  intro y hy
  rw [linearValue_dualNormal, linearValue_dualNormal]
  exact hbound y hy

/-- A nonzero support line has a contact point on the frontier of a compact
body with nonempty interior. -/
theorem exists_frontier_contact_of_support
    {K : Set ConvexSupport.Point}
    {n : ConvexSupport.Point} {r : ℝ} (hn : n ≠ 0)
    (hsupport : ConvexSupport.IsSupportOffset K n r) :
    ∃ x ∈ frontier K, ConvexSupport.linearValue n x = r := by
  rcases hsupport with hupper | hlower
  · obtain ⟨x, hxK, hxline, hbound⟩ := hupper
    have hxnot : x ∉ interior K := by
      intro hxint
      exact ConvexSupport.linearValue_lt_of_mem_interior_of_upper_bound
        hxint hn hbound hxline
    exact ⟨x, (mem_frontier_iff_notMem_interior hxK).mpr hxnot, hxline⟩
  · obtain ⟨x, hxK, hxline, hbound⟩ := hlower
    have hxnot : x ∉ interior K := by
      intro hxint
      exact ConvexSupport.linearValue_gt_of_mem_interior_of_lower_bound
        hxint hn hbound hxline
    exact ⟨x, (mem_frontier_iff_notMem_interior hxK).mpr hxnot, hxline⟩

/-- Algebraic tangents of a regular convex full level are support lines;
there is no separate geometric tangent hypothesis. -/
theorem tangent_is_support_of_regular_convex_level
    {P : MvPolynomial (Fin 3) ℝ} {d : ℕ}
    (hP : P.IsHomogeneous d)
    {K : Set ConvexSupport.Point} (hconvex : Convex ℝ K)
    (hcompact : IsCompact K) (hinterior : (interior K).Nonempty)
    (hlocus : frontier K =
      {x | MvPolynomial.eval ![1, x 0, x 1] P = 0})
    (hregular : ∀ x ∈ frontier K, RegularAt P ![1, x 0, x 1]) :
    ∀ {x : ConvexSupport.Point} {ell : Fin 3 → ℝ},
      x ∈ frontier K →
      (∃ b : ℝ, gradient P ![1, x 0, x 1] = b • ell) →
      ConvexSupport.IsSupportOffset K ![ell 1, ell 2] (-ell 0) := by
  intro x ell hx hparallel
  obtain ⟨n, hn, hsupport⟩ :=
    exists_supportLine_at_boundary hconvex hcompact hinterior hx
  let r := ConvexSupport.linearValue n x
  obtain ⟨a, ha, hgradient⟩ := gradient_eq_smul_supportLine
    hP hcompact hlocus hx (hregular x hx) hn hsupport rfl
  obtain ⟨b, hb⟩ := hparallel
  have hbne : b ≠ 0 := by
    intro hbzero
    apply (hregular x hx).2
    rw [hb, hbzero, zero_smul]
  let c : ℝ := a / b
  have hc : c ≠ 0 := div_ne_zero ha hbne
  let line : Fin 3 → ℝ := ![-r, n 0, n 1]
  have hell : ell = c • line := by
    funext i
    have hi := congrFun (hb.symm.trans hgradient) i
    change b * ell i = a * line i at hi
    calc
      ell i = (a * line i) / b := by
        apply (eq_div_iff hbne).2
        rw [mul_comm]
        exact hi
      _ = (a / b) * line i := by ring
  have hnormal : (![ell 1, ell 2] : ConvexSupport.Point) = c • n := by
    funext i
    fin_cases i
    · simpa [line] using congrFun hell (1 : Fin 3)
    · simpa [line] using congrFun hell (2 : Fin 3)
  have hoffset : -ell 0 = c * r := by
    have hzero := congrFun hell (0 : Fin 3)
    simp only [line, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero] at hzero
    rw [hzero]
    ring
  rw [hnormal, hoffset]
  exact ConvexSupport.isSupportOffset_smul hsupport hc

/-- Conversely, every nonzero support line of a regular convex full level is
the polynomial tangent at one of its frontier contact points. -/
theorem support_is_tangent_of_regular_convex_level
    {P : MvPolynomial (Fin 3) ℝ} {d : ℕ}
    (hP : P.IsHomogeneous d)
    {K : Set ConvexSupport.Point} (hcompact : IsCompact K)
    (hlocus : frontier K =
      {x | MvPolynomial.eval ![1, x 0, x 1] P = 0})
    (hregular : ∀ x ∈ frontier K, RegularAt P ![1, x 0, x 1]) :
    ∀ {n : ConvexSupport.Point} {r : ℝ},
      ConvexSupport.IsSupportOffset K n r → n ≠ 0 →
      ∃ x ∈ frontier K, ∃ a : ℝ, a ≠ 0 ∧
        gradient P ![1, x 0, x 1] = a • ![-r, n 0, n 1] := by
  intro n r hsupport hn
  obtain ⟨x, hx, hxline⟩ :=
    exists_frontier_contact_of_support hn hsupport
  obtain ⟨a, ha, hgradient⟩ := gradient_eq_smul_supportLine
    hP hcompact hlocus hx (hregular x hx) hn hsupport hxline
  exact ⟨x, hx, a, ha, hgradient⟩

end ConvexLevelSupport

end DiskRigidity.Algebraic
