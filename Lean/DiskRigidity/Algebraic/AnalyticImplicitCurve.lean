/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.AnalyticContact
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Analytic local graphs of regular affine plane curves

The analytic inverse-function theorem gives an analytic implicit function,
even though Mathlib's general implicit-function API currently only records
its differentiability class.  We specialize that construction to regular
affine zeros of a real multivariate polynomial.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace AnalyticImplicitCurve

open Filter Matrix MvPolynomial Set
open ProjectiveDual
open scoped Topology

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]

/-- The implicit function obtained from analytic implicit-function data is
analytic at its base parameter.  This is the analytic counterpart of the
`ContDiffAt` theorem in Mathlib. -/
theorem analyticAt_implicitFunction
    (φ : ImplicitFunctionData 𝕜 E F G)
    (hl : AnalyticAt 𝕜 φ.leftFun φ.pt)
    (hr : AnalyticAt 𝕜 φ.rightFun φ.pt) :
    AnalyticAt 𝕜 (φ.implicitFunction (φ.leftFun φ.pt))
      (φ.rightFun φ.pt) := by
  let e : E ≃L[𝕜] F × G :=
    φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv
      φ.range_leftDeriv φ.range_rightDeriv φ.isCompl_ker
  have hprod : AnalyticAt 𝕜 φ.prodFun φ.pt := by
    apply (hl.prod hr).congr
    filter_upwards with x
    exact (φ.prodFun_apply x).symm
  have hderiv : fderiv 𝕜 φ.prodFun φ.pt = (e : E →L[𝕜] F × G) := by
    exact φ.hasStrictFDerivAt.hasFDerivAt.fderiv
  have hinverse : AnalyticAt 𝕜 φ.toOpenPartialHomeomorph.symm
      (φ.leftFun φ.pt, φ.rightFun φ.pt) := by
    have h := φ.toOpenPartialHomeomorph.analyticAt_symm'
      φ.pt_mem_toOpenPartialHomeomorph_source
      (by
        rw [ImplicitFunctionData.toOpenPartialHomeomorph_coe]
        exact hprod)
      (by
        rw [ImplicitFunctionData.toOpenPartialHomeomorph_coe]
        exact hderiv)
    rw [φ.toOpenPartialHomeomorph_apply] at h
    exact h
  have hslice : AnalyticAt 𝕜
      (fun y : G ↦ (φ.leftFun φ.pt, y)) (φ.rightFun φ.pt) :=
    analyticAt_const.prod analyticAt_id
  have hcomp := hinverse.comp hslice
  apply hcomp.congr
  filter_upwards with y
  exact φ.implicitFunction_apply.symm

variable {E₁ E₂ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]

/-- Analyticity of the standard implicit function on a product domain. -/
theorem HasStrictFDerivAt.analyticAt_implicitFunctionOfProdDomain
    {u : E₁ × E₂} {f : E₁ × E₂ → F} {f' : E₁ × E₂ →L[𝕜] F}
    (hstrict : HasStrictFDerivAt f f' u)
    (hinv : (f' ∘L ContinuousLinearMap.inr 𝕜 E₁ E₂).IsInvertible)
    (hanalytic : AnalyticAt 𝕜 f u) :
    AnalyticAt 𝕜 (hstrict.implicitFunctionOfProdDomain hinv) u.1 := by
  let φ := hstrict.implicitFunctionDataOfProdDomain hinv
  have hpt : φ.pt = u := by
    exact hstrict.pt_implicitFunctionDataOfProdDomain hinv
  have hleft : φ.leftFun = f := by
    exact hstrict.leftFun_implicitFunctionDataOfProdDomain hinv
  have hright : φ.rightFun = Prod.fst := by
    exact hstrict.rightFun_implicitFunctionDataOfProdDomain hinv
  have hφ : AnalyticAt 𝕜 (φ.implicitFunction (φ.leftFun φ.pt))
      (φ.rightFun φ.pt) := by
    apply analyticAt_implicitFunction φ
    · rw [hleft, hpt]
      exact hanalytic
    · rw [hright, hpt]
      exact analyticAt_fst
  rw [hleft, hright, hpt] at hφ
  have hsnd : AnalyticAt 𝕜
      (fun x : E₁ ↦ (φ.implicitFunction (f u) x).2) u.1 := by
    exact analyticAt_snd.comp hφ
  apply hsnd.congr
  filter_upwards with x
  exact (congrFun hstrict.implicitFunctionOfProdDomain_def x).symm

section PlanePolynomial

/-- The affine evaluation of a homogeneous plane polynomial, with `Y` as
the independent coordinate and `X` as the dependent coordinate. -/
noncomputable def affineEvalYX (P : MvPolynomial (Fin 3) ℝ) : ℝ × ℝ → ℝ :=
  fun q ↦ MvPolynomial.eval ![1, q.2, q.1] P

theorem analyticAt_affineEvalYX (P : MvPolynomial (Fin 3) ℝ) (q : ℝ × ℝ) :
    AnalyticAt ℝ (affineEvalYX P) q := by
  unfold affineEvalYX
  apply AnalyticAt.aeval_mvPolynomial
  intro i
  fin_cases i
  · exact analyticAt_const
  · exact analyticAt_snd
  · exact analyticAt_fst

/-- The derivative in the dependent `X` coordinate is the `X` partial of
the projective polynomial. -/
theorem deriv_affineEvalYX_snd (P : MvPolynomial (Fin 3) ℝ)
    (y x : ℝ) :
    deriv (fun u ↦ affineEvalYX P (y, u)) x =
      gradient P ![1, x, y] 1 := by
  let ell : ℝ → Fin 3 → ℝ := fun u ↦ ![1, u, y]
  have hell : ∀ i, AnalyticAt ℝ (fun u ↦ ell u i) x := by
    intro i
    fin_cases i
    · exact analyticAt_const
    · exact analyticAt_id
    · exact analyticAt_const
  rw [show (fun u ↦ affineEvalYX P (y, u)) =
      (fun u ↦ MvPolynomial.eval (ell u) P) by rfl]
  rw [AnalyticContact.deriv_eval_mvPolynomial P hell]
  simp [directionalDerivative, dotProduct, Fin.sum_univ_three, ell]

/-- The partial Fréchet derivative in `X` is scalar multiplication by the
evaluated `X` partial. -/
theorem fderiv_comp_inr_affineEvalYX (P : MvPolynomial (Fin 3) ℝ)
    (y x : ℝ) :
    fderiv ℝ (affineEvalYX P) (y, x) ∘L
        ContinuousLinearMap.inr ℝ ℝ ℝ =
      (1 : ℝ →L[ℝ] ℝ).smulRight (gradient P ![1, x, y] 1) := by
  ext
  have hf := (analyticAt_affineEvalYX P (y, x)).hasStrictFDerivAt.hasFDerivAt
  have hline : HasFDerivAt (fun u : ℝ ↦ (y, u))
      (ContinuousLinearMap.inr ℝ ℝ ℝ) x :=
    (hasFDerivAt_const y x).prodMk (hasFDerivAt_id x)
  have hcomp := hf.comp x hline
  have hderiv : deriv (fun u ↦ affineEvalYX P (y, u)) x =
      (fderiv ℝ (affineEvalYX P) (y, x) ∘L
        ContinuousLinearMap.inr ℝ ℝ ℝ) 1 := by
    rw [show (fun u ↦ affineEvalYX P (y, u)) =
      affineEvalYX P ∘ Prod.mk y by funext u; rfl]
    exact hcomp.hasDerivAt.deriv
  rw [deriv_affineEvalYX_snd] at hderiv
  simpa [ContinuousLinearMap.smulRight_apply] using hderiv.symm

/-- A nonzero affine `X` partial makes the product-domain implicit function
available. -/
theorem isInvertible_fderiv_comp_inr_affineEvalYX
    (P : MvPolynomial (Fin 3) ℝ) (y x : ℝ)
    (hx : gradient P ![1, x, y] 1 ≠ 0) :
    (fderiv ℝ (affineEvalYX P) (y, x) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
  rw [fderiv_comp_inr_affineEvalYX]
  let u : ℝˣ := Units.mk0 (gradient P ![1, x, y] 1) hx
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ u, ?_⟩
  ext
  simp [u, ContinuousLinearMap.smulRight_apply]

/-- A regular zero with nonzero `X` partial has a genuine analytic graph
`[1,p(t),t]` on an open interval.  The interval and all equations are
constructed, rather than supplied as geometric input. -/
theorem exists_open_analytic_graph_of_pderiv_one_ne_zero
    (P : MvPolynomial (Fin 3) ℝ) (x₀ y₀ : ℝ)
    (hzero : MvPolynomial.eval ![1, x₀, y₀] P = 0)
    (hx : gradient P ![1, x₀, y₀] 1 ≠ 0) :
    ∃ (U : Set ℝ) (p : ℝ → ℝ),
      IsOpen U ∧ y₀ ∈ U ∧
      AnalyticOnNhd ℝ p U ∧ p y₀ = x₀ ∧
      ∀ t ∈ U, MvPolynomial.eval ![1, p t, t] P = 0 := by
  let f := affineEvalYX P
  have hf : AnalyticAt ℝ f (y₀, x₀) := analyticAt_affineEvalYX P (y₀, x₀)
  let f' := fderiv ℝ f (y₀, x₀)
  have hstrict : HasStrictFDerivAt f f' (y₀, x₀) := hf.hasStrictFDerivAt
  have hinv : (f' ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible :=
    isInvertible_fderiv_comp_inr_affineEvalYX P y₀ x₀ hx
  let p : ℝ → ℝ := hstrict.implicitFunctionOfProdDomain hinv
  have hpAt : AnalyticAt ℝ p y₀ :=
    HasStrictFDerivAt.analyticAt_implicitFunctionOfProdDomain
      hstrict hinv hf
  have hpSelf : p y₀ = x₀ := by
    exact eq_of_tendsto_nhds (hstrict.tendsto_implicitFunctionOfProdDomain hinv)
  have hzeroEventually : ∀ᶠ t in 𝓝 y₀,
      MvPolynomial.eval ![1, p t, t] P = 0 := by
    have h := hstrict.eventually_apply_implicitFunctionOfProdDomain hinv
    filter_upwards [h] with t ht
    simpa [f, affineEvalYX, hzero] using ht
  have hgood : {t | AnalyticAt ℝ p t} ∩
      {t | MvPolynomial.eval ![1, p t, t] P = 0} ∈ 𝓝 y₀ :=
    inter_mem hpAt.eventually_analyticAt hzeroEventually
  obtain ⟨U, hUsub, hUopen, hy₀⟩ := mem_nhds_iff.mp hgood
  refine ⟨U, p, hUopen, hy₀, ?_, hpSelf, ?_⟩
  · intro t ht
    exact (hUsub ht).1
  · intro t ht
    exact (hUsub ht).2

/-- The affine evaluation with `X` independent and `Y` dependent. -/
noncomputable def affineEvalXY (P : MvPolynomial (Fin 3) ℝ) : ℝ × ℝ → ℝ :=
  fun q ↦ MvPolynomial.eval ![1, q.1, q.2] P

theorem analyticAt_affineEvalXY (P : MvPolynomial (Fin 3) ℝ) (q : ℝ × ℝ) :
    AnalyticAt ℝ (affineEvalXY P) q := by
  unfold affineEvalXY
  apply AnalyticAt.aeval_mvPolynomial
  intro i
  fin_cases i
  · exact analyticAt_const
  · exact analyticAt_fst
  · exact analyticAt_snd

theorem deriv_affineEvalXY_snd (P : MvPolynomial (Fin 3) ℝ)
    (x y : ℝ) :
    deriv (fun u ↦ affineEvalXY P (x, u)) y =
      gradient P ![1, x, y] 2 := by
  let ell : ℝ → Fin 3 → ℝ := fun u ↦ ![1, x, u]
  have hell : ∀ i, AnalyticAt ℝ (fun u ↦ ell u i) y := by
    intro i
    fin_cases i
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_id
  rw [show (fun u ↦ affineEvalXY P (x, u)) =
      (fun u ↦ MvPolynomial.eval (ell u) P) by rfl]
  rw [AnalyticContact.deriv_eval_mvPolynomial P hell]
  simp [directionalDerivative, dotProduct, Fin.sum_univ_three, ell]

theorem fderiv_comp_inr_affineEvalXY (P : MvPolynomial (Fin 3) ℝ)
    (x y : ℝ) :
    fderiv ℝ (affineEvalXY P) (x, y) ∘L
        ContinuousLinearMap.inr ℝ ℝ ℝ =
      (1 : ℝ →L[ℝ] ℝ).smulRight (gradient P ![1, x, y] 2) := by
  ext
  have hf := (analyticAt_affineEvalXY P (x, y)).hasStrictFDerivAt.hasFDerivAt
  have hline : HasFDerivAt (fun u : ℝ ↦ (x, u))
      (ContinuousLinearMap.inr ℝ ℝ ℝ) y :=
    (hasFDerivAt_const x y).prodMk (hasFDerivAt_id y)
  have hcomp := hf.comp y hline
  have hderiv : deriv (fun u ↦ affineEvalXY P (x, u)) y =
      (fderiv ℝ (affineEvalXY P) (x, y) ∘L
        ContinuousLinearMap.inr ℝ ℝ ℝ) 1 := by
    rw [show (fun u ↦ affineEvalXY P (x, u)) =
      affineEvalXY P ∘ Prod.mk x by funext u; rfl]
    exact hcomp.hasDerivAt.deriv
  rw [deriv_affineEvalXY_snd] at hderiv
  simpa [ContinuousLinearMap.smulRight_apply] using hderiv.symm

theorem isInvertible_fderiv_comp_inr_affineEvalXY
    (P : MvPolynomial (Fin 3) ℝ) (x y : ℝ)
    (hy : gradient P ![1, x, y] 2 ≠ 0) :
    (fderiv ℝ (affineEvalXY P) (x, y) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
  rw [fderiv_comp_inr_affineEvalXY]
  let u : ℝˣ := Units.mk0 (gradient P ![1, x, y] 2) hy
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ u, ?_⟩
  ext
  simp [u, ContinuousLinearMap.smulRight_apply]

/-- Symmetric local graph `[1,t,p(t)]` when the `Y` partial is nonzero. -/
theorem exists_open_analytic_graph_of_pderiv_two_ne_zero
    (P : MvPolynomial (Fin 3) ℝ) (x₀ y₀ : ℝ)
    (hzero : MvPolynomial.eval ![1, x₀, y₀] P = 0)
    (hy : gradient P ![1, x₀, y₀] 2 ≠ 0) :
    ∃ (U : Set ℝ) (p : ℝ → ℝ),
      IsOpen U ∧ x₀ ∈ U ∧
      AnalyticOnNhd ℝ p U ∧ p x₀ = y₀ ∧
      ∀ t ∈ U, MvPolynomial.eval ![1, t, p t] P = 0 := by
  let f := affineEvalXY P
  have hf : AnalyticAt ℝ f (x₀, y₀) := analyticAt_affineEvalXY P (x₀, y₀)
  let f' := fderiv ℝ f (x₀, y₀)
  have hstrict : HasStrictFDerivAt f f' (x₀, y₀) := hf.hasStrictFDerivAt
  have hinv : (f' ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible :=
    isInvertible_fderiv_comp_inr_affineEvalXY P x₀ y₀ hy
  let p : ℝ → ℝ := hstrict.implicitFunctionOfProdDomain hinv
  have hpAt : AnalyticAt ℝ p x₀ :=
    HasStrictFDerivAt.analyticAt_implicitFunctionOfProdDomain
      hstrict hinv hf
  have hpSelf : p x₀ = y₀ := by
    exact eq_of_tendsto_nhds (hstrict.tendsto_implicitFunctionOfProdDomain hinv)
  have hzeroEventually : ∀ᶠ t in 𝓝 x₀,
      MvPolynomial.eval ![1, t, p t] P = 0 := by
    have h := hstrict.eventually_apply_implicitFunctionOfProdDomain hinv
    filter_upwards [h] with t ht
    simpa [f, affineEvalXY, hzero] using ht
  have hgood : {t | AnalyticAt ℝ p t} ∩
      {t | MvPolynomial.eval ![1, t, p t] P = 0} ∈ 𝓝 x₀ :=
    inter_mem hpAt.eventually_analyticAt hzeroEventually
  obtain ⟨U, hUsub, hUopen, hx₀⟩ := mem_nhds_iff.mp hgood
  refine ⟨U, p, hUopen, hx₀, ?_, hpSelf, ?_⟩
  · intro t ht
    exact (hUsub ht).1
  · intro t ht
    exact (hUsub ht).2

/-- At an affine regular zero of a homogeneous plane curve, one of the two
affine partials is nonzero. -/
theorem pderiv_one_ne_zero_or_pderiv_two_ne_zero
    {P : MvPolynomial (Fin 3) ℝ} {d : ℕ}
    (hP : P.IsHomogeneous d) {x y : ℝ}
    (hregular : RegularAt P ![1, x, y]) :
    gradient P ![1, x, y] 1 ≠ 0 ∨
      gradient P ![1, x, y] 2 ≠ 0 := by
  by_cases h₁ : gradient P ![1, x, y] 1 ≠ 0
  · exact Or.inl h₁
  · right
    intro h₂
    have h₁zero : gradient P ![1, x, y] 1 = 0 := not_ne_iff.mp h₁
    have hdot := dot_gradient_eq_zero hP hregular.1.2
    have h₀zero : gradient P ![1, x, y] 0 = 0 := by
      simpa [dotProduct, Fin.sum_univ_three, h₁zero, h₂] using hdot
    apply hregular.2
    funext i
    fin_cases i
    · exact h₀zero
    · exact h₁zero
    · exact h₂

/-- A regular affine zero lying in an ambient open set generates a
nontrivial connected analytic coordinate graph which stays in that open
set.  The disjunction merely records which affine partial is nonzero. -/
theorem exists_connected_analytic_coordinate_graph_in_open
    {P : MvPolynomial (Fin 3) ℝ} {d : ℕ}
    (hP : P.IsHomogeneous d) {x₀ y₀ : ℝ}
    (hregular : RegularAt P ![1, x₀, y₀])
    {W : Set (Fin 2 → ℝ)} (hWopen : IsOpen W)
    (hW : ![x₀, y₀] ∈ W) :
    (∃ (U : Set ℝ) (p : ℝ → ℝ),
      IsOpen U ∧ U.Nonempty ∧ IsPreconnected U ∧
      AnalyticOnNhd ℝ p U ∧
      ∀ t ∈ U, ![p t, t] ∈ W ∧
        MvPolynomial.eval ![1, p t, t] P = 0 ∧
        gradient P ![1, p t, t] 1 ≠ 0) ∨
    (∃ (U : Set ℝ) (p : ℝ → ℝ),
      IsOpen U ∧ U.Nonempty ∧ IsPreconnected U ∧
      AnalyticOnNhd ℝ p U ∧
      ∀ t ∈ U, ![t, p t] ∈ W ∧
        MvPolynomial.eval ![1, t, p t] P = 0 ∧
        gradient P ![1, t, p t] 2 ≠ 0) := by
  rcases pderiv_one_ne_zero_or_pderiv_two_ne_zero hP hregular with h₁ | h₂
  · left
    obtain ⟨U₀, p, hU₀open, hy₀, hp, hp₀, hzero⟩ :=
      exists_open_analytic_graph_of_pderiv_one_ne_zero P x₀ y₀
        hregular.1.2 h₁
    have hzAt : ContinuousAt (fun t : ℝ ↦ ![p t, t]) y₀ := by
      rw [continuousAt_pi]
      intro i
      fin_cases i
      · exact (hp y₀ hy₀).continuousAt
      · exact continuousAt_id
    have hz₀ : (fun t : ℝ ↦ ![p t, t]) y₀ = ![x₀, y₀] := by
      simp [hp₀]
    have hgAt : ContinuousAt
        (fun t : ℝ ↦ gradient P ![1, p t, t] 1) y₀ := by
      have hg : AnalyticAt ℝ
          (fun t : ℝ ↦ ProjectiveDual.gradient P ![1, p t, t] 1) y₀ := by
        unfold ProjectiveDual.gradient
        apply AnalyticAt.aeval_mvPolynomial
        intro i
        fin_cases i
        · exact analyticAt_const
        · exact hp y₀ hy₀
        · exact analyticAt_id
      exact hg.continuousAt
    have hg₀ : gradient P ![1, p y₀, y₀] 1 ≠ 0 := by
      simpa [hp₀] using h₁
    have hgood :
        (U₀ ∩ (fun t : ℝ ↦ ![p t, t]) ⁻¹' W) ∩
          {t | gradient P ![1, p t, t] 1 ≠ 0} ∈ 𝓝 y₀ := by
      apply inter_mem
      · apply inter_mem (hU₀open.mem_nhds hy₀)
        apply hzAt
        rw [hz₀]
        exact hWopen.mem_nhds hW
      · exact hgAt.eventually_ne hg₀
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgood
    refine ⟨Metric.ball y₀ ε, p, Metric.isOpen_ball,
      ⟨y₀, Metric.mem_ball_self hε⟩, Metric.isPreconnected_ball,
      hp.mono (hball.trans (inter_subset_left.trans inter_subset_left)), ?_⟩
    intro t ht
    have htg := hball ht
    exact ⟨htg.1.2, hzero t htg.1.1, htg.2⟩
  · right
    obtain ⟨U₀, p, hU₀open, hx₀, hp, hp₀, hzero⟩ :=
      exists_open_analytic_graph_of_pderiv_two_ne_zero P x₀ y₀
        hregular.1.2 h₂
    have hzAt : ContinuousAt (fun t : ℝ ↦ ![t, p t]) x₀ := by
      rw [continuousAt_pi]
      intro i
      fin_cases i
      · exact continuousAt_id
      · exact (hp x₀ hx₀).continuousAt
    have hz₀ : (fun t : ℝ ↦ ![t, p t]) x₀ = ![x₀, y₀] := by
      simp [hp₀]
    have hgAt : ContinuousAt
        (fun t : ℝ ↦ gradient P ![1, t, p t] 2) x₀ := by
      have hg : AnalyticAt ℝ
          (fun t : ℝ ↦ ProjectiveDual.gradient P ![1, t, p t] 2) x₀ := by
        unfold ProjectiveDual.gradient
        apply AnalyticAt.aeval_mvPolynomial
        intro i
        fin_cases i
        · exact analyticAt_const
        · exact analyticAt_id
        · exact hp x₀ hx₀
      exact hg.continuousAt
    have hg₀ : gradient P ![1, x₀, p x₀] 2 ≠ 0 := by
      simpa [hp₀] using h₂
    have hgood :
        (U₀ ∩ (fun t : ℝ ↦ ![t, p t]) ⁻¹' W) ∩
          {t | gradient P ![1, t, p t] 2 ≠ 0} ∈ 𝓝 x₀ := by
      apply inter_mem
      · apply inter_mem (hU₀open.mem_nhds hx₀)
        apply hzAt
        rw [hz₀]
        exact hWopen.mem_nhds hW
      · exact hgAt.eventually_ne hg₀
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgood
    refine ⟨Metric.ball x₀ ε, p, Metric.isOpen_ball,
      ⟨x₀, Metric.mem_ball_self hε⟩, Metric.isPreconnected_ball,
      hp.mono (hball.trans (inter_subset_left.trans inter_subset_left)), ?_⟩
    intro t ht
    have htg := hball ht
    exact ⟨htg.1.2, hzero t htg.1.1, htg.2⟩

end PlanePolynomial

end AnalyticImplicitCurve

end DiskRigidity.Algebraic
