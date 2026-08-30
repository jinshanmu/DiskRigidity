/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.AffineArcDensity
public import DiskRigidity.Algebraic.GaussPullback
public import DiskRigidity.Algebraic.PlaneGauss
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Global and local consequences of a contact arc

This file turns an explicit affine tangent/contact arc into the two algebraic
inputs used by the generic contact count: the global bidual divisor identity
and a local nonramification certificate.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace AnalyticContact

open Matrix MvPolynomial Set
open ProjectiveDual PlaneCurveSpecialization
open Filter
open scoped Topology

/-- Derivative of a multivariate polynomial evaluated along a real-analytic
path.  Using `deriv` avoids any choice of a presentation of the one-
dimensional normed-space structure on `ℝ`. -/
theorem deriv_eval_mvPolynomial
    (P : MvPolynomial (Fin 3) ℝ)
    {ell : ℝ → Fin 3 → ℝ} {t₀ : ℝ}
    (hell : ∀ i, AnalyticAt ℝ (fun t ↦ ell t i) t₀) :
    deriv (fun t ↦ MvPolynomial.eval (ell t) P) t₀ =
      directionalDerivative P (ell t₀)
        (fun i ↦ deriv (fun t ↦ ell t i) t₀) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [GaussPullback.directionalDerivative_C]
  | add P R hP hR =>
      have hPa : AnalyticAt ℝ (fun t ↦ MvPolynomial.eval (ell t) P) t₀ := by
        simpa [MvPolynomial.aeval_def] using
          (AnalyticAt.aeval_mvPolynomial hell P)
      have hRa : AnalyticAt ℝ (fun t ↦ MvPolynomial.eval (ell t) R) t₀ := by
        simpa [MvPolynomial.aeval_def] using
          (AnalyticAt.aeval_mvPolynomial hell R)
      rw [show (fun t ↦ MvPolynomial.eval (ell t) (P + R)) =
          (fun t ↦ MvPolynomial.eval (ell t) P +
            MvPolynomial.eval (ell t) R) by funext t; simp]
      calc
        deriv (fun t ↦ MvPolynomial.eval (ell t) P +
            MvPolynomial.eval (ell t) R) t₀ =
            deriv (fun t ↦ MvPolynomial.eval (ell t) P) t₀ +
              deriv (fun t ↦ MvPolynomial.eval (ell t) R) t₀ := by
                rw [show (fun t ↦ MvPolynomial.eval (ell t) P +
                    MvPolynomial.eval (ell t) R) =
                    (fun t ↦ MvPolynomial.eval (ell t) P) +
                      (fun t ↦ MvPolynomial.eval (ell t) R) by
                        funext t; rfl]
                exact deriv_add hPa.differentiableAt hRa.differentiableAt
        _ = directionalDerivative (P + R) (ell t₀)
            (fun i ↦ deriv (fun t ↦ ell t i) t₀) := by
              rw [hP, hR, GaussPullback.directionalDerivative_add]
  | mul_X P i hP =>
      have hPa : AnalyticAt ℝ (fun t ↦ MvPolynomial.eval (ell t) P) t₀ := by
        simpa [MvPolynomial.aeval_def] using
          (AnalyticAt.aeval_mvPolynomial hell P)
      rw [show (fun t ↦ MvPolynomial.eval (ell t) (P * MvPolynomial.X i)) =
          (fun t ↦ MvPolynomial.eval (ell t) P * ell t i) by
            funext t; simp]
      calc
        deriv (fun t ↦ MvPolynomial.eval (ell t) P * ell t i) t₀ =
            deriv (fun t ↦ MvPolynomial.eval (ell t) P) t₀ * ell t₀ i +
              MvPolynomial.eval (ell t₀) P *
                deriv (fun t ↦ ell t i) t₀ := by
                  rw [show (fun t ↦ MvPolynomial.eval (ell t) P * ell t i) =
                      (fun t ↦ MvPolynomial.eval (ell t) P) *
                        (fun t ↦ ell t i) by funext t; rfl]
                  exact deriv_mul hPa.differentiableAt
                    (hell i).differentiableAt
        _ = directionalDerivative (P * MvPolynomial.X i) (ell t₀)
            (fun i ↦ deriv (fun t ↦ ell t i) t₀) := by
              rw [hP, GaussPullback.directionalDerivative_mul,
                GaussPullback.directionalDerivative_X]
              simp [mul_comm]

/-- Vanishing on an analytic affine graph makes its ordinary velocity a
Zariski tangent vector. -/
theorem isTangentVector_of_analytic_graph_zero
    (P : MvPolynomial (Fin 3) ℝ) {U : Set ℝ}
    (hUopen : IsOpen U) (s : ℝ → ℝ) (hs : AnalyticOnNhd ℝ s U)
    (hzero : ∀ t ∈ U, MvPolynomial.eval ![s t, t, 1] P = 0)
    {t : ℝ} (ht : t ∈ U) :
    IsTangentVector P ![s t, t, 1] ![deriv s t, 1, 0] := by
  let ell : ℝ → Fin 3 → ℝ := fun u ↦ ![s u, u, 1]
  have hell : ∀ i, AnalyticAt ℝ (fun u ↦ ell u i) t := by
    intro i
    fin_cases i
    · exact hs t ht
    · exact analyticAt_id
    · exact analyticAt_const
  have hformula := deriv_eval_mvPolynomial P hell
  have hzeroNhd : (fun u ↦ MvPolynomial.eval (ell u) P) =ᶠ[𝓝 t]
      (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [hUopen.mem_nhds ht] with u hu
    exact hzero u hu
  have hderivZero : deriv (fun u ↦ MvPolynomial.eval (ell u) P) t = 0 := by
    rw [hzeroNhd.deriv_eq]
    simp
  rw [hformula] at hderivZero
  have hdell : (fun i ↦ deriv (fun u ↦ ell u i) t) =
      ![deriv s t, 1, 0] := by
    funext i
    fin_cases i <;> simp [ell]
  rw [hdell] at hderivZero
  exact hderivZero

theorem deriv_add_apply {f g : ℝ → ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t) :
    deriv (fun u ↦ f u + g u) t = deriv f t + deriv g t := by
  rw [show (fun u ↦ f u + g u) = f + g by funext u; rfl]
  exact deriv_add hf hg

theorem deriv_mul_apply {f g : ℝ → ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t) :
    deriv (fun u ↦ f u * g u) t =
      deriv f t * g t + f t * deriv g t := by
  rw [show (fun u ↦ f u * g u) = f * g by funext u; rfl]
  exact deriv_mul hf hg

/-- Differentiating the incidence equation shows that the line velocity is
incident with the contact point, once the line itself is incident with the
contact velocity.  Thus the conormal input to local biduality is derived
directly from the usual meaning of a moving tangent line. -/
theorem derivative_incidence_of_analytic_tangent_graph
    {U : Set ℝ} (hUopen : IsOpen U)
    (s : ℝ → ℝ) (hs : AnalyticOnNhd ℝ s U)
    (z : ℝ → Fin 3 → ℝ)
    (hz : ∀ i, AnalyticOnNhd ℝ (fun t ↦ z t i) U)
    (hincidence : ∀ t ∈ U, ![s t, t, 1] ⬝ᵥ z t = 0)
    {t : ℝ} (ht : t ∈ U)
    (htangent : ![s t, t, 1] ⬝ᵥ
      (fun i ↦ deriv (fun u ↦ z u i) t) = 0) :
    ![deriv s t, 1, 0] ⬝ᵥ z t = 0 := by
  let A : ℝ → ℝ := fun u ↦ s u * z u 0
  let B : ℝ → ℝ := fun u ↦ u * z u 1
  let C : ℝ → ℝ := fun u ↦ z u 2
  have hA : AnalyticAt ℝ A t := (hs t ht).mul (hz 0 t ht)
  have hB : AnalyticAt ℝ B t := analyticAt_id.mul (hz 1 t ht)
  have hC : AnalyticAt ℝ C t := hz 2 t ht
  have hzeroNhd : (fun u ↦ A u + B u + C u) =ᶠ[𝓝 t]
      (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [hUopen.mem_nhds ht] with u hu
    simpa [A, B, C, dotProduct, Fin.sum_univ_three] using hincidence u hu
  have hderivZero : deriv (fun u ↦ A u + B u + C u) t = 0 := by
    rw [hzeroNhd.deriv_eq]
    simp
  have hABdiff : DifferentiableAt ℝ (fun u ↦ A u + B u) t := by
    rw [show (fun u ↦ A u + B u) = A + B by funext u; rfl]
    exact hA.differentiableAt.add hB.differentiableAt
  rw [deriv_add_apply hABdiff hC.differentiableAt,
    deriv_add_apply hA.differentiableAt hB.differentiableAt] at hderivZero
  dsimp [A, B, C] at hderivZero
  rw [deriv_mul_apply (f := s) (g := fun u ↦ z u 0)
      (hs t ht).differentiableAt (hz 0 t ht).differentiableAt,
    deriv_mul_apply (f := fun u : ℝ ↦ u) (g := fun u ↦ z u 1)
      differentiableAt_id (hz 1 t ht).differentiableAt] at hderivZero
  have htangent' : s t * deriv (fun u ↦ z u 0) t +
      t * deriv (fun u ↦ z u 1) t + deriv (fun u ↦ z u 2) t = 0 := by
    simpa [dotProduct, Fin.sum_univ_three] using htangent
  simp only [deriv_id'', one_mul] at hderivZero
  have htwo : ![deriv s t, 1, 0] (2 : Fin 3) = (0 : ℝ) := by
    have h2 : (2 : Fin 3) = (1 : Fin 2).succ := by decide
    rw [h2, Matrix.cons_val_succ]
    have h1 : (1 : Fin 2) = (0 : Fin 1).succ := by decide
    rw [h1, Matrix.cons_val_succ, Matrix.cons_val_zero]
  simp only [dotProduct, Fin.sum_univ_three]
  rw [htwo, zero_mul, add_zero]
  norm_num
  linarith

/-- The Gauss differential is linear in its direction argument. -/
theorem gaussDifferential_smul_direction
    {K : Type*} [Field K] (Q : MvPolynomial (Fin 3) K)
    (ell dell : Fin 3 → K) (a : K) :
    gaussDifferential Q ell (a • dell) =
      a • gaussDifferential Q ell dell := by
  classical
  funext i
  simp only [gaussDifferential, directionalDerivative, dotProduct,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The position and velocity vectors of the affine graph
`t ↦ [s(t):t:1]` are automatically projectively independent. -/
theorem linearIndependent_affine_graph_frame (s t s' : ℝ) :
    LinearIndependent ℝ ![![s, t, 1], ![s', 1, 0]] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have ha : a = 0 := by
    simpa using congrFun hab (2 : Fin 3)
  have hb : b = 0 := by
    rw [ha] at hab
    simpa using congrFun hab (1 : Fin 3)
  exact ⟨ha, hb⟩

/-- A dense affine contact arc forces the bidual Gauss-pullback divisor
identity `Q ∣ F(∇Q)`. -/
theorem gradientPullback_dvd_of_contact_arc
    {F Q : MvPolynomial (Fin 3) ℝ} {d m : ℕ}
    (hF : F.IsHomogeneous d) (hQ : Q.IsHomogeneous m)
    (hQirr : Irreducible Q) (hm : m ≠ 0)
    (he : MvPolynomial.eval distinguishedPoint Q ≠ 0)
    {U : Set ℝ} (hUopen : IsOpen U) (hUnonempty : U.Nonempty)
    (s : ℝ → ℝ) (z : ℝ → Fin 3 → ℝ)
    (hQzero : ∀ t ∈ U, MvPolynomial.eval ![s t, t, 1] Q = 0)
    (hFzero : ∀ t ∈ U, MvPolynomial.eval (z t) F = 0)
    (hcontact : ∀ t ∈ U, ∃ a : ℝ,
      gradient Q ![s t, t, 1] = a • z t) :
    Q ∣ GaussPullback.gradientPullback F Q := by
  apply AffineArcDensity.dvd_of_vanishes_on_open_graph hQ
    (GaussPullback.gradientPullback_isHomogeneous hF hQ)
    hQirr hm he hUopen hUnonempty s hQzero
  intro t ht
  rw [GaussPullback.eval_gradientPullback]
  obtain ⟨a, ha⟩ := hcontact t ht
  rw [ha, eval_smul_of_isHomogeneous hF, hFzero t ht, mul_zero]

/-- The symmetric primal Gauss identity.  An open boundary graph
`[1:s(t):t]` whose tangent covectors lie on `Q` forces
`F ∣ Q(∇F)`.  This is the algebraic bridge used to prove that every support
line of the smooth oval lies on the globally selected dual component. -/
theorem gradientPullback_dvd_of_primal_contact_arc
    {F Q : MvPolynomial (Fin 3) ℝ} {d m : ℕ}
    (hF : F.IsHomogeneous d) (hQ : Q.IsHomogeneous m)
    (hFirr : Irreducible F) (hd : d ≠ 0)
    (he : MvPolynomial.eval ![0, 1, 0] F ≠ 0)
    {U : Set ℝ} (hUopen : IsOpen U) (hUnonempty : U.Nonempty)
    (s : ℝ → ℝ) (ell : ℝ → Fin 3 → ℝ)
    (hFzero : ∀ t ∈ U, MvPolynomial.eval ![1, s t, t] F = 0)
    (hQzero : ∀ t ∈ U, MvPolynomial.eval (ell t) Q = 0)
    (hcontact : ∀ t ∈ U, ∃ a : ℝ,
      gradient F ![1, s t, t] = a • ell t) :
    F ∣ GaussPullback.gradientPullback Q F := by
  apply AffineArcDensity.dvd_of_vanishes_on_open_first_chart hF
    (GaussPullback.gradientPullback_isHomogeneous hQ hF)
    hFirr hd he hUopen hUnonempty s hFzero
  intro t ht
  rw [GaussPullback.eval_gradientPullback]
  obtain ⟨a, ha⟩ := hcontact t ht
  rw [ha, eval_smul_of_isHomogeneous hQ, hQzero t ht, mul_zero]

/-- The same primal Gauss identity in the coordinate graph
`[1:t:p(t)]`.  This chart is the one naturally selected when the last
component of the tangent covector is nonzero. -/
theorem gradientPullback_dvd_of_primal_contact_second_chart
    {F Q : MvPolynomial (Fin 3) ℝ} {d m : ℕ}
    (hF : F.IsHomogeneous d) (hQ : Q.IsHomogeneous m)
    (hFirr : Irreducible F) (hd : d ≠ 0)
    (he : MvPolynomial.eval ![0, 0, 1] F ≠ 0)
    {U : Set ℝ} (hUopen : IsOpen U) (hUnonempty : U.Nonempty)
    (p : ℝ → ℝ) (ell : ℝ → Fin 3 → ℝ)
    (hFzero : ∀ t ∈ U, MvPolynomial.eval ![1, t, p t] F = 0)
    (hQzero : ∀ t ∈ U, MvPolynomial.eval (ell t) Q = 0)
    (hcontact : ∀ t ∈ U, ∃ a : ℝ,
      gradient F ![1, t, p t] = a • ell t) :
    F ∣ GaussPullback.gradientPullback Q F := by
  apply AffineArcDensity.dvd_of_vanishes_on_open_second_chart hF
    (GaussPullback.gradientPullback_isHomogeneous hQ hF)
    hFirr hd he hUopen hUnonempty p hFzero
  intro t ht
  rw [GaussPullback.eval_gradientPullback]
  obtain ⟨a, ha⟩ := hcontact t ht
  rw [ha, eval_smul_of_isHomogeneous hQ, hQzero t ht, mul_zero]

variable {K : Type*} [Field K]

/-- An invertible upper-triangular change of a linearly independent pair is
linearly independent. -/
theorem linearIndependent_contact_velocity
    {z dz : Fin 3 → K} {a b c : K}
    (hz : LinearIndependent K ![z, dz])
    (ha : a ≠ 0) (hc : c ≠ 0) :
    LinearIndependent K ![a • z, b • z + c • dz] := by
  rw [LinearIndependent.pair_iff] at hz ⊢
  intro r q hrq
  have hcomb : (r * a + q * b) • z + (q * c) • dz = 0 := by
    simpa only [smul_add, smul_smul, add_smul, add_assoc] using hrq
  obtain ⟨hfirst, hsecond⟩ := hz _ _ hcomb
  have hq : q = 0 := (mul_eq_zero.mp hsecond).resolve_right hc
  subst q
  simp only [zero_mul, add_zero] at hfirst
  have hr : r = 0 := (mul_eq_zero.mp hfirst).resolve_right ha
  exact ⟨hr, rfl⟩

/-- Explicit first-order contact motion gives a nonzero Gauss cross minor.
Here `z,dz` are a moving projective contact point and its nonradial velocity;
the two displayed equalities are precisely the differentiated contact/Gauss
relations. -/
theorem exists_gaussCross_ne_zero_of_moving_contact
    (Q : MvPolynomial (Fin 3) K) (ell z dz : Fin 3 → K)
    (a b c : K)
    (hcontact : gradient Q ell = a • z)
    (hvelocity : gaussDifferential Q ell
      (fun j ↦ MvPolynomial.eval ell
        (PlaneGauss.affineTangentPolynomial Q j)) =
      b • z + c • dz)
    (ha : a ≠ 0) (hc : c ≠ 0)
    (hmotion : LinearIndependent K ![z, dz]) :
    ∃ k : Fin 3,
      MvPolynomial.eval ell (PlaneGauss.gaussCrossPolynomial Q k) ≠ 0 := by
  have hLI : LinearIndependent K
      ![gradient Q ell,
        gaussDifferential Q ell
          (fun j ↦ MvPolynomial.eval ell
            (PlaneGauss.affineTangentPolynomial Q j))] := by
    rw [hcontact, hvelocity]
    exact linearIndependent_contact_velocity hmotion ha hc
  have hcross : gradient Q ell ⨯₃
      gaussDifferential Q ell
        (fun j ↦ MvPolynomial.eval ell
          (PlaneGauss.affineTangentPolynomial Q j)) ≠ 0 :=
    crossProduct_ne_zero_iff_linearIndependent.mpr hLI
  have hexists : ∃ k : Fin 3,
      (gradient Q ell ⨯₃
        gaussDifferential Q ell
          (fun j ↦ MvPolynomial.eval ell
            (PlaneGauss.affineTangentPolynomial Q j))) k ≠ 0 := by
    simpa only [ne_eq, funext_iff, not_forall, Pi.zero_apply] using hcross
  obtain ⟨k, hk⟩ := hexists
  refine ⟨k, ?_⟩
  rw [PlaneGauss.eval_gaussCrossPolynomial]
  exact hk

/-- The first-order jet of a smooth graph contact automatically supplies the
nonzero Gauss cross minor used in the generic contact count.  Compared with
`exists_gaussCross_ne_zero_of_moving_contact`, the tangent direction here is
the actual graph velocity `![s',1,0]`; the proof derives the polynomial
affine tangent and its contact velocity, including the nonzero scale. -/
theorem exists_gaussCross_ne_zero_of_firstOrder_graph_contact
    (Q : MvPolynomial (Fin 3) ℝ)
    (s t s' a a' : ℝ) (z dz : Fin 3 → ℝ)
    (hQdirection : IsTangentVector Q ![s, t, 1] ![s', 1, 0])
    (hcontact : gradient Q ![s, t, 1] = a • z)
    (hcontactVelocity : gaussDifferential Q ![s, t, 1] ![s', 1, 0] =
      a' • z + a • dz)
    (hpartial : MvPolynomial.eval ![s, t, 1]
      (MvPolynomial.pderiv 0 Q) ≠ 0)
    (ha : a ≠ 0)
    (hmotion : LinearIndependent ℝ ![z, dz]) :
    ∃ k : Fin 3, MvPolynomial.eval ![s, t, 1]
      (PlaneGauss.gaussCrossPolynomial Q k) ≠ 0 := by
  let ell : Fin 3 → ℝ := ![s, t, 1]
  let dell : Fin 3 → ℝ := ![s', 1, 0]
  let qₛ : ℝ := MvPolynomial.eval ell (MvPolynomial.pderiv 0 Q)
  have hdir : directionalDerivative Q ell dell = 0 := by
    exact hQdirection
  have hdir' : s' * MvPolynomial.eval ell (MvPolynomial.pderiv 0 Q) +
      MvPolynomial.eval ell (MvPolynomial.pderiv 1 Q) = 0 := by
    simpa [directionalDerivative, ProjectiveDual.gradient, dotProduct,
      Fin.sum_univ_three, dell] using hdir
  have htangent : (fun j ↦ MvPolynomial.eval ell
      (PlaneGauss.affineTangentPolynomial Q j)) = qₛ • dell := by
    funext j
    fin_cases j
    · simp [PlaneGauss.affineTangentPolynomial, qₛ, dell]
      linarith
    · simp [PlaneGauss.affineTangentPolynomial, qₛ, dell]
    · simp [PlaneGauss.affineTangentPolynomial, qₛ, dell]
  have hvelocity : gaussDifferential Q ell
      (fun j ↦ MvPolynomial.eval ell
        (PlaneGauss.affineTangentPolynomial Q j)) =
      (qₛ * a') • z + (qₛ * a) • dz := by
    rw [htangent, gaussDifferential_smul_direction, hcontactVelocity]
    simp [smul_add, smul_smul]
  apply exists_gaussCross_ne_zero_of_moving_contact Q ell z dz
    a (qₛ * a') (qₛ * a)
  · exact hcontact
  · exact hvelocity
  · exact ha
  · exact mul_ne_zero hpartial ha
  · exact hmotion

/-- An analytic moving contact point supplies the first-order contact
velocity automatically.  At a regular dual point the contact scale is the
first gradient coordinate because the primal representative is normalized by
`z₀ = 1`; differentiating this canonical equality gives the Gauss velocity.
-/
theorem exists_gaussCross_ne_zero_of_analytic_graph_contact
    (Q : MvPolynomial (Fin 3) ℝ)
    {U : Set ℝ} (hUopen : IsOpen U)
    (s : ℝ → ℝ) (hs : AnalyticOnNhd ℝ s U)
    (z : ℝ → Fin 3 → ℝ)
    (hz : ∀ i, AnalyticOnNhd ℝ (fun t ↦ z t i) U)
    (hzfirst : ∀ t ∈ U, z t 0 = 1)
    (hQzero : ∀ t ∈ U, MvPolynomial.eval ![s t, t, 1] Q = 0)
    (hcontact : ∀ t ∈ U, ∃ a : ℝ,
      gradient Q ![s t, t, 1] = a • z t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ U)
    (hregular : RegularAt Q ![s t₀, t₀, 1])
    (hmotion : LinearIndependent ℝ
      ![z t₀, fun i ↦ deriv (fun t ↦ z t i) t₀]) :
    ∃ k : Fin 3, MvPolynomial.eval ![s t₀, t₀, 1]
      (PlaneGauss.gaussCrossPolynomial Q k) ≠ 0 := by
  let ell : ℝ → Fin 3 → ℝ := fun t ↦ ![s t, t, 1]
  let a : ℝ → ℝ := fun t ↦
    MvPolynomial.eval (ell t) (MvPolynomial.pderiv 0 Q)
  let dz : Fin 3 → ℝ := fun i ↦ deriv (fun t ↦ z t i) t₀
  have hell : ∀ i, AnalyticAt ℝ (fun t ↦ ell t i) t₀ := by
    intro i
    fin_cases i
    · exact hs t₀ ht₀
    · exact analyticAt_id
    · exact analyticAt_const
  have haAnalytic : AnalyticAt ℝ a t₀ := by
    simpa [a, ell, MvPolynomial.aeval_def] using
      (AnalyticAt.aeval_mvPolynomial hell (MvPolynomial.pderiv 0 Q))
  have hcanonical : ∀ t ∈ U,
      gradient Q (ell t) = a t • z t := by
    intro t ht
    obtain ⟨b, hb⟩ := hcontact t ht
    have hbfirst := congrFun hb (0 : Fin 3)
    have hab : a t = b := by
      simpa [a, ell, ProjectiveDual.gradient, hzfirst t ht] using hbfirst
    rw [hab]
    exact hb
  have hdell : (fun i ↦ deriv (fun t ↦ ell t i) t₀) =
      ![deriv s t₀, 1, 0] := by
    funext i
    fin_cases i <;> simp [ell]
  have hvelocity : gaussDifferential Q (ell t₀)
      ![deriv s t₀, 1, 0] =
      deriv a t₀ • z t₀ + a t₀ • dz := by
    funext i
    have hleft := deriv_eval_mvPolynomial (MvPolynomial.pderiv i Q) hell
    rw [hdell] at hleft
    have hright := deriv_mul haAnalytic.differentiableAt
      (hz i t₀ ht₀).differentiableAt
    have hright' : deriv (fun t ↦ a t * z t i) t₀ =
        deriv a t₀ * z t₀ i + a t₀ * deriv (fun t ↦ z t i) t₀ := by
      rw [show (fun t ↦ a t * z t i) =
          a * (fun t ↦ z t i) by funext t; rfl]
      exact hright
    have heq : (fun t ↦ MvPolynomial.eval (ell t)
        (MvPolynomial.pderiv i Q)) =ᶠ[𝓝 t₀]
        (fun t ↦ a t * z t i) := by
      filter_upwards [hUopen.mem_nhds ht₀] with t ht
      exact congrFun (hcanonical t ht) i
    have hderivEq := heq.deriv_eq
    change directionalDerivative (MvPolynomial.pderiv i Q) (ell t₀)
        ![deriv s t₀, 1, 0] =
      deriv a t₀ * z t₀ i + a t₀ * dz i
    rw [← hleft, hderivEq]
    simpa [dz] using hright'
  have hpartial : a t₀ ≠ 0 := by
    intro ha0
    apply hregular.2
    rw [hcanonical t₀ ht₀, ha0, zero_smul]
  apply exists_gaussCross_ne_zero_of_firstOrder_graph_contact
    Q (s t₀) t₀ (deriv s t₀) (a t₀) (deriv a t₀) (z t₀) dz
  · exact isTangentVector_of_analytic_graph_zero Q hUopen s hs hQzero ht₀
  · exact hcanonical t₀ ht₀
  · exact hvelocity
  · exact hpartial
  · exact hpartial
  · exact hmotion

end AnalyticContact

end DiskRigidity.Algebraic
