/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.ConvexCauchyBoundary
public import DiskRigidity.Operator.FoundationGeometry
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Outer-parallel passage to the sharp numerical-range bound

This file formalizes the last paragraph of Proposition 3.2.  Once the
ordinary polynomial Cauchy formula is available on every compact convex
body with interior spectrum, the concrete double-layer construction on
closed thickenings of the numerical range yields the exact factor-two
polynomial bound, including boundary-spectrum and nonsmooth cases.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set Topology
open scoped BoundedContinuousFunction InnerProductSpace Matrix
  Matrix.Norms.L2Operator NNReal Pointwise

namespace DiskRigidity.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The sole residual analytic statement: the ordinary holomorphic
polynomial Cauchy formula on the concrete rectifiable boundary of every
compact convex body containing the spectrum in its interior. -/
def HasConvexBodyPolynomialCauchyFormula (A : SquareMatrix n) : Prop :=
  ∀ (K : Set ℂ) (c : ℂ), Convex ℝ K → c ∈ interior K → IsCompact K →
    spectrum ℂ A ⊆ interior K → ∀ q : Polynomial ℂ,
      polynomialRightResolventIntegral
          (mu := radialBoundaryArcLengthMeasure K c)
          (radialBoundaryParametrization K c)
          (radialOutwardUnitNormal K c)
          (convexBoundaryResolvent A K c) q =
        ((2 * Real.pi : ℝ) : ℂ) •
          euclideanOperator (polynomialEval q A)

/-- The ordinary convex-body Cauchy formula gives the normalized
double-layer estimate on that body. -/
theorem HasConvexBodyPolynomialCauchyFormula.norm_polynomialEval_le_two
    [Nonempty n]
    {A : SquareMatrix n} (hCauchy : HasConvexBodyPolynomialCauchyFormula A)
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hWA : numericalRange A ⊆ K)
    (hspectrum : spectrum ℂ A ⊆ interior K)
    (q : Polynomial ℂ) (hq : ∀ z ∈ K, ‖q.eval z‖ ≤ 1) :
    ‖polynomialEval q A‖ ≤ 2 := by
  exact norm_polynomialEval_le_two_of_convexBodyCauchy
    A hconv hc hcompact hWA hspectrum
      (hCauchy K c hconv hc hcompact hspectrum) q hq

/-- Outer parallel convex bodies tend to the numerical range strongly
enough to recover the exact sharp polynomial estimate. -/
theorem sharp_polynomial_bound_of_convexBodyPolynomialCauchy
    [Nonempty n]
    (A : SquareMatrix n) (hCauchy : HasConvexBodyPolynomialCauchyFormula A)
    (p : Polynomial ℂ) :
    ‖polynomialEval p A‖ ≤ 2 * maxPolynomialModulus A p := by
  let m := maxPolynomialModulus A p
  have hm : 0 ≤ m := maxPolynomialModulus_nonneg A p
  have happrox : ∀ δ : ℝ, 0 < δ →
      ‖polynomialEval p A‖ ≤ 2 * (m + δ) := by
    intro δ hδ
    let U : Set ℂ := {z | ‖p.eval z‖ < m + δ}
    have hUopen : IsOpen U :=
      isOpen_lt p.continuous.norm continuous_const
    have hWU : numericalRange A ⊆ U := by
      intro z hz
      exact (norm_eval_le_maxPolynomialModulus A p hz).trans_lt
        (lt_add_of_pos_right m hδ)
    obtain ⟨ε, hε, hthick⟩ :=
      (isCompact_numericalRange A).exists_cthickening_subset_open
        hUopen hWU
    let K := Metric.cthickening ε (numericalRange A)
    have hKcompact : IsCompact K := (isCompact_numericalRange A).cthickening
    have hKconv : Convex ℝ K := (numericalRange_convex A).cthickening ε
    have hWint : numericalRange A ⊆ interior K :=
      (self_subset_thickening hε (numericalRange A)).trans
        (thickening_subset_interior_cthickening ε (numericalRange A))
    obtain ⟨c, hcW⟩ := numericalRange_nonempty A
    have hc : c ∈ interior K := hWint hcW
    have hWA : numericalRange A ⊆ K := hWint.trans interior_subset
    have hspectrum : spectrum ℂ A ⊆ interior K :=
      (spectrum_subset_numericalRange A).trans hWint
    have hmδ : 0 < m + δ := lt_of_le_of_lt hm (lt_add_of_pos_right m hδ)
    let a : ℂ := (((m + δ)⁻¹ : ℝ) : ℂ)
    let q : Polynomial ℂ := a • p
    have ha : ‖a‖ = (m + δ)⁻¹ := by
      simp only [a, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hmδ)]
    have hq : ∀ z ∈ K, ‖q.eval z‖ ≤ 1 := by
      intro z hz
      have hpz : ‖p.eval z‖ ≤ m + δ := (hthick hz).le
      simp only [q, Polynomial.eval_smul, norm_smul, ha]
      calc
        (m + δ)⁻¹ * ‖p.eval z‖ ≤ (m + δ)⁻¹ * (m + δ) := by
          exact mul_le_mul_of_nonneg_left hpz (inv_nonneg.mpr hmδ.le)
        _ = 1 := inv_mul_cancel₀ hmδ.ne'
    have hqbound := hCauchy.norm_polynomialEval_le_two
      hKconv hc hKcompact hWA hspectrum q hq
    simp only [q, polynomialEval_smul, norm_smul, ha] at hqbound
    calc
      ‖polynomialEval p A‖ =
          (m + δ) * ((m + δ)⁻¹ * ‖polynomialEval p A‖) := by
        field_simp
      _ ≤ (m + δ) * 2 :=
        mul_le_mul_of_nonneg_left hqbound hmδ.le
      _ = 2 * (m + δ) := mul_comm _ _
  apply le_of_forall_pos_le_add
  intro ε hε
  have h := happrox (ε / 2) (half_pos hε)
  change ‖polynomialEval p A‖ ≤ 2 * m + ε
  nlinarith

end DiskRigidity.Operator
