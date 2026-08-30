/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib

/-!
# Real conics through the circular points

This file formalizes the last algebraic step of Proposition 7.1.  A real
homogeneous conic passing through `[1 : i : 0]` (and hence also its conjugate)
has equal `X²` and `Y²` coefficients and no `XY` term.  Its affine real
locus is therefore a circle after completing squares.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace Conic

/-- Coefficients of a real homogeneous quadratic polynomial in `X,Y,Z`.
The mixed terms occur without a factor of two. -/
structure Form where
  /-- Coefficient of `X²`. -/
  xx : ℝ
  /-- Coefficient of `XY`. -/
  xy : ℝ
  /-- Coefficient of `Y²`. -/
  yy : ℝ
  /-- Coefficient of `XZ`. -/
  xz : ℝ
  /-- Coefficient of `YZ`. -/
  yz : ℝ
  /-- Coefficient of `Z²`. -/
  zz : ℝ

/-- Evaluation of a real conic after extension of scalars to `ℂ`. -/
def Form.evalComplex (q : Form) (X Y Z : ℂ) : ℂ :=
  q.xx * X ^ 2 + q.xy * X * Y + q.yy * Y ^ 2 +
    q.xz * X * Z + q.yz * Y * Z + q.zz * Z ^ 2

/-- Affine real evaluation, i.e. the chart `Z=1`. -/
def Form.evalAffine (q : Form) (x y : ℝ) : ℝ :=
  q.xx * x ^ 2 + q.xy * x * y + q.yy * y ^ 2 +
    q.xz * x + q.yz * y + q.zz

/-- Vanishing at one circular point forces the Euclidean quadratic part. -/
theorem eval_circularPoint_eq_zero_iff (q : Form) :
    q.evalComplex 1 Complex.I 0 = 0 ↔ q.yy = q.xx ∧ q.xy = 0 := by
  constructor
  · intro h
    have hre := congr_arg Complex.re h
    have him := congr_arg Complex.im h
    simp [Form.evalComplex, Complex.I_sq] at hre him
    constructor <;> linarith
  · rintro ⟨hyy, hxy⟩
    simp [Form.evalComplex, hyy, hxy, Complex.I_sq]

/-- A real conic through one circular point also passes through its conjugate. -/
theorem eval_conjugateCircularPoint_eq_zero (q : Form)
    (h : q.evalComplex 1 Complex.I 0 = 0) :
    q.evalComplex 1 (-Complex.I) 0 = 0 := by
  rw [eval_circularPoint_eq_zero_iff] at h
  rcases h with ⟨hyy, hxy⟩
  simp [Form.evalComplex, hyy, hxy, Complex.I_sq]

/-- The center in the `x` coordinate after completing squares. -/
noncomputable def Form.centerX (q : Form) : ℝ := -q.xz / (2 * q.xx)

/-- The center in the `y` coordinate after completing squares. -/
noncomputable def Form.centerY (q : Form) : ℝ := -q.yz / (2 * q.xx)

/-- The squared radius after completing squares. -/
noncomputable def Form.radiusSq (q : Form) : ℝ :=
  (q.xz ^ 2 + q.yz ^ 2) / (4 * q.xx ^ 2) - q.zz / q.xx

/-- Completing squares for a conic with Euclidean quadratic part. -/
theorem evalAffine_eq_circleExpression (q : Form)
    (hxx : q.xx ≠ 0) (hyy : q.yy = q.xx) (hxy : q.xy = 0) (x y : ℝ) :
    q.evalAffine x y = q.xx *
      ((x - q.centerX) ^ 2 + (y - q.centerY) ^ 2 - q.radiusSq) := by
  rw [Form.evalAffine, Form.centerX, Form.centerY, Form.radiusSq, hyy, hxy]
  field_simp [hxx]
  ring

/-- The affine zero set of such a conic is exactly a Euclidean circle
equation. -/
theorem evalAffine_eq_zero_iff_circle (q : Form)
    (hxx : q.xx ≠ 0) (hyy : q.yy = q.xx) (hxy : q.xy = 0) (x y : ℝ) :
    q.evalAffine x y = 0 ↔
      (x - q.centerX) ^ 2 + (y - q.centerY) ^ 2 = q.radiusSq := by
  rw [evalAffine_eq_circleExpression q hxx hyy hxy]
  constructor
  · intro h
    have : (x - q.centerX) ^ 2 + (y - q.centerY) ^ 2 - q.radiusSq = 0 :=
      (mul_eq_zero.mp h).resolve_left hxx
    linarith
  · intro h
    apply mul_eq_zero.mpr
    right
    linarith

/-- A nonempty real affine locus has nonnegative squared radius. -/
theorem radiusSq_nonneg_of_evalAffine_eq_zero (q : Form)
    (hxx : q.xx ≠ 0) (hyy : q.yy = q.xx) (hxy : q.xy = 0)
    {x y : ℝ} (h : q.evalAffine x y = 0) :
    0 ≤ q.radiusSq := by
  rw [evalAffine_eq_zero_iff_circle q hxx hyy hxy] at h
  rw [← h]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

end Conic

end DiskRigidity.Algebraic
