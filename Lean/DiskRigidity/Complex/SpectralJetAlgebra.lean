/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.SpectralJets

/-!
# Algebra laws for the finite spectral-jet calculus

Hermite interpolation agrees with the prescribed analytic jet at every root
of the characteristic polynomial.  Consequently spectral-jet evaluation is
multiplicative, and hence preserves powers, for functions analytic at those
roots.
-/

noncomputable section

open Function Set
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Complex

@[expose] public section

open Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The canonical Hermite polynomial representing a function at a matrix. -/
def spectralJetPolynomial (A : Operator.SquareMatrix n) (f : ℂ → ℂ) : ℂ[X] :=
  hermiteInterpolate A.charpoly (holomorphicHermiteData A.charpoly f)

theorem spectralJetEval_eq_polynomialEval
    (A : Operator.SquareMatrix n) (f : ℂ → ℂ) :
    spectralJetEval A f = Operator.polynomialEval (spectralJetPolynomial A f) A :=
  rfl

/-- Constant scalar multiplication is preserved by spectral-jet evaluation. -/
theorem spectralJetEval_const_mul
    (A : Operator.SquareMatrix n) (c : ℂ) (f : ℂ → ℂ) :
    spectralJetEval A (fun z ↦ c * f z) = c • spectralJetEval A f := by
  simp only [spectralJetEval_eq_sum, holomorphicHermiteData,
    iteratedDeriv_const_mul_field, mul_div_assoc]
  simp only [Finset.smul_sum, smul_smul]

/-- Division by a nonzero scalar is preserved by spectral-jet evaluation. -/
theorem spectralJetEval_div_const
    (A : Operator.SquareMatrix n) (f : ℂ → ℂ) (c : ℂ) :
    spectralJetEval A (fun z ↦ f z / c) = c⁻¹ • spectralJetEval A f := by
  simpa [div_eq_inv_mul] using spectralJetEval_const_mul A c⁻¹ f

/-- Hermite interpolation has the prescribed Hasse derivative at each root. -/
theorem hasseDeriv_eval_spectralJetPolynomial
    (A : Operator.SquareMatrix n) (f : ℂ → ℂ)
    (a : HermiteRoot A.charpoly) {k : ℕ}
    (hk : k < A.charpoly.rootMultiplicity (a : ℂ)) :
    (hasseDeriv k (spectralJetPolynomial A f)).eval (a : ℂ) =
      holomorphicHermiteData A.charpoly f a ⟨k, hk⟩ := by
  have hmem := hermiteInterpolate_sub_local_mem A.charpoly
    (holomorphicHermiteData A.charpoly f) a
  have hdiv : (X - C (a : ℂ)) ^ A.charpoly.rootMultiplicity (a : ℂ) ∣
      spectralJetPolynomial A f -
        hermiteLocalPolynomial A.charpoly
          (holomorphicHermiteData A.charpoly f) a := by
    exact Ideal.mem_span_singleton.mp hmem
  have heq := (X_sub_C_pow_dvd_sub_iff_hasseDeriv_eval_eq
    (spectralJetPolynomial A f)
    (hermiteLocalPolynomial A.charpoly
      (holomorphicHermiteData A.charpoly f) a)
    (a : ℂ) (A.charpoly.rootMultiplicity (a : ℂ))).mp hdiv k hk
  exact heq.trans (hasseDeriv_eval_hermiteLocalPolynomial A.charpoly
    (holomorphicHermiteData A.charpoly f) a hk)

/-- The canonical Hermite polynomial and the represented analytic function
have identical iterated derivatives through the characteristic multiplicity. -/
theorem iteratedDeriv_spectralJetPolynomial_eval
    (A : Operator.SquareMatrix n) {f : ℂ → ℂ}
    (a : HermiteRoot A.charpoly) {k : ℕ}
    (hk : k < A.charpoly.rootMultiplicity (a : ℂ)) :
    iteratedDeriv k (fun z ↦ (spectralJetPolynomial A f).eval z) (a : ℂ) =
      iteratedDeriv k f (a : ℂ) := by
  rw [iteratedDeriv_polynomial_eval]
  have hfac := congrArg (fun q : ℂ[X] ↦ q.eval (a : ℂ))
    (congrFun (Polynomial.factorial_smul_hasseDeriv k)
      (spectralJetPolynomial A f))
  have hfac' : (k.factorial : ℂ) *
      (hasseDeriv k (spectralJetPolynomial A f)).eval (a : ℂ) =
      (derivative^[k] (spectralJetPolynomial A f)).eval (a : ℂ) := by
    simpa [smul_eq_mul] using hfac
  change (derivative^[k] (spectralJetPolynomial A f)).eval (a : ℂ) = _
  rw [← hfac', hasseDeriv_eval_spectralJetPolynomial A f a hk,
    holomorphicHermiteData]
  have hkfac : (k.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  field_simp

/-- Multiplicativity of the finite spectral-jet functional calculus. -/
theorem spectralJetEval_mul
    (A : Operator.SquareMatrix n) {f g : ℂ → ℂ}
    (hf : ∀ a : HermiteRoot A.charpoly, AnalyticAt ℂ f (a : ℂ))
    (hg : ∀ a : HermiteRoot A.charpoly, AnalyticAt ℂ g (a : ℂ)) :
    spectralJetEval A (f * g) = spectralJetEval A f * spectralJetEval A g := by
  let pf := spectralJetPolynomial A f
  let pg := spectralJetPolynomial A g
  calc
    spectralJetEval A (f * g) =
        spectralJetEval A (fun z ↦ (pf * pg).eval z) := by
      apply spectralJetEval_eq_of_iteratedDeriv_eq A
      intro a k
      simp only [Polynomial.eval_mul]
      change iteratedDeriv k.val (fun z ↦ f z * g z) (a : ℂ) = _
      rw [iteratedDeriv_fun_mul (hf a).contDiffAt (hg a).contDiffAt,
        iteratedDeriv_fun_mul
          (pf.differentiable.analyticAt (a : ℂ)).contDiffAt
          (pg.differentiable.analyticAt (a : ℂ)).contDiffAt]
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i ≤ k.val := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [iteratedDeriv_spectralJetPolynomial_eval A a
          (hik.trans_lt k.isLt),
        iteratedDeriv_spectralJetPolynomial_eval A a
          ((Nat.sub_le k.val i).trans_lt k.isLt)]
    _ = Operator.polynomialEval (pf * pg) A :=
      spectralJetEval_polynomial A (pf * pg)
    _ = Operator.polynomialEval pf A * Operator.polynomialEval pg A := by
      simp [Operator.polynomialEval]
    _ = spectralJetEval A f * spectralJetEval A g := by
      rfl

/-- Spectral-jet evaluation sends the constant one function to the identity
matrix. -/
@[simp]
theorem spectralJetEval_one (A : Operator.SquareMatrix n) :
    spectralJetEval A (fun _ ↦ 1) = 1 := by
  calc
    spectralJetEval A (fun _ ↦ 1) =
        Operator.polynomialEval (1 : ℂ[X]) A := by
      simpa using spectralJetEval_polynomial A (1 : ℂ[X])
    _ = 1 := by simp [Operator.polynomialEval]

/-- Power law for the finite spectral-jet functional calculus. -/
theorem spectralJetEval_pow
    (A : Operator.SquareMatrix n) {f : ℂ → ℂ}
    (hf : ∀ a : HermiteRoot A.charpoly, AnalyticAt ℂ f (a : ℂ))
    (k : ℕ) :
    spectralJetEval A (fun z ↦ f z ^ k) = (spectralJetEval A f) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        spectralJetEval A (fun z ↦ f z ^ (k + 1)) =
            spectralJetEval A ((fun z ↦ f z ^ k) * f) := by
          apply congrArg (spectralJetEval A)
          funext z
          exact pow_succ (f z) k
        _ = spectralJetEval A (fun z ↦ f z ^ k) * spectralJetEval A f :=
          spectralJetEval_mul A (fun a ↦ (hf a).pow k) hf
        _ = (spectralJetEval A f) ^ (k + 1) := by rw [ih, pow_succ]

end

end DiskRigidity.Complex
