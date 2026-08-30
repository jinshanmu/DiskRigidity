/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.ConformalSchurInterpolation
public import DiskRigidity.Operator.CrouzeixConstant
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Finite spectral jets and matrix evaluation

For a finite complex matrix, a holomorphic functional-calculus value is
determined by finitely many derivatives at the roots of its characteristic
polynomial.  This file constructs that value without Jordan normal form:
Chinese remaindering gives a fixed Hermite basis, and Cayley--Hamilton proves
that the resulting polynomial evaluation is independent of the representative.
-/

noncomputable section

open Filter Function Set
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Complex

@[expose] public section

open Polynomial

/-- The distinct roots of a polynomial. -/
abbrev HermiteRoot (p : ℂ[X]) := ↑p.roots.toFinset

/-- The local ideal encoding the full multiplicity at a root. -/
def hermiteIdeal (p : ℂ[X]) (a : HermiteRoot p) : Ideal ℂ[X] :=
  Ideal.span {((X - C (a : ℂ)) ^ p.rootMultiplicity (a : ℂ))}

/-- The local monomial whose only nonzero Hermite coordinate is `(a,k)`. -/
def hermiteLocalMonomial (p : ℂ[X]) (a : HermiteRoot p)
    (k : Fin (p.rootMultiplicity (a : ℂ))) (b : HermiteRoot p) : ℂ[X] :=
  if h : a = b then (X - C (b : ℂ)) ^ (h ▸ k).val else 0

theorem pairwise_isCoprime_hermiteIdeal (p : ℂ[X]) :
    Pairwise (IsCoprime on hermiteIdeal p) := by
  intro a b hab
  change IsCoprime
    (Ideal.span {((X - C (a : ℂ)) ^ p.rootMultiplicity (a : ℂ))})
    (Ideal.span {((X - C (b : ℂ)) ^ p.rootMultiplicity (b : ℂ))})
  rw [Ideal.isCoprime_span_singleton_iff]
  exact (Polynomial.pairwise_coprime_X_sub_C
    (show Function.Injective fun z : HermiteRoot p ↦ (z : ℂ) from Subtype.val_injective)
    hab).pow

/-- A fixed CRT Hermite basis polynomial. -/
def hermiteBasis (p : ℂ[X]) (a : HermiteRoot p)
    (k : Fin (p.rootMultiplicity (a : ℂ))) : ℂ[X] :=
  Classical.choose (Ideal.exists_forall_sub_mem_ideal
    (pairwise_isCoprime_hermiteIdeal p) (hermiteLocalMonomial p a k))

theorem hermiteBasis_sub_local_mem (p : ℂ[X]) (a : HermiteRoot p)
    (k : Fin (p.rootMultiplicity (a : ℂ))) (b : HermiteRoot p) :
    hermiteBasis p a k - hermiteLocalMonomial p a k b ∈ hermiteIdeal p b :=
  by
    unfold hermiteBasis
    exact Classical.choose_spec (Ideal.exists_forall_sub_mem_ideal
      (pairwise_isCoprime_hermiteIdeal p) (hermiteLocalMonomial p a k)) b

/-- The polynomial assembled from a finite family of Hermite coordinates. -/
def hermiteInterpolate (p : ℂ[X])
    (d : ∀ a : HermiteRoot p, Fin (p.rootMultiplicity (a : ℂ)) → ℂ) : ℂ[X] :=
  ∑ a : HermiteRoot p, ∑ k : Fin (p.rootMultiplicity (a : ℂ)),
    C (d a k) * hermiteBasis p a k

/-- The truncated local Taylor polynomial represented by Hermite coordinates. -/
def hermiteLocalPolynomial (p : ℂ[X])
    (d : ∀ a : HermiteRoot p, Fin (p.rootMultiplicity (a : ℂ)) → ℂ)
    (b : HermiteRoot p) : ℂ[X] :=
  ∑ k : Fin (p.rootMultiplicity (b : ℂ)), C (d b k) * (X - C (b : ℂ)) ^ k.val

private theorem sum_hermiteLocalMonomial_eq (p : ℂ[X])
    (d : ∀ a : HermiteRoot p, Fin (p.rootMultiplicity (a : ℂ)) → ℂ)
    (b : HermiteRoot p) :
    (∑ a : HermiteRoot p, ∑ k : Fin (p.rootMultiplicity (a : ℂ)),
      C (d a k) * hermiteLocalMonomial p a k b) = hermiteLocalPolynomial p d b := by
  classical
  rw [Fintype.sum_eq_single b]
  · simp [hermiteLocalMonomial, hermiteLocalPolynomial]
  · intro a hab
    simp [hermiteLocalMonomial, hab]

/-- The global Hermite interpolant has the prescribed residue at each root. -/
theorem hermiteInterpolate_sub_local_mem (p : ℂ[X])
    (d : ∀ a : HermiteRoot p, Fin (p.rootMultiplicity (a : ℂ)) → ℂ)
    (b : HermiteRoot p) :
    hermiteInterpolate p d - hermiteLocalPolynomial p d b ∈ hermiteIdeal p b := by
  classical
  have hsum :
      (∑ a : HermiteRoot p, ∑ k : Fin (p.rootMultiplicity (a : ℂ)),
        C (d a k) * (hermiteBasis p a k - hermiteLocalMonomial p a k b)) ∈
        hermiteIdeal p b := by
    apply Ideal.sum_mem
    intro a _
    apply Ideal.sum_mem
    intro k _
    exact (hermiteIdeal p b).mul_mem_left _ (hermiteBasis_sub_local_mem p a k b)
  simp_rw [mul_sub, Finset.sum_sub_distrib] at hsum
  rw [sum_hermiteLocalMonomial_eq] at hsum
  simpa [hermiteInterpolate] using hsum

/-- Divisibility by a power of `X - a` is equivalent to equality of the
corresponding finite Hasse jets. -/
theorem X_sub_C_pow_dvd_sub_iff_hasseDeriv_eval_eq (p q : ℂ[X]) (a : ℂ) (m : ℕ) :
    (X - C a) ^ m ∣ p - q ↔
      ∀ k < m, (hasseDeriv k p).eval a = (hasseDeriv k q).eval a := by
  rw [X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
  simp only [← taylor_apply, map_sub, coeff_sub, taylor_coeff, sub_eq_zero]

theorem taylor_hermiteLocalPolynomial (p : ℂ[X])
    (d : ∀ a : HermiteRoot p, Fin (p.rootMultiplicity (a : ℂ)) → ℂ)
    (b : HermiteRoot p) :
    taylor (b : ℂ) (hermiteLocalPolynomial p d b) =
      ∑ k : Fin (p.rootMultiplicity (b : ℂ)), C (d b k) * X ^ k.val := by
  simp [hermiteLocalPolynomial, taylor_apply]

theorem hasseDeriv_eval_hermiteLocalPolynomial (p : ℂ[X])
    (d : ∀ a : HermiteRoot p, Fin (p.rootMultiplicity (a : ℂ)) → ℂ)
    (b : HermiteRoot p) {k : ℕ} (hk : k < p.rootMultiplicity (b : ℂ)) :
    (hasseDeriv k (hermiteLocalPolynomial p d b)).eval (b : ℂ) = d b ⟨k, hk⟩ := by
  rw [← taylor_coeff, taylor_hermiteLocalPolynomial]
  simp
  have hs :
      (∑ x : Fin (p.rootMultiplicity (b : ℂ)), if k = x.val then d b x else 0) =
        (if k = (⟨k, hk⟩ : Fin (p.rootMultiplicity (b : ℂ))).val
          then d b ⟨k, hk⟩ else 0) := by
    refine Fintype.sum_eq_single
      (f := fun x : Fin (p.rootMultiplicity (b : ℂ)) ↦ if k = x.val then d b x else 0)
      ⟨k, hk⟩ ?_
    intro x hx
    rw [if_neg]
    exact fun h ↦ hx (Fin.ext h.symm)
  simpa using hs

/-- Hermite coordinates of an ordinary polynomial. -/
def polynomialHermiteData (p q : ℂ[X])
    (a : HermiteRoot p) (k : Fin (p.rootMultiplicity (a : ℂ))) : ℂ :=
  (hasseDeriv k.val q).eval (a : ℂ)

/-- Hermite interpolation recovers a polynomial modulo `p`. -/
theorem hermiteInterpolate_sub_polynomial_dvd (p q : ℂ[X])
    (hpmonic : p.Monic) (hpsplit : p.Splits) :
    p ∣ hermiteInterpolate p (polynomialHermiteData p q) - q := by
  classical
  let factor : HermiteRoot p → ℂ[X] := fun a ↦
    (X - C (a : ℂ)) ^ p.rootMultiplicity (a : ℂ)
  have hfactor (b : HermiteRoot p) :
      factor b ∣ hermiteInterpolate p (polynomialHermiteData p q) - q := by
    have hqLocal : factor b ∣
        q - hermiteLocalPolynomial p (polynomialHermiteData p q) b := by
      apply (X_sub_C_pow_dvd_sub_iff_hasseDeriv_eval_eq q
        (hermiteLocalPolynomial p (polynomialHermiteData p q) b) (b : ℂ)
        (p.rootMultiplicity (b : ℂ))).2
      intro k hk
      exact (hasseDeriv_eval_hermiteLocalPolynomial p (polynomialHermiteData p q) b hk).symm
    have hqLocalMem : q - hermiteLocalPolynomial p (polynomialHermiteData p q) b ∈
        hermiteIdeal p b := by
      exact Ideal.mem_span_singleton.mpr hqLocal
    have hsub := (hermiteIdeal p b).sub_mem
      (hermiteInterpolate_sub_local_mem p (polynomialHermiteData p q) b) hqLocalMem
    have hmem : hermiteInterpolate p (polynomialHermiteData p q) - q ∈
        hermiteIdeal p b := by
      convert hsub using 1
      ring
    exact Ideal.mem_span_singleton.mp hmem
  have hpair : (Set.univ : Set (HermiteRoot p)).Pairwise (IsCoprime on factor) := by
    intro a _ b _ hab
    exact (Polynomial.pairwise_coprime_X_sub_C
      (show Function.Injective fun z : HermiteRoot p ↦ (z : ℂ) from Subtype.val_injective)
      hab).pow
  have hprod : (∏ b : HermiteRoot p, factor b) = p := by
    calc
      (∏ b : HermiteRoot p, factor b) =
          ∏ a ∈ p.roots.toFinset, (X - C a) ^ p.rootMultiplicity a := by
            simpa [factor] using
              (Finset.prod_coe_sort p.roots.toFinset
                (fun a ↦ (X - C a) ^ p.rootMultiplicity a))
      _ = (p.roots.map fun a ↦ X - C a).prod :=
        Polynomial.prod_multiset_root_eq_finset_root.symm
      _ = p := (hpsplit.eq_prod_roots_of_monic hpmonic).symm
  have hdiv : (∏ b : HermiteRoot p, factor b) ∣
      hermiteInterpolate p (polynomialHermiteData p q) - q :=
    Finset.prod_dvd_of_coprime (by simpa using hpair) fun b _ ↦ hfactor b
  obtain ⟨r, hr⟩ := hdiv
  refine ⟨r, ?_⟩
  calc
    hermiteInterpolate p (polynomialHermiteData p q) - q =
        (∏ b : HermiteRoot p, factor b) * r := hr
    _ = p * r := congrArg (· * r) hprod

/-- Analytic iterated derivatives of a polynomial agree with its algebraic
iterated derivatives. -/
theorem iteratedDeriv_polynomial_eval (q : ℂ[X]) (k : ℕ) :
    iteratedDeriv k (fun z : ℂ ↦ q.eval z) = fun z ↦ (derivative^[k] q).eval z := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext z
      rw [Polynomial.deriv]
      rw [show k + 1 = k.succ by omega, Function.iterate_succ_apply']

/-- Hermite coordinates of an arbitrary function, normalized as Taylor
coefficients. -/
def holomorphicHermiteData (p : ℂ[X]) (f : ℂ → ℂ)
    (a : HermiteRoot p) (k : Fin (p.rootMultiplicity (a : ℂ))) : ℂ :=
  iteratedDeriv k.val f (a : ℂ) / (k.val.factorial : ℂ)

theorem holomorphicHermiteData_polynomial (p q : ℂ[X]) :
    holomorphicHermiteData p (fun z ↦ q.eval z) = polynomialHermiteData p q := by
  funext a k
  rw [holomorphicHermiteData, polynomialHermiteData, iteratedDeriv_polynomial_eval]
  have hfac := congrArg (fun r : ℂ[X] ↦ r.eval (a : ℂ))
    (congrFun (Polynomial.factorial_smul_hasseDeriv k.val) q)
  have hfac' : (k.val.factorial : ℂ) * (hasseDeriv k.val q).eval (a : ℂ) =
      (derivative^[k.val] q).eval (a : ℂ) := by
    simpa [smul_eq_mul] using hfac
  change (derivative^[k.val] q).eval (a : ℂ) / (k.val.factorial : ℂ) = _
  rw [← hfac']
  exact mul_div_cancel_left₀ _ (by exact_mod_cast Nat.factorial_ne_zero k.val)

/-- The characteristic-root list, with algebraic multiplicity. -/
def spectralJetNodes {n : Type*} [Fintype n] [DecidableEq n]
    (A : Operator.SquareMatrix n) : List ℂ :=
  A.charpoly.roots.toList

theorem jetMultiplicity_spectralJetNodes {n : Type*} [Fintype n] [DecidableEq n]
    (A : Operator.SquareMatrix n) (z : ℂ) :
    jetMultiplicity (spectralJetNodes A) z = A.charpoly.rootMultiplicity z := by
  classical
  change List.count z A.charpoly.roots.toList = A.charpoly.rootMultiplicity z
  rw [← Multiset.coe_count, Multiset.coe_toList, Polynomial.count_roots]

/-- Evaluation of a function at a matrix through its finite characteristic
spectral jet. -/
def spectralJetEval {n : Type*} [Fintype n] [DecidableEq n]
    (A : Operator.SquareMatrix n) (f : ℂ → ℂ) : Operator.SquareMatrix n :=
  Operator.polynomialEval (hermiteInterpolate A.charpoly
    (holomorphicHermiteData A.charpoly f)) A

theorem spectralJetEval_eq_sum {n : Type*} [Fintype n] [DecidableEq n]
    (A : Operator.SquareMatrix n) (f : ℂ → ℂ) :
    spectralJetEval A f =
      ∑ a : HermiteRoot A.charpoly,
        ∑ k : Fin (A.charpoly.rootMultiplicity (a : ℂ)),
          holomorphicHermiteData A.charpoly f a k •
            Operator.polynomialEval (hermiteBasis A.charpoly a k) A := by
  simp [spectralJetEval, hermiteInterpolate, Operator.polynomialEval, Algebra.smul_def]

/-- Spectral-jet evaluation agrees with ordinary polynomial evaluation. -/
theorem spectralJetEval_polynomial {n : Type*} [Fintype n] [DecidableEq n]
    (A : Operator.SquareMatrix n) (q : ℂ[X]) :
    spectralJetEval A (fun z ↦ q.eval z) = Operator.polynomialEval q A := by
  rw [spectralJetEval, holomorphicHermiteData_polynomial]
  apply sub_eq_zero.mp
  change Polynomial.aeval A (hermiteInterpolate A.charpoly
    (polynomialHermiteData A.charpoly q)) - Polynomial.aeval A q = 0
  rw [← map_sub]
  obtain ⟨r, hr⟩ := hermiteInterpolate_sub_polynomial_dvd A.charpoly q
    (Matrix.charpoly_monic A) (IsAlgClosed.splits A.charpoly)
  rw [hr, map_mul, Matrix.aeval_self_charpoly, zero_mul]

/-- The matrix value depends only on its finite characteristic spectral jet. -/
theorem spectralJetEval_eq_of_iteratedDeriv_eq {n : Type*} [Fintype n] [DecidableEq n]
    (A : Operator.SquareMatrix n) {f g : ℂ → ℂ}
    (hfg : ∀ (a : HermiteRoot A.charpoly)
      (k : Fin (A.charpoly.rootMultiplicity (a : ℂ))),
      iteratedDeriv k.val f (a : ℂ) = iteratedDeriv k.val g (a : ℂ)) :
    spectralJetEval A f = spectralJetEval A g := by
  unfold spectralJetEval
  congr 2
  funext a k
  simp only [holomorphicHermiteData, hfg a k]

/-- Vanishing-order jet equality on the characteristic-root list preserves
the matrix value. -/
theorem spectralJetEval_eq_of_jetEq {n : Type*} [Fintype n] [DecidableEq n]
    (A : Operator.SquareMatrix n) {f g : ℂ → ℂ}
    (hf : ∀ a : HermiteRoot A.charpoly, AnalyticAt ℂ f (a : ℂ))
    (hg : ∀ a : HermiteRoot A.charpoly, AnalyticAt ℂ g (a : ℂ))
    (hjet : JetEq (spectralJetNodes A) f g) :
    spectralJetEval A f = spectralJetEval A g := by
  apply spectralJetEval_eq_of_iteratedDeriv_eq A
  intro a k
  apply hjet.iteratedDeriv_eq (hf a) (hg a)
  rw [jetMultiplicity_spectralJetNodes]
  exact k.isLt

theorem differentiableOn_iteratedDeriv_of_isOpen {U : Set ℂ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (k : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv k f) U := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv hU

/-- Locally uniform convergence of holomorphic functions carries every
finite iterated derivative with it. -/
theorem tendstoLocallyUniformlyOn_iteratedDeriv {U : Set ℂ}
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hU : IsOpen U)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hconv : TendstoLocallyUniformlyOn F f atTop U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n ↦ iteratedDeriv k (F n))
      (iteratedDeriv k f) atTop U := by
  induction k with
  | zero => simpa using hconv
  | succ k ih =>
      have hd := ih.deriv
        (Eventually.of_forall fun n ↦ differentiableOn_iteratedDeriv_of_isOpen (hF n) hU k) hU
      simpa [Function.comp_def, iteratedDeriv_succ] using hd

/-- Locally uniform holomorphic convergence implies convergence of the
finite spectral-jet matrix values. -/
theorem spectralJetEval_tendsto_of_tendstoLocallyUniformlyOn
    {n : Type*} [Fintype n] [DecidableEq n] (A : Operator.SquareMatrix n)
    {U : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hF : ∀ m, DifferentiableOn ℂ (F m) U)
    (hroots : ∀ z ∈ A.charpoly.roots, z ∈ U)
    (hconv : TendstoLocallyUniformlyOn F f atTop U) :
    Tendsto (fun m ↦ spectralJetEval A (F m)) atTop (nhds (spectralJetEval A f)) := by
  have hcoord (a : HermiteRoot A.charpoly)
      (k : Fin (A.charpoly.rootMultiplicity (a : ℂ))) :
      Tendsto (fun m ↦ holomorphicHermiteData A.charpoly (F m) a k) atTop
        (nhds (holomorphicHermiteData A.charpoly f a k)) := by
    have hkconv := tendstoLocallyUniformlyOn_iteratedDeriv hU hF hconv k.val
    exact (hkconv.tendsto_at (hroots (a : ℂ) (Multiset.mem_toFinset.mp a.2))).div_const _
  simp_rw [spectralJetEval_eq_sum]
  apply tendsto_finsetSum Finset.univ
  intro a _
  apply tendsto_finsetSum Finset.univ
  intro k _
  exact (hcoord a k).smul_const _

end

end DiskRigidity.Complex
