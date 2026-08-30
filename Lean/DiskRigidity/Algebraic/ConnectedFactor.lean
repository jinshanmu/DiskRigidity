/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.ProjectiveDual
public import Mathlib

/-!
# A connected regular arc stays in one factor

This is the topological part of the factor-selection argument in Proposition
7.1.  On a connected set, suppose a finite product of continuous complex
functions vanishes and no point is a common zero of two different factors.
Then one fixed factor vanishes everywhere.  For an algebraic curve, the
second hypothesis is precisely what regularity of the product gives locally.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace ConnectedFactor

open Set
open MvPolynomial ProjectiveDual

variable {X ι : Type*} [TopologicalSpace X] [Fintype ι]

/-- A connected subset of the regular locus of a finite product belongs to a
single factor. -/
theorem exists_factor_zero_on_connected {s : Set X} (hs : IsConnected s)
    (f : ι → X → ℂ) (hcontinuous : ∀ i, ContinuousOn (f i) s)
    (hprod : ∀ x ∈ s, ∏ i, f i x = 0)
    (hunique : ∀ x ∈ s, ∀ i j, f i x = 0 → f j x = 0 → i = j) :
    ∃ i, ∀ x ∈ s, f i x = 0 := by
  let z : ι → Set s := fun i ↦ {x | f i x = 0}
  have hzclosed (i : ι) : IsClosed (z i) := by
    exact isClosed_singleton.preimage
      (continuousOn_iff_continuous_domRestrict.mp (hcontinuous i))
  have hzcompl (i : ι) :
      (z i)ᶜ = ⋃ j : {j : ι // j ≠ i}, z j := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion]
    constructor
    · intro hxi
      have hp : ∏ j, f j x = 0 := hprod x x.property
      rw [Finset.prod_eq_zero_iff] at hp
      obtain ⟨j, -, hj⟩ := hp
      have hji : j ≠ i := by
        intro h
        exact hxi (h ▸ hj)
      exact ⟨⟨j, hji⟩, hj⟩
    · rintro ⟨j, hj⟩ hxi
      exact j.property (hunique x x.property i j hxi hj).symm
  have hzopen (i : ι) : IsOpen (z i) := by
    apply isClosed_compl_iff.mp
    rw [hzcompl i]
    exact isClosed_iUnion_of_finite fun j ↦ hzclosed j
  obtain ⟨x, hx⟩ := hs.nonempty
  have hp : ∏ i, f i x = 0 := hprod x hx
  rw [Finset.prod_eq_zero_iff] at hp
  obtain ⟨i, -, hi⟩ := hp
  let _ : ConnectedSpace s := Subtype.connectedSpace hs
  have hzi : IsClopen (z i) := ⟨hzclosed i, hzopen i⟩
  have hzinonempty : (z i).Nonempty := ⟨⟨x, hx⟩, hi⟩
  have hziuniv : z i = Set.univ := hzi.eq_univ hzinonempty
  refine ⟨i, fun y hy ↦ ?_⟩
  have : (⟨y, hy⟩ : s) ∈ z i := by rw [hziuniv]; trivial
  exact this

section AlgebraicComponent

/-- If two (not necessarily distinct) factors vanish at a point, their
product with any third factor is singular there. -/
theorem gradient_mul_mul_eq_zero_of_eval_eq_zero
    {σ : Type*} {K : Type*} [Field K]
    (A B R : MvPolynomial σ K) (x : σ → K)
    (hA : MvPolynomial.eval x A = 0)
    (hB : MvPolynomial.eval x B = 0) :
    (fun i ↦ MvPolynomial.eval x
      (MvPolynomial.pderiv i ((A * B) * R))) = 0 := by
  funext i
  simp [hA, hB]

/-- **Irreducible component selection.**  A connected subset of the regular
zero locus of a nonzero nonunit complex polynomial lies on one irreducible
factor.  The factor is produced from the UFD factorization; regularity rules
out simultaneous vanishing of two distinct factor occurrences. -/
theorem exists_irreducible_factor_zero_on_connected_regular
    {N : ℕ}
    {s : Set (Fin N → ℂ)} (hs : IsConnected s)
    {P : MvPolynomial (Fin N) ℂ} (hPzero : P ≠ 0)
    (_hPnonunit : ¬ IsUnit P)
    (hzero : ∀ x ∈ s, MvPolynomial.eval x P = 0)
    (hregular : ∀ x ∈ s, RegularAt P x) :
    ∃ F : MvPolynomial (Fin N) ℂ,
      Irreducible F ∧ F ∣ P ∧
        ∀ x ∈ s, MvPolynomial.eval x F = 0 := by
  classical
  let factors := UniqueFactorizationMonoid.factors P
  let ι := {F : MvPolynomial (Fin N) ℂ // F ∈ factors.toFinset}
  let f : ι → (Fin N → ℂ) → ℂ := fun i x ↦ MvPolynomial.eval x i.1
  have hassociated : Associated factors.prod P :=
    UniqueFactorizationMonoid.factors_prod hPzero
  have hprod : ∀ x ∈ s, ∏ i : ι, f i x = 0 := by
    intro x hx
    have hfactorProduct : MvPolynomial.eval x factors.prod = 0 :=
      ((hassociated.map (MvPolynomial.eval x)).eq_zero_iff).mpr (hzero x hx)
    have hmappedProduct :
        (factors.map (MvPolynomial.eval x)).prod = 0 := by
      rw [← map_multiset_prod]
      exact hfactorProduct
    have hzeroMem : 0 ∈ factors.map (MvPolynomial.eval x) :=
      Multiset.prod_eq_zero_iff.mp hmappedProduct
    obtain ⟨G, hGfactors, hGeval⟩ := Multiset.mem_map.mp hzeroMem
    rw [Finset.prod_eq_zero_iff]
    let i : ι := ⟨G, Multiset.mem_toFinset.mpr hGfactors⟩
    exact ⟨i, Finset.mem_univ i, hGeval⟩
  have hunique : ∀ x ∈ s, ∀ i j : ι,
      f i x = 0 → f j x = 0 → i = j := by
    intro x hx i j hi hj
    apply Subtype.ext
    by_contra hij
    have hiFactors : i.1 ∈ factors := Multiset.mem_toFinset.mp i.2
    have hjFactors : j.1 ∈ factors := Multiset.mem_toFinset.mp j.2
    have hpair : ({i.1, j.1} : Multiset (MvPolynomial (Fin N) ℂ)) ≤ factors := by
      change i.1 ::ₘ ({j.1} : Multiset (MvPolynomial (Fin N) ℂ)) ≤ factors
      rw [Multiset.cons_le_of_notMem]
      · exact ⟨hiFactors, Multiset.singleton_le.mpr hjFactors⟩
      · simp [hij]
    have hpairDvd : i.1 * j.1 ∣ P := by
      have hprodDvd : ({i.1, j.1} : Multiset (MvPolynomial (Fin N) ℂ)).prod ∣
          factors.prod := Multiset.prod_dvd_prod_of_le hpair
      have hijDvd : i.1 * j.1 ∣ factors.prod := by
        simpa using hprodDvd
      exact hijDvd.trans hassociated.dvd
    obtain ⟨R, hR⟩ := hpairDvd
    have hgrad : gradient P x = 0 := by
      rw [hR]
      exact gradient_mul_mul_eq_zero_of_eval_eq_zero i.1 j.1 R x hi hj
    exact (hregular x hx).2 hgrad
  obtain ⟨i, hi⟩ := exists_factor_zero_on_connected hs f
    (fun i ↦ (MvPolynomial.continuous_eval i.1).continuousOn) hprod hunique
  have hiFactors : i.1 ∈ factors := Multiset.mem_toFinset.mp i.2
  exact ⟨i.1,
    UniqueFactorizationMonoid.irreducible_of_factor i.1 hiFactors,
    UniqueFactorizationMonoid.dvd_of_mem_factors hiFactors, hi⟩

end AlgebraicComponent

end ConnectedFactor

end DiskRigidity.Algebraic
