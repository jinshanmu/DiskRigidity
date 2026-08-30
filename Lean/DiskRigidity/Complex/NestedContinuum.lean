/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Nested compact continua

The intersection of a decreasing sequence of compact preconnected subsets of
a metric space is preconnected.  The result is elementary, but is not
currently packaged in Mathlib in this sequential form.
-/

noncomputable section

open Filter Function Metric Set Topology

namespace DiskRigidity.Complex

@[expose] public section

private theorem antitone_compact_eventually_subset_open
    {X : Type*} [PseudoMetricSpace X] [T2Space X]
    (C : ℕ → Set X) (hcompact : ∀ n, IsCompact (C n))
    (hanti : Antitone C) {O : Set X} (hO : IsOpen O)
    (hsub : (⋂ n, C n) ⊆ O) :
    ∃ n, C n ⊆ O := by
  by_contra hn
  have hn' (n : ℕ) : ∃ x ∈ C n, x ∉ O := by
    by_contra h
    apply hn
    refine ⟨n, fun x hx ↦ ?_⟩
    by_contra hxO
    exact h ⟨x, hx, hxO⟩
  choose x hxC hxO using hn'
  have hxC0 (n : ℕ) : x n ∈ C 0 := hanti (Nat.zero_le n) (hxC n)
  obtain ⟨a, haC, sigma, hsigmaMono, hsigmaLim⟩ :=
    (hcompact 0).tendsto_subseq hxC0
  have haNotO : a ∉ O := by
    exact hO.isClosed_compl.mem_of_tendsto hsigmaLim
      (Eventually.of_forall fun k ↦ hxO (sigma k))
  have haAll (n : ℕ) : a ∈ C n := by
    have hsigmaTop : Tendsto sigma atTop atTop := hsigmaMono.tendsto_atTop
    have heventually : ∀ᶠ k in atTop, x (sigma k) ∈ C n := by
      filter_upwards [hsigmaTop.eventually (eventually_ge_atTop n)] with k hk
      exact hanti hk (hxC (sigma k))
    exact (hcompact n).isClosed.mem_of_tendsto hsigmaLim heventually
  exact haNotO (hsub (mem_iInter.mpr haAll))

/-- A decreasing intersection of compact preconnected sets in a metric space
is preconnected. -/
theorem isPreconnected_iInter_of_antitone_compact
    {X : Type*} [PseudoMetricSpace X] [T2Space X]
    (C : ℕ → Set X) (hcompact : ∀ n, IsCompact (C n))
    (hpreconnected : ∀ n, IsPreconnected (C n))
    (hanti : Antitone C) :
    IsPreconnected (⋂ n, C n) := by
  rw [isPreconnected_closed_iff]
  intro t t' ht ht' hcover hmeet hmeet'
  have htNonempty : t.Nonempty := hmeet.mono inter_subset_right
  have ht'Nonempty : t'.Nonempty := hmeet'.mono inter_subset_right
  let radius : ℕ → ℝ := fun n ↦ 1 / (n + 1 : ℝ)
  have hradiusPos (n : ℕ) : 0 < radius n := by
    dsimp [radius]
    positivity
  have hradiusZero : Tendsto radius atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hopen (n : ℕ) : IsOpen
      (thickening (radius n) t ∪ thickening (radius n) t') :=
    isOpen_thickening.union isOpen_thickening
  have hfiberSub (n : ℕ) : (⋂ m, C m) ⊆
      thickening (radius n) t ∪ thickening (radius n) t' := by
    intro z hz
    rcases hcover hz with hzt | hzt'
    · exact Or.inl (self_subset_thickening (hradiusPos n) t hzt)
    · exact Or.inr (self_subset_thickening (hradiusPos n) t' hzt')
  have hexistsN (n : ℕ) : ∃ N, C N ⊆
      thickening (radius n) t ∪ thickening (radius n) t' :=
    antitone_compact_eventually_subset_open C hcompact hanti
      (hopen n) (hfiberSub n)
  choose N hN using hexistsN
  let m : ℕ → ℕ := fun n ↦ max (N n) n
  have hmN (n : ℕ) : N n ≤ m n := le_max_left _ _
  have hmn (n : ℕ) : n ≤ m n := le_max_right _ _
  have hCmCover (n : ℕ) : C (m n) ⊆
      thickening (radius n) t ∪ thickening (radius n) t' :=
    (hanti (hmN n)).trans (hN n)
  obtain ⟨xt, hxtFiber, hxt⟩ := hmeet
  obtain ⟨xt', hxt'Fiber, hxt'⟩ := hmeet'
  have hleftMeet (n : ℕ) :
      (C (m n) ∩ thickening (radius n) t).Nonempty := by
    exact ⟨xt, (mem_iInter.mp hxtFiber) (m n),
      self_subset_thickening (hradiusPos n) t hxt⟩
  have hrightMeet (n : ℕ) :
      (C (m n) ∩ thickening (radius n) t').Nonempty := by
    exact ⟨xt', (mem_iInter.mp hxt'Fiber) (m n),
      self_subset_thickening (hradiusPos n) t' hxt'⟩
  have hzExists (n : ℕ) : ∃ z, z ∈ C (m n) ∩
      (thickening (radius n) t ∩ thickening (radius n) t') := by
    exact hpreconnected (m n) _ _ isOpen_thickening isOpen_thickening
      (hCmCover n) (hleftMeet n) (hrightMeet n)
  choose z hz using hzExists
  have hzC0 (n : ℕ) : z n ∈ C 0 :=
    hanti (Nat.zero_le (m n)) (hz n).1
  obtain ⟨a, haC0, sigma, hsigmaMono, hsigmaLim⟩ :=
    (hcompact 0).tendsto_subseq hzC0
  have hsigmaTop : Tendsto sigma atTop atTop := hsigmaMono.tendsto_atTop
  have haAll (k : ℕ) : a ∈ C k := by
    have heventually : ∀ᶠ j in atTop, z (sigma j) ∈ C k := by
      filter_upwards [hsigmaTop.eventually (eventually_ge_atTop k)] with j hj
      exact hanti (hj.trans (hmn (sigma j))) (hz (sigma j)).1
    exact (hcompact k).isClosed.mem_of_tendsto hsigmaLim heventually
  have hradiusSub : Tendsto (fun j ↦ radius (sigma j)) atTop (nhds 0) :=
    hradiusZero.comp hsigmaTop
  have hinfDistTendsto : Tendsto (fun j ↦ infDist (z (sigma j)) t)
      atTop (nhds (infDist a t)) :=
    (continuous_infDist_pt t).continuousAt.tendsto.comp hsigmaLim
  have hinfDistTendsto' : Tendsto (fun j ↦ infDist (z (sigma j)) t')
      atTop (nhds (infDist a t')) :=
    (continuous_infDist_pt t').continuousAt.tendsto.comp hsigmaLim
  have hinfDistZero : Tendsto (fun j ↦ infDist (z (sigma j)) t)
      atTop (nhds 0) := by
    exact squeeze_zero (fun _ ↦ infDist_nonneg)
      (fun j ↦ (mem_thickening_iff_infDist_lt htNonempty).mp
        (hz (sigma j)).2.1 |>.le) hradiusSub
  have hinfDistZero' : Tendsto (fun j ↦ infDist (z (sigma j)) t')
      atTop (nhds 0) := by
    exact squeeze_zero (fun _ ↦ infDist_nonneg)
      (fun j ↦ (mem_thickening_iff_infDist_lt ht'Nonempty).mp
        (hz (sigma j)).2.2 |>.le) hradiusSub
  have haT : a ∈ t := by
    rw [ht.mem_iff_infDist_zero htNonempty]
    exact tendsto_nhds_unique hinfDistTendsto hinfDistZero
  have haT' : a ∈ t' := by
    rw [ht'.mem_iff_infDist_zero ht'Nonempty]
    exact tendsto_nhds_unique hinfDistTendsto' hinfDistZero'
  exact ⟨a, mem_iInter.mpr haAll, haT, haT'⟩

end

end DiskRigidity.Complex
