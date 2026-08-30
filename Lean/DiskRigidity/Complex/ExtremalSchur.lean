/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.FiniteSchurInterpolation

/-!
# Extremal finite Schur interpolation

This file proves the uniqueness part of finite confluent Schur interpolation.  The formulation of
minimal norm used below is the elementary one needed in applications: there is no interpolant
whose norm is bounded by a real number strictly smaller than one on the open disc.
-/

open Filter Function Metric Set
open scoped ComplexConjugate Topology

namespace DiskRigidity.Complex

@[expose] public section

/-- A function is uniformly bounded by a number strictly below one on the open unit disc. -/
def HasStrictDiscBound (f : ℂ → ℂ) : Prop :=
  ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ r

theorem hasStrictDiscBound_zero : HasStrictDiscBound (Function.const ℂ 0) := by
  refine ⟨0, le_rfl, zero_lt_one, ?_⟩
  simp

/-- A strict uniform bound survives one inverse Schur step. -/
theorem HasStrictDiscBound.schurReconstruct {g : ℂ → ℂ}
    (hgb : HasStrictDiscBound g) {a w : ℂ}
    (ha : a ∈ ball 0 1) (hw : w ∈ ball 0 1) :
    HasStrictDiscBound (schurReconstruct a w g) := by
  obtain ⟨r, hr0, hr1, hgr⟩ := hgb
  let R : ℝ := (‖w‖ + r) / (1 + ‖w‖ * r)
  have hwn : ‖w‖ < 1 := by simpa [mem_ball_zero_iff] using hw
  have hdenR : 0 < 1 + ‖w‖ * r := by positivity
  have hR0 : 0 ≤ R := div_nonneg (add_nonneg (norm_nonneg _) hr0) hdenR.le
  have hR1 : R < 1 := by
    rw [div_lt_one hdenR]
    nlinarith only [hwn, hr1, mul_pos (sub_pos.mpr hwn) (sub_pos.mpr hr1)]
  refine ⟨R, hR0, hR1, fun z hz => ?_⟩
  let x : ℂ := blaschkeFactor a z * g z
  have hbn : ‖blaschkeFactor a z‖ < 1 := by
    simpa [mem_ball_zero_iff] using mapsTo_ball_blaschkeFactor ha hz
  have hxn_le : ‖x‖ ≤ r := by
    dsimp only [x]
    rw [norm_mul]
    calc
      ‖blaschkeFactor a z‖ * ‖g z‖ ≤ 1 * ‖g z‖ :=
        mul_le_mul_of_nonneg_right hbn.le (norm_nonneg _)
      _ ≤ r := by simpa using hgr z hz
  have hxn : ‖x‖ < 1 := hxn_le.trans_lt hr1
  let w' : _root_.Complex.UnitDisc :=
    ⟨w, by simpa [mem_ball_zero_iff] using hw⟩
  let x' : _root_.Complex.UnitDisc :=
    ⟨x, by simpa using hxn⟩
  have hshift := _root_.Complex.UnitDisc.norm_shift_le w' x'
  have hformula :
      (‖w‖ + ‖x‖) / (1 + ‖w‖ * ‖x‖) ≤
        (‖w‖ + r) / (1 + ‖w‖ * r) := by
    have hdenX : 0 < 1 + ‖w‖ * ‖x‖ := by positivity
    rw [div_le_div_iff₀ hdenX hdenR]
    have hprod : 0 ≤ (r - ‖x‖) * (1 - ‖w‖ ^ 2) :=
      mul_nonneg (sub_nonneg.mpr hxn_le) (by nlinarith [norm_nonneg w])
    nlinarith only [hprod]
  change ‖discShift w x‖ ≤ R
  calc
    ‖discShift w x‖ = ‖(w'.shift x' : ℂ)‖ := by
      congr 1
      rw [← show (w' : ℂ) = w by rfl, ← show (x' : ℂ) = x by rfl]
      exact discShift_eq_coe_shift w' x'
    _ ≤ (‖(w' : ℂ)‖ + ‖(x' : ℂ)‖) /
        (1 + ‖(w' : ℂ)‖ * ‖(x' : ℂ)‖) := hshift
    _ ≤ R := hformula

/-- The first value condition contained in a nonempty jet family. -/
theorem JetEq.eq_at_head {a : ℂ} {nodes : List ℂ} {f g : ℂ → ℂ}
    (hjet : JetEq (a :: nodes) f g)
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a) : f a = g a := by
  have hk : 0 < jetMultiplicity (a :: nodes) a := by
    rw [jetMultiplicity_cons]
    simp
  have h := hjet.iteratedDeriv_eq hf hg hk
  simpa using h

/-- A direct Schur step removes the head value condition and preserves all remaining jets. -/
theorem JetEq.schurReduce {a : ℂ} {nodes : List ℂ} {F f : ℂ → ℂ}
    (hjet : JetEq (a :: nodes) F f) (hF : IsSchur F) (hf : IsSchur f)
    (hFmaps : MapsTo F (ball 0 1) (ball 0 1))
    (hfmaps : MapsTo f (ball 0 1) (ball 0 1))
    (ha : a ∈ ball (0 : ℂ) 1) (hnodes : ∀ z ∈ nodes, z ∈ ball (0 : ℂ) 1) :
    JetEq nodes (DiskRigidity.Complex.schurReduce F a)
      (DiskRigidity.Complex.schurReduce f a) := by
  have hFa : AnalyticAt ℂ F a :=
    hF.differentiableOn.analyticAt (isOpen_ball.mem_nhds ha)
  have hfa : AnalyticAt ℂ f a :=
    hf.differentiableOn.analyticAt (isOpen_ball.mem_nhds ha)
  have hw : F a = f a := hjet.eq_at_head hFa hfa
  have hRF : IsSchur (DiskRigidity.Complex.schurReduce F a) :=
    isSchur_schurReduce hF hFmaps ha
  have hRf : IsSchur (DiskRigidity.Complex.schurReduce f a) :=
    isSchur_schurReduce hf hfmaps ha
  intro z
  by_cases hzmem : z ∈ nodes
  · have hzD := hnodes z hzmem
    have hlocal : (F - f) =ᶠ[nhds z]
        (DiskRigidity.Complex.schurReconstruct a (f a)
            (DiskRigidity.Complex.schurReduce F a) -
          DiskRigidity.Complex.schurReconstruct a (f a)
            (DiskRigidity.Complex.schurReduce f a)) := by
      filter_upwards [isOpen_ball.mem_nhds hzD] with y hy
      simp only [Pi.sub_apply]
      rw [← hw, schurReconstruct_reduce hFmaps ha hy, hw,
        schurReconstruct_reduce hfmaps ha hy]
    have horder := hjet z
    rw [analyticOrderAt_congr hlocal,
      analyticOrderAt_schurReconstruct_sub hRF hRf ha (hfmaps ha) hzD,
      analyticOrderAt_blaschkeFactor ha hzD, jetMultiplicity_cons] at horder
    by_cases haz : a = z
    · subst z
      simpa [Nat.cast_add, add_comm] using horder
    · simpa [haz, Ne.symm haz] using horder
  · have hcount : jetMultiplicity nodes z = 0 := by
      classical
      exact List.count_eq_zero.mpr hzmem
    simp [hcount]

/-- A Schur function with one value in the open disc maps the whole open disc into itself. -/
theorem IsSchur.mapsTo_ball_of_apply_mem_ball {f : ℂ → ℂ} (hf : IsSchur f)
    {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) (hfa : f a ∈ ball (0 : ℂ) 1) :
    MapsTo f (ball 0 1) (ball 0 1) := by
  rcases hf.eqOn_unimodular_const_or_mapsTo_ball with ⟨c, hc, hfc⟩ | hmaps
  · have heq : f a = c := hfc ha
    have hlt : ‖f a‖ < 1 := by simpa [mem_ball_zero_iff] using hfa
    rw [heq, hc] at hlt
    exfalso
    exact (lt_self_iff_false 1).mp hlt
  · exact hmaps

/-- There is no interpolant for these jets with a uniform norm bound strictly below one.  For a
feasible Schur datum this is precisely the assertion that its least interpolation norm is one. -/
def HasMinimalNormOneJets (nodes : List ℂ) (f : ℂ → ℂ) : Prop :=
  ¬ ∃ g : ℂ → ℂ, IsSchur g ∧ JetEq nodes g f ∧ HasStrictDiscBound g

/-- **Uniqueness in the extremal finite Schur problem.** If a feasible finite confluent jet datum
has least norm one, then its norm-one Schur interpolant is unique on the disc. -/
theorem eqOn_of_hasMinimalNormOneJets (nodes : List ℂ)
    (hnodes : ∀ z ∈ nodes, z ∈ ball (0 : ℂ) 1)
    {f g : ℂ → ℂ} (hf : IsSchur f) (hg : IsSchur g)
    (hmin : HasMinimalNormOneJets nodes f) (hjet : JetEq nodes g f) :
    EqOn g f (ball 0 1) := by
  induction nodes generalizing f g with
  | nil =>
      exfalso
      apply hmin
      refine ⟨Function.const ℂ 0, ?_, ?_, hasStrictDiscBound_zero⟩
      · exact ⟨by fun_prop, by simp [MapsTo]⟩
      · intro z
        simp [jetMultiplicity_nil]
  | cons a nodes ih =>
      have ha : a ∈ ball (0 : ℂ) 1 := hnodes a (by simp)
      have htail : ∀ z ∈ nodes, z ∈ ball (0 : ℂ) 1 :=
        fun z hz => hnodes z (by simp [hz])
      have hfa : AnalyticAt ℂ f a :=
        hf.differentiableOn.analyticAt (isOpen_ball.mem_nhds ha)
      have hga : AnalyticAt ℂ g a :=
        hg.differentiableOn.analyticAt (isOpen_ball.mem_nhds ha)
      have hvalue : g a = f a := hjet.eq_at_head hga hfa
      rcases hf.eqOn_unimodular_const_or_mapsTo_ball with hconst | hfmaps
      · obtain ⟨c, hc, hfc⟩ := hconst
        rcases hg.eqOn_unimodular_const_or_mapsTo_ball with ⟨d, hd, hgd⟩ | hgmaps
        · intro z hz
          calc
            g z = d := hgd hz
            _ = g a := (hgd ha).symm
            _ = f a := hvalue
            _ = c := hfc ha
            _ = f z := (hfc hz).symm
        · have hgaD := hgmaps ha
          have hlt : ‖g a‖ < 1 := by simpa [mem_ball_zero_iff] using hgaD
          have heq : ‖g a‖ = 1 := by
            calc
              ‖g a‖ = ‖f a‖ := congrArg norm hvalue
              _ = ‖c‖ := by simpa using congrArg norm (hfc ha)
              _ = 1 := hc
          rw [heq] at hlt
          exfalso
          exact (lt_self_iff_false 1).mp hlt
      · have hgmaps : MapsTo g (ball 0 1) (ball 0 1) :=
          hg.mapsTo_ball_of_apply_mem_ball ha (by rw [hvalue]; exact hfmaps ha)
        let rf := DiskRigidity.Complex.schurReduce f a
        let rg := DiskRigidity.Complex.schurReduce g a
        have hrf : IsSchur rf := isSchur_schurReduce hf hfmaps ha
        have hrg : IsSchur rg := isSchur_schurReduce hg hgmaps ha
        have hrjet : JetEq nodes rg rf := hjet.schurReduce hg hf hgmaps hfmaps ha htail
        have hrmin : HasMinimalNormOneJets nodes rf := by
          intro hex
          obtain ⟨q, hq, hqjet, hqbound⟩ := hex
          let Q := schurReconstruct a (f a) q
          have hQ : IsSchur Q := isSchur_schurReconstruct hq ha (hfmaps ha)
          have htmp : JetEq (a :: nodes) Q (schurReconstruct a (f a) rf) :=
            hqjet.schurReconstruct hq hrf ha (hfmaps ha) htail
          have hrec : EqOn (schurReconstruct a (f a) rf) f (ball 0 1) :=
            fun z hz => schurReconstruct_reduce hfmaps ha hz
          have hQjet : JetEq (a :: nodes) Q f := htmp.congr_right hnodes hrec
          have hQbound : HasStrictDiscBound Q :=
            hqbound.schurReconstruct ha (hfmaps ha)
          exact hmin ⟨Q, hQ, hQjet, hQbound⟩
        have hreduced : EqOn rg rf (ball 0 1) :=
          ih htail hrf hrg hrmin hrjet
        intro z hz
        calc
          g z = schurReconstruct a (g a) rg z :=
            (schurReconstruct_reduce hgmaps ha hz).symm
          _ = schurReconstruct a (f a) rf z := by
            simp only [schurReconstruct, hvalue, hreduced hz]
          _ = f z := schurReconstruct_reduce hfmaps ha hz

/-- Existence of a finite Blaschke interpolant together with uniqueness of every norm-one Schur
interpolant in the minimal-norm case. -/
theorem exists_schurFiniteBlaschke_unique_of_hasMinimalNormOneJets (nodes : List ℂ)
    (hnodes : ∀ z ∈ nodes, z ∈ ball (0 : ℂ) 1)
    {f : ℂ → ℂ} (hf : IsSchur f) (hmin : HasMinimalNormOneJets nodes f) :
    ∃ B : ℂ → ℂ, IsSchurFiniteBlaschke B ∧ JetEq nodes B f ∧
      ∀ g : ℂ → ℂ, IsSchur g → JetEq nodes g f → EqOn g B (ball 0 1) := by
  obtain ⟨B, hB, hBjet⟩ := exists_schurFiniteBlaschke_jetEq nodes hnodes hf
  have hBf : EqOn B f (ball 0 1) :=
    eqOn_of_hasMinimalNormOneJets nodes hnodes hf hB.isSchur hmin hBjet
  refine ⟨B, hB, hBjet, fun g hg hgjet z hz => ?_⟩
  calc
    g z = f z := eqOn_of_hasMinimalNormOneJets nodes hnodes hf hg hmin hgjet hz
    _ = B z := (hBf hz).symm

end

end DiskRigidity.Complex
