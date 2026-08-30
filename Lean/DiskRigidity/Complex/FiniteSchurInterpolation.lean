/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.SchurReduction
public import Mathlib.Analysis.Analytic.Order

/-!
# Finite confluent Schur interpolation

The interpolation conditions are encoded by a finite list of nodes.  Repetition of a node records
successive derivatives there.  The proof is the finite Schur recursion, with vanishing orders used
to avoid choosing coordinates for Taylor jets.
-/

open Filter Function Metric Set
open scoped ComplexConjugate Topology

namespace DiskRigidity.Complex

@[expose] public section

/-- The multiplicity of a point in a finite list of interpolation nodes. -/
noncomputable def jetMultiplicity (nodes : List ℂ) (z : ℂ) : ℕ := by
  classical exact nodes.count z

/-- Two functions have the same jets prescribed by `nodes` when their difference vanishes at each
point to at least its multiplicity in the list. -/
def JetEq (nodes : List ℂ) (f g : ℂ → ℂ) : Prop :=
  ∀ z, (jetMultiplicity nodes z : ℕ∞) ≤ analyticOrderAt (f - g) z

theorem jetMultiplicity_nil (z : ℂ) : jetMultiplicity [] z = 0 := by
  simp [jetMultiplicity]

theorem jetMultiplicity_cons (a : ℂ) (nodes : List ℂ) (z : ℂ) :
    jetMultiplicity (a :: nodes) z = (if a = z then jetMultiplicity nodes z + 1
      else jetMultiplicity nodes z) := by
  classical
  by_cases h : a = z
  · subst z
    simp [jetMultiplicity]
  · rw [if_neg h, jetMultiplicity, jetMultiplicity, List.count_cons_of_ne h]

/-- Vanishing-order jet equality implies equality of all the corresponding iterated derivatives. -/
theorem JetEq.iteratedDeriv_eq {nodes : List ℂ} {f g : ℂ → ℂ} (hfg : JetEq nodes f g)
    {z : ℂ} (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    {k : ℕ} (hk : k < jetMultiplicity nodes z) :
    iteratedDeriv k f z = iteratedDeriv k g z := by
  have horder : (jetMultiplicity nodes z : ℕ∞) ≤ analyticOrderAt (f - g) z := hfg z
  have hz := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf.sub hg)).mp horder k hk
  change iteratedDeriv k (fun i => f i - g i) z = 0 at hz
  rw [iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt] at hz
  exact sub_eq_zero.mp hz

/-- The vanishing order of an elementary Blaschke factor is one at its centre and zero at every
other point of the open disc. -/
theorem analyticOrderAt_blaschkeFactor {a z : ℂ} (ha : a ∈ ball 0 1)
    (hz : z ∈ ball 0 1) :
    analyticOrderAt (blaschkeFactor a) z = if z = a then 1 else 0 := by
  have hb : AnalyticAt ℂ (blaschkeFactor a) z :=
    analyticOnNhd_blaschkeFactor ha z (ball_subset_closedBall hz)
  split_ifs with hza
  · subst z
    let q : ℂ → ℂ := fun y => (1 - conj a * y)⁻¹
    have hden : 1 - conj a * a ≠ 0 :=
      blaschkeFactor_den_ne_zero ha (ball_subset_closedBall ha)
    have hq : AnalyticAt ℂ q a := by
      dsimp only [q]
      fun_prop
    have hq0 : q a ≠ 0 := inv_ne_zero hden
    have heq : blaschkeFactor a = (fun y => y - a) * q := by
      funext y
      simp [blaschkeFactor_apply, q, div_eq_mul_inv]
    rw [heq, analyticOrderAt_mul (by fun_prop) hq,
      analyticOrderAt_id_sub_const_self, hq.analyticOrderAt_eq_zero.mpr hq0]
    norm_num
  · exact hb.analyticOrderAt_eq_zero.mpr
      ((blaschkeFactor_eq_zero_iff ha hz).not.mpr hza)

/-- The nonvanishing analytic multiplier relating the differences of two inverse Schur steps. -/
noncomputable def reconstructDiffMultiplier (a w : ℂ) (G g : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 - w * conj w) /
    ((1 + conj w * (blaschkeFactor a z * G z)) *
      (1 + conj w * (blaschkeFactor a z * g z)))

/-- Difference formula for two inverse Schur steps at points of the open disc. -/
theorem schurReconstruct_sub_eq {G g : ℂ → ℂ} (hG : IsSchur G) (hg : IsSchur g)
    {a w z : ℂ} (ha : a ∈ ball 0 1) (hw : w ∈ ball 0 1) (hz : z ∈ ball 0 1) :
    schurReconstruct a w G z - schurReconstruct a w g z =
      reconstructDiffMultiplier a w G g z * blaschkeFactor a z * (G z - g z) := by
  have hb := mapsTo_ball_blaschkeFactor ha hz
  have hxG : blaschkeFactor a z * G z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_mul]
    have hb' : ‖blaschkeFactor a z‖ < 1 := by simpa [mem_ball_zero_iff] using hb
    calc
      ‖blaschkeFactor a z‖ * ‖G z‖ ≤ ‖blaschkeFactor a z‖ * 1 :=
        mul_le_mul_of_nonneg_left (hG.norm_le hz) (norm_nonneg _)
      _ < 1 := by simpa using hb'
  have hxg : blaschkeFactor a z * g z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_mul]
    have hb' : ‖blaschkeFactor a z‖ < 1 := by simpa [mem_ball_zero_iff] using hb
    calc
      ‖blaschkeFactor a z‖ * ‖g z‖ ≤ ‖blaschkeFactor a z‖ * 1 :=
        mul_le_mul_of_nonneg_left (hg.norm_le hz) (norm_nonneg _)
      _ < 1 := by simpa using hb'
  have hdenG := discShift_den_ne_zero hw (ball_subset_closedBall hxG)
  have hdeng := discShift_den_ne_zero hw (ball_subset_closedBall hxg)
  have halg (x y : ℂ) (hx : 1 + conj w * x ≠ 0) (hy : 1 + conj w * y ≠ 0) :
      (w + x) / (1 + conj w * x) - (w + y) / (1 + conj w * y) =
        ((1 - w * conj w) / ((1 + conj w * x) * (1 + conj w * y))) * (x - y) := by
    have hx' : 1 + x * conj w ≠ 0 := by simpa [mul_comm] using hx
    have hy' : 1 + y * conj w ≠ 0 := by simpa [mul_comm] using hy
    field_simp [hx', hy']
    ring
  rw [schurReconstruct, schurReconstruct, discShift, discShift, reconstructDiffMultiplier]
  calc
    (w + blaschkeFactor a z * G z) / (1 + conj w * (blaschkeFactor a z * G z)) -
        (w + blaschkeFactor a z * g z) / (1 + conj w * (blaschkeFactor a z * g z)) =
      ((1 - w * conj w) /
        ((1 + conj w * (blaschkeFactor a z * G z)) *
          (1 + conj w * (blaschkeFactor a z * g z)))) *
        (blaschkeFactor a z * G z - blaschkeFactor a z * g z) :=
      halg _ _ hdenG hdeng
    _ = ((1 - w * conj w) /
        ((1 + conj w * (blaschkeFactor a z * G z)) *
          (1 + conj w * (blaschkeFactor a z * g z)))) *
        blaschkeFactor a z * (G z - g z) := by ring

/-- Multiplying a Schur function by a Blaschke factor gives a strict-disc value at every
open-disc point. -/
theorem blaschkeFactor_mul_mem_ball {g : ℂ → ℂ} (hg : IsSchur g)
    {a z : ℂ} (ha : a ∈ ball 0 1) (hz : z ∈ ball 0 1) :
    blaschkeFactor a z * g z ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_mul]
  have hb : ‖blaschkeFactor a z‖ < 1 := by
    simpa [mem_ball_zero_iff] using mapsTo_ball_blaschkeFactor ha hz
  calc
    ‖blaschkeFactor a z‖ * ‖g z‖ ≤ ‖blaschkeFactor a z‖ * 1 :=
      mul_le_mul_of_nonneg_left (hg.norm_le hz) (norm_nonneg _)
    _ < 1 := by simpa using hb

/-- The difference multiplier is analytic and nonzero at every interpolation node. -/
theorem analyticAt_reconstructDiffMultiplier_ne_zero {G g : ℂ → ℂ}
    (hG : IsSchur G) (hg : IsSchur g) {a w z : ℂ}
    (ha : a ∈ ball 0 1) (hw : w ∈ ball 0 1) (hz : z ∈ ball 0 1) :
    AnalyticAt ℂ (reconstructDiffMultiplier a w G g) z ∧
      reconstructDiffMultiplier a w G g z ≠ 0 := by
  have hGa : AnalyticAt ℂ G z :=
    hG.differentiableOn.analyticAt (isOpen_ball.mem_nhds hz)
  have hga : AnalyticAt ℂ g z :=
    hg.differentiableOn.analyticAt (isOpen_ball.mem_nhds hz)
  have hba : AnalyticAt ℂ (blaschkeFactor a) z :=
    analyticOnNhd_blaschkeFactor ha z (ball_subset_closedBall hz)
  have hxG := blaschkeFactor_mul_mem_ball hG ha hz
  have hxg := blaschkeFactor_mul_mem_ball hg ha hz
  have hdenG := discShift_den_ne_zero hw (ball_subset_closedBall hxG)
  have hdeng := discShift_den_ne_zero hw (ball_subset_closedBall hxg)
  have hnum : 1 - w * conj w ≠ 0 := by
    have h := blaschkeFactor_den_ne_zero hw (ball_subset_closedBall hw)
    simpa [mul_comm] using h
  constructor
  · change AnalyticAt ℂ (fun y => (1 - w * conj w) /
      ((1 + conj w * (blaschkeFactor a y * G y)) *
        (1 + conj w * (blaschkeFactor a y * g y)))) z
    fun_prop (disch := exact mul_ne_zero hdenG hdeng)
  · exact div_ne_zero hnum (mul_ne_zero hdenG hdeng)

/-- An inverse Schur step adds precisely the zero of its source Blaschke factor to the order of
the difference. -/
theorem analyticOrderAt_schurReconstruct_sub {G g : ℂ → ℂ}
    (hG : IsSchur G) (hg : IsSchur g) {a w z : ℂ}
    (ha : a ∈ ball 0 1) (hw : w ∈ ball 0 1) (hz : z ∈ ball 0 1) :
    analyticOrderAt (schurReconstruct a w G - schurReconstruct a w g) z =
      analyticOrderAt (blaschkeFactor a) z + analyticOrderAt (G - g) z := by
  let M := reconstructDiffMultiplier a w G g
  have hM := analyticAt_reconstructDiffMultiplier_ne_zero hG hg ha hw hz
  have hb : AnalyticAt ℂ (blaschkeFactor a) z :=
    analyticOnNhd_blaschkeFactor ha z (ball_subset_closedBall hz)
  have hGz : AnalyticAt ℂ G z :=
    hG.differentiableOn.analyticAt (isOpen_ball.mem_nhds hz)
  have hgz : AnalyticAt ℂ g z :=
    hg.differentiableOn.analyticAt (isOpen_ball.mem_nhds hz)
  have heq : (schurReconstruct a w G - schurReconstruct a w g) =ᶠ[𝓝 z]
      fun y => M y * blaschkeFactor a y * (G y - g y) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    exact schurReconstruct_sub_eq hG hg ha hw hy
  rw [analyticOrderAt_congr heq]
  change analyticOrderAt ((M * blaschkeFactor a) * (G - g)) z = _
  rw [analyticOrderAt_mul (hM.1.mul hb) (hGz.sub hgz),
    analyticOrderAt_mul hM.1 hb, hM.1.analyticOrderAt_eq_zero.mpr hM.2, zero_add]

/-- A Schur inverse step transports all tail jets and adds the value condition at its new node. -/
theorem JetEq.schurReconstruct {nodes : List ℂ} {G g : ℂ → ℂ} (hjet : JetEq nodes G g)
    (hG : IsSchur G) (hg : IsSchur g) {a w : ℂ}
    (ha : a ∈ ball 0 1) (hw : w ∈ ball 0 1)
    (hnodes : ∀ z ∈ nodes, z ∈ ball (0 : ℂ) 1) :
    JetEq (a :: nodes) (schurReconstruct a w G) (schurReconstruct a w g) := by
  intro z
  by_cases hzmem : z ∈ a :: nodes
  · have hzD : z ∈ ball (0 : ℂ) 1 := by
      have hz_cases : z = a ∨ z ∈ nodes := by simpa using hzmem
      rcases hz_cases with hza | hztail
      · rw [hza]
        exact ha
      · exact hnodes z hztail
    rw [analyticOrderAt_schurReconstruct_sub hG hg ha hw hzD,
      analyticOrderAt_blaschkeFactor ha hzD, jetMultiplicity_cons]
    by_cases haz : a = z
    · subst z
      simpa [Nat.cast_add, add_comm] using add_le_add_left (hjet a) 1
    · rw [if_neg haz, if_neg (Ne.symm haz), zero_add]
      exact hjet z
  · have hcount : jetMultiplicity (a :: nodes) z = 0 := by
      classical
      exact List.count_eq_zero.mpr hzmem
    simp [hcount]

/-- Equality on the disc gives equality of every finite family of jets supported there. -/
theorem jetEq_of_eqOn {nodes : List ℂ} {f g : ℂ → ℂ}
    (hnodes : ∀ z ∈ nodes, z ∈ ball (0 : ℂ) 1)
    (hfg : EqOn f g (ball 0 1)) : JetEq nodes f g := by
  intro z
  by_cases hzmem : z ∈ nodes
  · have hzD := hnodes z hzmem
    have heq : (f - g) =ᶠ[𝓝 z] 0 := by
      filter_upwards [isOpen_ball.mem_nhds hzD] with y hy
      simp [hfg hy]
    rw [analyticOrderAt_congr heq, analyticOrderAt_eq_top.mpr (by simp)]
    exact le_top
  · have hcount : jetMultiplicity nodes z = 0 := by
      classical
      exact List.count_eq_zero.mpr hzmem
    simp [hcount]

/-- Replacing the right-hand function by one equal to it on the disc preserves all supported
jets. -/
theorem JetEq.congr_right {nodes : List ℂ} {B f g : ℂ → ℂ} (hBf : JetEq nodes B f)
    (hnodes : ∀ z ∈ nodes, z ∈ ball (0 : ℂ) 1) (hfg : EqOn f g (ball 0 1)) :
    JetEq nodes B g := by
  intro z
  by_cases hzmem : z ∈ nodes
  · have hzD := hnodes z hzmem
    have heq : (B - f) =ᶠ[𝓝 z] (B - g) := by
      filter_upwards [isOpen_ball.mem_nhds hzD] with y hy
      simp [hfg hy]
    rw [← analyticOrderAt_congr heq]
    exact hBf z
  · have hcount : jetMultiplicity nodes z = 0 := by
      classical
      exact List.count_eq_zero.mpr hzmem
    simp [hcount]

/-- **Finite confluent Schur interpolation.** Every finite family of jets realized by a Schur
function is realized by a finite Blaschke product.  Repeated entries of `nodes` are the confluent
(derivative) conditions. -/
theorem exists_schurFiniteBlaschke_jetEq (nodes : List ℂ)
    (hnodes : ∀ z ∈ nodes, z ∈ ball (0 : ℂ) 1) {f : ℂ → ℂ} (hf : IsSchur f) :
    ∃ B : ℂ → ℂ, IsSchurFiniteBlaschke B ∧ JetEq nodes B f := by
  induction nodes generalizing f with
  | nil =>
      refine ⟨Function.const ℂ 1, IsSchurFiniteBlaschke.const 1 (by simp), ?_⟩
      intro z
      simp [jetMultiplicity_nil]
  | cons a nodes ih =>
      have ha : a ∈ ball (0 : ℂ) 1 := hnodes a (by simp)
      have htail : ∀ z ∈ nodes, z ∈ ball (0 : ℂ) 1 := fun z hz => hnodes z (by simp [hz])
      rcases hf.eqOn_unimodular_const_or_mapsTo_ball with hconst | hmaps
      · obtain ⟨c, hc, hfc⟩ := hconst
        refine ⟨Function.const ℂ c, IsSchurFiniteBlaschke.const c hc, ?_⟩
        exact jetEq_of_eqOn hnodes fun z hz => (hfc hz).symm
      · have hred : IsSchur (schurReduce f a) := isSchur_schurReduce hf hmaps ha
        obtain ⟨G, hGfin, hGjet⟩ := ih htail hred
        let B := schurReconstruct a (f a) G
        have hfa := hmaps ha
        have hBfin : IsSchurFiniteBlaschke B :=
          IsSchurFiniteBlaschke.reconstruct hGfin ha hfa
        have htmp : JetEq (a :: nodes) B
            (schurReconstruct a (f a) (schurReduce f a)) :=
          hGjet.schurReconstruct hGfin.isSchur hred ha hfa htail
        have hrec : EqOn (schurReconstruct a (f a) (schurReduce f a)) f (ball 0 1) :=
          fun z hz => schurReconstruct_reduce hmaps ha hz
        exact ⟨B, hBfin, htmp.congr_right hnodes hrec⟩

/-- Derivative-facing form of finite confluent Schur interpolation. -/
theorem exists_schurFiniteBlaschke_iteratedDeriv_eq (nodes : List ℂ)
    (hnodes : ∀ z ∈ nodes, z ∈ ball (0 : ℂ) 1) {f : ℂ → ℂ} (hf : IsSchur f) :
    ∃ B : ℂ → ℂ, IsSchurFiniteBlaschke B ∧
      ∀ z ∈ nodes, ∀ k < jetMultiplicity nodes z,
        iteratedDeriv k B z = iteratedDeriv k f z := by
  obtain ⟨B, hB, hjet⟩ := exists_schurFiniteBlaschke_jetEq nodes hnodes hf
  refine ⟨B, hB, fun z hz k hk => ?_⟩
  have hBa : AnalyticAt ℂ B z := hB.analyticOnNhd z (ball_subset_closedBall (hnodes z hz))
  have hfa : AnalyticAt ℂ f z := hf.differentiableOn.analyticAt
    (isOpen_ball.mem_nhds (hnodes z hz))
  exact hjet.iteratedDeriv_eq hBa hfa hk


end

end DiskRigidity.Complex
