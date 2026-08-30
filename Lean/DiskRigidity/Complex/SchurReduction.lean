/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.FiniteBlaschke
public import DiskRigidity.Complex.UnitDiscShift
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.Schwarz

/-!
# The one-step Schur reduction

This file develops the scalar Schwarz--Pick estimate and the removable quotient used by the
finite Schur algorithm.  Everything is stated for ordinary functions on `ℂ`; no bundled space of
holomorphic functions is needed.
-/

open Filter Function Metric Set
open scoped ComplexConjugate Topology

namespace DiskRigidity.Complex

@[expose] public section

/-- The inverse of the Blaschke factor centred at `-w`. -/
noncomputable def discShift (w z : ℂ) : ℂ :=
  (w + z) / (1 + conj w * z)

@[simp]
theorem discShift_zero (w : ℂ) : discShift w 0 = w := by
  simp [discShift]

theorem discShift_eq_blaschkeFactor_neg (w z : ℂ) :
    discShift w z = blaschkeFactor (-w) z := by
  simp [discShift, blaschkeFactor_apply, add_comm]

/-- The scalar formula agrees with the bundled unit-disc shift. -/
theorem discShift_eq_coe_shift (w z : _root_.Complex.UnitDisc) :
    discShift w z = (w.shift z : ℂ) := by
  rw [discShift, _root_.Complex.UnitDisc.coe_shift]

/-- A scalar disc shift maps the open unit disc to itself. -/
theorem mapsTo_ball_discShift {w : ℂ} (hw : w ∈ ball 0 1) :
    MapsTo (discShift w) (ball 0 1) (ball 0 1) := by
  intro z hz
  let w' : _root_.Complex.UnitDisc := ⟨w, by simpa [mem_ball_zero_iff] using hw⟩
  let z' : _root_.Complex.UnitDisc := ⟨z, by simpa [mem_ball_zero_iff] using hz⟩
  have h := (w'.shift z').norm_lt_one
  have heq : discShift w z = (w'.shift z' : ℂ) := by
    rw [← show (w' : ℂ) = w by rfl, ← show (z' : ℂ) = z by rfl]
    exact discShift_eq_coe_shift w' z'
  rw [mem_ball_zero_iff]
  calc
    ‖discShift w z‖ = ‖(w'.shift z' : ℂ)‖ := congrArg norm heq
    _ < 1 := h

/-- A scalar disc shift is holomorphic in a neighbourhood of the closed unit disc. -/
theorem analyticOnNhd_discShift {w : ℂ} (hw : w ∈ ball 0 1) :
    AnalyticOnNhd ℂ (discShift w) (closedBall 0 1) := by
  rw [show discShift w = blaschkeFactor (-w) from funext (discShift_eq_blaschkeFactor_neg w)]
  exact analyticOnNhd_blaschkeFactor (show -w ∈ ball (0 : ℂ) 1 by simpa using hw)

/-- A scalar disc shift maps the closed unit disc to itself. -/
theorem mapsTo_closedBall_discShift {w : ℂ} (hw : w ∈ ball 0 1) :
    MapsTo (discShift w) (closedBall 0 1) (closedBall 0 1) := by
  have hcont : ContinuousOn (discShift w) (closure (ball (0 : ℂ) 1)) := by
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact (analyticOnNhd_discShift hw).continuousOn
  have h := (mapsTo_ball_discShift hw).closure_of_continuousOn
    hcont
  simpa only [closure_ball (0 : ℂ) one_ne_zero] using h

/-- A scalar disc shift preserves the unit circle. -/
theorem norm_discShift_eq_one {w z : ℂ} (hw : w ∈ ball 0 1) (hz : z ∈ sphere 0 1) :
    ‖discShift w z‖ = 1 := by
  rw [discShift_eq_blaschkeFactor_neg]
  exact norm_blaschkeFactor_eq_one (by simpa using hw) hz

/-- Opposite scalar shifts are inverse on the open unit disc. -/
theorem discShift_neg_apply_discShift {w z : ℂ} (hw : w ∈ ball 0 1)
    (hz : z ∈ ball 0 1) : discShift (-w) (discShift w z) = z := by
  let w' : _root_.Complex.UnitDisc := ⟨w, by simpa [mem_ball_zero_iff] using hw⟩
  let z' : _root_.Complex.UnitDisc := ⟨z, by simpa [mem_ball_zero_iff] using hz⟩
  have h := congrArg (fun u : _root_.Complex.UnitDisc => (u : ℂ))
    (_root_.Complex.UnitDisc.shift_neg_apply_shift w' z')
  have h₁ : discShift w z = (w'.shift z' : ℂ) := by
    rw [← show (w' : ℂ) = w by rfl, ← show (z' : ℂ) = z by rfl]
    exact discShift_eq_coe_shift w' z'
  have h₂ : discShift (-w) (w'.shift z') = ((-w').shift (w'.shift z') : ℂ) := by
    rw [← show ((-w' : _root_.Complex.UnitDisc) : ℂ) = -w by rfl]
    exact discShift_eq_coe_shift (-w') (w'.shift z')
  calc
    discShift (-w) (discShift w z) = discShift (-w) (w'.shift z') := by rw [h₁]
    _ = ((-w').shift (w'.shift z') : _root_.Complex.UnitDisc) := h₂
    _ = z := h

/-- A denominator occurring in a disc automorphism cannot vanish on the closed disc. -/
theorem discShift_den_ne_zero {w z : ℂ} (hw : w ∈ ball 0 1)
    (hz : z ∈ closedBall 0 1) : 1 + conj w * z ≠ 0 := by
  have h := blaschkeFactor_den_ne_zero
    (show -w ∈ ball (0 : ℂ) 1 by simpa using hw) hz
  simpa [map_neg] using h

/-- The pseudo-hyperbolic factor between two scalar points. -/
noncomputable def pseudoHyperbolicFactor (w z : ℂ) : ℂ :=
  blaschkeFactor w z

/-- **Schwarz--Pick inequality.** A holomorphic self-map of the open disc contracts the
pseudo-hyperbolic factor. -/
theorem norm_pseudoHyperbolicFactor_map_le {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hmaps : MapsTo f (ball 0 1) (ball 0 1))
    {a z : ℂ} (ha : a ∈ ball 0 1) (hz : z ∈ ball 0 1) :
    ‖pseudoHyperbolicFactor (f a) (f z)‖ ≤ ‖pseudoHyperbolicFactor a z‖ := by
  let a' : _root_.Complex.UnitDisc := ⟨a, by simpa [mem_ball_zero_iff] using ha⟩
  let fa' : _root_.Complex.UnitDisc :=
    ⟨f a, by simpa [mem_ball_zero_iff] using hmaps ha⟩
  let source : ℂ → ℂ := discShift a
  let target : ℂ → ℂ := fun y => blaschkeFactor (f a) y
  let g : ℂ → ℂ := target ∘ f ∘ source
  have hsource_maps : MapsTo source (ball 0 1) (ball 0 1) :=
    mapsTo_ball_discShift ha
  have htarget_maps : MapsTo target (ball 0 1) (ball 0 1) := by
    intro y hy
    let hy' : _root_.Complex.UnitDisc :=
      ⟨y, by simpa [mem_ball_zero_iff] using hy⟩
    have hshift := ((-fa').shift hy').norm_lt_one
    have heq : discShift (-(f a)) y = ((-fa').shift hy' : ℂ) := by
      rw [← show ((-fa' : _root_.Complex.UnitDisc) : ℂ) = -(f a) by rfl,
        ← show (hy' : ℂ) = y by rfl]
      exact discShift_eq_coe_shift (-fa') hy'
    rw [mem_ball_zero_iff]
    calc
      ‖target y‖ = ‖discShift (-(f a)) y‖ := by
        simp only [target, discShift_eq_blaschkeFactor_neg, neg_neg]
      _ = ‖((-fa').shift hy' : ℂ)‖ := congrArg norm heq
      _ < 1 := hshift
  have hsource_diff : DifferentiableOn ℂ source (ball 0 1) :=
    (analyticOnNhd_discShift ha).differentiableOn.mono ball_subset_closedBall
  have htarget_diff : DifferentiableOn ℂ target (ball 0 1) :=
    (analyticOnNhd_blaschkeFactor (hmaps ha)).differentiableOn.mono ball_subset_closedBall
  have hgdiff : DifferentiableOn ℂ g (ball 0 1) :=
    htarget_diff.comp (hf.comp hsource_diff hsource_maps) (hmaps.comp hsource_maps)
  have hgmaps : MapsTo g (ball 0 1) (closedBall 0 1) := fun x hx =>
    ball_subset_closedBall (htarget_maps (hmaps (hsource_maps hx)))
  have hgzero : g 0 = 0 := by simp [g, target, source, discShift, blaschkeFactor_apply]
  have hxi : pseudoHyperbolicFactor a z ∈ ball (0 : ℂ) 1 := by
    let z' : _root_.Complex.UnitDisc :=
      ⟨z, by simpa [mem_ball_zero_iff] using hz⟩
    have hshift := ((-a').shift z').norm_lt_one
    have heq : discShift (-a) z = ((-a').shift z' : ℂ) := by
      rw [← show ((-a' : _root_.Complex.UnitDisc) : ℂ) = -a by rfl,
        ← show (z' : ℂ) = z by rfl]
      exact discShift_eq_coe_shift (-a') z'
    rw [mem_ball_zero_iff]
    calc
      ‖pseudoHyperbolicFactor a z‖ = ‖discShift (-a) z‖ := by
        simp only [pseudoHyperbolicFactor, discShift_eq_blaschkeFactor_neg, neg_neg]
      _ = ‖((-a').shift z' : ℂ)‖ := congrArg norm heq
      _ < 1 := hshift
  have hsource_inv : source (pseudoHyperbolicFactor a z) = z := by
    change discShift a (blaschkeFactor a z) = z
    have hbshift : blaschkeFactor a z = discShift (-a) z := by
      simpa using (discShift_eq_blaschkeFactor_neg (-a) z).symm
    rw [hbshift]
    simpa only [neg_neg] using
      discShift_neg_apply_discShift (w := -a) (z := z) (by simpa using ha) hz
  calc
    ‖pseudoHyperbolicFactor (f a) (f z)‖ = ‖g (pseudoHyperbolicFactor a z)‖ := by
      change ‖blaschkeFactor (f a) (f z)‖ =
        ‖blaschkeFactor (f a) (f (source (pseudoHyperbolicFactor a z)))‖
      rw [hsource_inv]
    _ ≤ ‖pseudoHyperbolicFactor a z‖ :=
      _root_.Complex.norm_le_norm_of_mapsTo_ball hgdiff hgmaps hgzero
        (by simpa [mem_ball_zero_iff] using hxi)

/-- A Blaschke factor maps the open disc to itself. -/
theorem mapsTo_ball_blaschkeFactor {a : ℂ} (ha : a ∈ ball 0 1) :
    MapsTo (blaschkeFactor a) (ball 0 1) (ball 0 1) := by
  rw [show blaschkeFactor a = discShift (-a) from
    funext fun z => by simpa using (discShift_eq_blaschkeFactor_neg (-a) z).symm]
  exact mapsTo_ball_discShift (show -a ∈ ball (0 : ℂ) 1 by simpa using ha)

/-- A Blaschke factor maps the closed disc to itself. -/
theorem mapsTo_closedBall_blaschkeFactor {a : ℂ} (ha : a ∈ ball 0 1) :
    MapsTo (blaschkeFactor a) (closedBall 0 1) (closedBall 0 1) := by
  rw [show blaschkeFactor a = discShift (-a) from
    funext fun z => by simpa using (discShift_eq_blaschkeFactor_neg (-a) z).symm]
  exact mapsTo_closedBall_discShift (show -a ∈ ball (0 : ℂ) 1 by simpa using ha)

/-- The target-normalized function used in one Schur step. -/
noncomputable def schurNormalize (f : ℂ → ℂ) (a z : ℂ) : ℂ :=
  blaschkeFactor (f a) (f z)

@[simp]
theorem schurNormalize_self (f : ℂ → ℂ) (a : ℂ) : schurNormalize f a a = 0 := by
  simp [schurNormalize, blaschkeFactor_apply]

/-- The removable quotient in one Schur step.  Writing it with `dslope` gives the value at the
removed point canonically, namely the derivative of the normalized function. -/
noncomputable def schurReduce (f : ℂ → ℂ) (a z : ℂ) : ℂ :=
  (1 - conj a * z) * dslope (schurNormalize f a) a z

/-- Reconstruction from a reduced Schur function. -/
noncomputable def schurReconstruct (a w : ℂ) (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  discShift w (blaschkeFactor a z * g z)

/-- Away from the removed node, the Schur reduction is the quotient of the two
pseudo-hyperbolic factors. -/
theorem schurReduce_apply_of_ne {f : ℂ → ℂ} {a z : ℂ} (hza : z ≠ a) :
    schurReduce f a z = schurNormalize f a z / blaschkeFactor a z := by
  rw [schurReduce, dslope_of_ne _ hza]
  simp only [slope_def_module, smul_eq_mul, schurNormalize_self, sub_zero,
    blaschkeFactor_apply]
  have hden : z - a ≠ 0 := sub_ne_zero.mpr hza
  field_simp

/-- Reduction followed by reconstruction recovers the original function on the open disc. -/
theorem schurReconstruct_reduce {f : ℂ → ℂ}
    (hmaps : MapsTo f (ball 0 1) (ball 0 1))
    {a z : ℂ} (ha : a ∈ ball 0 1) (hz : z ∈ ball 0 1) :
    schurReconstruct a (f a) (schurReduce f a) z = f z := by
  have hfa := hmaps ha
  rw [schurReconstruct]
  by_cases hza : z = a
  · subst z
    simp [blaschkeFactor_apply]
  · rw [schurReduce_apply_of_ne hza]
    have hb : blaschkeFactor a z ≠ 0 :=
      (blaschkeFactor_eq_zero_iff ha hz).not.mpr hza
    have hcancel : blaschkeFactor a z *
        (schurNormalize f a z / blaschkeFactor a z) = schurNormalize f a z := by
      field_simp
    rw [hcancel]
    change discShift (f a) (blaschkeFactor (f a) (f z)) = f z
    have hbshift : blaschkeFactor (f a) (f z) = discShift (-(f a)) (f z) := by
      simpa using (discShift_eq_blaschkeFactor_neg (-(f a)) (f z)).symm
    rw [hbshift]
    simpa [schurNormalize, pseudoHyperbolicFactor] using
      discShift_neg_apply_discShift (w := -(f a)) (z := f z) (by simpa using hfa)
        (hmaps hz)

/-! ## Schur-class closure -/

/-- A scalar Schur function is holomorphic on the open disc and has norm at most one there. -/
def IsSchur (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f (ball 0 1) ∧ MapsTo f (ball 0 1) (closedBall 0 1)

theorem IsSchur.differentiableOn {f : ℂ → ℂ} (hf : IsSchur f) :
    DifferentiableOn ℂ f (ball 0 1) :=
  hf.1

theorem IsSchur.norm_le {f : ℂ → ℂ} (hf : IsSchur f) {z : ℂ} (hz : z ∈ ball 0 1) :
    ‖f z‖ ≤ 1 := by
  simpa [mem_closedBall_zero_iff] using hf.2 hz

/-- A Schur function either is a unimodular constant or takes all of its values in the open
disc.  This is the maximum-modulus dichotomy needed at every recursive step. -/
theorem IsSchur.eqOn_unimodular_const_or_mapsTo_ball {f : ℂ → ℂ} (hf : IsSchur f) :
    (∃ c : ℂ, ‖c‖ = 1 ∧ EqOn f (Function.const ℂ c) (ball 0 1)) ∨
      MapsTo f (ball 0 1) (ball 0 1) := by
  by_cases hmaps : MapsTo f (ball 0 1) (ball 0 1)
  · exact Or.inr hmaps
  · left
    simp only [MapsTo, mem_ball_zero_iff, not_forall] at hmaps
    obtain ⟨z, hz⟩ := hmaps
    push Not at hz
    have hzD : z ∈ ball (0 : ℂ) 1 := by simpa [mem_ball_zero_iff] using hz.1
    have hle := hf.norm_le hzD
    have heq : ‖f z‖ = 1 := le_antisymm hle hz.2
    have hmax : IsMaxOn (norm ∘ f) (ball 0 1) z := by
      intro y hy
      change ‖f y‖ ≤ ‖f z‖
      rw [heq]
      exact hf.norm_le hy
    exact ⟨f z, heq,
      _root_.Complex.eq_const_of_exists_max hf.differentiableOn hzD hmax⟩

/-- The normalized function in a Schur step is holomorphic on the disc. -/
theorem differentiableOn_schurNormalize {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hmaps : MapsTo f (ball 0 1) (ball 0 1)) {a : ℂ} (ha : a ∈ ball 0 1) :
    DifferentiableOn ℂ (schurNormalize f a) (ball 0 1) := by
  have hout := (analyticOnNhd_blaschkeFactor (hmaps ha)).differentiableOn.mono
    ball_subset_closedBall
  exact hout.comp hf hmaps

/-- The removable Schur quotient is holomorphic on the disc. -/
theorem differentiableOn_schurReduce {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hmaps : MapsTo f (ball 0 1) (ball 0 1)) {a : ℂ} (ha : a ∈ ball 0 1) :
    DifferentiableOn ℂ (schurReduce f a) (ball 0 1) := by
  have hn := differentiableOn_schurNormalize hf hmaps ha
  have hds : DifferentiableOn ℂ (dslope (schurNormalize f a) a) (ball 0 1) :=
    (_root_.Complex.differentiableOn_dslope (isOpen_ball.mem_nhds ha)).mpr hn
  intro z hz
  have hp : DifferentiableWithinAt ℂ (fun y : ℂ => 1 - conj a * y) (ball 0 1) z := by
    fun_prop
  change DifferentiableWithinAt ℂ
    (fun y : ℂ => (1 - conj a * y) * dslope (schurNormalize f a) a y) (ball 0 1) z
  exact hp.mul (hds z hz)

/-- The Schur quotient has norm at most one away from the removed node. -/
theorem norm_schurReduce_le_of_ne {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hmaps : MapsTo f (ball 0 1) (ball 0 1)) {a z : ℂ}
    (ha : a ∈ ball 0 1) (hz : z ∈ ball 0 1) (hza : z ≠ a) :
    ‖schurReduce f a z‖ ≤ 1 := by
  rw [schurReduce_apply_of_ne hza, norm_div, div_le_one]
  · exact norm_pseudoHyperbolicFactor_map_le hf hmaps ha hz
  · exact norm_pos_iff.mpr ((blaschkeFactor_eq_zero_iff ha hz).not.mpr hza)

/-- One Schur reduction stays in the Schur class. -/
theorem isSchur_schurReduce {f : ℂ → ℂ} (hf : IsSchur f)
    (hmaps : MapsTo f (ball 0 1) (ball 0 1)) {a : ℂ} (ha : a ∈ ball 0 1) :
    IsSchur (schurReduce f a) := by
  have hdiff := differentiableOn_schurReduce hf.differentiableOn hmaps ha
  refine ⟨hdiff, fun z hz => ?_⟩
  rw [mem_closedBall_zero_iff]
  by_cases hza : z = a
  · subst z
    have hcont : ContinuousAt (schurReduce f a) a :=
      (hdiff.differentiableAt (isOpen_ball.mem_nhds ha)).continuousAt
    have hD : ball (0 : ℂ) 1 ∈ 𝓝[≠] a :=
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds ha)
    have hevent : ∀ᶠ y in 𝓝[≠] a, schurReduce f a y ∈ closedBall (0 : ℂ) 1 := by
      filter_upwards [hD, self_mem_nhdsWithin] with y hyD hya
      rw [mem_closedBall_zero_iff]
      exact norm_schurReduce_le_of_ne hf.differentiableOn hmaps ha hyD hya
    have hmem := isClosed_closedBall.mem_of_tendsto
      (hcont.tendsto.mono_left nhdsWithin_le_nhds) hevent
    simpa [mem_closedBall_zero_iff] using hmem
  · exact norm_schurReduce_le_of_ne hf.differentiableOn hmaps ha hz hza

/-- Reconstruction from a Schur function is again a Schur function. -/
theorem isSchur_schurReconstruct {g : ℂ → ℂ} (hg : IsSchur g)
    {a w : ℂ} (ha : a ∈ ball 0 1) (hw : w ∈ ball 0 1) :
    IsSchur (schurReconstruct a w g) := by
  let x : ℂ → ℂ := fun z => blaschkeFactor a z * g z
  have hbdiff : DifferentiableOn ℂ (blaschkeFactor a) (ball 0 1) :=
    (analyticOnNhd_blaschkeFactor ha).differentiableOn.mono ball_subset_closedBall
  have hxdiff : DifferentiableOn ℂ x (ball 0 1) := hbdiff.mul hg.differentiableOn
  have hxmaps : MapsTo x (ball 0 1) (ball 0 1) := by
    intro z hz
    rw [mem_ball_zero_iff]
    simp only [x, norm_mul]
    have hb : ‖blaschkeFactor a z‖ < 1 := by
      simpa [mem_ball_zero_iff] using mapsTo_ball_blaschkeFactor ha hz
    calc
      ‖blaschkeFactor a z‖ * ‖g z‖ ≤ ‖blaschkeFactor a z‖ * 1 :=
        mul_le_mul_of_nonneg_left (hg.norm_le hz) (norm_nonneg _)
      _ < 1 := by simpa using hb
  have hsdiff := (analyticOnNhd_discShift hw).differentiableOn.mono ball_subset_closedBall
  have hdiff : DifferentiableOn ℂ (discShift w ∘ x) (ball 0 1) :=
    hsdiff.comp hxdiff hxmaps
  refine ⟨?_, ?_⟩
  · change DifferentiableOn ℂ (discShift w ∘ x) (ball 0 1)
    exact hdiff
  · intro z hz
    have hout := mapsTo_ball_discShift hw (hxmaps hz)
    exact ball_subset_closedBall <| by
      change discShift w (x z) ∈ ball (0 : ℂ) 1
      exact hout

/-! ## Recursive finite Blaschke products -/

/-- The Schur-recursive characterization of a finite Blaschke product.  A unimodular constant is
the degree-zero case; adjoining a Schur node is the inverse step of the finite Schur algorithm. -/
inductive IsSchurFiniteBlaschke : (ℂ → ℂ) → Prop
  | const (c : ℂ) (hc : ‖c‖ = 1) :
      IsSchurFiniteBlaschke (Function.const ℂ c)
  | reconstruct {B : ℂ → ℂ} (hB : IsSchurFiniteBlaschke B)
      {a w : ℂ} (ha : a ∈ ball 0 1) (hw : w ∈ ball 0 1) :
      IsSchurFiniteBlaschke (schurReconstruct a w B)

/-- Every recursively presented finite Blaschke product belongs to the Schur class. -/
theorem IsSchurFiniteBlaschke.isSchur {B : ℂ → ℂ} (hB : IsSchurFiniteBlaschke B) :
    IsSchur B := by
  induction hB with
  | const c hc =>
      refine ⟨by fun_prop, fun z hz => ?_⟩
      simp [hc]
  | reconstruct hB ha hw ih => exact isSchur_schurReconstruct ih ha hw

/-- Every recursively presented finite Blaschke product has modulus one on the unit circle. -/
theorem IsSchurFiniteBlaschke.norm_eq_one {B : ℂ → ℂ} (hB : IsSchurFiniteBlaschke B)
    {z : ℂ} (hz : z ∈ sphere 0 1) : ‖B z‖ = 1 := by
  induction hB with
  | const c hc => simpa using hc
  | @reconstruct B hB a w ha hw ih =>
      have hx : blaschkeFactor a z * B z ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_mul, norm_blaschkeFactor_eq_one ha hz, ih,
          one_mul]
      change ‖discShift w (blaschkeFactor a z * B z)‖ = 1
      exact norm_discShift_eq_one hw hx

/-- A recursively presented finite Blaschke product is holomorphic in a neighbourhood of the
closed unit disc. -/
theorem IsSchurFiniteBlaschke.analyticOnNhd {B : ℂ → ℂ} (hB : IsSchurFiniteBlaschke B) :
    AnalyticOnNhd ℂ B (closedBall 0 1) := by
  induction hB with
  | const c hc => exact fun z hz => analyticAt_const
  | @reconstruct B hB a w ha hw ih =>
      intro z hz
      have hba := analyticOnNhd_blaschkeFactor ha z hz
      have hx : AnalyticAt ℂ (fun y => blaschkeFactor a y * B y) z := hba.mul (ih z hz)
      have hcont : ContinuousOn B (closure (ball (0 : ℂ) 1)) := by
        rw [closure_ball (0 : ℂ) one_ne_zero]
        exact ih.continuousOn
      have hBclosed : MapsTo B (closedBall 0 1) (closedBall 0 1) := by
        have hm := hB.isSchur.2.closure_of_continuousOn hcont
        simpa only [closure_ball (0 : ℂ) one_ne_zero, closure_closedBall] using hm
      have hxmem : blaschkeFactor a z * B z ∈ closedBall (0 : ℂ) 1 := by
        rw [mem_closedBall_zero_iff, norm_mul]
        have hb := mapsTo_closedBall_blaschkeFactor ha hz
        have hBc := hBclosed hz
        simp only [mem_closedBall_zero_iff] at hb hBc
        calc
          ‖blaschkeFactor a z‖ * ‖B z‖ ≤ 1 * 1 :=
            mul_le_mul hb hBc (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      change AnalyticAt ℂ (discShift w ∘ fun y => blaschkeFactor a y * B y) z
      have hout : AnalyticAt ℂ (discShift w) (blaschkeFactor a z * B z) :=
        (analyticOnNhd_discShift hw) (blaschkeFactor a z * B z) hxmem
      exact hout.comp (f := fun y => blaschkeFactor a y * B y) hx

end

end DiskRigidity.Complex
