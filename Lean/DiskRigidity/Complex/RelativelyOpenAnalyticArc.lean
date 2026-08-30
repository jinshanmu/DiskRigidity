/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Complex.RadialUniqueExposure

/-!
# Relatively open subarcs of a convex boundary

An injective continuous interval in the frontier of a planar compact convex
body contains a smaller subarc which is relatively open in the whole
frontier.  The proof transports the frontier to the circle by radial gauge
rescaling and uses a local argument coordinate on the circle.
-/

noncomputable section

open Filter Function Metric Set Topology
open scoped Real

namespace DiskRigidity.Complex

@[expose] public section

namespace NumericalRangeArc

/-- A smaller part of an injective continuous convex-boundary arc is the
intersection of the frontier with an ambient open set. -/
theorem exists_open_inter_frontier_eq_image_Ioo
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    {gamma : ℝ → ℂ} {t r : ℝ} (hr : 0 < r)
    (hgamma : ContinuousOn gamma (ball t r))
    (hinj : Set.InjOn gamma (ball t r))
    (hfront : ∀ u ∈ ball t r, gamma u ∈ frontier K) :
    ∃ a b : ℝ, ∃ O : Set ℂ,
      a < t ∧ t < b ∧ Icc a b ⊆ ball t r ∧ IsOpen O ∧
        O ∩ frontier K = gamma '' Ioo a b := by
  classical
  let B : Set ℝ := ball t r
  have hBopen : IsOpen B := by simp [B]
  have htB : t ∈ B := mem_ball_self hr
  let valF : ℝ → ℂ := fun u ↦ if hu : u ∈ B then gamma u else gamma t
  have hvalF_mem (u : ℝ) : valF u ∈ frontier K := by
    by_cases hu : u ∈ B
    · simpa [valF, hu] using hfront u hu
    · simpa [valF, hu] using hfront t htB
  let gammaF : ℝ → frontier K :=
    Set.codRestrict valF (frontier K) hvalF_mem
  have hgammaF_of_mem {u : ℝ} (hu : u ∈ B) :
      (gammaF u : ℂ) = gamma u := by
    simp [gammaF, valF, hu]
  have hgammaFAt {u : ℝ} (hu : u ∈ B) : ContinuousAt gammaF u := by
    rw [continuousAt_codRestrict_iff]
    apply (hgamma u hu).continuousAt (hBopen.mem_nhds hu) |>.congr_of_eventuallyEq
    filter_upwards [hBopen.mem_nhds hu] with v hv
    simp [valF, hv]
  let e : frontier K ≃ₜ Circle :=
    (radialBoundaryHomeomorph hconv hc hcompact).symm.trans
      unitSphereCircleHomeomorph
  let delta : ℝ → Circle := fun u ↦ e (gammaF u)
  have hdeltaAt {u : ℝ} (hu : u ∈ B) : ContinuousAt delta u :=
    e.continuous.continuousAt.comp (hgammaFAt hu)
  have hdeltaInj : Set.InjOn delta B := by
    intro u hu v hv huv
    apply hinj hu hv
    have hgammaFEq : gammaF u = gammaF v := e.injective huv
    simpa only [hgammaF_of_mem hu, hgammaF_of_mem hv] using
      congrArg Subtype.val hgammaFEq
  let rot : Circle ≃ₜ Circle := Homeomorph.mulLeft (delta t)⁻¹
  let eta : ℝ → Circle := fun u ↦ rot (delta u)
  have hetaAt {u : ℝ} (hu : u ∈ B) : ContinuousAt eta u :=
    rot.continuous.continuousAt.comp (hdeltaAt hu)
  have heta_t : eta t = 1 := by simp [eta, rot]
  let N : Set Circle := ((↑) : Circle → ℂ) ⁻¹' Complex.slitPlane
  have hNopen : IsOpen N :=
    Complex.isOpen_slitPlane.preimage continuous_subtype_val
  have heta_tN : eta t ∈ N := by
    rw [heta_t]
    change (1 : ℂ) ∈ Complex.slitPlane
    rw [Complex.mem_slitPlane_iff]
    left
    norm_num
  have heventB : B ∈ 𝓝 t := isOpen_ball.mem_nhds htB
  have heventN : eta ⁻¹' N ∈ 𝓝 t :=
    (hetaAt htB).preimage_mem_nhds (hNopen.mem_nhds heta_tN)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (inter_mem heventB heventN)
  let a := t - ε / 2
  let b := t + ε / 2
  have hat : a < t := by dsimp [a]; linarith
  have htb : t < b := by dsimp [b]; linarith
  have hab : a < b := hat.trans htb
  have hIccBall : Icc a b ⊆ ball t ε := by
    intro u hu
    rcases hu with ⟨hua, hub⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    dsimp [a, b] at hua hub
    constructor <;> nlinarith
  have hIccB : Icc a b ⊆ B := fun u hu ↦ (hεsub (hIccBall hu)).1
  have hIccN : ∀ u ∈ Icc a b, eta u ∈ N :=
    fun u hu ↦ (hεsub (hIccBall hu)).2
  let F : ℝ → ℝ := fun u ↦ Complex.arg (eta u : ℂ)
  have hFcont : ContinuousOn F (Icc a b) := by
    intro u hu
    have harg : ContinuousAt Complex.arg (eta u : ℂ) :=
      Complex.continuousAt_arg (hIccN u hu)
    have hargcoe : ContinuousAt (fun q : Circle ↦ Complex.arg (q : ℂ)) (eta u) :=
      harg.comp continuous_subtype_val.continuousAt
    have hcomp : ContinuousAt (fun v ↦ Complex.arg (eta v : ℂ)) u :=
      hargcoe.comp (hetaAt (hIccB hu))
    simpa [F, Function.comp_def] using
      hcomp.continuousWithinAt
  have hFinj : Set.InjOn F (Icc a b) := by
    intro u hu v hv huv
    have hetaEq : eta u = eta v := Circle.injective_arg huv
    have hdeltaEq : delta u = delta v := rot.injective hetaEq
    exact hdeltaInj (hIccB hu) (hIccB hv) hdeltaEq
  have hfinish (J : Set ℝ) (hJopen : IsOpen J)
      (hJrange : J ⊆ Ioo (-Real.pi) Real.pi)
      (hFimage : F '' Ioo a b = J) :
      ∃ O : Set ℂ, IsOpen O ∧ O ∩ frontier K = gamma '' Ioo a b := by
    let coord : Circle → ℝ := fun q ↦ Complex.arg (q : ℂ)
    let S : Set Circle := coord ⁻¹' J
    have hcoordCont : ContinuousOn coord N := by
      intro q hq
      have harg : ContinuousAt Complex.arg (q : ℂ) :=
        Complex.continuousAt_arg hq
      have hcomp : ContinuousAt coord q :=
        harg.comp continuous_subtype_val.continuousAt
      exact hcomp.continuousWithinAt
    have hSsubN : S ⊆ N := by
      intro q hq
      have hqrange : coord q ∈ Ioo (-Real.pi) Real.pi := hJrange hq
      rw [show q ∈ N ↔ (q : ℂ) ∈ Complex.slitPlane by rfl,
        Complex.mem_slitPlane_iff_arg]
      exact ⟨ne_of_lt hqrange.2, Circle.coe_ne_zero q⟩
    have hSopen : IsOpen S :=
      hcoordCont.isOpen_preimage hNopen hSsubN hJopen
    have hSeta : S = eta '' Ioo a b := by
      ext q
      constructor
      · intro hq
        have hqJ : coord q ∈ J := hq
        rw [← hFimage] at hqJ
        obtain ⟨u, hu, huq⟩ := hqJ
        refine ⟨u, hu, ?_⟩
        apply Circle.injective_arg
        simpa [F, coord] using huq
      · rintro ⟨u, hu, rfl⟩
        change F u ∈ J
        rw [← hFimage]
        exact ⟨u, hu, rfl⟩
    let T : Set Circle := rot.symm '' S
    have hTopen : IsOpen T := by
      exact rot.symm.isOpen_image.mpr hSopen
    let R : Set (frontier K) := e.symm '' T
    have hRopen : IsOpen R := by
      exact e.symm.isOpen_image.mpr hTopen
    have hRimage : R = gammaF '' Ioo a b := by
      rw [show R = e.symm '' T by rfl, show T = rot.symm '' S by rfl,
        hSeta, image_image, image_image]
      apply image_congr
      intro u _
      simp [eta, delta]
    obtain ⟨O, hOopen, hOpre⟩ := isOpen_induced_iff.mp hRopen
    refine ⟨O, hOopen, ?_⟩
    ext z
    constructor
    · rintro ⟨hzO, hzfront⟩
      let zz : frontier K := ⟨z, hzfront⟩
      have hzzR : zz ∈ R := by
        rw [← hOpre]
        exact hzO
      rw [hRimage] at hzzR
      obtain ⟨u, hu, huEq⟩ := hzzR
      refine ⟨u, hu, ?_⟩
      have huB : u ∈ B := hIccB (Ioo_subset_Icc_self hu)
      have := congrArg Subtype.val huEq
      simpa only [hgammaF_of_mem huB] using this
    · rintro ⟨u, hu, rfl⟩
      have huB : u ∈ B := hIccB (Ioo_subset_Icc_self hu)
      constructor
      · have hmemR : gammaF u ∈ R := by
          rw [hRimage]
          exact ⟨u, hu, rfl⟩
        have hmemO : (gammaF u : ℂ) ∈ O := by
          have : gammaF u ∈ Subtype.val ⁻¹' O := by
            rw [hOpre]
            exact hmemR
          exact this
        simpa only [hgammaF_of_mem huB] using hmemO
      · exact hfront u huB
  obtain hFmono | hFanti :=
    hFcont.strictMonoOn_of_injOn_Icc' hab.le hFinj
  · let J : Set ℝ := Ioo (F a) (F b)
    have hFimage : F '' Ioo a b = J :=
      hFcont.image_Ioo_of_strictMonoOn hab.le hFmono
    have hJrange : J ⊆ Ioo (-Real.pi) Real.pi := by
      intro x hx
      constructor
      · exact (Complex.neg_pi_lt_arg (eta a : ℂ)).trans hx.1
      · exact hx.2.trans <| (Complex.arg_le_pi (eta b : ℂ)).lt_of_ne
          (Complex.slitPlane_arg_ne_pi (hIccN b ⟨hab.le, le_rfl⟩))
    obtain ⟨O, hOopen, hO⟩ := hfinish J isOpen_Ioo hJrange hFimage
    exact ⟨a, b, O, hat, htb, by simpa [B] using hIccB, hOopen, hO⟩
  · let J : Set ℝ := Ioo (F b) (F a)
    have hFimage : F '' Ioo a b = J :=
      hFcont.image_Ioo_of_strictAntiOn hab.le hFanti
    have hJrange : J ⊆ Ioo (-Real.pi) Real.pi := by
      intro x hx
      constructor
      · exact (Complex.neg_pi_lt_arg (eta b : ℂ)).trans hx.1
      · exact hx.2.trans <| (Complex.arg_le_pi (eta a : ℂ)).lt_of_ne
          (Complex.slitPlane_arg_ne_pi (hIccN a ⟨le_rfl, hab.le⟩))
    obtain ⟨O, hOopen, hO⟩ := hfinish J isOpen_Ioo hJrange hFimage
    exact ⟨a, b, O, hat, htb, by simpa [B] using hIccB, hOopen, hO⟩

end NumericalRangeArc

end

end DiskRigidity.Complex
