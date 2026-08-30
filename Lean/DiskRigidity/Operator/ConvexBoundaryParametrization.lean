/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# A rectifiable radial parametrization of a planar convex boundary

A compact convex body, viewed from any interior point, is star-shaped.  Its
Minkowski gauge gives an explicit radial parametrization of the boundary.
This file records the construction in a form suitable for the double-layer
boundary integral.
-/

@[expose] public section

noncomputable section

open Bornology Filter Metric Set Topology
open scoped NNReal Pointwise

namespace DiskRigidity.Operator

/-- Translate a convex body so that the chosen interior point is the
origin. -/
def centeredConvexBody (K : Set ℂ) (c : ℂ) : Set ℂ :=
  (-c) +ᵥ K

theorem convex_centeredConvexBody {K : Set ℂ} {c : ℂ}
    (hK : Convex ℝ K) : Convex ℝ (centeredConvexBody K c) := by
  simpa [centeredConvexBody] using hK.vadd (-c)

theorem centeredConvexBody_mem_nhds_zero {K : Set ℂ} {c : ℂ}
    (hc : c ∈ interior K) : centeredConvexBody K c ∈ 𝓝 0 := by
  rw [← mem_interior_iff_mem_nhds, centeredConvexBody, interior_vadd]
  simpa [mem_vadd_set_iff_neg_vadd_mem]

theorem centeredConvexBody_isVonNBounded {K : Set ℂ} {c : ℂ}
    (hK : IsCompact K) : IsVonNBounded ℝ (centeredConvexBody K c) := by
  exact (hK.isVonNBounded ℝ).vadd (-c)

/-- The radial point in direction `u`, based at `c`, obtained by rescaling
the unit ball to the translated convex body with its Minkowski gauge. -/
def radialBoundaryPoint (K : Set ℂ) (c u : ℂ) : ℂ :=
  c + gaugeRescale (Metric.ball (0 : ℂ) 1) (centeredConvexBody K c) u

/-- Every unit direction is sent to the topological boundary. -/
theorem radialBoundaryPoint_mem_frontier
    {K : Set ℂ} {c u : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (hu : u ∈ sphere (0 : ℂ) 1) :
    radialBoundaryPoint K c u ∈ frontier K := by
  let S := centeredConvexBody K c
  have hSconv : Convex ℝ S := convex_centeredConvexBody hconv
  have hS0 : S ∈ 𝓝 (0 : ℂ) := centeredConvexBody_mem_nhds_zero hc
  have hSb : IsVonNBounded ℝ S := centeredConvexBody_isVonNBounded hcompact
  have hfront :
      gaugeRescale (Metric.ball (0 : ℂ) 1) S u ∈ frontier S := by
    rw [← gauge_eq_one_iff_mem_frontier hSconv hS0,
      gauge_gaugeRescale (Metric.ball (0 : ℂ) 1)
        (absorbent_nhds_zero hS0) hSb]
    rw [gauge_ball (by norm_num)]
    simpa [mem_sphere_zero_iff_norm] using hu
  change c + gaugeRescale (Metric.ball (0 : ℂ) 1) S u ∈ frontier K
  rw [frontier] at hfront ⊢
  constructor
  · have hclosure := hfront.1
    dsimp [S, centeredConvexBody] at hclosure
    rw [closure_vadd] at hclosure
    simpa [S, centeredConvexBody, mem_vadd_set_iff_neg_vadd_mem, add_comm]
      using hclosure
  · intro hinterior
    apply hfront.2
    dsimp [S, centeredConvexBody]
    rw [interior_vadd]
    dsimp [S, centeredConvexBody] at hinterior
    simpa [mem_vadd_set_iff_neg_vadd_mem, add_comm]
      using hinterior

/-- On a unit direction, the gauge-rescaling formula is simply radial
division by the gauge of the centered body. -/
theorem radialBoundaryPoint_eq_inv_gauge_smul
    (K : Set ℂ) (c u : ℂ) (hu : u ∈ sphere (0 : ℂ) 1) :
    radialBoundaryPoint K c u =
      c + (gauge (centeredConvexBody K c) u)⁻¹ • u := by
  rw [radialBoundaryPoint, gaugeRescale, gauge_ball (by norm_num)]
  have hunorm : ‖u‖ = 1 := by simpa [mem_sphere_zero_iff_norm] using hu
  rw [hunorm]
  simp [div_eq_mul_inv]

/-- Quantitative elementary estimate for reciprocal differences away from
zero. -/
theorem abs_inv_sub_inv_le {a b R : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hR : 0 ≤ R)
    (haR : a⁻¹ ≤ R) (hbR : b⁻¹ ≤ R) :
    |a⁻¹ - b⁻¹| ≤ |a - b| * R ^ 2 := by
  have hainv : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
  have hbinv : 0 ≤ b⁻¹ := inv_nonneg.mpr hb.le
  have hid : a⁻¹ - b⁻¹ = (b - a) * a⁻¹ * b⁻¹ := by
    field_simp [ha.ne', hb.ne']
  rw [hid, abs_mul, abs_mul, abs_inv, abs_inv,
    abs_of_pos ha, abs_of_pos hb, abs_sub_comm]
  calc
    |a - b| * a⁻¹ * b⁻¹ ≤ |a - b| * R * R := by
      gcongr
    _ = |a - b| * R ^ 2 := by ring

/-- The radial boundary map is Lipschitz on the unit circle.  In particular,
the resulting convex Jordan parametrization is rectifiable. -/
theorem exists_lipschitzOnWith_radialBoundaryPoint
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K) :
    ∃ C : ℝ≥0,
      LipschitzOnWith C (radialBoundaryPoint K c) (sphere (0 : ℂ) 1) := by
  let S := centeredConvexBody K c
  have hSconv : Convex ℝ S := convex_centeredConvexBody hconv
  have hS0 : S ∈ 𝓝 (0 : ℂ) := centeredConvexBody_mem_nhds_zero hc
  obtain ⟨r, hr, hrS⟩ := Metric.mem_nhds_iff.mp hS0
  let rnn : ℝ≥0 := ⟨r, hr.le⟩
  have hrnn : 0 < rnn := by exact_mod_cast hr
  have hglip : LipschitzWith rnn⁻¹ (gauge S) :=
    hSconv.lipschitzWith_gauge hrnn (by
      change ball (0 : ℂ) r ⊆ S
      exact hrS)
  have hScompact : IsCompact S := by
    exact IsCompact.vadd (-c) hcompact
  obtain ⟨R₀, hSR₀⟩ := hScompact.isBounded.subset_closedBall (0 : ℂ)
  let R : ℝ := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right R₀ 1)
  have hSR : S ⊆ closedBall (0 : ℂ) R :=
    hSR₀.trans (closedBall_subset_closedBall (le_max_left R₀ 1))
  let L : ℝ := ((rnn⁻¹ : ℝ≥0) : ℝ)
  have hL : 0 ≤ L := by positivity
  let C : ℝ≥0 := ⟨R + L * R ^ 2, by positivity⟩
  refine ⟨C, LipschitzOnWith.of_dist_le_mul fun u hu v hv ↦ ?_⟩
  have hunorm : ‖u‖ = 1 := by simpa [mem_sphere_zero_iff_norm] using hu
  have hvnorm : ‖v‖ = 1 := by simpa [mem_sphere_zero_iff_norm] using hv
  let a : ℝ := gauge S u
  let b : ℝ := gauge S v
  have haLower : R⁻¹ ≤ a := by
    have h := le_gauge_of_subset_closedBall (x := u)
      (absorbent_nhds_zero hS0) hR.le hSR
    simpa [a, hunorm, one_div] using h
  have hbLower : R⁻¹ ≤ b := by
    have h := le_gauge_of_subset_closedBall (x := v)
      (absorbent_nhds_zero hS0) hR.le hSR
    simpa [b, hvnorm, one_div] using h
  have ha : 0 < a := (inv_pos.mpr hR).trans_le haLower
  have hb : 0 < b := (inv_pos.mpr hR).trans_le hbLower
  have haR : a⁻¹ ≤ R := (inv_le_comm₀ ha hR).2 haLower
  have hbR : b⁻¹ ≤ R := (inv_le_comm₀ hb hR).2 hbLower
  have hgdist : |a - b| ≤ L * dist u v := by
    simpa [a, b, L, Real.dist_eq] using hglip.dist_le_mul u v
  rw [radialBoundaryPoint_eq_inv_gauge_smul K c u hu,
    radialBoundaryPoint_eq_inv_gauge_smul K c v hv, dist_add_left]
  change dist (a⁻¹ • u) (b⁻¹ • v) ≤ (C : ℝ) * dist u v
  rw [dist_eq_norm]
  have hdecomp :
      a⁻¹ • u - b⁻¹ • v =
        a⁻¹ • (u - v) + (a⁻¹ - b⁻¹) • v := by
    module
  rw [hdecomp]
  calc
    ‖a⁻¹ • (u - v) + (a⁻¹ - b⁻¹) • v‖ ≤
        ‖a⁻¹ • (u - v)‖ + ‖(a⁻¹ - b⁻¹) • v‖ := norm_add_le _ _
    _ = |a⁻¹| * dist u v + |a⁻¹ - b⁻¹| := by
      rw [norm_smul, norm_smul, dist_eq_norm, hvnorm]
      simp
    _ ≤ R * dist u v + (|a - b| * R ^ 2) := by
      gcongr
      · simpa [abs_of_nonneg (inv_nonneg.mpr ha.le)] using haR
      · exact abs_inv_sub_inv_le ha hb hR.le haR hbR
    _ ≤ R * dist u v + (L * dist u v) * R ^ 2 := by
      gcongr
    _ = (C : ℝ) * dist u v := by
      change _ = (R + L * R ^ 2) * dist u v
      ring

/-- Counterclockwise angular parametrization obtained from the radial
boundary map. -/
def radialBoundaryParametrization (K : Set ℂ) (c : ℂ) (t : ℝ) : ℂ :=
  radialBoundaryPoint K c (circleMap 0 1 t)

/-- The angular parametrization is globally Lipschitz, hence absolutely
continuous and rectifiable on every bounded interval. -/
theorem exists_lipschitzWith_radialBoundaryParametrization
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K) :
    ∃ C : ℝ≥0, LipschitzWith C (radialBoundaryParametrization K c) := by
  obtain ⟨C, hC⟩ :=
    exists_lipschitzOnWith_radialBoundaryPoint hconv hc hcompact
  refine ⟨C * Real.nnabs 1, lipschitzOnWith_univ.mp ?_⟩
  change LipschitzOnWith (C * Real.nnabs 1)
    (fun t ↦ radialBoundaryPoint K c (circleMap 0 1 t)) Set.univ
  have hcomp := hC.comp (s := Set.univ)
    (lipschitzWith_circleMap (0 : ℂ) 1).lipschitzOnWith
    (fun t _ ↦ circleMap_mem_sphere 0 zero_le_one t)
  change LipschitzOnWith (C * Real.nnabs 1)
    (fun t ↦ radialBoundaryPoint K c (circleMap 0 1 t)) Set.univ at hcomp
  exact hcomp

/-- Every point of the parametrized curve lies on the convex boundary. -/
theorem radialBoundaryParametrization_mem_frontier
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (t : ℝ) : radialBoundaryParametrization K c t ∈ frontier K := by
  exact radialBoundaryPoint_mem_frontier hconv hc hcompact
    (circleMap_mem_sphere 0 zero_le_one t)

/-- The radial map covers the entire convex boundary, not merely a subset
of it. -/
theorem image_radialBoundaryPoint_sphere
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K) :
    radialBoundaryPoint K c '' sphere (0 : ℂ) 1 = frontier K := by
  apply Subset.antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact radialBoundaryPoint_mem_frontier hconv hc hcompact hu
  · intro z hz
    let S := centeredConvexBody K c
    let x : ℂ := z - c
    have hSconv : Convex ℝ S := convex_centeredConvexBody hconv
    have hS0 : S ∈ 𝓝 (0 : ℂ) := centeredConvexBody_mem_nhds_zero hc
    have hSb : IsVonNBounded ℝ S := centeredConvexBody_isVonNBounded hcompact
    have hxfront : x ∈ frontier S := by
      rw [frontier] at hz ⊢
      constructor
      · dsimp [x, S, centeredConvexBody]
        rw [closure_vadd]
        simpa [mem_vadd_set_iff_neg_vadd_mem, sub_eq_add_neg, add_comm,
          add_left_comm, add_assoc] using hz.1
      · intro hxint
        apply hz.2
        dsimp [x, S, centeredConvexBody] at hxint
        rw [interior_vadd] at hxint
        simpa [mem_vadd_set_iff_neg_vadd_mem, sub_eq_add_neg, add_comm,
          add_left_comm, add_assoc] using hxint
    let e : ℂ ≃ₜ ℂ := gaugeRescaleHomeomorph (Metric.ball (0 : ℂ) 1) S
      (convex_ball 0 1) (Metric.ball_mem_nhds 0 zero_lt_one)
      (NormedSpace.isVonNBounded_ball ℝ ℂ 1) hSconv hS0 hSb
    have hclosureImage :
        e '' closure (Metric.ball (0 : ℂ) 1) = closure S :=
      image_gaugeRescaleHomeomorph_closure
        (convex_ball (0 : ℂ) 1) (Metric.ball_mem_nhds 0 zero_lt_one)
        (NormedSpace.isVonNBounded_ball ℝ ℂ 1) hSconv hS0 hSb
    have hximage : x ∈ e '' closure (Metric.ball (0 : ℂ) 1) := by
      rw [hclosureImage]
      exact hxfront.1
    obtain ⟨u, huclosure, heu⟩ := hximage
    have hunot : u ∉ interior (Metric.ball (0 : ℂ) 1) := by
      intro huinterior
      apply hxfront.2
      rw [← heu]
      exact mapsTo_gaugeRescale_interior hS0 hSconv huinterior
    have husphere : u ∈ sphere (0 : ℂ) 1 := by
      rw [← frontier_ball (0 : ℂ) one_ne_zero, frontier]
      exact ⟨huclosure, hunot⟩
    refine ⟨u, husphere, ?_⟩
    change c + e u = z
    rw [heu]
    dsimp [x]
    abel

/-- Consequently the angular Lipschitz parametrization has exactly the
convex boundary as its range. -/
theorem range_radialBoundaryParametrization
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K) :
    Set.range (radialBoundaryParametrization K c) = frontier K := by
  change Set.range (fun t ↦ radialBoundaryPoint K c (circleMap 0 1 t)) = _
  rw [← Set.image_univ,
    ← Function.comp_def, Set.image_comp, Set.image_univ, range_circleMap]
  simpa using image_radialBoundaryPoint_sphere hconv hc hcompact

/-- The parametrization closes after one positive turn. -/
theorem radialBoundaryParametrization_periodic (K : Set ℂ) (c : ℂ) :
    Function.Periodic (radialBoundaryParametrization K c) (2 * Real.pi) := by
  intro t
  rw [radialBoundaryParametrization, radialBoundaryParametrization,
    periodic_circleMap]

/-- Radial distance of the boundary point from the chosen interior center. -/
def radialBoundaryRadius (K : Set ℂ) (c : ℂ) (t : ℝ) : ℝ :=
  ‖radialBoundaryParametrization K c t - c‖

/-- The radial distance is globally Lipschitz. -/
theorem exists_lipschitzWith_radialBoundaryRadius
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K) :
    ∃ C : ℝ≥0, LipschitzWith C (radialBoundaryRadius K c) := by
  obtain ⟨C, hC⟩ :=
    exists_lipschitzWith_radialBoundaryParametrization hconv hc hcompact
  refine ⟨1 * (C + 0), ?_⟩
  change LipschitzWith (1 * (C + 0))
    (fun t ↦ ‖radialBoundaryParametrization K c t - c‖)
  exact lipschitzWith_one_norm.comp (hC.sub (LipschitzWith.const c))

/-- The boundary parametrization is the product of its positive radial
distance and the unit angular direction. -/
theorem radialBoundaryParametrization_eq_radius_mul_circleMap
    {K : Set ℂ} {c : ℂ}
    (_hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (t : ℝ) :
    radialBoundaryParametrization K c t = c +
      radialBoundaryRadius K c t • circleMap 0 1 t := by
  let S := centeredConvexBody K c
  let u := circleMap 0 1 t
  have hu : u ∈ sphere (0 : ℂ) 1 := circleMap_mem_sphere 0 zero_le_one t
  have hunorm : ‖u‖ = 1 := by simpa [mem_sphere_zero_iff_norm] using hu
  have hS0 : S ∈ 𝓝 (0 : ℂ) := centeredConvexBody_mem_nhds_zero hc
  have hSb : IsVonNBounded ℝ S := centeredConvexBody_isVonNBounded hcompact
  have hg : 0 < gauge S u :=
    (gauge_pos (absorbent_nhds_zero hS0) hSb).2 (by
      intro hu0
      rw [hu0, norm_zero] at hunorm
      norm_num at hunorm)
  change 0 < gauge (centeredConvexBody K c) u at hg
  have hformula := radialBoundaryPoint_eq_inv_gauge_smul K c u hu
  change radialBoundaryPoint K c u = c +
    ‖radialBoundaryPoint K c u - c‖ • u
  rw [hformula]
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hunorm, mul_one]
  rw [abs_of_pos (inv_pos.mpr hg)]

/-- The radial distance is strictly positive. -/
theorem radialBoundaryRadius_pos
    {K : Set ℂ} {c : ℂ}
    (_hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (t : ℝ) : 0 < radialBoundaryRadius K c t := by
  let S := centeredConvexBody K c
  let u := circleMap 0 1 t
  have hu : u ∈ sphere (0 : ℂ) 1 := circleMap_mem_sphere 0 zero_le_one t
  have hunorm : ‖u‖ = 1 := by simpa [mem_sphere_zero_iff_norm] using hu
  have hS0 : S ∈ 𝓝 (0 : ℂ) := centeredConvexBody_mem_nhds_zero hc
  have hSb : IsVonNBounded ℝ S := centeredConvexBody_isVonNBounded hcompact
  have hg : 0 < gauge S u :=
    (gauge_pos (absorbent_nhds_zero hS0) hSb).2 (by
      intro hu0
      rw [hu0, norm_zero] at hunorm
      norm_num at hunorm)
  change 0 < gauge (centeredConvexBody K c) u at hg
  rw [radialBoundaryRadius, radialBoundaryParametrization,
    radialBoundaryPoint_eq_inv_gauge_smul K c u hu]
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hunorm, mul_one]
  rw [abs_of_pos (inv_pos.mpr hg)]
  exact inv_pos.mpr hg

/-- Differentiating the polar representation gives the tangent explicitly
at every differentiability point of the radial distance. -/
theorem hasDerivAt_radialBoundaryParametrization
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    {t r' : ℝ} (hr : HasDerivAt (radialBoundaryRadius K c) r' t) :
    HasDerivAt (radialBoundaryParametrization K c)
      (radialBoundaryRadius K c t • (circleMap 0 1 t * Complex.I) +
        r' • circleMap 0 1 t) t := by
  have heq : radialBoundaryParametrization K c = fun s ↦
      c + radialBoundaryRadius K c s • circleMap 0 1 s := by
    funext s
    exact radialBoundaryParametrization_eq_radius_mul_circleMap
      hconv hc hcompact s
  rw [heq]
  exact (hr.smul (hasDerivAt_circleMap 0 1 t)).const_add c

/-- The polar tangent cannot vanish because its angular component is the
strictly positive radial distance. -/
theorem radialBoundary_tangent_ne_zero
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K)
    (t r' : ℝ) :
    radialBoundaryRadius K c t • (circleMap 0 1 t * Complex.I) +
        r' • circleMap 0 1 t ≠ 0 := by
  let rho := radialBoundaryRadius K c t
  let u := circleMap 0 1 t
  have hrho : 0 < rho := radialBoundaryRadius_pos hconv hc hcompact t
  intro hzero
  have hmul := congrArg (fun z : ℂ ↦ star u * z) hzero
  have him := congrArg Complex.im hmul
  dsimp [u] at him
  simp [circleMap] at him
  ring_nf at him
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- Rademacher's theorem therefore gives a nonzero tangent almost
everywhere along the rectifiable convex boundary. -/
theorem ae_differentiableAt_radialBoundaryParametrization_and_deriv_ne_zero
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K) :
    ∀ᵐ t : ℝ,
      DifferentiableAt ℝ (radialBoundaryParametrization K c) t ∧
        deriv (radialBoundaryParametrization K c) t ≠ 0 := by
  obtain ⟨C, hC⟩ :=
    exists_lipschitzWith_radialBoundaryRadius hconv hc hcompact
  filter_upwards [hC.ae_differentiableAt_real] with t ht
  let r' := deriv (radialBoundaryRadius K c) t
  have hr : HasDerivAt (radialBoundaryRadius K c) r' t := ht.hasDerivAt
  have hsigma := hasDerivAt_radialBoundaryParametrization
    hconv hc hcompact hr
  refine ⟨hsigma.differentiableAt, ?_⟩
  rw [hsigma.deriv]
  exact radialBoundary_tangent_ne_zero hconv hc hcompact t r'

/-- Speed of the rectifiable boundary parametrization. -/
def radialBoundarySpeed (K : Set ℂ) (c : ℂ) (t : ℝ) : ℝ :=
  ‖deriv (radialBoundaryParametrization K c) t‖

/-- The outward unit normal obtained by rotating the positive tangent
clockwise. -/
def radialOutwardUnitNormal (K : Set ℂ) (c : ℂ) (t : ℝ) : ℂ :=
  (-Complex.I * deriv (radialBoundaryParametrization K c) t) /
    radialBoundarySpeed K c t

/-- The rotated normalized tangent has norm at most one everywhere (and
equals zero only where the chosen derivative is zero). -/
theorem norm_radialOutwardUnitNormal_le_one
    (K : Set ℂ) (c : ℂ) (t : ℝ) :
    ‖radialOutwardUnitNormal K c t‖ ≤ 1 := by
  by_cases hd : deriv (radialBoundaryParametrization K c) t = 0
  · simp [radialOutwardUnitNormal, radialBoundarySpeed, hd]
  · have hspeed : radialBoundarySpeed K c t ≠ 0 := by
      rw [radialBoundarySpeed, norm_ne_zero_iff]
      exact hd
    have heq : ‖radialOutwardUnitNormal K c t‖ = 1 := by
      rw [radialOutwardUnitNormal, norm_div, norm_mul, norm_neg,
        Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg
          (show 0 ≤ radialBoundarySpeed K c t from norm_nonneg _)]
      change radialBoundarySpeed K c t / radialBoundarySpeed K c t = 1
      exact div_self hspeed
    rw [heq]

/-- The constructed normal has unit length almost everywhere. -/
theorem ae_norm_radialOutwardUnitNormal_eq_one
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K) :
    ∀ᵐ t : ℝ, ‖radialOutwardUnitNormal K c t‖ = 1 := by
  filter_upwards
    [ae_differentiableAt_radialBoundaryParametrization_and_deriv_ne_zero
      hconv hc hcompact] with t ht
  have hspeed : radialBoundarySpeed K c t ≠ 0 := by
    rw [radialBoundarySpeed, norm_ne_zero_iff]
    exact ht.2
  rw [radialOutwardUnitNormal, norm_div, norm_mul, norm_neg, Complex.norm_I,
    one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ radialBoundarySpeed K c t from norm_nonneg _)]
  change radialBoundarySpeed K c t / radialBoundarySpeed K c t = 1
  exact div_self hspeed

/-- The exact differential relation `dσ = i ν ds` used in the manuscript,
expressed for the speed-weighted angular parametrization. -/
theorem ae_deriv_eq_I_mul_normal_mul_speed
    {K : Set ℂ} {c : ℂ}
    (hconv : Convex ℝ K) (hc : c ∈ interior K) (hcompact : IsCompact K) :
    ∀ᵐ t : ℝ,
      deriv (radialBoundaryParametrization K c) t =
        Complex.I * radialOutwardUnitNormal K c t *
          radialBoundarySpeed K c t := by
  filter_upwards
    [ae_differentiableAt_radialBoundaryParametrization_and_deriv_ne_zero
      hconv hc hcompact] with t ht
  have hspeed : (radialBoundarySpeed K c t : ℂ) ≠ 0 := by
    exact_mod_cast (show radialBoundarySpeed K c t ≠ 0 by
      rw [radialBoundarySpeed, norm_ne_zero_iff]
      exact ht.2)
  rw [radialOutwardUnitNormal, div_eq_mul_inv]
  field_simp
  rw [pow_two, Complex.I_mul_I]
  ring

/-- The speed and normal fields are measurable, so they can be used to
define arclength and the double-layer boundary density. -/
theorem measurable_radialBoundarySpeed (K : Set ℂ) (c : ℂ) :
    Measurable (radialBoundarySpeed K c) := by
  exact (measurable_deriv (radialBoundaryParametrization K c)).norm

theorem measurable_radialOutwardUnitNormal (K : Set ℂ) (c : ℂ) :
    Measurable (radialOutwardUnitNormal K c) := by
  exact ((measurable_const.mul
    (measurable_deriv (radialBoundaryParametrization K c))).div
      (Complex.measurable_ofReal.comp (measurable_radialBoundarySpeed K c)))

end DiskRigidity.Operator
