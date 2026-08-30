/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.DoubleLayer
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The iterated dilation estimate and its equality case

This module formalizes Lemma 3.1, including the telescoping estimate and all
four operator identities forced at equality.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate InnerProduct InnerProductSpace Topology
open Filter

namespace DiskRigidity.Operator

/-- The last scalar inequality in the iterated-dilation argument forces the
operator norm to be at most two.  Here `w` is the squared norm of the defect
vector `ω` in the manuscript. -/
theorem dilation_master_inequality_forces_le_two
    {κ w : ℝ} (hκ : 1 < κ) (hw : 0 ≤ w)
    (hmaster : w * (1 - 1 / (κ - 1) ^ 2) ≤ κ ^ 2 * (2 - κ)) :
    κ ≤ 2 := by
  by_contra hnot
  have htwo : 2 < κ := lt_of_not_ge hnot
  have hden : 1 < (κ - 1) ^ 2 := by
    nlinarith [sq_nonneg (κ - 2)]
  have hcoeff : 0 < 1 - 1 / (κ - 1) ^ 2 := by
    rw [sub_pos, div_lt_one (by positivity)]
    exact hden
  have hleft : 0 ≤ w * (1 - 1 / (κ - 1) ^ 2) :=
    mul_nonneg hw hcoeff.le
  have hright : κ ^ 2 * (2 - κ) < 0 :=
    mul_neg_of_pos_of_neg (sq_pos_of_pos (lt_trans (by norm_num) hκ)) (sub_neg.mpr htwo)
  linarith

/-- At norm two, the two inequalities in the manuscript squeeze to equalities. -/
theorem dilation_equality_squeeze {m w : ℝ}
    (hfirst : -w ≤ 2 * m) (hsecond : w ≤ -2 * m) :
    2 * m = -w ∧ w = -2 * m := by
  constructor <;> linarith

/-- The telescoping step in (3.1), stated with the manuscript's constants.
The sequence is indexed from zero here, so `m 0` is the paper's `m₁`. -/
theorem dilation_telescoping_lower_bound
    {κ w : ℝ} (m : ℕ → ℝ) (hκ : 1 < κ)
    (hbounded : ∃ B : ℝ, ∀ n, |m n| ≤ B)
    (hrecurrence : ∀ n,
      -w / (κ * (κ - 1)) ≤ κ * m n - m (n + 1)) :
    -w / (κ - 1) ^ 2 ≤ κ * m 0 := by
  have hκpos : 0 < κ := lt_trans (by norm_num) hκ
  have hκne : κ ≠ 0 := ne_of_gt hκpos
  have hκsubpos : 0 < κ - 1 := sub_pos.mpr hκ
  have hκsubne : κ - 1 ≠ 0 := ne_of_gt hκsubpos
  let a : ℝ := w / (κ * (κ - 1))
  let L : ℝ := -w / (κ * (κ - 1) ^ 2)
  have hfixed : κ * L + a = L := by
    dsimp [L, a]
    field_simp
    ring
  have hstep : ∀ n, m (n + 1) ≤ κ * m n + a := by
    intro n
    have := hrecurrence n
    dsimp [a]
    rw [neg_div] at this
    linarith
  by_contra hconclusion
  have hmzero : m 0 < L := by
    have hstrict : κ * m 0 < -w / (κ - 1) ^ 2 := lt_of_not_ge hconclusion
    calc
      m 0 < (-w / (κ - 1) ^ 2) / κ :=
        (lt_div_iff₀ hκpos).2 (by simpa [mul_comm] using hstrict)
      _ = L := by
        dsimp [L]
        field_simp
  let δ : ℝ := L - m 0
  have hδ : 0 < δ := by simpa [δ] using sub_pos.mpr hmzero
  have hupper : ∀ n, m n ≤ L - κ ^ n * δ := by
    intro n
    induction n with
    | zero =>
        simp [δ]
    | succ n ih =>
        calc
          m (n + 1) ≤ κ * m n + a := hstep n
          _ ≤ κ * (L - κ ^ n * δ) + a := by gcongr
          _ = L - κ ^ (n + 1) * δ := by
            rw [pow_succ]
            nlinarith [hfixed]
  obtain ⟨B, hB⟩ := hbounded
  have hBnonneg : 0 ≤ B := le_trans (abs_nonneg (m 0)) (hB 0)
  have hpow : Tendsto (fun n : ℕ ↦ κ ^ n * δ) atTop atTop :=
    Tendsto.atTop_mul_const hδ (tendsto_pow_atTop_atTop_of_one_lt hκ)
  obtain ⟨n, hn⟩ := (hpow.eventually_gt_atTop (B + |L|)).exists
  have hlower : -B ≤ m n := (abs_le.mp (hB n)).1
  have hL : L ≤ |L| := le_abs_self L
  have : m n < -B := lt_of_le_of_lt (hupper n) (by linarith)
  linarith

/-- Equality in the telescoping estimate forces equality in every shifted
recurrence.  This is the bounded-sequence form of the positive-weighted-slack
argument in the manuscript. -/
theorem dilation_telescoping_rigidity
    {κ w : ℝ} (m : ℕ → ℝ) (hκ : 1 < κ)
    (hbounded : ∃ B : ℝ, ∀ n, |m n| ≤ B)
    (hrecurrence : ∀ n,
      -w / (κ * (κ - 1)) ≤ κ * m n - m (n + 1))
    (hinitial : κ * m 0 = -w / (κ - 1) ^ 2) :
    ∀ n, κ * m n - m (n + 1) = -w / (κ * (κ - 1)) := by
  have hκpos : 0 < κ := lt_trans (by norm_num) hκ
  have hκne : κ ≠ 0 := ne_of_gt hκpos
  have hκsubne : κ - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hκ)
  let L : ℝ := -w / (κ * (κ - 1) ^ 2)
  have hκL : κ * L = -w / (κ - 1) ^ 2 := by
    dsimp [L]
    field_simp
  have hzero : m 0 = L := by
    exact (mul_left_cancel₀ hκne) (hinitial.trans hκL.symm)
  have hlower : ∀ n, L ≤ m n := by
    intro n
    let tail : ℕ → ℝ := fun k ↦ m (n + k)
    have htailBounded : ∃ B : ℝ, ∀ k, |tail k| ≤ B := by
      obtain ⟨B, hB⟩ := hbounded
      exact ⟨B, fun k ↦ hB (n + k)⟩
    have htailRecurrence : ∀ k,
        -w / (κ * (κ - 1)) ≤ κ * tail k - tail (k + 1) := by
      intro k
      simpa [tail, Nat.add_assoc] using hrecurrence (n + k)
    have htail := dilation_telescoping_lower_bound tail hκ htailBounded htailRecurrence
    dsimp [tail] at htail
    exact le_of_mul_le_mul_left (by simpa [hκL] using htail) hκpos
  have hupper : ∀ n, m n ≤ L := by
    intro n
    induction n with
    | zero => exact hzero.le
    | succ n ih =>
        have hstep := hrecurrence n
        have hfixed : κ * L + w / (κ * (κ - 1)) = L := by
          dsimp [L]
          field_simp
          ring
        have : m (n + 1) ≤ κ * m n + w / (κ * (κ - 1)) := by
          rw [neg_div] at hstep
          linarith
        calc
          m (n + 1) ≤ κ * m n + w / (κ * (κ - 1)) := this
          _ ≤ κ * L + w / (κ * (κ - 1)) := by gcongr
          _ = L := hfixed
  intro n
  have hn : m n = L := le_antisymm (hupper n) (hlower n)
  have hnext : m (n + 1) = L := le_antisymm (hupper (n + 1)) (hlower (n + 1))
  rw [hn, hnext]
  dsimp [L]
  field_simp
  ring

/-- A sum of nonnegative weighted slacks can vanish only if every slack vanishes. -/
theorem slack_eq_zero_of_hasSum_zero
    (weight slack : ℕ → ℝ)
    (hweight : ∀ n, 0 < weight n) (hslack : ∀ n, 0 ≤ slack n)
    (hsum : HasSum (fun n ↦ weight n * slack n) 0) :
    ∀ n, slack n = 0 := by
  have hterm : ∀ n, weight n * slack n = 0 :=
    fun n ↦ congrFun
      ((hasSum_zero_iff_of_nonneg fun k ↦
        mul_nonneg (hweight k).le (hslack k)).mp hsum) n
  intro n
  exact (mul_eq_zero.mp (hterm n)).resolve_left (ne_of_gt (hweight n))

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A finite-dimensional operator has a unit top right-singular vector. -/
theorem exists_unit_top_singular_vector [FiniteDimensional ℂ H] [Nontrivial H]
    (T : H →L[ℂ] H) :
    ∃ x : H, ‖x‖ = 1 ∧ (T†) (T x) = (‖T‖ ^ 2 : ℂ) • x := by
  let A : H →L[ℂ] H := star T * T
  have hAself : IsSelfAdjoint A := by
    exact IsSelfAdjoint.star_mul_self T
  have hAnonneg : ∀ z : H, 0 ≤ A.rayleighQuotient z := by
    intro z
    have hinner : A.reApplyInnerSelf z = ‖T z‖ ^ 2 := by
      rw [ContinuousLinearMap.reApplyInnerSelf_apply]
      simpa [A, ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp] using
        (T.apply_norm_sq_eq_inner_adjoint_left z).symm
    rw [ContinuousLinearMap.rayleighQuotient]
    apply div_nonneg
    · rw [hinner]
      exact sq_nonneg _
    · exact sq_nonneg _
  have hnormA : ‖A‖ = ‖T‖ ^ 2 := by
    simpa [A, pow_two] using (CStarRing.norm_star_mul_self (x := T))
  have hbddSub :
      BddAbove (Set.range fun z : {z : H // z ≠ 0} ↦ A.rayleighQuotient z) := by
    refine ⟨‖A‖, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact le_trans (le_abs_self _) (A.rayleighQuotient_le_norm z)
  obtain ⟨z₀, hz₀⟩ : ∃ z : H, z ≠ 0 := exists_ne 0
  let _ : Nonempty {z : H // z ≠ 0} := ⟨⟨z₀, hz₀⟩⟩
  have hsubnonneg :
      0 ≤ ⨆ z : {z : H // z ≠ 0}, A.rayleighQuotient z := by
    exact le_trans (hAnonneg z₀) (le_ciSup hbddSub ⟨z₀, hz₀⟩)
  have hiSup :
      (⨆ z : {z : H // z ≠ 0}, A.rayleighQuotient z : ℝ) = ‖T‖ ^ 2 := by
    have hnormRayleigh := A.norm_eq_iSup_rayleighQuotient hAself.isSymmetric
    simp_rw [abs_of_nonneg (hAnonneg _)] at hnormRayleigh
    have hnorm_le :
        ‖A‖ ≤ ⨆ z : {z : H // z ≠ 0}, A.rayleighQuotient z := by
      rw [hnormRayleigh]
      refine ciSup_le fun z ↦ ?_
      by_cases hz : z = 0
      · simpa [hz] using hsubnonneg
      · exact le_ciSup hbddSub ⟨z, hz⟩
    have hsub_le :
        (⨆ z : {z : H // z ≠ 0}, A.rayleighQuotient z) ≤ ‖A‖ := by
      refine ciSup_le fun z ↦ ?_
      exact le_trans (le_abs_self _) (A.rayleighQuotient_le_norm z)
    exact (le_antisymm hsub_le hnorm_le).trans hnormA
  have heigen := hAself.isSymmetric.hasEigenvalue_iSup_of_finiteDimensional
  change Module.End.HasEigenvalue (A : H →ₗ[ℂ] H)
    ((⨆ z : {z : H // z ≠ 0}, A.rayleighQuotient z : ℝ) : ℂ) at heigen
  rw [hiSup] at heigen
  obtain ⟨z, hz⟩ := heigen.exists_hasEigenvector
  let x : H := (‖z‖ : ℂ)⁻¹ • z
  have hznorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz.2
  have hxnorm : ‖x‖ = 1 := by
    simp [x, norm_smul, hznorm]
  refine ⟨x, hxnorm, ?_⟩
  have hzmap : A z = (‖T‖ ^ 2 : ℂ) • z := by
    simpa using hz.apply_eq_smul
  change A x = (‖T‖ ^ 2 : ℂ) • x
  dsimp [x]
  rw [map_smul, hzmap, smul_smul]
  simp only [smul_smul]
  rw [mul_comm]

/-- The compressed adjoint powers `Qₙ = V† M†ⁿ V` in Lemma 3.1. -/
def dilationCompression (M : K →L[ℂ] K) (V : H →ₗᵢ[ℂ] K) (n : ℕ) :
    H →L[ℂ] H :=
  (V.toContinuousLinearMap†) ∘L ((M†) ^ n) ∘L V.toContinuousLinearMap

/-- The raw error operators from Lemma 3.1. -/
def dilationError (T : H →L[ℂ] H) (M : K →L[ℂ] K)
    (V : H →ₗᵢ[ℂ] K) (n : ℕ) : H →L[ℂ] H :=
  (2 : ℂ) • dilationCompression M V n - (T†) ^ n

/-- The defect vector `ω = M† V T x - κ V x` from Lemma 3.1. -/
def dilationDefect (T : H →L[ℂ] H) (M : K →L[ℂ] K)
    (V : H →ₗᵢ[ℂ] K) (κ : ℝ) (x : H) : K :=
  (M†) (V (T x)) - (κ : ℂ) • V x

/-- The real moments `mₙ = Re ⟪x, Eₙ Tⁿx⟫`. -/
def dilationMoment (T : H →L[ℂ] H) (M : K →L[ℂ] K)
    (V : H →ₗᵢ[ℂ] K) (x : H) (n : ℕ) : ℝ :=
  RCLike.re ⟪x, dilationError T M V n ((T ^ n) x)⟫_ℂ

@[simp]
theorem dilationCompression_apply (M : K →L[ℂ] K) (V : H →ₗᵢ[ℂ] K)
    (n : ℕ) (z : H) :
    dilationCompression M V n z =
      (V.toContinuousLinearMap†) (((M†) ^ n) (V z)) := by
  rfl

@[simp]
theorem dilationError_apply (T : H →L[ℂ] H) (M : K →L[ℂ] K)
    (V : H →ₗᵢ[ℂ] K) (n : ℕ) (z : H) :
    dilationError T M V n z =
      (2 : ℂ) • dilationCompression M V n z - ((T†) ^ n) z := by
  rfl

omit [CompleteSpace K] in
/-- All powers of a contraction are contractions, including the zeroth power
on a possibly trivial Hilbert space. -/
theorem norm_pow_le_one_of_norm_le_one (S : K →L[ℂ] K) (hS : ‖S‖ ≤ 1) :
    ∀ n : ℕ, ‖S ^ n‖ ≤ 1 := by
  intro n
  induction n with
  | zero =>
      change ‖ContinuousLinearMap.id ℂ K‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
      rw [pow_succ]
      exact (norm_mul_le (S ^ n) S).trans (by nlinarith [norm_nonneg (S ^ n)])

/-- Compression of powers of a contraction by an isometry is contractive. -/
theorem norm_dilationCompression_le_one
    (M : K →L[ℂ] K) (V : H →ₗᵢ[ℂ] K) (hM : ‖M‖ ≤ 1) (n : ℕ) :
    ‖dilationCompression M V n‖ ≤ 1 := by
  have hMadj : ‖M†‖ ≤ 1 := by
    simpa [← ContinuousLinearMap.star_eq_adjoint] using hM
  have hV : ‖V.toContinuousLinearMap‖ ≤ 1 := V.norm_toContinuousLinearMap_le
  have hVadj : ‖V.toContinuousLinearMap†‖ ≤ 1 := by
    simpa [← ContinuousLinearMap.star_eq_adjoint] using hV
  have hpow : ‖(M†) ^ n‖ ≤ 1 := norm_pow_le_one_of_norm_le_one (M†) hMadj n
  have hfirst :
      ‖(V.toContinuousLinearMap†) ∘L ((M†) ^ n)‖ ≤
        ‖V.toContinuousLinearMap†‖ * ‖(M†) ^ n‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  calc
    ‖dilationCompression M V n‖ ≤
        ‖(V.toContinuousLinearMap†) ∘L ((M†) ^ n)‖ *
          ‖V.toContinuousLinearMap‖ := by
      rw [dilationCompression]
      exact ((V.toContinuousLinearMap†) ∘L ((M†) ^ n)).opNorm_comp_le
        V.toContinuousLinearMap
    _ ≤ ‖V.toContinuousLinearMap†‖ * ‖(M†) ^ n‖ *
          ‖V.toContinuousLinearMap‖ :=
      mul_le_mul_of_nonneg_right hfirst (norm_nonneg _)
    _ ≤ 1 * 1 * 1 := by
      gcongr
    _ = 1 := by norm_num

/-- The vectors `V† M†ⁿ ω` used in the completed-square recurrence are
bounded in norm by `ω`. -/
theorem norm_adjoint_compression_apply_le
    (M : K →L[ℂ] K) (V : H →ₗᵢ[ℂ] K) (hM : ‖M‖ ≤ 1)
    (n : ℕ) (ω : K) :
    ‖(V.toContinuousLinearMap†) (((M†) ^ n) ω)‖ ≤ ‖ω‖ := by
  have hV : ‖V.toContinuousLinearMap‖ ≤ 1 := V.norm_toContinuousLinearMap_le
  have hVadj : ‖V.toContinuousLinearMap†‖ ≤ 1 := by
    simpa [← ContinuousLinearMap.star_eq_adjoint] using hV
  have hMadj : ‖M†‖ ≤ 1 := by
    simpa [← ContinuousLinearMap.star_eq_adjoint] using hM
  have hpow : ‖(M†) ^ n‖ ≤ 1 := norm_pow_le_one_of_norm_le_one (M†) hMadj n
  calc
    ‖(V.toContinuousLinearMap†) (((M†) ^ n) ω)‖ ≤
        ‖V.toContinuousLinearMap†‖ * ‖((M†) ^ n) ω‖ :=
      (V.toContinuousLinearMap†).le_opNorm _
    _ ≤ 1 * ‖((M†) ^ n) ω‖ := by gcongr
    _ ≤ 1 * (‖(M†) ^ n‖ * ‖ω‖) := by
      gcongr
      exact ((M†) ^ n).le_opNorm ω
    _ ≤ 1 * (1 * ‖ω‖) := by gcongr
    _ = ‖ω‖ := by ring

/-- Commutativity of `Eₙ` with `T` is exactly the commutator identity used
in the proof of Lemma 3.1. -/
theorem dilation_commutator_identity
    (T : H →L[ℂ] H) (M : K →L[ℂ] K) (V : H →ₗᵢ[ℂ] K)
    (n : ℕ) (hcomm : Commute (dilationError T M V n) T) (z : H) :
    (2 : ℂ) •
        (dilationCompression M V n (T z) - T (dilationCompression M V n z)) =
      ((T†) ^ n) (T z) - T (((T†) ^ n) z) := by
  have hz := congrArg (fun S : H →L[ℂ] H ↦ S z) hcomm.eq
  simp only [mul_apply_eq_comp, dilationError_apply, map_sub, map_smul] at hz
  calc
    (2 : ℂ) •
        (dilationCompression M V n (T z) - T (dilationCompression M V n z)) =
        ((2 : ℂ) • dilationCompression M V n (T z) - ((T†) ^ n) (T z)) -
          ((2 : ℂ) • T (dilationCompression M V n z) -
            T (((T†) ^ n) z)) +
          (((T†) ^ n) (T z) - T (((T†) ^ n) z)) := by
      rw [smul_sub]
      abel
    _ = ((T†) ^ n) (T z) - T (((T†) ^ n) z) := by
      rw [hz]
      simp

/-- The exact identity
`V† M†ⁿ ω = Qₙ₊₁ T x - κ Qₙ x` from the manuscript. -/
theorem dilation_defect_compression_identity
    (T : H →L[ℂ] H) (M : K →L[ℂ] K) (V : H →ₗᵢ[ℂ] K)
    (κ : ℝ) (x : H) (n : ℕ) :
    (V.toContinuousLinearMap†) (((M†) ^ n) (dilationDefect T M V κ x)) =
      dilationCompression M V (n + 1) (T x) -
        (κ : ℂ) • dilationCompression M V n x := by
  simp only [dilationDefect, map_sub, map_smul, dilationCompression_apply]
  rw [pow_succ]
  rfl

/-- The identity
`mₙ = 2 Re ⟪T†ⁿx,Qₙx⟫ - ‖T†ⁿx‖²` used before the recurrence. -/
theorem dilationMoment_eq
    (T : H →L[ℂ] H) (M : K →L[ℂ] K) (V : H →ₗᵢ[ℂ] K)
    (x : H) (n : ℕ) (hcomm : Commute (dilationError T M V n) T) :
    dilationMoment T M V x n =
      2 * RCLike.re ⟪((T†) ^ n) x, dilationCompression M V n x⟫_ℂ -
        ‖((T†) ^ n) x‖ ^ 2 := by
  have hpowcomm := hcomm.pow_right n
  have happ := congrArg (fun S : H →L[ℂ] H ↦ S x) hpowcomm.eq
  have happ' :
      dilationError T M V n ((T ^ n) x) =
        (T ^ n) (dilationError T M V n x) := by
    simpa only [mul_apply_eq_comp] using happ
  rw [dilationMoment, happ']
  rw [← (T ^ n).adjoint_inner_left (dilationError T M V n x) x]
  have hadjpow : (T ^ n)† = (T†) ^ n := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_pow,
      ContinuousLinearMap.star_eq_adjoint]
  rw [hadjpow]
  simp only [dilationError_apply, inner_sub_right, inner_smul_right]
  change Complex.re
      (2 * ⟪((T†) ^ n) x, dilationCompression M V n x⟫_ℂ -
        ⟪((T†) ^ n) x, ((T†) ^ n) x⟫_ℂ) = _
  rw [Complex.sub_re, Complex.mul_re]
  norm_num
  norm_cast

/-- The exact raw recurrence in Lemma 3.1, before completing the square. -/
theorem dilationMoment_recurrence
    (T : H →L[ℂ] H) (M : K →L[ℂ] K) (V : H →ₗᵢ[ℂ] K)
    (κ : ℝ) (x : H) (n : ℕ)
    (htop : (T†) (T x) = (κ ^ 2 : ℂ) • x)
    (hcommn : Commute (dilationError T M V n) T)
    (hcommnext : Commute (dilationError T M V (n + 1)) T) :
    κ * dilationMoment T M V x n - dilationMoment T M V x (n + 1) =
      κ * (κ - 1) * ‖((T†) ^ n) x‖ ^ 2 -
        2 * RCLike.re
          ⟪(V.toContinuousLinearMap†)
              (((M†) ^ n) (dilationDefect T M V κ x)),
            ((T†) ^ n) x⟫_ℂ := by
  rw [dilationMoment_eq T M V x n hcommn,
    dilationMoment_eq T M V x (n + 1) hcommnext]
  have hqnext :
      ((T†) ^ (n + 1)) x = (T†) (((T†) ^ n) x) := by
    rw [pow_succ']
    rfl
  have htopn :
      ((T†) ^ (n + 1)) (T x) =
        (κ ^ 2 : ℂ) • ((T†) ^ n) x := by
    rw [pow_succ, mul_apply_eq_comp, htop, map_smul]
  have hcommVector :=
    dilation_commutator_identity T M V (n + 1) hcommnext x
  have hinnerTop :
      Complex.re
          ⟪((T†) ^ n) x, ((T†) ^ (n + 1)) (T x)⟫_ℂ =
        κ ^ 2 * ‖((T†) ^ n) x‖ ^ 2 := by
    rw [htopn, inner_smul_right, inner_self_eq_norm_sq_to_K]
    change Complex.re
      ((κ ^ 2 : ℂ) * (‖((T†) ^ n) x‖ : ℂ) ^ 2) = _
    norm_cast
  have hinnerNext :
      Complex.re
          ⟪((T†) ^ n) x, T (((T†) ^ (n + 1)) x)⟫_ℂ =
        ‖((T†) ^ (n + 1)) x‖ ^ 2 := by
    rw [← T.adjoint_inner_left (((T†) ^ (n + 1)) x) (((T†) ^ n) x),
      hqnext, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hcommReal :
      2 * (RCLike.re
          ⟪((T†) ^ n) x, dilationCompression M V (n + 1) (T x)⟫_ℂ -
        RCLike.re
          ⟪((T†) ^ n) x, T (dilationCompression M V (n + 1) x)⟫_ℂ) =
        κ ^ 2 * ‖((T†) ^ n) x‖ ^ 2 -
          ‖((T†) ^ (n + 1)) x‖ ^ 2 := by
    calc
      2 * (RCLike.re
          ⟪((T†) ^ n) x, dilationCompression M V (n + 1) (T x)⟫_ℂ -
        RCLike.re
          ⟪((T†) ^ n) x, T (dilationCompression M V (n + 1) x)⟫_ℂ) =
          RCLike.re
            ⟪((T†) ^ n) x,
              (2 : ℂ) •
                (dilationCompression M V (n + 1) (T x) -
                  T (dilationCompression M V (n + 1) x))⟫_ℂ := by
            simp only [inner_smul_right, inner_sub_right]
            change _ = Complex.re (2 * (_ - _))
            rw [Complex.mul_re, Complex.sub_re]
            norm_num
      _ = RCLike.re
            ⟪((T†) ^ n) x,
              ((T†) ^ (n + 1)) (T x) -
                T (((T†) ^ (n + 1)) x)⟫_ℂ := by rw [hcommVector]
      _ = κ ^ 2 * ‖((T†) ^ n) x‖ ^ 2 -
          ‖((T†) ^ (n + 1)) x‖ ^ 2 := by
            rw [inner_sub_right]
            change Complex.re (_ - _) = _
            rw [Complex.sub_re, hinnerTop, hinnerNext]
  have hdefectVector := dilation_defect_compression_identity T M V κ x n
  have hdefectReal :
      RCLike.re
          ⟪((T†) ^ n) x,
            (V.toContinuousLinearMap†)
              (((M†) ^ n) (dilationDefect T M V κ x))⟫_ℂ =
        RCLike.re
            ⟪((T†) ^ n) x, dilationCompression M V (n + 1) (T x)⟫_ℂ -
          κ * RCLike.re
            ⟪((T†) ^ n) x, dilationCompression M V n x⟫_ℂ := by
    rw [hdefectVector, inner_sub_right, inner_smul_right]
    change Complex.re (_ - (κ : ℂ) * _) = _
    rw [Complex.sub_re, Complex.mul_re]
    norm_num
  have hdefectSym :
      RCLike.re
          ⟪(V.toContinuousLinearMap†)
              (((M†) ^ n) (dilationDefect T M V κ x)),
            ((T†) ^ n) x⟫_ℂ =
        RCLike.re
          ⟪((T†) ^ n) x,
            (V.toContinuousLinearMap†)
              (((M†) ^ n) (dilationDefect T M V κ x))⟫_ℂ :=
    by
      simpa using (inner_re_symm (𝕜 := ℂ)
        ((V.toContinuousLinearMap†)
          (((M†) ^ n) (dilationDefect T M V κ x))) (((T†) ^ n) x))
  have hmove :
      RCLike.re
          ⟪((T†) ^ n) x, T (dilationCompression M V (n + 1) x)⟫_ℂ =
        RCLike.re
          ⟪((T†) ^ (n + 1)) x, dilationCompression M V (n + 1) x⟫_ℂ := by
    rw [← T.adjoint_inner_left (dilationCompression M V (n + 1) x)
      (((T†) ^ n) x), hqnext]
  nlinarith [hcommReal, hdefectReal, hdefectSym, hmove]

omit [CompleteSpace H] in
/-- Young's inequality in exactly the normalization used to complete the
square in Lemma 3.1. -/
theorem real_inner_young_lower_bound {a : ℝ} (ha : 0 < a)
    (q d : H) (w : ℝ) (hw : 0 ≤ w) (hd : ‖d‖ ≤ w) :
    -w ^ 2 / a ≤ a * ‖q‖ ^ 2 - 2 * RCLike.re ⟪d, q⟫_ℂ := by
  have hre : RCLike.re ⟪d, q⟫_ℂ ≤ ‖d‖ * ‖q‖ := re_inner_le_norm d q
  have hdSq : ‖d‖ ^ 2 ≤ w ^ 2 := by
    nlinarith [norm_nonneg d]
  rw [div_le_iff₀ ha]
  nlinarith [sq_nonneg (a * ‖q‖ - ‖d‖)]

/-- The lower recurrence inequality displayed immediately before (3.1). -/
theorem dilationMoment_recurrence_lower_bound
    (T : H →L[ℂ] H) (M : K →L[ℂ] K) (V : H →ₗᵢ[ℂ] K)
    (κ : ℝ) (x : H) (n : ℕ) (hκ : 1 < κ) (hM : ‖M‖ ≤ 1)
    (htop : (T†) (T x) = (κ ^ 2 : ℂ) • x)
    (hcommn : Commute (dilationError T M V n) T)
    (hcommnext : Commute (dilationError T M V (n + 1)) T) :
    -‖dilationDefect T M V κ x‖ ^ 2 / (κ * (κ - 1)) ≤
      κ * dilationMoment T M V x n - dilationMoment T M V x (n + 1) := by
  rw [dilationMoment_recurrence T M V κ x n htop hcommn hcommnext]
  apply real_inner_young_lower_bound
    (mul_pos (lt_trans (by norm_num) hκ) (sub_pos.mpr hκ))
    (((T†) ^ n) x)
    ((V.toContinuousLinearMap†)
      (((M†) ^ n) (dilationDefect T M V κ x)))
    ‖dilationDefect T M V κ x‖ (norm_nonneg _)
  exact norm_adjoint_compression_apply_le M V hM n (dilationDefect T M V κ x)

/-- Adjoint powers have the same operator norm as the original powers. -/
theorem norm_adjoint_pow_eq (T : H →L[ℂ] H) (n : ℕ) :
    ‖(T†) ^ n‖ = ‖T ^ n‖ := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← star_pow, norm_star]

/-- Gelfand's formula in the form used in Lemma 3.1: if the spectral radius
is strictly smaller than one, then the powers converge to zero in operator
norm. -/
theorem powers_tendsto_zero_of_spectralRadius_lt_one
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (a : A) (hρ : spectralRadius ℂ a < 1) :
    Tendsto (fun n : ℕ ↦ a ^ n) atTop (𝓝 0) := by
  obtain ⟨r, hρr, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hρ
  have hrReal : (r : ℝ) < 1 := by
    exact_mod_cast hr
  have hroot : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (‖a ^ n‖ ^ (1 / n : ℝ)) < (r : ENNReal) :=
    (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a).eventually
      (Iio_mem_nhds hρr)
  apply squeeze_zero_norm' ?_
    (tendsto_pow_atTop_nhds_zero_of_lt_one r.coe_nonneg hrReal)
  filter_upwards [hroot, eventually_ge_atTop 1] with n hnroot hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hrootReal : ‖a ^ n‖ ^ (1 / n : ℝ) < (r : ℝ) := by
    rw [← ENNReal.ofReal_lt_coe_iff (Real.rpow_nonneg (norm_nonneg _) _)]
    exact hnroot
  have hraised := Real.rpow_lt_rpow
    (Real.rpow_nonneg (norm_nonneg (a ^ n)) _) hrootReal hnpos
  have hnorm : ‖a ^ n‖ < (r : ℝ) ^ n := by
    calc
      ‖a ^ n‖ = (‖a ^ n‖ ^ (1 / n : ℝ)) ^ (n : ℝ) := by
        rw [← Real.rpow_mul (norm_nonneg _), one_div, inv_mul_cancel₀ hnne,
          Real.rpow_one]
      _ < (r : ℝ) ^ (n : ℝ) := hraised
      _ = (r : ℝ) ^ n := Real.rpow_natCast _ _
  exact hnorm.le

/-- Pointwise adjoint-power decay derived from the spectral-radius hypothesis
in Lemma 3.1. -/
theorem adjoint_powers_apply_tendsto_zero_of_spectralRadius_lt_one
    (T : H →L[ℂ] H) (x : H) (hρ : spectralRadius ℂ T < 1) :
    Tendsto (fun n : ℕ ↦ ((T†) ^ n) x) atTop (𝓝 0) := by
  have hpow := powers_tendsto_zero_of_spectralRadius_lt_one T hρ
  apply squeeze_zero_norm'
    (Filter.Eventually.of_forall fun n ↦ by
      calc
        ‖((T†) ^ n) x‖ ≤ ‖(T†) ^ n‖ * ‖x‖ := ((T†) ^ n).le_opNorm x
        _ = ‖T ^ n‖ * ‖x‖ := by rw [norm_adjoint_pow_eq])
  simpa using hpow.norm.mul_const ‖x‖

/-- Uniform boundedness of the errors gives the power bound used in the
manuscript. -/
theorem norm_pow_le_of_dilationError_bound
    (T : H →L[ℂ] H) (M : K →L[ℂ] K) (V : H →ₗᵢ[ℂ] K)
    (hM : ‖M‖ ≤ 1) (C : ℝ) (n : ℕ)
    (hE : ‖dilationError T M V n‖ ≤ C) :
    ‖T ^ n‖ ≤ 2 + C := by
  have hrewrite :
      (T†) ^ n = (2 : ℂ) • dilationCompression M V n -
        dilationError T M V n := by
    rw [dilationError]
    abel
  rw [← norm_adjoint_pow_eq T n, hrewrite]
  calc
    ‖(2 : ℂ) • dilationCompression M V n - dilationError T M V n‖ ≤
        ‖(2 : ℂ) • dilationCompression M V n‖ +
          ‖dilationError T M V n‖ := norm_sub_le _ _
    _ = 2 * ‖dilationCompression M V n‖ +
          ‖dilationError T M V n‖ := by
      rw [norm_smul]
      norm_num
    _ ≤ 2 * 1 + C :=
      add_le_add
        (mul_le_mul_of_nonneg_left (norm_dilationCompression_le_one M V hM n)
          (by norm_num)) hE
    _ = 2 + C := by ring

/-- The sequence of moments in (3.1) is bounded.  It is indexed from zero,
so this is the sequence `m₁,m₂,…`. -/
theorem dilationMoment_succ_bounded
    (T : H →L[ℂ] H) (M : K →L[ℂ] K) (V : H →ₗᵢ[ℂ] K)
    (x : H) (hx : ‖x‖ = 1) (hM : ‖M‖ ≤ 1)
    (hbounded : ∃ C : ℝ, ∀ n, 1 ≤ n → ‖dilationError T M V n‖ ≤ C) :
    ∃ B : ℝ, ∀ k, |dilationMoment T M V x (k + 1)| ≤ B := by
  obtain ⟨C, hC⟩ := hbounded
  have hCnonneg : 0 ≤ C :=
    le_trans (norm_nonneg (dilationError T M V 1)) (hC 1 le_rfl)
  refine ⟨C * (2 + C), fun k ↦ ?_⟩
  have hpos : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have hE := hC (k + 1) hpos
  have hpow := norm_pow_le_of_dilationError_bound T M V hM C (k + 1) hE
  have hTapply : ‖(T ^ (k + 1)) x‖ ≤ 2 + C := by
    calc
      ‖(T ^ (k + 1)) x‖ ≤ ‖T ^ (k + 1)‖ * ‖x‖ :=
        (T ^ (k + 1)).le_opNorm x
      _ = ‖T ^ (k + 1)‖ := by rw [hx, mul_one]
      _ ≤ 2 + C := hpow
  have hEapply :
      ‖dilationError T M V (k + 1) ((T ^ (k + 1)) x)‖ ≤ C * (2 + C) := by
    calc
      ‖dilationError T M V (k + 1) ((T ^ (k + 1)) x)‖ ≤
          ‖dilationError T M V (k + 1)‖ * ‖(T ^ (k + 1)) x‖ :=
        (dilationError T M V (k + 1)).le_opNorm _
      _ ≤ C * (2 + C) :=
        mul_le_mul hE hTapply (norm_nonneg _) hCnonneg
  rw [dilationMoment]
  calc
    |RCLike.re
        ⟪x, dilationError T M V (k + 1) ((T ^ (k + 1)) x)⟫_ℂ| ≤
        ‖⟪x, dilationError T M V (k + 1) ((T ^ (k + 1)) x)⟫_ℂ‖ :=
      RCLike.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖dilationError T M V (k + 1) ((T ^ (k + 1)) x)‖ :=
      norm_inner_le_norm _ _
    _ ≤ 1 * (C * (2 + C)) := by
      rw [hx]
      gcongr
    _ = C * (2 + C) := by ring

/-- Equation (3.1), obtained from the raw recurrence by telescoping. -/
theorem dilation_first_inequality
    (T : H →L[ℂ] H) (M : K →L[ℂ] K) (V : H →ₗᵢ[ℂ] K)
    (κ : ℝ) (x : H) (hκ : 1 < κ) (hx : ‖x‖ = 1) (hM : ‖M‖ ≤ 1)
    (htop : (T†) (T x) = (κ ^ 2 : ℂ) • x)
    (hbounded : ∃ C : ℝ, ∀ n, 1 ≤ n → ‖dilationError T M V n‖ ≤ C)
    (hcomm : ∀ n, 1 ≤ n → Commute (dilationError T M V n) T) :
    -‖dilationDefect T M V κ x‖ ^ 2 / (κ - 1) ^ 2 ≤
      κ * dilationMoment T M V x 1 := by
  have hmomentBounded := dilationMoment_succ_bounded T M V x hx hM hbounded
  have htel := dilation_telescoping_lower_bound
    (fun k ↦ dilationMoment T M V x (k + 1)) hκ hmomentBounded
    (fun k ↦ dilationMoment_recurrence_lower_bound T M V κ x (k + 1)
      hκ hM htop (hcomm (k + 1) (Nat.le_add_left 1 k))
      (hcomm (k + 1 + 1) (by omega)))
  simpa using htel

/-- The first moment expressed by the mixed compressed matrix coefficient. -/
theorem dilationMoment_one_eq
    (T : H →L[ℂ] H) (M : K →L[ℂ] K) (V : H →ₗᵢ[ℂ] K)
    (κ : ℝ) (x : H) (hx : ‖x‖ = 1)
    (htop : (T†) (T x) = (κ ^ 2 : ℂ) • x) :
    dilationMoment T M V x 1 =
      2 * RCLike.re ⟪x, dilationCompression M V 1 (T x)⟫_ℂ - κ ^ 2 := by
  rw [dilationMoment]
  simp only [pow_one, dilationError_apply, inner_sub_right, inner_smul_right]
  rw [htop, inner_smul_right, inner_self_eq_norm_sq_to_K, hx]
  change Complex.re (2 * _ - (κ ^ 2 : ℂ) * (1 : ℂ) ^ 2) = _
  rw [Complex.sub_re, Complex.mul_re]
  norm_num
  norm_cast

/-- Equation (3.2), with the two elementary norm facts separated as explicit
inputs for reuse in the equality case. -/
theorem dilation_second_inequality
    (T : H →L[ℂ] H) (M : K →L[ℂ] K) (V : H →ₗᵢ[ℂ] K)
    (κ : ℝ) (x : H) (hκ : 0 ≤ κ) (hx : ‖x‖ = 1) (hM : ‖M‖ ≤ 1)
    (hTx : ‖T x‖ = κ)
    (htop : (T†) (T x) = (κ ^ 2 : ℂ) • x) :
    ‖dilationDefect T M V κ x‖ ^ 2 ≤
      2 * κ ^ 2 - κ * dilationMoment T M V x 1 - κ ^ 3 := by
  have hMadj : ‖M†‖ ≤ 1 := by
    simpa [← ContinuousLinearMap.star_eq_adjoint] using hM
  have ha : ‖(M†) (V (T x))‖ ≤ κ := by
    calc
      ‖(M†) (V (T x))‖ ≤ ‖M†‖ * ‖V (T x)‖ := (M†).le_opNorm _
      _ ≤ 1 * ‖V (T x)‖ := by gcongr
      _ = κ := by rw [V.norm_map, hTx, one_mul]
  have hb : ‖(κ : ℂ) • V x‖ = κ := by
    rw [norm_smul, V.norm_map, hx, mul_one]
    simpa using hκ
  have hmixed :
      Complex.re ⟪(M†) (V (T x)), V x⟫_ℂ =
        Complex.re ⟪x, dilationCompression M V 1 (T x)⟫_ℂ := by
    rw [dilationCompression_apply, pow_one,
      V.toContinuousLinearMap.adjoint_inner_right]
    simpa using (inner_re_symm (𝕜 := ℂ) ((M†) (V (T x))) (V x))
  have hcross :
      RCLike.re ⟪(M†) (V (T x)), (κ : ℂ) • V x⟫_ℂ =
        κ * RCLike.re ⟪x, dilationCompression M V 1 (T x)⟫_ℂ := by
    rw [inner_smul_right]
    change Complex.re ((κ : ℂ) * _) = κ * Complex.re _
    rw [Complex.mul_re]
    simpa only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      congrArg (fun r : ℝ ↦ κ * r) hmixed
  have hmoment := dilationMoment_one_eq T M V κ x hx htop
  rw [dilationDefect, norm_sub_sq (𝕜 := ℂ), hcross, hb]
  have haSq : ‖(M†) (V (T x))‖ ^ 2 ≤ κ ^ 2 := by
    nlinarith [norm_nonneg ((M†) (V (T x)))]
  nlinarith

/-- The norm conclusion of Lemma 3.1, with `Eₙ` represented by its defining
formula `dilationError`. -/
theorem abstract_dilation_norm_le_two [FiniteDimensional ℂ H] [Nontrivial H]
    (T : H →L[ℂ] H) (M : K →L[ℂ] K) (V : H →ₗᵢ[ℂ] K)
    (hM : ‖M‖ ≤ 1)
    (hbounded : ∃ C : ℝ, ∀ n, 1 ≤ n → ‖dilationError T M V n‖ ≤ C)
    (hcomm : ∀ n, 1 ≤ n → Commute (dilationError T M V n) T) :
    ‖T‖ ≤ 2 := by
  by_cases hsmall : ‖T‖ ≤ 1
  · linarith
  have hκ : 1 < ‖T‖ := lt_of_not_ge hsmall
  obtain ⟨x, hx, htop⟩ := exists_unit_top_singular_vector T
  have hsquare : ‖T x‖ ^ 2 = ‖T‖ ^ 2 := by
    rw [T.apply_norm_sq_eq_inner_adjoint_left]
    change RCLike.re ⟪(T†) (T x), x⟫_ℂ = _
    rw [htop, inner_smul_left,
      inner_self_eq_norm_sq_to_K, hx]
    simp
    norm_cast
  have hTx : ‖T x‖ = ‖T‖ := by
    nlinarith [norm_nonneg (T x), norm_nonneg T]
  have hfirst := dilation_first_inequality T M V ‖T‖ x hκ hx hM htop hbounded hcomm
  have hsecond := dilation_second_inequality T M V ‖T‖ x (norm_nonneg T)
    hx hM hTx htop
  rw [neg_div] at hfirst
  have hmaster :
      ‖dilationDefect T M V ‖T‖ x‖ ^ 2 *
          (1 - 1 / (‖T‖ - 1) ^ 2) ≤ ‖T‖ ^ 2 * (2 - ‖T‖) := by
    calc
      ‖dilationDefect T M V ‖T‖ x‖ ^ 2 *
          (1 - 1 / (‖T‖ - 1) ^ 2) =
          ‖dilationDefect T M V ‖T‖ x‖ ^ 2 -
            ‖dilationDefect T M V ‖T‖ x‖ ^ 2 / (‖T‖ - 1) ^ 2 := by ring
      _ ≤ ‖dilationDefect T M V ‖T‖ x‖ ^ 2 +
          ‖T‖ * dilationMoment T M V x 1 := by
        simpa [sub_eq_add_neg, add_comm] using
          add_le_add_left hfirst (‖dilationDefect T M V ‖T‖ x‖ ^ 2)
      _ ≤ 2 * ‖T‖ ^ 2 - ‖T‖ ^ 3 := by linarith
      _ = ‖T‖ ^ 2 * (2 - ‖T‖) := by ring
  exact dilation_master_inequality_forces_le_two hκ (sq_nonneg _) hmaster

omit [CompleteSpace H] in
/-- The exact nonnegative slack at `κ = 2` from the equality analysis in
Lemma 3.1. -/
theorem dilation_slack_identity (q d : H) (w : ℝ) :
    2 * ‖q - (2 : ℂ)⁻¹ • d‖ ^ 2 +
        (1 / 2 : ℝ) * (w ^ 2 - ‖d‖ ^ 2) =
      (2 * ‖q‖ ^ 2 - 2 * RCLike.re ⟪d, q⟫_ℂ) + w ^ 2 / 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul]
  have hre : Complex.re ⟪q, d⟫_ℂ = Complex.re ⟪d, q⟫_ℂ := by
    simpa using (inner_re_symm (𝕜 := ℂ) q d)
  change
    2 * (‖q‖ ^ 2 - 2 * Complex.re ((2 : ℂ)⁻¹ * ⟪q, d⟫_ℂ) +
      (‖(2 : ℂ)⁻¹‖ * ‖d‖) ^ 2) +
        (1 / 2 : ℝ) * (w ^ 2 - ‖d‖ ^ 2) = _
  norm_num
  rw [hre]
  ring

omit [CompleteSpace H] in
/-- Vanishing of the special `κ=2` slack gives both equality statements
used in the manuscript. -/
theorem dilation_slack_zero_forces (q d : H) (w : ℝ)
    (hw : 0 ≤ w) (hd : ‖d‖ ≤ w)
    (hequality : 2 * ‖q‖ ^ 2 - 2 * RCLike.re ⟪d, q⟫_ℂ = -w ^ 2 / 2) :
    d = (2 : ℂ) • q ∧ ‖d‖ = w := by
  have hgap : 0 ≤ w ^ 2 - ‖d‖ ^ 2 := by
    nlinarith [norm_nonneg d]
  have hsum :
      2 * ‖q - (2 : ℂ)⁻¹ • d‖ ^ 2 +
        (1 / 2 : ℝ) * (w ^ 2 - ‖d‖ ^ 2) = 0 := by
    rw [dilation_slack_identity]
    nlinarith
  have hfirst : ‖q - (2 : ℂ)⁻¹ • d‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖q - (2 : ℂ)⁻¹ • d‖]
  have hsecond : w ^ 2 - ‖d‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖q - (2 : ℂ)⁻¹ • d‖]
  constructor
  · have hz : q - (2 : ℂ)⁻¹ • d = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (q - (2 : ℂ)⁻¹ • d)]
    have hhalf : q = (2 : ℂ)⁻¹ • d := sub_eq_zero.mp hz
    calc
      d = (2 : ℂ) • ((2 : ℂ)⁻¹ • d) := by
        rw [smul_smul]
        norm_num
      _ = (2 : ℂ) • q := by rw [← hhalf]
  · nlinarith [norm_nonneg d]

/-- At norm two, every completed-square slack vanishes.  This is the pair of
identities immediately preceding the spectral-radius argument in Lemma 3.1. -/
theorem abstract_dilation_equality_sequences
    (T : H →L[ℂ] H) (M : K →L[ℂ] K) (V : H →ₗᵢ[ℂ] K)
    (x : H) (hx : ‖x‖ = 1) (hM : ‖M‖ ≤ 1)
    (htop : (T†) (T x) = (4 : ℂ) • x)
    (hbounded : ∃ C : ℝ, ∀ n, 1 ≤ n → ‖dilationError T M V n‖ ≤ C)
    (hcomm : ∀ n, 1 ≤ n → Commute (dilationError T M V n) T) :
    ∀ k : ℕ,
      let n := k + 1
      let d := (V.toContinuousLinearMap†)
        (((M†) ^ n) (dilationDefect T M V 2 x))
      d = (2 : ℂ) • ((T†) ^ n) x ∧
        ‖d‖ = ‖dilationDefect T M V 2 x‖ := by
  have htop' : (T†) (T x) = ((2 : ℝ) ^ 2 : ℂ) • x := by
    have hcoeff : (4 : ℂ) = ((2 : ℝ) : ℂ) ^ 2 := by
      apply Complex.ext <;> norm_num
    exact htop.trans (congrArg (fun c : ℂ ↦ c • x) hcoeff)
  have hsquare : ‖T x‖ ^ 2 = 2 ^ 2 := by
    rw [T.apply_norm_sq_eq_inner_adjoint_left]
    change RCLike.re ⟪(T†) (T x), x⟫_ℂ = _
    rw [htop, inner_smul_left, inner_self_eq_norm_sq_to_K, hx]
    simp
    norm_num
  have hTx : ‖T x‖ = 2 := by
    nlinarith [norm_nonneg (T x)]
  have hfirst := dilation_first_inequality T M V 2 x (by norm_num) hx hM
    htop' hbounded hcomm
  have hsecond := dilation_second_inequality T M V 2 x (by norm_num) hx hM
    hTx htop'
  have hfirst' : -‖dilationDefect T M V 2 x‖ ^ 2 ≤
      2 * dilationMoment T M V x 1 := by
    norm_num at hfirst ⊢
    exact hfirst
  have hsecond' : ‖dilationDefect T M V 2 x‖ ^ 2 ≤
      -2 * dilationMoment T M V x 1 := by
    norm_num at hsecond ⊢
    linarith
  obtain ⟨hinitial, -⟩ := dilation_equality_squeeze hfirst' hsecond'
  have hmomentBounded := dilationMoment_succ_bounded T M V x hx hM hbounded
  have hrecurrence : ∀ k,
      -‖dilationDefect T M V 2 x‖ ^ 2 / (2 * (2 - 1)) ≤
        2 * dilationMoment T M V x (k + 1) -
          dilationMoment T M V x (k + 1 + 1) := by
    intro k
    exact dilationMoment_recurrence_lower_bound T M V 2 x (k + 1)
      (by norm_num) hM htop'
      (hcomm (k + 1) (Nat.le_add_left 1 k))
      (hcomm (k + 1 + 1) (by omega))
  have hrigid := dilation_telescoping_rigidity
    (fun k ↦ dilationMoment T M V x (k + 1)) (κ := 2)
    (w := ‖dilationDefect T M V 2 x‖ ^ 2) (by norm_num)
    hmomentBounded hrecurrence (by
      rw [show ((2 : ℝ) - 1) ^ 2 = 1 by norm_num, div_one]
      exact hinitial)
  intro k
  dsimp only
  let n := k + 1
  let q : H := ((T†) ^ n) x
  let d : H := (V.toContinuousLinearMap†)
    (((M†) ^ n) (dilationDefect T M V 2 x))
  have hexact := dilationMoment_recurrence T M V 2 x n htop'
    (hcomm n (by omega)) (hcomm (n + 1) (by omega))
  have hrigidk := hrigid k
  have hequality :
      2 * ‖q‖ ^ 2 - 2 * RCLike.re ⟪d, q⟫_ℂ =
        -‖dilationDefect T M V 2 x‖ ^ 2 / 2 := by
    dsimp [n, q, d] at hexact ⊢
    norm_num at hexact hrigidk ⊢
    linarith
  have hd : ‖d‖ ≤ ‖dilationDefect T M V 2 x‖ := by
    dsimp [d, n]
    exact norm_adjoint_compression_apply_le M V hM (k + 1)
      (dilationDefect T M V 2 x)
  exact dilation_slack_zero_forces q d ‖dilationDefect T M V 2 x‖
    (norm_nonneg _) hd hequality

/-- The spectral-decay step of Lemma 3.1: convergence of the adjoint powers,
together with the equality-slack identities, forces `ω=0`. -/
theorem dilationDefect_eq_zero_of_adjoint_powers_tendsto
    (T : H →L[ℂ] H) (M : K →L[ℂ] K) (V : H →ₗᵢ[ℂ] K)
    (x : H) (hx : ‖x‖ = 1) (hM : ‖M‖ ≤ 1)
    (htop : (T†) (T x) = (4 : ℂ) • x)
    (hbounded : ∃ C : ℝ, ∀ n, 1 ≤ n → ‖dilationError T M V n‖ ≤ C)
    (hcomm : ∀ n, 1 ≤ n → Commute (dilationError T M V n) T)
    (hpow : Tendsto (fun n : ℕ ↦ ((T†) ^ n) x) atTop (𝓝 0)) :
    dilationDefect T M V 2 x = 0 := by
  have hseq := abstract_dilation_equality_sequences T M V x hx hM htop hbounded hcomm
  have hq : Tendsto (fun k : ℕ ↦ ((T†) ^ (k + 1)) x) atTop (𝓝 0) :=
    hpow.comp (tendsto_add_atTop_nat 1)
  have hnormq :
      Tendsto (fun k : ℕ ↦ ‖((T†) ^ (k + 1)) x‖) atTop (𝓝 0) := by
    simpa using hq.norm
  have hscaled :
      Tendsto (fun k : ℕ ↦ 2 * ‖((T†) ^ (k + 1)) x‖) atTop (𝓝 0) := by
    simpa using hnormq.const_mul 2
  have heq : ∀ k : ℕ,
      ‖dilationDefect T M V 2 x‖ = 2 * ‖((T†) ^ (k + 1)) x‖ := by
    intro k
    obtain ⟨hmap, hnorm⟩ := hseq k
    rw [← hnorm, hmap, norm_smul]
    norm_num
  have hconstant :
      Tendsto (fun _ : ℕ ↦ ‖dilationDefect T M V 2 x‖) atTop (𝓝 0) :=
    hscaled.congr' (Filter.Eventually.of_forall fun k ↦ (heq k).symm)
  have hself :
      Tendsto (fun _ : ℕ ↦ ‖dilationDefect T M V 2 x‖) atTop
        (𝓝 ‖dilationDefect T M V 2 x‖) := tendsto_const_nhds
  have hnormzero : ‖dilationDefect T M V 2 x‖ = 0 :=
    tendsto_nhds_unique hself hconstant
  exact norm_eq_zero.mp hnormzero

omit [CompleteSpace H] in
/-- Equality in the contraction step used at the end of the dilation lemma:
if `M†(Vy)=Vx` for unit vectors and `V` is isometric, then `M(Vx)=Vy`. -/
theorem contraction_equality_of_adjoint
    (M : K →L[ℂ] K) (V : H →ₗᵢ[ℂ] K) (x y : H)
    (hM : ‖M‖ ≤ 1) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hadj : (M†) (V y) = V x) :
    M (V x) = V y := by
  have hVx : ‖V x‖ = 1 := (V.norm_map x).trans hx
  have hVy : ‖V y‖ = 1 := (V.norm_map y).trans hy
  have hnorm : ‖M (V x)‖ ≤ 1 := by
    calc
      ‖M (V x)‖ ≤ ‖M‖ * ‖V x‖ := M.le_opNorm (V x)
      _ ≤ 1 * 1 := mul_le_mul hM hVx.le (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hinner : ⟪M (V x), V y⟫_ℂ = 1 := by
    rw [← M.adjoint_inner_right, hadj, inner_self_eq_norm_sq_to_K, hVx]
    norm_num
  have hsquare : ‖M (V x) - V y‖ ^ 2 = 0 := by
    rw [norm_sub_sq (𝕜 := ℂ), hinner, hVy]
    norm_num
    have hsquare_le : ‖M (V x)‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg (M (V x))]
    have hdiff_nonneg : 0 ≤ ‖M (V x) - V y‖ ^ 2 := sq_nonneg _
    rw [norm_sub_sq (𝕜 := ℂ), hinner, hVy] at hdiff_nonneg
    norm_num at hdiff_nonneg
    nlinarith
  have hnormzero : ‖M (V x) - V y‖ = 0 := by
    nlinarith [norm_nonneg (M (V x) - V y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnormzero)

/-- The equality-pair relations extracted by the dilation argument. -/
structure DilationEqualityPair (T : H →L[ℂ] H) (x y : H) : Prop where
  map_x : T x = (2 : ℂ) • y
  adjoint_map_x : (T†) x = 0
  map_y : T y = 0
  adjoint_map_y : (T†) y = (2 : ℂ) • x

/-- The relation `T†T x=4x` immediately gives `T†(Tx/2)=2x`. -/
theorem adjoint_map_half_of_adjoint_comp
    (T : H →L[ℂ] H) (x : H)
    (htop : (T†) (T x) = (4 : ℂ) • x) :
    (T†) ((2 : ℂ)⁻¹ • T x) = (2 : ℂ) • x := by
  rw [map_smul, htop]
  module

/-- The two extremal vectors are orthogonal once `Tx=2y` and `T†x=0`. -/
theorem inner_eq_zero_of_dilation_pair
    (T : H →L[ℂ] H) (x y : H)
    (hTx : T x = (2 : ℂ) • y) (hTstarx : (T†) x = 0) :
    ⟪x, y⟫_ℂ = 0 := by
  have hzero : ⟪x, T x⟫_ℂ = 0 := by
    rw [← T.adjoint_inner_left, hTstarx, inner_zero_left]
  rw [hTx, inner_smul_right] at hzero
  norm_num at hzero
  exact hzero

/-- Exact identities (3.10)--(3.11) from the manuscript.  They use only the
equality-pair relations and commutation of the auxiliary functional calculus
value `S` with `T`. -/
theorem dilationEquality_coefficient_identities
    (T S : H →L[ℂ] H) (x y : H)
    (hp : DilationEqualityPair T x y)
    (hcomm : ∀ z, S (T z) = T (S z)) :
    ⟪x, S (T x)⟫_ℂ = 0 ∧
      ⟪y, S (T x)⟫_ℂ = (2 : ℂ) * ⟪x, S x⟫_ℂ ∧
      ⟪x, S y⟫_ℂ = 0 ∧
      ⟪y, S y⟫_ℂ = ⟪x, S x⟫_ℂ := by
  have hfirst : ⟪x, S (T x)⟫_ℂ = 0 := by
    rw [hcomm, ← T.adjoint_inner_left, hp.adjoint_map_x, inner_zero_left]
  have hthird : ⟪x, S y⟫_ℂ = 0 := by
    have hscaled : S (T x) = (2 : ℂ) • S y := by
      rw [hp.map_x, map_smul]
    rw [hscaled, inner_smul_right] at hfirst
    have htwo : (2 : ℂ) * ⟪x, S y⟫_ℂ = 0 := by
      simpa using hfirst
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hfourth : ⟪y, S y⟫_ℂ = ⟪x, S x⟫_ℂ := by
    have hleft : ⟪y, T (S x)⟫_ℂ = (2 : ℂ) * ⟪x, S x⟫_ℂ := by
      calc
        ⟪y, T (S x)⟫_ℂ = ⟪(T†) y, S x⟫_ℂ :=
          (T.adjoint_inner_left (S x) y).symm
        _ = ⟪(2 : ℂ) • x, S x⟫_ℂ := by rw [hp.adjoint_map_y]
        _ = (2 : ℂ) * ⟪x, S x⟫_ℂ := by
          simp only [inner_smul_left, map_ofNat]
    have hright : ⟪y, T (S x)⟫_ℂ = (2 : ℂ) * ⟪y, S y⟫_ℂ := by
      rw [← hcomm, hp.map_x, map_smul, inner_smul_right]
    have htwo : (2 : ℂ) * ⟪y, S y⟫_ℂ =
        (2 : ℂ) * ⟪x, S x⟫_ℂ := hright.symm.trans hleft
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) htwo
  have hsecond :
      ⟪y, S (T x)⟫_ℂ = (2 : ℂ) * ⟪x, S x⟫_ℂ := by
    rw [hp.map_x, map_smul, inner_smul_right, hfourth]
  exact ⟨hfirst, hsecond, hthird, hfourth⟩

/-- The four equality conclusions of Lemma 3.1, assuming the power decay
which is supplied there by `r(T)<1`. -/
theorem abstract_dilation_equality_of_adjoint_powers_tendsto
    (T : H →L[ℂ] H) (M : K →L[ℂ] K) (V : H →ₗᵢ[ℂ] K)
    (x : H) (hx : ‖x‖ = 1) (hM : ‖M‖ ≤ 1)
    (htop : (T†) (T x) = (4 : ℂ) • x)
    (hbounded : ∃ C : ℝ, ∀ n, 1 ≤ n → ‖dilationError T M V n‖ ≤ C)
    (hcomm : ∀ n, 1 ≤ n → Commute (dilationError T M V n) T)
    (hpow : Tendsto (fun n : ℕ ↦ ((T†) ^ n) x) atTop (𝓝 0)) :
    let y := (2 : ℂ)⁻¹ • T x
    (T†) x = 0 ∧ (T†) y = (2 : ℂ) • x ∧
      M (V x) = V y ∧ (M†) (V y) = V x := by
  have hω := dilationDefect_eq_zero_of_adjoint_powers_tendsto
    T M V x hx hM htop hbounded hcomm hpow
  have hseq := abstract_dilation_equality_sequences T M V x hx hM htop hbounded hcomm
  have hfirstSequence := (hseq 0).1
  have hstarx : (T†) x = 0 := by
    norm_num at hfirstSequence
    rw [hω] at hfirstSequence
    simp only [map_zero] at hfirstSequence
    have : (2 : ℂ) • (T†) x = 0 := hfirstSequence.symm
    exact (smul_eq_zero.mp this).resolve_left (by norm_num)
  let y : H := (2 : ℂ)⁻¹ • T x
  have hstary : (T†) y = (2 : ℂ) • x := by
    dsimp [y]
    exact adjoint_map_half_of_adjoint_comp T x htop
  have hsquare : ‖T x‖ ^ 2 = 2 ^ 2 := by
    rw [T.apply_norm_sq_eq_inner_adjoint_left]
    change RCLike.re ⟪(T†) (T x), x⟫_ℂ = _
    rw [htop, inner_smul_left, inner_self_eq_norm_sq_to_K, hx]
    simp
    norm_num
  have hTx : ‖T x‖ = 2 := by
    nlinarith [norm_nonneg (T x)]
  have hy : ‖y‖ = 1 := by
    dsimp [y]
    rw [norm_smul, hTx]
    norm_num
  have hMadjy : (M†) (V y) = V x := by
    have hdefect : (M†) (V (T x)) = (2 : ℂ) • V x := by
      rw [dilationDefect, sub_eq_zero] at hω
      exact hω
    dsimp [y]
    rw [LinearIsometry.map_smul, map_smul, hdefect, smul_smul]
    norm_num
  have hMy : M (V x) = V y :=
    contraction_equality_of_adjoint M V x y hM hx hy hMadjy
  exact ⟨hstarx, hstary, hMy, hMadjy⟩

/-- The equality conclusion of Lemma 3.1 with its stated spectral-radius
hypothesis. -/
theorem abstract_dilation_equality_of_spectralRadius_lt_one
    (T : H →L[ℂ] H) (M : K →L[ℂ] K) (V : H →ₗᵢ[ℂ] K)
    (x : H) (hx : ‖x‖ = 1) (hM : ‖M‖ ≤ 1)
    (htop : (T†) (T x) = (4 : ℂ) • x)
    (hρ : spectralRadius ℂ T < 1)
    (hbounded : ∃ C : ℝ, ∀ n, 1 ≤ n → ‖dilationError T M V n‖ ≤ C)
    (hcomm : ∀ n, 1 ≤ n → Commute (dilationError T M V n) T) :
    let y := (2 : ℂ)⁻¹ • T x
    (T†) x = 0 ∧ (T†) y = (2 : ℂ) • x ∧
      M (V x) = V y ∧ (M†) (V y) = V x := by
  exact abstract_dilation_equality_of_adjoint_powers_tendsto
    T M V x hx hM htop hbounded hcomm
      (adjoint_powers_apply_tendsto_zero_of_spectralRadius_lt_one T x hρ)

/-- Lemma 3.1 as one interface: the uniform dilation hypotheses imply the
sharp norm bound, and at equality its stated extra hypotheses imply all four
operator identities. -/
theorem abstract_dilation_estimate [FiniteDimensional ℂ H] [Nontrivial H]
    (T : H →L[ℂ] H) (M : K →L[ℂ] K) (V : H →ₗᵢ[ℂ] K)
    (hM : ‖M‖ ≤ 1)
    (hbounded : ∃ C : ℝ, ∀ n, 1 ≤ n → ‖dilationError T M V n‖ ≤ C)
    (hcomm : ∀ n, 1 ≤ n → Commute (dilationError T M V n) T) :
    ‖T‖ ≤ 2 ∧
      ∀ x : H, ‖T‖ = 2 → spectralRadius ℂ T < 1 →
        (T†) (T x) = (4 : ℂ) • x → ‖x‖ = 1 →
        let y := (2 : ℂ)⁻¹ • T x
        (T†) x = 0 ∧ (T†) y = (2 : ℂ) • x ∧
          M (V x) = V y ∧ (M†) (V y) = V x := by
  refine ⟨abstract_dilation_norm_le_two T M V hM hbounded hcomm, ?_⟩
  intro x _hTnorm hρ htop hx
  exact abstract_dilation_equality_of_spectralRadius_lt_one
    T M V x hx hM htop hρ hbounded hcomm

end DiskRigidity.Operator
