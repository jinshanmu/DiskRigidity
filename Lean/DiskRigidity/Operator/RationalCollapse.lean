/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.EqualityData

/-!
# The boundary scalar identity behind rational collapse

This file formalizes equations (5.5)--(5.7).  Once the boundary-kernel vector
is a support vector, its vanishing quadratic form expands, using the equality
data (3.8), to the transfer identity `c(σ) f(σ) = 2 a(σ)`.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate InnerProductSpace

namespace DiskRigidity.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The two resolvent coefficient identities in (5.6), valid for every
operator commuting with the extremal matrix value. -/
theorem SharpEqualityData.resolvent_coefficient_identities
    {T R : H →L[ℂ] H} {x y : H} (hxy : SharpEqualityData T x y)
    (hcomm : ∀ z, R (T z) = T (R z)) :
    ⟪x, R y⟫_ℂ = 0 ∧ ⟪y, R y⟫_ℂ = ⟪x, R x⟫_ℂ := by
  exact ⟨(hxy.coefficient_identities hcomm).2.2.1,
    (hxy.coefficient_identities hcomm).2.2.2⟩

/-- Expanding (5.5) gives (5.7) pointwise. -/
theorem boundary_quadratic_zero_imp_transfer_identity
    {T R : H →L[ℂ] H} {x y : H} (hxy : SharpEqualityData T x y)
    (hcomm : ∀ z, R (T z) = T (R z))
    (f : ℂ) (hf : ‖f‖ = 1)
    (hquad : ⟪y - f • x, R (y - f • x)⟫_ℂ = 0) :
    f * ⟪y, R x⟫_ℂ = 2 * ⟪x, R x⟫_ℂ := by
  obtain ⟨hxyR, hyyR⟩ := hxy.resolvent_coefficient_identities hcomm
  have hnormsq : (starRingEnd ℂ) f * f = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hf]
    norm_num
  have hnormsq' : f * (starRingEnd ℂ) f = 1 := by
    rw [mul_comm, hnormsq]
  rw [map_sub, map_smul] at hquad
  rw [inner_sub_left, inner_sub_right, inner_sub_right,
    inner_smul_left, inner_smul_right,
    hxyR, hyyR] at hquad
  rw [inner_smul_right, inner_smul_left] at hquad
  simp only [mul_zero] at hquad
  rw [← mul_assoc f ((starRingEnd ℂ) f) ⟪x, R x⟫_ℂ] at hquad
  rw [hnormsq', one_mul] at hquad
  linear_combination -hquad

end DiskRigidity.Operator
