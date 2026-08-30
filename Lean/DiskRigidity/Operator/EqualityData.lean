/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.BoundaryMultiplication

/-!
# Equality data for the sharp numerical-range estimate

This file performs the two equality runs in Proposition 3.3.  The forward
dilation produces `T†x = 0`, `T†y = 2x`, and the multiplication identity.  A
second, independently verified dilation for `T†` then gives `Ty = 0`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped BoundedContinuousFunction ComplexConjugate InnerProduct InnerProductSpace

namespace DiskRigidity.Operator

variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

/-- The vector conclusions (3.8), together with the asserted
orthonormality. -/
structure SharpEqualityData (T : H →L[ℂ] H) (x y : H) : Prop extends
    DilationEqualityPair T x y where
  norm_x : ‖x‖ = 1
  norm_y : ‖y‖ = 1
  inner_xy : ⟪x, y⟫_ℂ = 0

/-- Equality in a dilation witness, in the form used by Proposition 3.3. -/
theorem DilationWitness.equality
    {T : H →L[ℂ] H} (D : DilationWitness (K := K) T)
    (x : H) (hx : ‖x‖ = 1)
    (htop : (T†) (T x) = (4 : ℂ) • x)
    (hρ : spectralRadius ℂ T < 1) :
    let y := (2 : ℂ)⁻¹ • T x
    (T†) x = 0 ∧ (T†) y = (2 : ℂ) • x ∧
      D.multiplication (D.boundaryIsometry x) = D.boundaryIsometry y ∧
      (D.multiplication†) (D.boundaryIsometry y) = D.boundaryIsometry x := by
  exact abstract_dilation_equality_of_spectralRadius_lt_one
    T D.multiplication D.boundaryIsometry x hx D.contraction htop hρ
      D.errors_bounded D.errors_commute

/-- Taking the Hilbert-space adjoint preserves spectral radius.  This follows
directly from Gelfand's formula and equality of the norms of all adjoint
powers. -/
theorem spectralRadius_adjoint_eq (T : H →L[ℂ] H) :
    spectralRadius ℂ (T†) = spectralRadius ℂ T := by
  apply tendsto_nhds_unique
    (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius (T†))
  apply
    (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius T).congr'
  filter_upwards [] with k
  rw [norm_adjoint_pow_eq]

/-- Running the equality argument for both `T` and `T†` derives all of
(3.8), rather than assuming any of those four identities.  The final
conjunct is the forward multiplication equality which becomes (3.9). -/
theorem exists_sharpEqualityData_of_two_dilations
    [FiniteDimensional ℂ H] [Nontrivial H]
    (T : H →L[ℂ] H)
    (D : DilationWitness (K := K) T)
    (Dadj : DilationWitness (K := L) (T†))
    (hT : ‖T‖ = 2) (hρ : spectralRadius ℂ T < 1) :
    ∃ x y : H, SharpEqualityData T x y ∧
      D.multiplication (D.boundaryIsometry x) = D.boundaryIsometry y := by
  obtain ⟨x, hx, htopNorm⟩ := exists_unit_top_singular_vector T
  have htop : (T†) (T x) = (4 : ℂ) • x := by
    rw [hT] at htopNorm
    norm_num at htopNorm ⊢
    exact htopNorm
  let y : H := (2 : ℂ)⁻¹ • T x
  have hforward :
      (T†) x = 0 ∧ (T†) y = (2 : ℂ) • x ∧
        D.multiplication (D.boundaryIsometry x) = D.boundaryIsometry y ∧
        (D.multiplication†) (D.boundaryIsometry y) = D.boundaryIsometry x := by
    simpa [y] using D.equality x hx htop hρ
  have hTx : T x = (2 : ℂ) • y := by
    dsimp [y]
    rw [smul_smul]
    norm_num
  have hTxNormSq : ‖T x‖ ^ 2 = 4 := by
    rw [T.apply_norm_sq_eq_inner_adjoint_left]
    change Complex.re ⟪(T†) (T x), x⟫_ℂ = 4
    rw [htop, inner_smul_left, inner_self_eq_norm_sq_to_K, hx]
    norm_num
  have hTxNorm : ‖T x‖ = 2 := by
    nlinarith [norm_nonneg (T x)]
  have hy : ‖y‖ = 1 := by
    change ‖(2 : ℂ)⁻¹ • T x‖ = 1
    rw [norm_smul, hTxNorm]
    norm_num
  have hadjTop : ((T†)†) ((T†) y) = (4 : ℂ) • y := by
    rw [hforward.2.1, map_smul, ContinuousLinearMap.adjoint_adjoint, hTx,
      smul_smul]
    norm_num
  have hρadj : spectralRadius ℂ (T†) < 1 := by
    rw [spectralRadius_adjoint_eq]
    exact hρ
  have hbackward := Dadj.equality y hy hadjTop hρadj
  have hTy : T y = 0 := by
    simpa using hbackward.1
  have hxy : ⟪x, y⟫_ℂ = 0 :=
    inner_eq_zero_of_dilation_pair T x y hTx hforward.1
  let hp : DilationEqualityPair T x y :=
    ⟨hTx, hforward.1, hTy, hforward.2.1⟩
  refine ⟨x, y, ?_, hforward.2.2.1⟩
  exact
    { toDilationEqualityPair := hp
      norm_x := hx
      norm_y := hy
      inner_xy := hxy }

/-- The coefficient identities (3.10)--(3.11), now exposed directly from the
full sharp equality data. -/
theorem SharpEqualityData.coefficient_identities
    {T S : H →L[ℂ] H} {x y : H} (hxy : SharpEqualityData T x y)
    (hcomm : ∀ z, S (T z) = T (S z)) :
    ⟪x, S (T x)⟫_ℂ = 0 ∧
      ⟪y, S (T x)⟫_ℂ = (2 : ℂ) * ⟪x, S x⟫_ℂ ∧
      ⟪x, S y⟫_ℂ = 0 ∧
      ⟪y, S y⟫_ℂ = ⟪x, S x⟫_ℂ :=
  dilationEquality_coefficient_identities T S x y
    hxy.toDilationEqualityPair hcomm

variable {i : Type*} [MeasurableSpace i] {mu : Measure i}

/-- The exact pointwise realization of a boundary multiplication operator.
For the manuscript's construction, `factor σ` is
`P(σ)^(1/2) / sqrt 2`, and equality in the ambient `L²` space yields the
stated almost-everywhere identity. -/
structure BoundaryMultiplicationRealization
    {T : H →L[ℂ] H} (D : DilationWitness (K := K) T) (mu : Measure i) where
  /-- Scalar boundary multiplier. -/
  boundaryValue : i → ℂ
  /-- Pointwise factor realizing the boundary isometry. -/
  factor : i → H →L[ℂ] H
  /-- Measurable coefficient representative of a boundary-space vector. -/
  coefficient : K → i → H
  isometry_coefficient_ae : ∀ x : H,
    ∀ᵐ σ ∂mu, coefficient (D.boundaryIsometry x) σ = factor σ x
  multiplication_coefficient_ae : ∀ u : K,
    ∀ᵐ σ ∂mu,
      coefficient (D.multiplication u) σ =
        boundaryValue σ • coefficient u σ

/-- The canonical realization when the ambient boundary Hilbert space is an
actual `L²` space and its operator is the pointwise multiplier constructed in
`BoundaryMultiplication`. -/
def BoundaryMultiplicationRealization.ofLp
    [TopologicalSpace i] [BorelSpace i] [IsFiniteMeasure mu]
    {T : H →L[ℂ] H}
    (D : DilationWitness (K := Lp H 2 mu) T)
    (f : i →ᵇ ℂ) (factor : i → H →L[ℂ] H)
    (hmultiplication : D.multiplication = boundaryMultiplier f)
    (hisometry : ∀ x : H,
      (D.boundaryIsometry x : i → H) =ᵐ[mu] fun σ ↦ factor σ x) :
    BoundaryMultiplicationRealization D mu where
  boundaryValue := f
  factor := factor
  coefficient := fun u ↦ u
  isometry_coefficient_ae := hisometry
  multiplication_coefficient_ae := by
    intro u
    rw [hmultiplication]
    exact boundaryMultiplier_coe_ae f u

/-- Equality in the ambient boundary Hilbert space becomes the expected
pointwise multiplication identity.  This is proved solely from the two
representative laws in `BoundaryMultiplicationRealization`. -/
theorem BoundaryMultiplicationRealization.multiplication_equality_ae
    {T : H →L[ℂ] H} {D : DilationWitness (K := K) T}
    (B : BoundaryMultiplicationRealization D mu) (x y : H)
    (hmul : D.multiplication (D.boundaryIsometry x) = D.boundaryIsometry y) :
    ∀ᵐ σ ∂mu, B.boundaryValue σ • B.factor σ x = B.factor σ y := by
  have heq : B.coefficient (D.multiplication (D.boundaryIsometry x)) =
      B.coefficient (D.boundaryIsometry y) := congrArg B.coefficient hmul
  have heqae : ∀ᵐ σ ∂mu,
      B.coefficient (D.multiplication (D.boundaryIsometry x)) σ =
        B.coefficient (D.boundaryIsometry y) σ :=
    Filter.Eventually.of_forall (congrFun heq)
  filter_upwards [B.multiplication_coefficient_ae (D.boundaryIsometry x),
    B.isometry_coefficient_ae x, B.isometry_coefficient_ae y, heqae]
      with σ hM hx hy heqσ
  calc
    B.boundaryValue σ • B.factor σ x =
        B.boundaryValue σ • B.coefficient (D.boundaryIsometry x) σ := by rw [hx]
    _ = B.coefficient (D.multiplication (D.boundaryIsometry x)) σ := hM.symm
    _ = B.coefficient (D.boundaryIsometry y) σ := heqσ
    _ = B.factor σ y := hy

/-- The almost-everywhere boundary-kernel conclusion (3.9), derived from the
two dilation equality arguments and the concrete pointwise realization of
boundary multiplication. -/
theorem exists_sharpEqualityData_and_boundaryKernel
    [FiniteDimensional ℂ H] [Nontrivial H]
    (T : H →L[ℂ] H)
    (D : DilationWitness (K := K) T)
    (Dadj : DilationWitness (K := L) (T†))
    (B : BoundaryMultiplicationRealization D mu)
    (hT : ‖T‖ = 2) (hρ : spectralRadius ℂ T < 1) :
    ∃ x y : H, SharpEqualityData T x y ∧
      ∀ᵐ σ ∂mu,
        B.factor σ (y - B.boundaryValue σ • x) = 0 := by
  obtain ⟨x, y, hdata, hmul⟩ :=
    exists_sharpEqualityData_of_two_dilations T D Dadj hT hρ
  refine ⟨x, y, hdata, ?_⟩
  exact boundary_kernel_identity_of_multiplication_equality
    B.factor B.boundaryValue x y (B.multiplication_equality_ae x y hmul)

end DiskRigidity.Operator
