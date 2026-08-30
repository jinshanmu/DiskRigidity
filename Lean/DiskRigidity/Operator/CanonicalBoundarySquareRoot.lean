/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.BoundaryIsometry
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Canonical measurable square root of a positive boundary density

In finite dimensions, an integrable operator-valued density which is positive
almost everywhere has a measurable positive representative.  Applying the
continuous functional-calculus square root on the positive cone constructs
the factor `P(σ)^(1/2) / sqrt 2` used after (3.6), with no factorization
hypothesis.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ComplexOrder InnerProductSpace

namespace DiskRigidity.Operator

variable {i n : Type*} [TopologicalSpace i] [MeasurableSpace i]
  [Fintype n] [DecidableEq n] {mu : Measure i}

/-- A pointwise positive, strongly measurable version of an a.e.-positive
boundary density. -/
structure PositiveMeasurableRepresentative
    (D : PositiveBoundaryDensity (n := n) mu) where
  /-- Pointwise positive representative of the density. -/
  value : i → EuclideanEndomorphism n
  stronglyMeasurable_value : StronglyMeasurable value
  nonneg_value : ∀ t, 0 ≤ value t
  density_ae : D.density =ᵐ[mu] value

/-- Every positive boundary density admits a pointwise positive measurable
representative equal to it almost everywhere. -/
noncomputable def PositiveBoundaryDensity.positiveMeasurableRepresentative
    (D : PositiveBoundaryDensity (n := n) mu) :
    PositiveMeasurableRepresentative D := by
  letI : MeasurableSpace (EuclideanEndomorphism n) := borel _
  letI : BorelSpace (EuclideanEndomorphism n) := ⟨rfl⟩
  have hnonneg : ∀ᵐ t ∂mu, 0 ≤ D.density t := by
    filter_upwards [D.isPositive_ae] with t ht
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr ht
  let hex :=
    D.integrable_density.aestronglyMeasurable.aemeasurable.exists_measurable_nonneg
      hnonneg
  let g := Classical.choose hex
  have hg := Classical.choose_spec hex
  exact ⟨g, hg.1.stronglyMeasurable, hg.2.1, hg.2.2⟩

/-- Half of the pointwise positive representative. -/
noncomputable def PositiveBoundaryDensity.halfPositiveDensity
    (D : PositiveBoundaryDensity (n := n) mu) (t : i) :
    EuclideanEndomorphism n :=
  (2 : ℂ)⁻¹ • D.positiveMeasurableRepresentative.value t

/-- Half of the representative remains positive. -/
theorem PositiveBoundaryDensity.halfPositiveDensity_nonneg
    (D : PositiveBoundaryDensity (n := n) mu) (t : i) :
    0 ≤ D.halfPositiveDensity t := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (D.positiveMeasurableRepresentative.nonneg_value t)).smul_of_nonneg (by
      rw [Complex.nonneg_iff]
      norm_num)

/-- Half of the density, valued in the positive cone. -/
noncomputable def PositiveBoundaryDensity.halfPositiveDensitySubtype
    (D : PositiveBoundaryDensity (n := n) mu) :
    i → {a : EuclideanEndomorphism n // 0 ≤ a} :=
  fun t => ⟨D.halfPositiveDensity t, D.halfPositiveDensity_nonneg t⟩

/-- Strong measurability of the halved representative. -/
theorem PositiveBoundaryDensity.stronglyMeasurable_halfPositiveDensity
    (D : PositiveBoundaryDensity (n := n) mu) :
    StronglyMeasurable D.halfPositiveDensity := by
  exact D.positiveMeasurableRepresentative.stronglyMeasurable_value.const_smul
    (2 : ℂ)⁻¹

/-- Strong measurability persists after restricting the range to the positive
cone. -/
theorem PositiveBoundaryDensity.stronglyMeasurable_halfPositiveDensitySubtype
    (D : PositiveBoundaryDensity (n := n) mu) :
    StronglyMeasurable D.halfPositiveDensitySubtype := by
  apply (Embedding.comp_stronglyMeasurable_iff
    Topology.IsEmbedding.subtypeVal).mp
  exact D.stronglyMeasurable_halfPositiveDensity

omit [DecidableEq n] in
/-- The continuous functional-calculus square root restricted to positive
operators. -/
noncomputable def sqrtPositiveOperator
    (a : {a : EuclideanEndomorphism n // 0 ≤ a}) :
    EuclideanEndomorphism n :=
  CFC.sqrt a.1

omit [DecidableEq n] in
/-- The square root is continuous on the positive cone. -/
theorem continuous_sqrtPositiveOperator :
    Continuous (sqrtPositiveOperator (n := n)) :=
  CFC.continuousOn_sqrt.domRestrict

/-- The canonical measurable factor of half the positive density. -/
noncomputable def PositiveBoundaryDensity.canonicalFactor
    (D : PositiveBoundaryDensity (n := n) mu) (t : i) :
    EuclideanEndomorphism n :=
  sqrtPositiveOperator (D.halfPositiveDensitySubtype t)

/-- The canonical factor is strongly measurable as an operator-valued
function. -/
theorem PositiveBoundaryDensity.stronglyMeasurable_canonicalFactor
    (D : PositiveBoundaryDensity (n := n) mu) :
    StronglyMeasurable D.canonicalFactor :=
  continuous_sqrtPositiveOperator.comp_stronglyMeasurable
    D.stronglyMeasurable_halfPositiveDensitySubtype

/-- The functional-calculus square root satisfies the required Gram identity
almost everywhere. -/
theorem PositiveBoundaryDensity.canonicalFactor_gram_ae
    (D : PositiveBoundaryDensity (n := n) mu) :
    ∀ᵐ t ∂mu, star (D.canonicalFactor t) ∘L D.canonicalFactor t =
      (2 : ℂ)⁻¹ • D.density t := by
  filter_upwards [D.positiveMeasurableRepresentative.density_ae] with t ht
  let a : EuclideanEndomorphism n := D.halfPositiveDensity t
  have ha : 0 ≤ a := D.halfPositiveDensity_nonneg t
  have hsqrtstar : star (CFC.sqrt a) = CFC.sqrt a :=
    (CFC.sqrt_nonneg a).star_eq
  change star (CFC.sqrt a) ∘L CFC.sqrt a = (2 : ℂ)⁻¹ • D.density t
  rw [hsqrtstar]
  change CFC.sqrt a * CFC.sqrt a = (2 : ℂ)⁻¹ • D.density t
  rw [CFC.sqrt_mul_sqrt_self a ha]
  dsimp [a, PositiveBoundaryDensity.halfPositiveDensity]
  rw [ht]

/-- The measurable positive square root needed for the boundary `L²`
isometry is therefore constructed from the density itself. -/
noncomputable def PositiveBoundaryDensity.canonicalSquareRoot
    (D : PositiveBoundaryDensity (n := n) mu) :
    PositiveBoundarySquareRoot D where
  factor := D.canonicalFactor
  aestronglyMeasurable_apply := fun x =>
    (ContinuousLinearMap.apply ℂ (EuclideanVector n) x).continuous.comp_aestronglyMeasurable
      D.stronglyMeasurable_canonicalFactor.aestronglyMeasurable
  gram_ae := D.canonicalFactor_gram_ae

end DiskRigidity.Operator
