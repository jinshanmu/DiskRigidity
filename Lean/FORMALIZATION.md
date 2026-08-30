# Lean formalization of disk rigidity

This directory contains the formal proof accompanying
`../preprint/disk_rigidity.tex`.  The project is pinned to Lean `4.33.1` and
mathlib `v4.33.1`.

## Closed main theorem

The final result is
`DiskRigidity.Operator.diskRigidity` in
`DiskRigidity/Operator/MainTheorem.lean`:

```lean
theorem diskRigidity
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : SquareMatrix n) (hpsi : crouzeixConstant A = 2) :
    ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ numericalRange A = Metric.closedBall c r
```

It has no project-specific axioms or unproved hypotheses.  Lean reports only
`propext`, `Classical.choice`, and `Quot.sound` in its axiom footprint.

## Manuscript correspondence

| Manuscript result | Principal Lean declarations |
| --- | --- |
| Theorem 1.1 | `Operator.diskRigidity` |
| Lemma 2.1(1) | `numericalRange_nonempty`, `isCompact_numericalRange`, `numericalRange_convex` |
| Lemma 2.1(2) | `isStarNormal_of_numericalRange_in_line`, `crouzeixConstant_eq_one_of_numericalRange_in_line`, `crouzeixConstant_eq_one_of_interior_numericalRange_not_nonempty` |
| Lemma 2.1(3) | `numericalRange_affine`, `crouzeixConstant_affine`, `numericalRange_unitary_similarity`, `crouzeixConstant_unitary_similarity`, `numericalRange_conjTranspose`, `crouzeixConstant_conjTranspose` |
| Lemma 2.1(4) | `numericalRange_matrixFiniteFamilyDirectSum`, `crouzeixConstant_matrixFiniteFamilyDirectSum_le` |
| Lemma 2.1(5) | `numericalRangeSupport_exp_eq_largestEigenvalue`, `largestEigenvalue_hasEigenvalue` |
| Lemma 3.1 | `abstract_dilation_estimate` |
| Proposition 3.2 | `sharp_polynomial_bound`, `norm_spectralJetEval_le_two_of_convex_diskAlgebra`, `hasRelativeSharpHolomorphicCalculusBound`, `holomorphic_cauchy_of_convex_radial_contraction` |
| Proposition 3.3 | `exists_sharpEqualityData_and_concreteBoundaryKernel_of_nonconstant`, `spectralJet_coefficient_identities_of_sharpEqualityData` |
| Lemma 3.4 | `conjTranspose_mulVec_eq_of_unit_eigenvector_mem_frontier`, `boundaryReducingDecomposition`, `boundaryDecompositionMatrix_eq_matrixDirectSum`, `isStarNormal_boundarySpaceMatrix`, `spectrum_boundaryComplementMatrix_subset_interior` |
| Lemma 3.5 | `exists_riemannMap_of_convex`, `exists_homeomorph_closure_closedDisc_extends_riemannMap`, and the `exists_riemannMap_schurFiniteBlaschke_comp_*` interpolation theorems |
| Lemma 3.6 | `holomorphicCalculusNorm_strict_anti_of_ssubset_of_larger_gt_one` |
| Lemma 4.2 | `numericalRange_eq_closedBall_of_boundaryEigenspaceSpan_ne_bot` |
| Lemma 4.3 | `exists_boundaryContinuous_finiteBlaschke_extremizer_direct` |
| Lemma 5.1 | `numericalRange_not_isPolygon_of_spectrum_subset_interior`, `exists_strictlyCurved_exposed_numericalRangeArc`, `exists_strictlyCurved_radial_uniquelyExposed_numericalRangeArc` |
| Proposition 5.2 | `eqOn_zero_of_diffContOnCl_of_ae_radial_strictlyCurved_affineArc`, `exists_reduced_adjugate_transfer`, `reduced_transfer_agrees_on_convex_interior`, `reduced_transfer_numerator_degree_gt` |
| Lemma 6.1 | `exists_probabilityMeasure_numericalRange_of_extremal_spectralJet` |
| Lemma 6.2 | `transfer_function_zero_pole_location_of_matrixResolvent`, with the direct matrix-resolvent nonvanishing lemma `inner_matrix_inv_ne_zero_of_not_mem_numericalRange` |
| Proposition 6.3 | `full_rationalLevel_and_strictConvex_of_reduced_inner_transfer`, `quotient_deriv_ne_zero_on_frontier_of_coprime_convex_full_sublevel` |
| Proposition 7.1 | `boundary_is_circle_of_full_strictly_convex_level_and_support_determinant_of_deriv_ne_zero`, specialized by `numericalRange_eq_closedBall_of_full_rationalLevel` |

The final dependency chain is

```text
diskRigidity
  -> diskRigidity_of_finSucc_interiorSpectrum
     -> diskRigidity_of_interiorSpectrum_case
     -> interiorSpectrum_diskRigidity_finSucc
        -> finite-Blaschke extremizer and concrete equality data
        -> curved exposed arc and Morera continuation
        -> reduced rational transfer and full-level identity
        -> Hermitian-pencil tangent argument and circle conclusion
```

Every abstract interface occurring in an intermediate module is instantiated
before reaching `diskRigidity`.

## Manuscript corrections exposed by formalization

Only local corrections were made to the TeX source: the disk algebra and
finite-dimensional holomorphic calculus were defined explicitly; the direct
sum was stated for a nonempty finite family; a malformed `n` was corrected;
the interpolation norm wording was made precise; the exterior nonvanishing
step was replaced by its shorter direct resolvent proof; the noncritical-level
argument was made noncircular; and the Hermitian matrices `H_A` and `J_A` were
written explicitly.  Lemma 6.1 remains fully formalized even though the final
route uses the shorter resolvent proof.

## Verification

From this directory, the complete checks are:

```text
lake build --wfail
lake lint
```

The TeX source is checked separately with `latexmk` in `../preprint`.
