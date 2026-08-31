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

| Manuscript label and result | Principal declarations |
| --- | --- |
| `thm:main` — main theorem | `Operator.diskRigidity` |
| `lem:foundation`(1) — numerical-range geometry | `numericalRange_nonempty`, `isCompact_numericalRange`, `numericalRange_convex` |
| `lem:foundation`(2) — empty-interior case | `isStarNormal_of_numericalRange_in_line`, `crouzeixConstant_eq_one_of_numericalRange_in_line`, `crouzeixConstant_eq_one_of_interior_numericalRange_not_nonempty` |
| `lem:foundation`(3) — symmetries | `numericalRange_affine`, `crouzeixConstant_affine`, `numericalRange_unitary_similarity`, `crouzeixConstant_unitary_similarity`, `numericalRange_conjTranspose`, `crouzeixConstant_conjTranspose` |
| `lem:foundation`(4) — finite direct sums | `numericalRange_matrixFiniteFamilyDirectSum`, `crouzeixConstant_matrixFiniteFamilyDirectSum_le` |
| `lem:foundation`(5) — support function | `numericalRangeSupport_exp_eq_largestEigenvalue`, `largestEigenvalue_hasEigenvalue` |
| `lem:dilation` — abstract dilation estimate | `abstract_dilation_estimate` |
| `prop:sharp` — sharp numerical-range estimate | `sharp_polynomial_bound`, `norm_spectralJetEval_le_two_of_convex_diskAlgebra`, `hasRelativeSharpHolomorphicCalculusBound`, `holomorphic_cauchy_of_convex_radial_contraction` |
| `prop:equality-data` — equality vectors and boundary-kernel identity | `exists_sharpEqualityData_and_concreteBoundaryKernel_of_nonconstant` |
| `lem:boundary-eigen` — boundary eigenvalues reduce | `conjTranspose_mulVec_eq_of_unit_eigenvector_mem_frontier`, `boundaryReducingDecomposition`, `boundaryDecompositionMatrix_eq_matrixDirectSum`, `isStarNormal_boundarySpaceMatrix`, `spectrum_boundaryComplementMatrix_subset_interior` |
| `lem:complexfacts` — conformal and finite-interpolation facts | `exists_riemannMap_of_convex`, `exists_homeomorph_closure_closedDisc_extends_riemannMap`, and the `exists_riemannMap_schurFiniteBlaschke_comp_*` interpolation theorems |
| `lem:strict-domain` — strict domain monotonicity | `holomorphicCalculusNorm_strict_anti_of_ssubset_of_larger_gt_one` |
| `lem:induction` — boundary-spectrum induction dichotomy | `numericalRange_eq_closedBall_of_boundaryEigenspaceSpan_ne_bot`, `spectrum_subset_interior_of_boundaryEigenspaceSpan_eq_bot` |
| `lem:extremizer` — holomorphic extremizer | `exists_boundaryContinuous_finiteBlaschke_extremizer_direct` |
| `lem:arc` — curved numerical-range arc | `numericalRange_not_isPolygon_of_spectrum_subset_interior`, `exists_strictlyCurved_exposed_numericalRangeArc`, `exists_strictlyCurved_radial_uniquelyExposed_numericalRangeArc` |
| `prop:rational` — rational collapse | `eqOn_zero_of_diffContOnCl_of_ae_radial_strictlyCurved_affineArc`, `exists_reduced_adjugate_transfer`, `reduced_transfer_agrees_on_convex_interior`, `reduced_transfer_numerator_degree_gt` |
| `lem:zeros` — zeros of the transfer function | `transfer_function_zero_pole_location_of_matrixResolvent`, with the direct matrix-resolvent nonvanishing lemma `inner_matrix_inv_ne_zero_of_not_mem_numericalRange` |
| `prop:full-level` — full-level identity | `full_rationalLevel_and_strictConvex_of_reduced_inner_transfer`, `quotient_deriv_ne_zero_on_frontier_of_coprime_convex_full_sublevel` |
| `prop:circle` — rational lemniscate circle criterion from an open tangent arc | `quotient_deriv_ne_zero_on_frontier_of_coprime_convex_full_sublevel`, `regularAt_primalOrderProjectiveLevelPolynomial_on_set`, `projectiveLevel_zero_iff_mem_frontier_realImage`, `boundary_is_circle_of_full_regular_strictly_convex_level` |
| Application of `prop:circle` to the numerical range, where every support line lies in the Hermitian pencil | `boundary_is_circle_of_full_regular_strictly_convex_level_and_support_determinant`, `boundary_is_circle_of_full_strictly_convex_level_and_support_determinant`, `numericalRange_eq_closedBall_of_full_rationalLevel` |

The final dependency chain is

```text
diskRigidity
  -> diskRigidity_of_finSucc_interiorSpectrum
     -> interiorSpectrum_diskRigidity_of_finSucc
        -> interiorSpectrum_diskRigidity_finSucc
           -> finite Blaschke extremizer and concrete equality data
           -> curved exposed arc and Morera continuation
           -> reduced rational transfer and full-level identity
           -> Hermitian-pencil tangent argument and circle conclusion
     -> diskRigidity_of_interiorSpectrum_case
        -> spectrum_subset_interior_of_boundaryEigenspaceSpan_eq_bot
           -> the reindexed interior-spectrum branch above
        -> numericalRange_eq_closedBall_of_boundaryEigenspaceSpan_ne_bot
           -> the lower-dimensional induction hypothesis
```

Every abstract interface occurring in an intermediate module is instantiated
before reaching `diskRigidity`.

## Clarifications prompted by formalization

Formalization prompted the manuscript to state explicitly the disk algebra,
finite-dimensional holomorphic calculus, nonempty-family condition for finite
direct sums, and exact spectral-jet interpolation data.  It also records the
reduced identity \(UC_A=2D_AV\), restricts rational level sets to nonpoles,
states the noncriticality hypothesis used in the projective argument, and uses
the direct resolvent proof of exterior nonvanishing.  The equality-data path
uses one forward dilation and retains exactly \(Tx=2y\), \(T^*x=0\), and
\(T^*y=2x\), as in `prop:equality-data`.  The manuscript omits the unused
coefficient and representing-measure detours.

## Verification

From this directory, the complete checks are:

```text
lake build --wfail
lake lint
```

The TeX source is checked separately with `latexmk` in `../preprint`.
