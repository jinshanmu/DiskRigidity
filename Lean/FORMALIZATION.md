# Lean formalization of disk rigidity

This directory contains the theorem-matched formal proof accompanying
`../preprint/disk_rigidity.tex`.  The project is pinned to Lean `4.33.1` and
mathlib `v4.33.1`.

The immutable Lean proof-source snapshot audited for the current manuscript is
Git commit `5af901c72a5148f782cc91551f76127ec93a98c5` in this repository.
If any `.lean` file or toolchain file changes before release, this hash must be
updated to the final release commit or tag in both this file and the manuscript's
data-availability statement.

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

This is the necessary-condition theorem only.  The development does not claim
or formalize its converse, a classification of all equality matrices, a
quantitative stability theorem, an infinite-dimensional version, or a
completely bounded analogue.

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
| `lem:boundary-uniqueness` — analytic straightening, Morera gluing, and identity theorem | `differentiableOn_ball_of_continuousOn_of_differentiableAt_off_real`, `eqOn_zero_of_diffContOnCl_of_regularAnalytic_frontier_arc`, `eqOn_zero_of_diffContOnCl_of_ae_radial_strictlyCurved_affineArc` |
| `prop:rational` — rational collapse | `eqOn_zero_of_diffContOnCl_of_ae_radial_strictlyCurved_affineArc`, `exists_reduced_adjugate_transfer`, `reduced_transfer_agrees_on_convex_interior`, `reduced_transfer_numerator_degree_gt` |
| `lem:zeros` — zeros of the transfer function | `transfer_function_zero_pole_location_of_matrixResolvent`, with the direct matrix-resolvent nonvanishing lemma `inner_matrix_inv_ne_zero_of_not_mem_numericalRange` |
| `prop:full-level` — full-level identity | `full_rationalLevel_and_strictConvex_of_reduced_inner_transfer`, `quotient_deriv_ne_zero_on_frontier_of_coprime_convex_full_sublevel` |
| `prop:generic-contact` — generic real contact recovery and two-support degree count | `dual_degree_eq_two`, using `PlaneGauss.lean`, `GenericSpecialization.lean`, `GenericAvoidance.lean`, and `ProjectiveDual.lean` |
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

## Reviewer-sensitive checkpoints

The following points are not merely assumed at the main theorem.

| Issue | What Lean checks |
| --- | --- |
| Measurable boundary square root and a.e. identities | `PositiveBoundaryDensity.positiveMeasurableRepresentative`, `stronglyMeasurable_canonicalFactor`, and `canonicalFactor_gram_ae` construct a strongly measurable positive square root of half the density. `boundaryIsometry_coe_ae` and the equality-data theorems formulate boundary identities almost everywhere for the arclength measure. |
| Finite confluent interpolation | Repetition in `List ℂ` records contiguous jets through `jetMultiplicity` and `JetEq`. `exists_schurFiniteBlaschke_jetEq` constructs a finite Blaschke interpolant by finite Schur reduction; `eqOn_of_hasMinimalNormOneJets` proves extremal uniqueness by the same recursion. The matrix value is linked to the characteristic spectral jet in `SpectralJets.lean`. |
| Boundary uniqueness used in rational collapse | `differentiableOn_ball_of_continuousOn_of_differentiableAt_off_real` proves the Morera gluing step. `eqOn_zero_of_diffContOnCl_of_regularAnalytic_frontier_arc` complexifies and locally inverts the analytic arc, glues across it, and applies the identity theorem. Its arclength-a.e. endpoint is `eqOn_zero_of_diffContOnCl_of_ae_radial_strictlyCurved_affineArc`. |
| One real irreducible component and its real locus | `exists_irreducible_factor_zero_on_connected_regular` selects the component on a connected regular level; `exists_real_irreducible_component` makes it real; `exists_primal_oval_component` proves the exact real affine locus, absence of real points at infinity, and projective regularity. |
| Hermitian divisibility and hyperbolicity | `exists_dual_factor_on_open_analytic_graph` constructs the real absolutely irreducible factor carried by the tangent arc and its divisibility into the Hermitian determinant. `splits_specialize_affineFamily_of_dvd` supplies real-rooted specializations, while `coeff_affineFamily_degree` and `natDegree_specialize_affineFamily` prove that specialization does not lower the degree. |
| Generic contact count | Rather than importing normalization/reflexivity as a black box, the formalization uses the explicit Gauss differential and cross-minor in `PlaneGauss.lean`, finite discriminant/resultant exceptional sets in `GenericSpecialization.lean` and `GenericAvoidance.lean`, contact recovery in `ProjectiveDual.lean`, and the two-support-root count in `dual_degree_eq_two`. |
| Circular conic conclusion | `projective_circle_conclusion_of_lemniscate` obtains the circular point directly from the homogeneous lemniscate equation, constructs the primal conic envelope, and proves the boundary circle equation. |

The projective modules use the coordinate order `[Z:X:Y]` for primal points
and `[s:u:v]` for lines, so incidence is `sZ + uX + vY = 0` throughout.

## Formalization boundary

The formalization is theorem-matched, not a line-by-line encoding of the
English proof.  Two differences are especially relevant to citation and
exposition:

- The Lean interpolation proof does not define a generalized Pick matrix and
  does not use singularity of that matrix or a separate linear-independence
  theorem for evaluation/derivative functionals.  It proves the existence and
  uniqueness statements directly by Schur recursion.  The manuscript instead
  defines its generalized Pick matrix explicitly, records the Hermite-cardinal
  proof of independence, and reduces minimal singular uniqueness to Sarason's
  finite-dimensional maximal-vector theorem.
- The Lean algebraic endgame replaces the manuscript's normalization,
  reflexivity, generic-contact, and Bezout narrative by explicit homogeneous
  factor selection, Gauss-pullback divisibility, discriminant/resultant
  avoidance, and a conic-envelope calculation.  Thus the closed Lean theorem
  is independent evidence for the endpoint, but it is not a formalization of
  each cited algebraic-geometric sentence verbatim.

Bibliographic assertions, priority/novelty claims, the Jordan-block
nonconverse example, and the AI-use and data-availability prose are not
mathematical statements checked by Lean.  The sanitized development transcript
is a historical record only; it is not part of the proof or an independent
correctness certificate.

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

### Toolchain and dependencies

- Lean: `leanprover/lean4:v4.33.1`, selected by `lean-toolchain`.
- Direct library dependency: mathlib `v4.33.1`, resolved to commit
  `0df444a360eaa60ab8c11dca51a86af692955474`.
- All transitive Lake dependencies and their exact commits are recorded in
  `lake-manifest.json`; no unpinned project-specific package is used.
- The build requires Git and an `elan` installation capable of installing the
  pinned Lean toolchain.  A first build requires network access to fetch the
  packages in the manifest.

From a fresh checkout, the complete checks are:

```sh
git clone https://github.com/jinshanmu/DiskRigidity.git
cd DiskRigidity
git checkout 5af901c72a5148f782cc91551f76127ec93a98c5
cd Lean
lake build --wfail
lake lint
```

On the audited snapshot both commands pass.  To inspect the closed theorem's
logical footprint, load `DiskRigidity` and run
`#print axioms DiskRigidity.Operator.diskRigidity`; the output is
`[propext, Classical.choice, Quot.sound]`.

The TeX source and its bibliography are outside Lean's trusted proof artifact;
they are checked separately with `latexmk` in `../preprint`.
