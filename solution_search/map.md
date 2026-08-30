# DiskRigidity investigation map

This canonical file maps active mathematical routes, their concrete outputs, dependencies, failure modes, and status.

## Active routes

- **Polynomial preimages / lemniscates.** Exact identity (q(A)=(b(a-e)+cd)e_{12}) for the (3\times3) commutant form has been derived. Status: `blocked as a counterexample in sizes 3--7` by extremal-innerness plus the Cassini dual-degree/Kippenhahn obstruction. Higher-dimensional determinantal representations of convex Cassini ovals remain a logically possible but presently unsupported route; one must additionally prove (\|p(A)\|=2\), not merely (W(A)) equals the lemniscate.
- **Defective (3\times3) conformal candidates.** The Åhag–Czyż–Perälä–Virtanen family (A_t), (0<t<1/2\), has a boundary segment and (\psi(A_t)\to2), but its exact boundary-kernel quotient (R_t) satisfies (R_t(A_t)=yx^*) of norm one, whereas equality would require (2yx^*). Thus every interior parameter is strictly below two.
- **Direct sums, tensor sums, and reducible matrices.** Tensor sums with a normal factor become direct sums of translated disk blocks. Conformal-radius monotonicity gives a uniform strict gap whenever the convex hull is genuinely larger than each extremal disk. Status: strong negative result; no counterexample.

### Conformal normalization / dilation (`conformal_operator`)

- **Concrete outputs:** exact (2\times2) strictness; strict conformal-radius lemma; reduction of boundary eigenvalues; rigorous holomorphic extremizer compactification (so polynomial nonattainment is harmless); monomial rigidity; exclusion of finite direct sums of sharp Jordan-disk blocks plus normal blocks.
- **Dependencies for a full proof:** after writing an extremizer as (B\circ\phi), one still needs a new mechanism showing equality (2) forces either a monomial/Crabb chain or that \(\phi\) is affine.  Existing mapping, dilation, configuration-constant, and extremal-vector results do not provide this.
- **Status:** `blocked` at a theorem-strength equality/stability lemma.  Reopen only with (i) a quantitative equality analysis surviving simple-spectrum/outer-domain limits, (ii) a proof that every norm-(2) extremizer is monomial up to affine normalization, or (iii) an explicit counterexample invalidating that claim.

#### Quantitative coalescence and minimal-counterexample reduction (`conformal_operator`)

- The positive-real Gramian has an exact defect identity (4-\|T\|^2=4(2-\langle Pe,e\rangle)+\langle(P-I)Te,Te\rangle).  It quantitatively forces an approximate orthogonal square-zero chain, with (\|T^2e\|\le2\sqrt{4-\|T\|^2}), and forces eigenvalues to coalesce at zero.  Applying the limiting argument also to the adjoint yields a reducing (2J_2) block of the extremal image (f(A)).
- This block need not reduce the conformal coordinate (\phi(A)); the explicit (3\times3) weighted shift (\begin{psmallmatrix}0&2&0\\0&0&a\\0&0&0\end{psmallmatrix}) is an exact warning.  If the saturated plane is invariant for (\phi(A)), however, Schwarz--Pick plus conformal-radius monotonicity forces the numerical range to be a disk for every finite Blaschke degree.
- In a least-dimensional nondisk equality case, the generalized zero space of (f(A)) either gives a smaller equality block with the same numerical range (hence a disk by induction) or is the whole space.  Thus a least counterexample must have (f(A)) globally nilpotent, dimension at least (4), and (\dim\ker f(A)^2\ge3).
- The sharper cyclic-subspace reduction makes the maximizing vector (x) cyclic for (A) and the corresponding left singular vector (y) cyclic for (A^*).  Since (f(A)y=0), cyclicity forces the global identity (f(A)^2=0), and hence (W(f(A))=\overline{\mathbb D}).  Also (\operatorname{ran}f(A)=\operatorname{span}\{A^ky\}) and its adjoint analogue.  CCC blocks show these conditions still do not make the endpoint plane (A)-invariant.
- The boundary-kernel identity plus cyclicity rules out every flat boundary edge: analytic continuation along an edge with fixed support defect (H) forces (Hh(A)x=0) for every (h), hence (H=0), contradicting two-dimensional numerical range.  Therefore a least counterexample is strictly convex.  Applied explicitly to the formerly unresolved defective family (A_t), it forces a rational candidate (R_t) with (R_t(A_t)) of norm (1), contradicting the required norm (2); thus every interior (A_t) is strict.
- On the resulting strictly convex boundary, the quadratic support relation collapses because (f(A)^2=0): resolvent commutation gives (x^*Ry=0) and (y^*Ry=x^*Rx), hence the extremizer is exactly the rational transfer quotient (f(z)=2x^*\operatorname{adj}(zI-A)x/[y^*\operatorname{adj}(zI-A)x]).  Extremal variation makes (x^*h(A)x) a probability state, whose exterior Cauchy transform has no zeros.  This forces the global rational sublevel set to equal the numerical-range interior and eliminates all other real lemniscate components.  The dual curve divides the hyperbolic Kippenhahn determinant; a generic direction supplies only the two tangents of the single strictly convex oval, so the curve is a conic through the circular points, hence a positive-radius circle.
- The analytic prerequisites of this reduction are now independently closed.  Extremal one-sided variations make (L(h)=x^*h(A)x) a positive unital state, represented by a probability measure on (\partial K).  Its diagonal resolvent is a Cauchy transform with strictly positive rotated real part off the convex body, so it has no exterior zeros.  Cyclicity of (x) and adjoint-cyclicity of (y) make the off-diagonal transfer realization minimal (no characteristic-denominator cancellation).  After reducing the rational extremizer as (P/Q), one has (\deg P>\deg Q), every zero of (P) lies in (K^\circ), and every zero of (Q) lies outside (K).  Properness shows every component of (\{|P|<|Q|\}) contains a zero; hence that sublevel set is exactly (K^\circ), and open mapping shows the **full** level (\{|P|=|Q|\}) equals (\partial K), with no unused ovals or hidden critical components.
- Extremal variation proves (L(h)=x^*h(A)x) is a positive state.  Together with the norming off-diagonal functional, all quotient data are classified by a normalized outer vector (q\in K_B): (L(h)=\int h|q|^2dm) and (\delta(h)=2\int h\bar B|q|^2dm).  Non-evaluation states already occur for (B=z^2), so positivity/factorization alone does not force degree one.
- The model-space similarity on (K_{B^2}=K_B\oplus BK_B) realizes every such quotient state with exact abstract calculus norm (2).  A concrete Möbius transform of the (3\times3) CCC block has disk-domain constant (2) and a provably nondisk numerical range; it fails the original normalization because (|B|>1) on its actual numerical range.  This isolates numerical-range self-consistency as the indispensable missing input.

### G1. Global geometric rigidity from extremal holomorphic functions — proved and independently audited

- Polynomial extremizing sequences can be normalized on (K=W(A)). After splitting boundary eigenvalues, the nonnormal block has spectrum in int(K); Montel then yields an (H^\infty(\operatorname{int}K)) extremal limit, with convergence of all spectral jets needed for (f(A)).
- Literature gives that an extremal function is (B\circ\phi), a finite Blaschke product composed with a Riemann map, and extremal vectors satisfy ⟨f(A)x,x⟩=0.
- The decisive mechanism is the state/no-hidden-level lemma recorded in `registry.md`: after rational collapse, the representing probability measure excludes exterior zeros, which makes the entire rational unit level equal to the single numerical-range boundary; hyperbolic duality then forces class two and circularity.
- Status: established.  The proof is integrated into DiskRigidity/LaTeX/disk_rigidity.tex; three independent final audits rederived the sharp-bound equality, the meromorphic rational collapse, and the hyperbolic-dual contact count.

#### G1a. Equality extraction and degree-one closure — established

- Equality in the sharp dilation lemma, together with spectral radius (<1), forces (u=0), (T^*x=0), and the boundary-kernel identity (P^{1/2}(y-fx)=0). Applying the adjoint argument also gives (Ty=0).
- All analytic compressions to \(\operatorname{span}\{x,y\}\) are triangular with equal diagonal, encoded by (L(hf)=0) and δ(hf)=2L(h).
- If the extremal finite Blaschke product has degree one, these identities produce an actual Euclidean disk inside (W(A)) whose radius equals the conformal radius. Schwarz equality forces (W(A)) to equal that disk. This is a complete, self-contained rigidity proof for degree one.
- For higher degree, the quotient algebra (A(K)/fA(K)) has dimension (>1), so (L) need not be point evaluation and the 2D compression need not reveal the conformal radius. This is the sharpened remaining obstruction.
- This obstruction is exact, not merely hypothetical: positive quotient states are precisely outer-vector states in (K_B), and explicit non-point states exist for every degree at least two.  Any closure must exploit further support geometry or a larger Crabb-type chain.

#### G1b. Boundary algebraicity — active

- Under strict convexity, the boundary-kernel identity gives a quadratic polynomial relation over \(\mathbb C(z)\) for the extremal inner function. A nondisk counterexample must therefore come from an unusually algebraic conformal/Blaschke configuration (a convex quadrature-domain-type candidate), not a generic numerical range.
- Need either classify numerical ranges compatible with this quadratic relation, or explicitly realize one and audit the all-polynomial ratio.

The adjoint endpoint identity strengthens this: (x^*h(A)y=0) for all (h), so one adjugate coefficient vanishes identically and the quadratic relation collapses to an exact rational formula for (f).  The live candidates are therefore rational-lemniscate numerical ranges.  Convex noncircular lemniscates show that rationality is a reduction, not yet rigidity.

Kato's global rational mapping theorem cannot manufacture a counterexample from a nonlinear univalent map of the disk: its hypothesis concerns the convex kernel of the full inverse image, and the unused inverse branches generally make that kernel empty.

The rational collapse now covers arbitrary numerical ranges: a support-function branch argument supplies an open analytic strictly convex arc unless the range is a polygon, while polygonal ranges are strictly below two after corner reduction and strict domain monotonicity.  No global smoothness hypothesis remains.

A stronger full-level argument closes this route and supersedes the tentative Pluecker count.  Positivity confines every zero of the reduced rational extremizer to (K), while rationality, boundary innerness, and the pole at infinity put every pole outside (K).  Every component of (\{|f|<1\}) contains a zero, so the entire sublevel set is (K^\circ) and the entire unit lemniscate is (\partial K).  Hence the relevant irreducible complex curve has exactly one real oval.  Its dual divides the Hermitian Kippenhahn determinant and is hyperbolic.  In a generic real normal direction all dual intersections are smooth real points; bidual uniqueness makes all their contacts real.  The sole strictly convex oval has exactly two such contacts, so the dual has degree two.  Biduality makes the primal a conic, and its leading form divides ((x^2+y^2)^n), forcing a circle.  Status: `established`; the earlier Gauss-map/Pluecker formula is not needed and was unsafe for repeated pole fibers.

The final independent audit rederived both quantitative bottlenecks.  In the
sharp-dilation argument, equality at \(\kappa=2\) annihilates every individual
nonnegative recurrence slack once \(r(T)<1\), yielding the claimed kernel
identity.  In the geometric argument, a generic normal is chosen away from
the discriminant, the singular dual locus, and Gauss-critical images; its
hyperbolic roots are smooth real dual points whose gradient contacts are
unique and real.  The audit also corrected the local rational identity to a
meromorphic identity on the connected punctured domain
\(\Omega\setminus\operatorname{spec}(A)\).

The lean final dependency chain also bypasses the global square-zero/cyclic and flat-edge
lemmas.  Once boundary eigenvalues are removed inductively, a polygon is impossible because
each vertex would itself be a reducing boundary eigenvalue.  A nonpolygonal numerical range
has one analytic strictly exposed curved arc, which is enough for the rational-collapse identity;
the endpoint relations from the equality lemma alone give (b=0,d=a).  The full-level algebraic
factor then rules out line segments and supplies the global smooth strict convexity used in the
dual contact count.

### G2. Reducible/direct-sum counterexample search — closed for the induction

- Exact strict-gap lemma excludes (J_r\oplus\lambda) with ∣λ∣>r and, more generally, finite sums of extremal (2\times2) Jordan disk blocks plus scalars when the convex hull is nondisk.
- Boundary eigenvalues are reducing and peel off as a finite diagonal summand.  An asymptotically extremizing polynomial sequence forces the remaining lower-dimensional block to retain relative and intrinsic constant (2), so induction makes its numerical range a disk.  One must then peel this block's eigenvalues on that disk's boundary as a **second** stage.  The remaining block still has relative constant (2), has spectrum in the disk interior, and has the same disk numerical range because finitely many scalar points cannot supply any missing extreme points of a circle.  Crouzeix's strict domain monotonicity now forces the original numerical range to equal that disk.  This closes the arbitrary boundary-spectrum case without assuming polynomial attainment; the one-stage version was missing the hypothesis (\sigma(C)\subset W(C)^\circ).
- Status: established.  Any least-dimensional nondisk equality case necessarily has all of its spectrum in the interior of its numerical range.

### G3. Low-dimensional/structured audit — established evidence

- (N=1) and all degenerate numerical ranges have ψ=1.
- (N=2): exact ellipse formula gives strict (<2) for noncircular ellipses; disk is the only equality geometry.
- (3\times3) nilpotent matrices: Crouzeix proved equality rigidity.
- Cyclic weighted shifts: nonzero cyclic product implies strict (<2); zero product gives disk numerical range.
- None of these yields a nondisk counterexample.

## Established foundations

- Direct-sum numerical range and ratio inequalities recorded in `registry.md`.
- Monomial equality is completely characterized by a CCC reducing block and forces a disk numerical range.
- Every diagonalizable finite matrix has (\psi(A)<2) (2026 square-function theorem); hence a counterexample must be defective.
- In the (3\times3) polynomial-preimage form, boundary eigenvalues reduce the matrix; the irreducible case has interior spectrum and is subject to the finite Blaschke extremal theorem.
- An attained polynomial extremal forces a lemniscate boundary.  For a quadratic, the obstruction is now dimension-free: the Cassini dual has explicit nonreal vertical-tangent roots, whereas every factor of a Kippenhahn determinant is hyperbolic.  Thus quadratic polynomial preimages cannot be counterexamples in any finite size.  For general higher-degree lemniscates, a corresponding nonhyperbolicity classification is not yet proved.

- Singleton and line-segment numerical ranges give \(\psi=1\); hence any equality-(2) case is a genuine two-dimensional convex body.
- Translation, nonzero complex scaling, unitary similarity, and adjoint preserve \(\psi\); arbitrary real-affine transformations do not.
- Boundary eigenvalues split off as diagonal reducing summands; the remaining spectrum lies in the numerical-range interior.
- Polynomial extremizing sequences admit a bounded-holomorphic extremal limit after the above reduction; no polynomial-attainment assumption is needed.
- Exact equality for (p(z)=z^k) forces a disk numerical range.

- Compactness, Toeplitz–Hausdorff convexity, singleton/line degeneracies, affine/unitary/adjoint invariances, direct-sum convex-hull formula, support-function formula, and boundary-eigenvalue reduction are recorded with proof sketches in `registry.md`.
- Exact half-radial rigidity: ‖B‖=2w(B) iff (W(B)) is a nondegenerate centered disk (for (B\ne0)). This settles equality produced by an affine polynomial but does not automatically apply to (B=p(A)).
- Direct-sum inequality: ψ(A⊕B)≤max(ψ(A),ψ(B)); equality can fail strictly because the denominator is on the convex hull.

## Candidate resolutions

- No exact nondisk counterexample survived.  The former defective (A_t) candidate is now excluded by its exact boundary-kernel rational quotient, and the general least-counterexample rational self-consistency step forces a circle.

- **Completed induction for boundary spectrum:** two-stage peeling (first relative to the original range, then relative to the lower-dimensional disk supplied by induction) verifies all hypotheses of strict relative-domain monotonicity and forces the original range to be that disk.  The interior-spectrum case is handled separately by the equality/rational-lemniscate argument.
- **2026 positive-real completion route:** its simple-spectrum stage is strictly (<2); a candidate rigidity proof would need quantitative control showing that saturation of the approximation forces circular support geometry.  No such estimate is currently in the manuscript or derived here.

- No counterexample survived the geometric/direct-sum audit.  The completed proof architecture is: (i) prove the universal bound self-contained; (ii) remove boundary eigenvalues by the two-stage induction and extract a finite-Blaschke holomorphic extremizer for the interior-spectrum block; (iii) extract the double-layer endpoint and boundary-kernel equalities; (iv) use one curved exposed arc to make the extremizer rational; and (v) combine its positive state with Kippenhahn hyperbolicity and biduality to force a circle.  The former half-radial/support-function missing step is superseded.

## Adversarial audits

- The implication “one polynomial gives ratio (2)” was never treated as enough by itself: every proposed witness was paired with a full upper bound (universal scalar theorem or a special-class bound), and polynomial-preimage attempts were checked against the exact supremum on the full numerical range.
- Cassini obstruction hypotheses to retain: (p) must actually be extremal; spectrum must be interior or boundary blocks must first be split off; the relevant lemniscate component must be noncritical/irreducible; repeated-root/proper-power polynomials are separate and include the disk monomial case.

- Do not use (w(\phi(A))\le1\) for a Riemann map; that is essentially the missing mapping theorem.
- Do not infer half-radiality of (f(A)) from \(\|f(A)\|=2\); first prove (w(f(A))=1\).
- Do not replace the polynomial supremum by a polynomial maximum; use the normal-family/Mergelyan passage.
- Track strictness through outer-domain and simple-spectrum limits: pointwise strict inequalities can converge to (2).

- A direct sum containing a ψ=2 block need not itself have ψ=2. The explicit (J_r\oplus\lambda) strictness proof should be used to test every proposed reducible counterexample.
- A (2\times2) compression controls only the degree-one numerical range; polynomial functional calculi do not commute with compression.
- Exact universal-bound proofs currently available do not, merely by tracing equalities, prove rigidity at 2.
