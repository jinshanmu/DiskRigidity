# DiskRigidity source and result registry

This canonical file records sources, exact statements, URLs, and the mathematical lesson extracted from each source. Preserve prior entries and amend in place.

## Sources

- **Crouzeix (2004), “Bounds for Analytical Functions of Matrices,” IEOT 48, 461–477.** DOI: https://doi.org/10.1007/s00020-002-1188-6 . Theorem 1.1 proves the constant-2 estimate for every (2\times2) matrix; Theorem 2.5 gives the exact (2\times2) ratio as a function of the eccentricity of its elliptical numerical range, and the discussion/equation (2.7) makes the value strictly below (2) for every noncircular ellipse. Theorem 4.1 proves the related domain statement (C_\Omega(2)=2\Rightarrow\Omega) is a disk, including nonattainment.
- **Hnětynková–Tichý (2018), “Characterization of half-radial matrices.”** https://arxiv.org/abs/1804.10407 . Theorem 14: if 
  \(\|A^k\|=2\max_{W(A)}|z|^k\), then, after scaling and unitary similarity, (A=C_k\oplus B), where (C_k) is the Crabb–Choi–Crouzeix block and (W(B)\subset\overline{\mathbb D}); hence (W(A)) is a disk. This rules out every monomial-based nondisk witness, in every finite size.
- **Malman–Mashreghi–O’Loughlin–Ransford (2024), “On the Crouzeix ratio for (N\times N) matrices.”** https://arxiv.org/abs/2409.14127 . Proposition 2.3 studies the explicit “ice-cream cone” matrix (A_\alpha=[1]\oplus\begin{psmallmatrix}0&\alpha\\0&0\end{psmallmatrix}), with (W(A_\alpha)=\operatorname{conv}(\overline D(0,\alpha/2)\cup\{1\})), and obtains (\psi(A_\alpha)\ge\pi/2) for (\alpha>0). It is a useful nondisk stress test, not an equality-2 example.
- **Greenbaum–Overton (2018), “Numerical investigation of Crouzeix’s conjecture.”** https://cs.nyu.edu/~overton/papers/pdffiles/NumerInvestCrouzeixConj.pdf . Their Section 8 proves exact monomial examples only for CCC blocks and records the conjecture that polynomial attainment of the factor (2) requires a monomial; nonmonomial searches approach (2) only through divergent matrices or shrinking disks. This is evidence, not by itself a rigidity theorem.
- **Åhag–Czyż–Perälä–Virtanen (2026), “Square Functions and the Complete Crouzeix Conjecture in Dimension Three.”** https://arxiv.org/abs/2608.27346 . Theorems 1.1–1.4 prove the complete constant-2 bound through size three and strict scalar inequality for every diagonalizable matrix (all sizes). Theorem 10.2 proves disk rigidity when an attained extremal (f) algebra-generates (A). Theorem 10.7 reduces any unitarily irreducible nondisk (3\times3) equality case to defective Jordan forms (J_2(\lambda)\oplus[\nu]) or (J_3(\lambda)). Corollary 11.10 gives the remaining explicit one-parameter nondisk candidate family (A_t); the paper expressly leaves open whether any interior parameter attains (2), while proving (\psi(A_t)\to2) as (t\to1/2^-). This is the sharp current structured obstruction/candidate family.
- **Lorist–Schwenninger (2026), “A solution to Crouzeix’s conjecture.”** https://arxiv.org/abs/2608.03841 . Provides the now-available universal scalar upper bound (2). For the present problem it supplies the matching upper bound once a lower-bound construction is found, but equality rigidity is not classified there and the final solution must reproduce any required form rather than cite it as a black box.
- **Nevanlinna (2012), “Lemniscates and (K)-spectral sets.”** https://doi.org/10.1016/j.jfa.2011.11.019 . Multicentric functional calculus makes polynomial lemniscates (K)-spectral under smooth-boundary hypotheses, but gives geometry-dependent (K), not an exact factor-2 witness.
- **Beckermann–Crouzeix (2013), “Faber polynomials of matrices for non-convex sets.”** https://arxiv.org/abs/1310.1356 . Extends the bound (\|F_n(A)\|\le2) for Faber polynomials when the numerical range lies in a prescribed convex compact set. No finite nondisk equality construction was found in this source; sharpness can be asymptotic.

### Conformal maps, spectral sets, and equality (route: `conformal_operator`)

- Michel Crouzeix, **“Bounds for Analytical Functions of Matrices,”** *Integral Equations and Operator Theory* 48 (2004), 461–477, DOI: https://doi.org/10.1007/s00020-002-1188-6 (searchable full-text mirror: https://www.scribd.com/document/987904687/crouzeix2004).  Exact items checked: Lemma 2.2 (relative functional-calculus constant is monotone in the domain, strictly so away from the value (1)); Corollary 2.4 (exact relative constant for an upper-triangular (2\times2) matrix in a simply connected domain); Theorem 2.5/formula (2.7) (for a nonnormal (2\times2) matrix, 
  \[
  \psi(A)=2\exp\!\left(-\sum_{n\ge1}\frac{(-1)^{n+1}}n\frac{2}{1+\rho^{4n}}\right),
  \]
  with the usual ellipse parameter \(\rho>1\); hence it is exactly (2) only in the circular limit); Theorem 4.1 ((C_\Omega(2)\le2), and equality of the *domain constant* forces \(\Omega\) to be a disk).  Quantifier warning: Theorem 4.1 concerns a supremum over all (2\times2) matrices subordinate to a fixed domain, not a fixed (N\times N) matrix.
- Cătălin Badea, Michel Crouzeix, Bernard Delyon, **“Convex domains and (K)-spectral sets,”** *Math. Z.* 252 (2006), 345–365; preprint https://arxiv.org/abs/math/0501184 and author PDF https://perso.univ-rennes1.fr/michel.crouzeix/publis/bacrde.pdf.  Section 5 verifies the disk estimate from Berger/Okubo–Ando and gives, for a noncircular (2\times2) ellipse, an explicit conformal map and similarity with condition number (X<2).  Thus every nondisk (2\times2) numerical range has \(\psi(A)<2\), while disk numerical ranges have the all-polynomial upper bound (2).
- Michel Crouzeix, **“Some constants related to numerical ranges,”** *SIAM J. Matrix Anal. Appl.* 37 (2016), 420–442, author PDF https://perso.univ-rennes1.fr/michel.crouzeix/publis/M102041.pdf.  Section 2 states/proves the extremal-function reduction: after boundary spectral summands are removed, a Riemann map (a:W(A)^\circ\to\mathbb D) gives \(\psi(A)=\psi_{\mathbb D}(a(A))\), and the latter is attained in the holomorphic class by a finite Blaschke product of degree at most (N-1) (at most (N-k-1) after (k) boundary eigenvalues).  Section 9 records the rigorous reducible (3\times3) subcase: if the numerical range is the convex hull of one point and one ellipse, then \(\psi(A)\le2\), with equality only when the ellipse is a disk and the point lies in it.  Section 10 characterizes (3\times3) disk matrices with \(\psi=2\).
- Michel Crouzeix and César Palencia, **“The Numerical Range is a \((1+\sqrt2)\)-Spectral Set,”** *SIAM J. Matrix Anal. Appl.* 38 (2017), 649–655, https://perso.univ-rennes1.fr/michel.crouzeix/publis/CrouzeixPalencia2017.pdf and https://arxiv.org/abs/1702.00668.  Their double-layer/Cauchy-companion method gives the uniform all-polynomial bound (1+\sqrt2).  It does not supply a (2)-bound or its equality cases.  Ransford–Schwenninger show the abstract norm lemma used there is itself sharp at (1+\sqrt2): https://ris.utwente.nl/ws/portalfiles/portal/171656886/17m1143757.pdf.
- K. R. Davidson, V. I. Paulsen, H. J. Woerdeman, **“Complete spectral sets and numerical range,”** preprint https://www.math.uwaterloo.ca/~krdavids/Preprints/DPWnum_range.pdf.  Records Berger’s theorem (w(T)\le1\Rightarrow T\) has a unitary (2)-dilation and Okubo–Ando’s theorem that a \(\rho\)-contraction is similar to a contraction with condition number at most \(\rho\).  Consequently (w(T)\le1\) makes \(\overline{\mathbb D}\) a complete (2)-spectral set.  Also, a complete (C)-spectral-set bound corresponds to numerical-radius bound \((C+C^{-1})/2\), not to (w(f(T))\le1).
- Bartosz Malman, Javad Mashreghi, Ryan O’Loughlin, Thomas Ransford, **“Double-layer potentials, configuration constants and applications to numerical ranges,”** IMRN (2025), https://arxiv.org/abs/2407.19049.  The refined bound is
  \[
  \psi(A)\le 1+\sqrt{1+a(W(A))},\qquad 0\le a(W(A))<1.
  \]
  This is pointwise strict relative to (1+\sqrt2), but it is never below (2) from this formula alone; therefore configuration constants do not prove nondisk rigidity.
- Bartosz Malman, Javad Mashreghi, Ryan O’Loughlin, Thomas Ransford, **“On the Crouzeix ratio for (N\times N) matrices,”** https://arxiv.org/abs/2409.14127.  Exact useful results: (A\mapsto\psi(A)) is lower semicontinuous everywhere; it is continuous when \(\sigma(A)\subset W(A)^\circ\); a boundary eigenvalue is a reducing normal summand; every fixed-dimensional universal constant is attained after quotienting translations/scalings; and each fixed-dimensional constant is (<1+\sqrt2).  The paper also explicitly warns that \(\psi\) is discontinuous at scalar matrices and at certain non-scalars, so naive compactness/limit arguments are invalid.
- Thomas Ransford and Nathan Walsh, **“Spectral sets, extremal functions and exceptional matrices,”** *Linear Multilinear Algebra* 70 (2022), 3310–3318, https://arxiv.org/abs/2011.02845.  If (f) is an extremal bounded holomorphic function and \(\|f(A)\|>1\), then every principal right singular vector (x) satisfies \(\langle f(A)x,x\rangle=0\).  This necessary orthogonality does **not** imply (w(f(A))\le1) or that (f(A)) is half-radial.
- Kenan Li, **“On the Uniqueness of Functions that Maximize the Crouzeix Ratio,”** https://arxiv.org/abs/2002.01027.  Extremizers can be written (B\circ\phi) (finite Blaschke product after a Riemann map), but higher-dimensional examples can have distinct extremizers of different degrees.  Any rigidity proof may not assume a unique extremizer or degree one.
- Iveta Hnetynkova and Petr Tichy, **“Characterization of half-radial matrices,”** *Linear Algebra Appl.* 542 (2018), 225–245, https://arxiv.org/abs/1804.10407.  Theorem 9: \(\|T\|=2w(T)\) iff (T\) is unitarily similar to \((\|T\|I_m\otimes J_2)\oplus B\) with \(\|B\|<\|T\|\), (w(B)\le\|T\|/2\), iff (W(T)) is the centered disk of radius \(\|T\|/2\).  Lemma 11 and Theorem 14: equality for a monomial (p(z)=z^k) forces a reducing Crabb–Choi–Crouzeix block; in particular (W(A)) is a disk.  This fully proves rigidity for linear and monomial exact extremizers, but the paper expressly leaves general polynomials/extremizing sequences open.
- A. Berger and J. G. Stampfli, **mapping theorem for numerical radius** (primary theorem discussed in https://arxiv.org/abs/1510.08132): if (w(T)\le1), (f\in A(\mathbb D)), and (f(0)=0), then (w(f(T))\le\|f\|_\infty).  The hypotheses concern a disk numerical range and a zero at its center; using it for a Riemann map of an arbitrary (W(A)) would silently assume the missing mapping inclusion.
- Jinshan Mu, **“The Numerical Range Is a 2-Spectral Set,”** July/August 2026 preprint, source https://github.com/jinshanmu/CrouzeixConjecture/blob/main/AnnMath/the_numerical_range_is_a_2_spectral_set.tex and preprint page https://www.preprints.org/manuscript/202607.1919/v3.  This very recent, not-yet-peer-reviewed manuscript claims the universal scalar constant (2) using a positive-real completion theorem, simple-spectrum approximation, and smooth convex outer approximation.  Its proof does not classify equality; its own discussion identifies equality classification as further work.  A directly checkable saturation consequence of its core theorem is recorded below.

### Geometric/extremal reconnaissance (agent `geometric_rigidity`, 2026-08-30)

- E. Lorist and F. L. Schwenninger, *A solution to Crouzeix's conjecture*, arXiv:2608.03841v2, https://arxiv.org/html/2608.03841 . Theorem 3 proves the universal scalar (2)-spectral-set inequality. The proof passes through Lemma 1: uniformly bounded commuting defects of a (2)-dilation imply ‖T‖≤2. Equality audit: at κ=2 the final inequality in Lemma 1 becomes (0\le0), so this proof as written supplies no rigidity condition. It is therefore useful for the uniform upper bound but cannot simply be cited for the desired equality characterization; any final use must reproduce the needed proof because the problem forbids assuming the theorem.
- A. Mathew, *Geometry of Algebraic Curves*, Lecture 17, https://math.uchicago.edu/~amathew/287y.pdf .  The plane-curve Gauss map is birational onto the dual in characteristic zero, and biduality recovers the original curve.  This is the precise fact needed below to turn a generic smooth **real dual point** into a unique, hence real, contact point; hyperbolicity alone would not justify that conclusion at a singular bitangent point.
- S. Orevkov and F. Pakovich, *On intersection of lemniscates of rational functions*, https://arxiv.org/abs/2309.04983 .  Lemma 3.1 identifies irreducibility of a rational lemniscate with that of its separated-variable complexification; Theorem 3.3 gives the polynomial proper-power criterion.  The paper also warns that for rational maps the naive composition condition is sufficient but not necessary for reducibility.  The final argument below therefore selects the unique irreducible factor carrying the real oval instead of assuming the entire cleared numerator is irreducible.
- R. Kippenhahn, *On the numerical range of a matrix* (English translation of the 1951 paper by P. Zachlin and M. Hochstenbach), original DOI/PDF https://doi.org/10.1002/mana.19510060306 .  Theorem 10 writes the boundary-generating curve in line coordinates as \(\det(u\operatorname{Re}A+v\operatorname{Im}A+wI)=0\) and identifies every numerical-range support line with a real generating element.  The present proof uses only this directly checkable support-line inclusion, plus the elementary fact that the pencil is Hermitian for real \((u,v)\).
- S. Jin, *The numerical range is a 2-spectral set*, current manuscript source https://github.com/jinshanmu/CrouzeixConjecture/blob/main/AnnMath/the_numerical_range_is_a_2_spectral_set.tex and preprint https://www.preprints.org/manuscript/202607.1919 . Independent 2026 proof of the universal (2) bound via positive-real completion and two weighted Gramians. Its manuscript explicitly lists classification of extremal pairs as further work; no disk-rigidity theorem was located.
- I. Hnětynková and P. Tichý, *Characterization of half-radial matrices*, Linear Algebra Appl. 552 (2018), 35–59; open HTML https://arxiv.org/html/1804.10407v3 . Theorem 2 / Theorem 9: for nonzero finite matrices, ‖B‖=2w(B) iff (B/‖B‖) is unitarily similar to (J_2\oplus C) with (w(C)\le1/2), iff (W(B)) is the closed disk centered at (0) of radius ‖B‖/2. The paper also shows monomial equality is equivalent to (A^k) half-radial together with (w(A^k)=w(A)^k), and connects this to Crabb–Choi–Crouzeix blocks. Lesson: equality for the identity polynomial is rigid, but applying this to a general extremal (p(A)) would require the generally false/unavailable mapping inclusion (W(p(A))\subset p(W(A))).
- M. Crouzeix, *Spectral sets and (3\times3) nilpotent matrices*, https://perso.univ-rennes1.fr/michel.crouzeix/publis/nilcub.pdf . Proves ψ(A)≤2 for every (3\times3) nilpotent matrix and proves equality ψ(A)=2 forces (W(A)) to be a disk. The normalized nondisk family (A_s), (0<s<1), is treated strictly. This is a genuine special-case rigidity theorem, not a general equality characterization.
- M. Crouzeix, *Bounds for analytical functions of matrices*, Integral Equations Operator Theory 48 (2004), 461–477. Accessible summaries/formula in https://sites.math.washington.edu/~greenbau/PREPRINTS/michigan.pdf and discussion in https://arxiv.org/abs/2002.01027 . For a nonnormal (2\times2) matrix the exact ratio depends only on the eccentricity of its elliptical numerical range; it is strictly below (2) for every noncircular ellipse and tends to (2) only in the circular case. Degenerate line segments are normal and have ratio (1). Thus the target implication is true in sizes 1 and 2.
- M. Crouzeix and A. Greenbaum, *A New Proof that the Numerical Range is a Complete 2-Spectral Set for Weighted Shift Matrices*, https://arxiv.org/abs/2508.12768 . Theorem 2: for the cyclic weighted-shift family (P_d\operatorname{diag}(\alpha_1,\ldots,\alpha_d)), ψ≤2, and if the cyclic product is nonzero then ψ<2. If the product is zero, the numerical range is a disk. Remark 2 gives disk matrices whose ratio is strictly less than 2. This rules out a large structured nondisk counterexample family and warns that “disk” does not imply ψ=2.
- B. Malman, J. Mashreghi, R. O'Loughlin, T. Ransford, *On the Crouzeix ratio for (N\times N) matrices*, arXiv:2409.14127, https://arxiv.org/html/2409.14127 . Establishes lower semicontinuity of ψ; continuity when the spectrum lies in the interior; and the boundary-eigenvalue decomposition (A\simeq D\oplus\widetilde A), with (D) diagonal on boundary eigenvalues and σ(ẼA) in the interior. Proposition 2.3 studies (A_\alpha=1\oplus\alpha J_2), whose numerical range is the convex hull of a disk and an exterior point, and obtains ψ(Aα)≥π/2 for α>0. This is a central direct-sum pathology but not an equality-2 example.
- A. Greenbaum et al., *Crouzeix's Conjecture and Related Problems*, https://ris.utwente.nl/ws/portalfiles/portal/462934522/2006.04901v1.pdf . Records: an extremal function over (H^\infty(\Omega)) exists and is a finite Blaschke product (degree ≤N−1) composed with a Riemann map; for an extremal pair ((f,x)) with ‖f(A)‖>1 one has ⟨f(A)x,x⟩=0; and further factorization identities. These facts show how nonattainment of the polynomial supremum can be handled after passing to the interior function class, but the passage must be proved in the final document.
- Chandler Davis, *The Toeplitz–Hausdorff theorem explained*, Canad. Math. Bull. 14 (1971), 245–246, https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BA251EBB1E1DE08DBD3D84964F65938B/S0008439500058197a.pdf/the-toeplitz-hausdorff-theorem-explained.pdf . Conceptual two-dimensional proof of convexity of numerical ranges.
- G. Lakos, *A short proof of the elliptical range theorem*, arXiv:2208.06248, https://arxiv.org/abs/2208.06248 , and P. Paparella–L. Ramirez–Y.-F. Wang, https://arxiv.org/abs/1807.04268 . Authoritative formulations that a (2\times2) numerical range is a filled (possibly degenerate) ellipse with eigenvalues as foci.
- J. H. Shapiro, *Notes on the numerical range*, https://carmamaths.org/jon/Preprints/Books/CUP/CUPold/numrange_notes.pdf . Theorem 6.5 (Hildebrandt): every eigenvalue on ∂W(A) is a normal/reducing eigenvalue. A short finite-dimensional proof is also recorded below.

## Exact proved facts and constructions

- **Direct-sum upper bound.** If (A=\bigoplus_{j=1}^m A_j), then
  \[
  W(A)=\operatorname{conv}\Bigl(\bigcup_jW(A_j)\Bigr),\qquad
  \psi(A)\le\max_j\psi(A_j).
  \]
  Indeed (p(A)=\oplus_jp(A_j)), whereas the supremum norm on (W(A)) dominates that on every block range. Thus direct sums cannot create a ratio above the worst block.
- **Strict ice-cream-cone obstruction.** Put (J_r=\begin{psmallmatrix}0&2r\\0&0\end{psmallmatrix}), (0<r<1), and (A=[1]\oplus J_r), so (K=W(A)=\operatorname{conv}(\overline D(0,r)\cup\{1\})) is not a disk. If (R=\operatorname{crad}_{K^\circ}(0)), strict domain monotonicity gives (R>r). For every holomorphic (f:K^\circ\to\mathbb D), Schwarz–Pick gives
  \[
  |f'(0)|\le \frac{1-|f(0)|^2}{R}.
  \]
  Writing (q=r/R<1), the exact norm formula yields
  \[
  \|f(J_r)\|\le \sqrt{x^2+q^2(1-x^2)^2}+q(1-x^2)<2,
  \quad x=|f(0)|.
  \]
  The maximum over (x\in[0,1]) is strictly below (2); the scalar block contributes at most (1). Polynomial approximation therefore gives (\psi(A)<2). This closes the tempting direct-sum counterexample, despite the lower bound (\pi/2).
- **Quadratic polynomial-preimage identity.** For
  \[
  A=\begin{pmatrix}a&b&c\\0&a&0\\0&d&e\end{pmatrix},\qquad q(z)=(z-a)(z-e),
  \]
  direct multiplication gives
  \[
  q(A)=\bigl(b(a-e)+cd\bigr)e_{12}.
  \]
  Hence (p=2q/(b(a-e)+cd)) is the exact natural attempt to force (p(A)=2e_{12}).
- **Algebraic obstruction to the preceding attempt (irreducible/interior-spectrum case).** If (a\ne e), (W(A)\subset\{|p|\le1\}), and the constant-2 bound is used, then (p) attains the Crouzeix ratio (2). The finite-dimensional extremal theorem forces 
  ‎(|p|=1) on (\partial W(A)), so an open boundary arc is a Cassini oval. After centering the foci at (\pm c), its projective equation is
  \[
  (X^2+Y^2)^2-2c^2(X^2-Y^2)Z^2+(c^4-R^2)Z^4=0.
  \]
  In the noncritical connected regime this irreducible quartic has exactly two ordinary nodes, at the circular points ([1:\pm i:0]); its dual therefore has degree (4(4-1)-2\cdot2=8). On the other hand every smooth boundary tangent of a (3\times3) numerical range lies on the Kippenhahn determinant curve
  \(\det(u\operatorname{Re}A+v\operatorname{Im}A+wI)=0\), of degree (3). An irreducible degree-8 dual curve cannot be a component of a cubic. Thus no (3\times3) witness of this quadratic polynomial-preimage form exists. If a focus is a boundary eigenvalue, boundary-eigenvalue reduction gives a (2\times2) Jordan disk plus a scalar; on that disk the point in the direction away from the other focus makes ‎(|p|>1), again a contradiction.
- **General degree/class filter for polynomial attainment.** If a polynomial (p) actually attains ratio (2) and all eigenvalues lie in (W(A)^\circ), every normalized extremal is inner relative to (W(A)^\circ); hence (\partial W(A)) lies on a polynomial lemniscate. For a degree-(m) polynomial with simple roots, the irreducible projective lemniscate has degree (2m), two ordinary (m)-fold points at infinity, and dual degree
  \[
  2m(2m-1)-2m(m-1)=2m^2.
  \]
  Kippenhahn therefore rules out such an attained polynomial extremal whenever (N<2m^2). In particular, quadratic Cassini witnesses are impossible through size (7), and the natural (2m\)-dimensional block companion linearizations are impossible for every (m>1). Repeated-root/proper-power cases require separate factor analysis; the pure monomial case reduces to the CCC/disk theorem above.

### Conformal/operator lemmas proved or independently checked

1. **Degenerate numerical ranges.** If (W(A)=\{\gamma\}\), then (A=\gamma I) (apply polarization to (x^*(A-\gamma I)x=0)), hence \(\psi(A)=1\).  If (W(A)) is contained in a line, rotate/translate so every quadratic form of (A) is real; then (A=A^*\), so (A) is normal and \(\psi(A)=1\).  Thus \(\psi(A)=2\) automatically implies (W(A)) has nonempty interior.
2. **Exact invariances.** For \(\alpha\ne0\), \(\beta\in\mathbb C\), and unitary (U),
   \[
   W(\alpha U^*AU+\beta I)=\alpha W(A)+\beta,
   \qquad \psi(\alpha U^*AU+\beta I)=\psi(A).
   \]
   Also (W(A^*)=\overline{W(A)}\) and \(\psi(A^*)=\psi(A)\), using (q(z)=\overline{p(\bar z)}\).  These statements do not extend to arbitrary real-affine deformations.
3. **Boundary-eigenvalue reduction.** If an eigenvalue \(\lambda\in\sigma(A)\cap\partial W(A)\), choose a supporting line and rotate so \(\operatorname{Re}(A-\lambda I)\preceq0\).  For (Av=\lambda v\), equality of its quadratic form forces \(\operatorname{Re}(A-\lambda I)v=0\), hence (A^*v=\bar\lambda v\).  Thus (v) reduces (A); iterating yields (A\simeq D\oplus A_0), where (D) is diagonal with boundary eigenvalues and \(\sigma(A_0)\subset W(A)^\circ\).
4. **Polynomial supremum versus holomorphic extremizer (nonattainment handled).** After removing the normal boundary block, \(\sigma(A_0)\Subset\Omega:=W(A)^\circ\).  Mergelyan approximation and radial dilation through a Riemann map show that the polynomial supremum equals
   \[
   \sup\{\|f(A_0)\|: f\in H^\infty(\Omega),\ \|f\|_\infty\le1\}.
   \]
   A normal-family subsequence converges locally uniformly, including all derivatives needed by the finite-dimensional functional calculus, so this enlarged supremum is attained even when no polynomial attains the original supremum.  Crouzeix’s finite interpolation theorem then permits an extremizer (B\circ\phi) with (B) a finite Blaschke product of degree at most the nonnormal block size minus one.  Boundary diagonal blocks contribute at most (1) and cannot produce a ratio (>1).
5. **Strict conformal-radius lemma.** Let a closed disk \(\overline{D(c,r)}\subset K\), where (K) is compact convex with nonempty interior, and let (a:K^\circ\to\mathbb D) be normalized by (a(c)=0\).  Schwarz’s lemma applied to (z\mapsto a(c+rz)) gives (r|a'(c)|\le1\).  Equality forces (a(c+rz)=e^{it}z) on the disk, hence by the identity theorem throughout (K^\circ); boundedness then forces (K=\overline{D(c,r)}\).  Thus containment is strict exactly when (r|a'(c)|<1).
6. **Obvious reducible counterexamples are impossible.** Let
   \[
   A=\bigoplus_{j=1}^m\begin{pmatrix}c_j&2r_j\\0&c_j\end{pmatrix}\oplus D,
   \]
   with (r_j>0) and (D) normal, and put (K=W(A)\).  For each Jordan block, Crouzeix’s exact relative (2\times2) formula gives
   \(\psi_K(J_j)=\max\{1,2r_j|a_j'(c_j)|\}\), where (a_j:K^\circ\to\mathbb D), (a_j(c_j)=0\).  If (K) is not one of those disks, the strict conformal-radius lemma makes every block constant (<2), while the normal block contributes at most (1).  Finitely many blocks imply \(\psi(A)<2\).  Hence adding an exterior scalar/normal block to a sharp (2\times2) disk block cannot yield a nondisk counterexample with ratio (2).
7. **Monomial rigidity.** If \(\|A^k\|=2\max_{z\in W(A)}|z|^k\), then
   \[
   \|A^k\|\le2w(A^k)\le2w(A)^k
   \]
   is equality throughout.  Crabb’s equality theorem yields a reducing Crabb–Choi–Crouzeix block (w(A)C_k\), and the remaining block has numerical radius at most (w(A)); since (W(C_k)) is the full disk of that radius, (W(A)) is that disk.  This includes (k=1) (half-radial matrices).
8. **Strictness inside the 2026 positive-real completion theorem.** In the notation of Mu’s claimed core theorem, one obtains a positive Gramian (I\preceq P\preceq2I) and
   \[
   P=I+\tfrac14T^*PT,\qquad T^*T\preceq T^*PT=4(P-I)\preceq4I.
   \]
   If (T) has distinct eigenvalues, equality \(\|T\|=2\) is actually impossible: for a unit maximizing vector (e), equality throughout forces (Pe=2e) and (PTe=Te).  Applying the Stein identity to (Te\) gives (T^2e=0\), while (Te\ne0\), contradicting diagonalizability (\(\ker T^2=\ker T\)).  Therefore the core simple-spectrum stage is strict; equality can only emerge through coalescing-eigenvalue/outer-domain limits.  This explains why its non-strict approximation endpoint supplies no rigidity statement without a separate quantitative stability theorem.

9. **Quantitative saturation and eigenvalue coalescence in the positive-real completion.**  Suppose
   \[
   P=\sum_{k\ge0}4^{-k}T^{*k}T^k,\qquad I\preceq P\preceq2I,
   \qquad P=I+\tfrac14T^*PT.
   \]
   Put (s=\|T\|), (\Delta=4-s^2), and choose a unit vector (e) with (\|Te\|=s).  If
   \(a=2-\langle Pe,e\rangle\) and
   \(b=\langle(P-I)Te,Te\rangle\), then the Stein identity gives the exact defect formula
   \[
   \boxed{\Delta=4a+b.}
   \]
   Since (0\preceq2I-P\preceq I) and (0\preceq P-I\preceq I), functional calculus for positive contractions yields
   \[
   \|(2I-P)e\|\le\tfrac12\sqrt\Delta,
   \qquad \|(P-I)Te\|\le\sqrt\Delta,
   \qquad \|T^2e\|\le2\sqrt\Delta.
   \]
   For (y=Te/s), one has (T^*y=se) exactly,
   \[
   \|Ty\|\le\frac{2\sqrt\Delta}{s},\qquad
   \|(P-I)y\|\le\frac{\sqrt\Delta}{s},\qquad
   |\langle e,y\rangle|\le\frac{\sqrt\Delta}{2}+\frac{\sqrt\Delta}{s}.
   \]
   Thus, if (T_j\to T), (\|T_j\|\to2), and maximizing vectors are passed to a subsequence, the limit contains an orthonormal chain
   \[
   Te=2y,\qquad Ty=0,\qquad T^*y=2e.
   \]
   Applying the same argument to the adjoint gives (T^*e=0), so the span of (e,y) reduces (T) to (2J_2).  In particular zero is a nonsemisimple eigenvalue.  For the approximants,
   \[
   \sigma_{\min}(T_j)\le \frac{2\sqrt{4-\|T_j\|^2}}{\|T_j\|},
   \qquad
   \min_{\lambda\in\sigma(T_j)}|\lambda|
   \le\left(\frac{2^N\sqrt{4-\|T_j\|^2}}{\|T_j\|}\right)^{1/N},
   \]
   the second estimate following from (|\det T|\le\sigma_{\min}(T)\|T\|^{N-1}) and (\|T\|\le2).  Hence at least two eigenvalues coalesce at zero in any simple-spectrum approximation of an equality case (algebraic multiplicity is stable under a small Riesz circle).

10. **An extremal singular chain need not reduce the conformal coordinate.**  For (0<a\le\sqrt2), set
   \[
   T_a=\begin{pmatrix}0&2&0\\0&0&a\\0&0&0\end{pmatrix}.
   \]
   Then (\|T_a\|=2) and its Gramian is
   \[
   P=\sum_{k\ge0}4^{-k}T_a^{*k}T_a^k
    =\operatorname{diag}(1,2,1+a^2/2)\preceq2I.
   \]
   The saturated plane (\operatorname{span}\{e_1,e_2\}) is invariant but not reducing for (T_a) when (a\ne0), since (T_ae_3=ae_2).  Its numerical range is nevertheless a centered disk (rotational unitary similarity) of radius (\sqrt{4+a^2}/2).  Thus the Gramian equality chain by itself cannot justify splitting off a Crabb block; one must obtain invariance for the conformal coordinate, not merely for its extremal function.

11. **Invariant-chain closure for an arbitrary finite Blaschke extremizer.**  Let (K=W(A)), let (\phi:K^\circ\to\mathbb D) be conformal with inverse (g), and write an equality extremizer as (f=B\circ\phi).  Put (S=\phi(A)) and (F=B(S)).  Suppose the saturated plane (E=\operatorname{span}\{e,y\}) reducing (F) is also invariant under (S).  Since the commutant of (J_2) consists of upper triangular Toeplitz matrices, for some zero (\alpha) of (B), necessarily simple on this block,
   \[
   S|_E=\alpha I+\frac{2}{B'(\alpha)}J_2,\qquad
   A|_E=g(\alpha)I+\frac{2g'(\alpha)}{B'(\alpha)}J_2.
   \]
   Therefore (K) contains the disk of radius (R=|g'(\alpha)/B'(\alpha)|) centered at (g(\alpha)).  Its conformal radius there is ((1-|\alpha|^2)|g'(\alpha)|), so disk inclusion and Schwarz--Pick give opposite inequalities
   \[
   R\le(1-|\alpha|^2)|g'(\alpha)|,
   \qquad (1-|\alpha|^2)|B'(\alpha)|\le1.
   \]
   Both are equalities.  Schwarz--Pick makes (B) an automorphism and strict conformal-radius monotonicity makes (K) exactly that disk.  In particular, if (\dim\ker F^2=2), then (E=\ker F^2) is automatically (S)-invariant and disk rigidity follows.  Any nondisk equality case must have (\dim\ker F^2\ge3).

12. **Minimal-counterexample reduction to a globally nilpotent extremal image.**  Assume the universal upper bound (2) has been proved and disk rigidity is known below dimension (N).  In a least-dimensional nondisk equality case take the attained bounded-holomorphic extremizer (f) and its saturated vectors (e,y), and let
   \(G=\ker f(A)^N\).  This is (A)-invariant, contains (e,y), and
   \(\|f(A|_G)\|=2\).  Hence (\psi(A|_G)=2).  If (G) were proper, iteratively remove its reducing boundary eigenvalues.  Crouzeix's strict relative-domain lemma then implies that the surviving smaller block cannot have numerical range properly contained in (W(A)); otherwise its relative calculus constant on the larger interior would be strictly smaller than its intrinsic value (2).  Thus a smaller equality block has the same numerical range, and induction makes it a disk, a contradiction.  Consequently
   \[
   \boxed{f(A)\text{ is nilpotent on the whole space}.}
   \]
   Combined with item 11, a least counterexample has (N\ge4), (\dim\ker f(A)^2\ge3), and is necessarily defective.  This sharply localizes the unresolved coupling: it lies among several zero Jordan chains of (f(A)), not among diagonalizable or isolated-double-collision cases.

13. **Positive quotient-state classification (higher Blaschke degree).**  Retain an attained normalized extremizer (f=B\circ\phi), a unit maximizing vector (x), and write (T=f(A)), (Tx=2y).  The functionals
   \[
   L(h)=x^*h(A)x,\qquad
   \delta(h)=y^*h(A)x.
   \]
   These satisfy (L(fh)=0) and (\delta(fh)=2L(h)).  In addition, (L) is a state, not merely a bounded functional.  Indeed, if (\operatorname{Re}h\ge0), then (f_t=f e^{-th}) remains in the Schur ball for (t\ge0), and extremality at (x) gives
   \[
   0\ge\left.\frac d{dt}\right|_{0+}\|f_t(A)x\|^2=-8\operatorname{Re}L(h).
   \]
   Hence (\operatorname{Re}L(h)\ge0), (L(1)=1), and (\|L\|=1).

   Transfer by (\phi) to the disk, still denoting the functionals by (L,\delta).  The universal bound gives (\|\delta\|\le2), while (\delta(B)=2), so (\eta=\delta/2) is a norm-one functional norming (B).  There is a unique probability measure (\mu) on (\mathbb T) representing (L), and equality in the norming relation forces
   \[
   L(h)=\int_{\mathbb T}h\,d\mu,\qquad
   \delta(h)=2\int_{\mathbb T}h\,\overline B\,d\mu.
   \]
   The condition (L(Bh)=0) and the F. and M. Riesz theorem imply that (B\mu) has an (H^1_0) density.  Positivity then gives the exact model-space form
   \[
   \boxed{d\mu=|q|^2dm,\qquad q\in K_B:=H^2\ominus BH^2
   \text{ outer},\quad\|q\|_2=1.}
   \]
   Conversely every normalized outer (q\in K_B) gives such a pair (L,\delta).  For the converse/classification, note that (B|q|^2\in H^1_0) is equivalent to (q\perp BH^2) after taking the outer spectral factor of the positive density.  Thus positivity and factorization alone do **not** force (L) to be evaluation at a zero of (B).

   An explicit non-evaluation state is obtained with (B(z)=z^2) and
   \(q(z)=(1+az)/\sqrt{1+a^2}\), (0<a\le1):
   \[
   L(h)=h(0)+\frac{a}{1+a^2}h'(0),
   \qquad L(z^2h)=0.
   \]
   (Here the derivative coefficient is interpreted from the Taylor coefficient.)  This is the precise higher-degree obstruction to promoting the quotient identities to a point evaluation.

14. **Exact model showing the quotient identities are not themselves rigid.**  On (K_{B^2}=K_B\oplus BK_B), compress multiplication by (h) and conjugate by the diagonal similarity which multiplies the second summand by (2).  This gives a finite-dimensional unital homomorphism (\Theta) with
   \[
   \|\Theta(h)\|\le2\|h\|_{\mathbb D},\qquad \|\Theta(B)\|=2.
   \]
   For (x=q\oplus0) and (y=0\oplus Bq), its two-vector compressions have exactly the functionals in item 13.  Hence all of the singular-chain, positivity, quotient, and norming-functional equalities are compatible with arbitrary finite Blaschke degree and arbitrary normalized outer (q\in K_B).  A proof of numerical-range rigidity must use the self-consistency (\Omega=W(A)^\circ), not merely the abstract (2)-bounded functional calculus.

   A concrete adversarial instance makes this visible.  Let
   \[
   C=\begin{pmatrix}0&\sqrt2&0\\0&0&\sqrt2\\0&0&0\end{pmatrix},\quad
   g(w)=\frac{w+1/2}{1+w/2},\quad
   A=g(C)=\begin{pmatrix}
   1/2&3\sqrt2/4&-3/4\\0&1/2&3\sqrt2/4\\0&0&1/2
   \end{pmatrix},
   \]
   and (B(z)=((z-1/2)/(1-z/2))^2).  Since (W(C)=\overline{\mathbb D}) and (\|C^2\|=2), the disk is a (2)-spectral set for (A), the disk-domain calculus constant is exactly (2), and (B(A)=C^2).  Nevertheless (W(A)) is not a disk.  After subtracting (I/2), the widths in the real and imaginary directions are respectively
   \[
   \frac{3\sqrt{17}}8\quad\hbox{and}\quad\frac{3\sqrt5}4,
   \]
   obtained from the characteristic polynomials
   \[
   \frac{(8t-3)(16t^2+6t-9)}{128},
   \qquad \frac{t(64t^2-45)}{64}.
   \]
   They are unequal.  This is not a counterexample to the problem: the rightmost support point is ((5+3\sqrt{17})/16>1), where (|B|>1), so normalization on the actual numerical range destroys the ratio (2).  It is an exact counterexample to any argument that replaces (W(A)) by an externally prescribed disk or uses only the quotient-state identities.

15. **Self-contained double-layer package actually needed for the universal bound and equality extraction.**  Smooth outer approximation is unnecessary once boundary eigenvalues have been split off.  Let (K) be any compact convex body with interior, let (W(A)\subset K) and (\sigma(A)\subset K^\circ), and let (\Gamma=\partial K) be counterclockwise arclength-parametrized.  Its outward normal (n) exists almost everywhere.  For (R(\sigma)=(\sigma I-A)^{-1}) set
   \[
   P(\sigma)=\frac1\pi\operatorname{Re}(n(\sigma)R(\sigma)).
   \]
   If (H_\sigma=\operatorname{Re}(\overline n(\sigma)(\sigma I-A))), then support of (K) gives (H_\sigma\succeq0), and the resolvent identity gives
   \[
   \operatorname{Re}(nR)=R^*H_\sigma R\succeq0.
   \]
   Cauchy's formula gives (\int_\Gamma P\,ds=2I).  Thus
   \[
   (Vx)(\sigma)=2^{-1/2}P(\sigma)^{1/2}x
   \]
   is an isometry into (L^2(\Gamma;\mathbb C^N)).  If (f\in A(K)), (\|f\|_K\le1), let (Q) be multiplication by (f) and (T=f(A)).  Directly splitting the two terms of (P), without invoking any bounded Cauchy-companion theorem, yields
   \[
   E_n:=2V^*Q^{*n}V-T^{*n}
   =\frac1{2\pi i}\int_\Gamma \overline{f(\sigma)^n}(\sigma I-A)^{-1}\,d\sigma.
   \]
   Hence every (E_n) commutes with (T) and
   \[
   \sup_n\|E_n\|\le\frac{\operatorname{length}(\Gamma)}{2\pi}
      \max_{\sigma\in\Gamma}\|R(\sigma)\|<\infty.
   \]
   The Lorist--Schwenninger abstract lemma (whose elementary telescoping proof must be reproduced) now gives (\|f(A)\|\le2).  Boundary-eigenvalue reduction covers arbitrary matrices, since the diagonal boundary block has norm at most (1).  This is a complete universal-(2) proof for the function class needed here; no Crouzeix conjecture is assumed and no smoothness of (\partial K) is hidden.

   At equality, let (T^*Tx=4x), (y=Tx/2), and note that (\rho(T)<1) for a nonconstant extremizer because the spectrum of (A) is interior.  Auditing every equality in the telescoping lemma gives
   \[
   Q^*VTx-2Vx=0,\qquad T^*x=0,\qquad QVx=Vy,\qquad Q^*Vy=Vx.
   \]
   Applying the reflected construction to (A^*) and the right singular vector (y) gives (Ty=0); norm equality already gives (T^*y=2x).  Thus the (2J_2) block of (T) is genuinely reducing.  The pointwise identity
   \[
   P(\sigma)^{1/2}(y-f(\sigma)x)=0\quad\text{a.e. on }\Gamma
   \]
   follows from (QVx=Vy).  The only separate compactness input is the passage from polynomial extremizing sequences to an attained finite-Blaschke extremizer in (A(K)); convexity makes (K^\circ) a Jordan domain, so the Riemann map and finite Blaschke product extend continuously to (\overline K).

16. **Least-dimension cyclic reduction and global square-zero conclusion.**  Work in a least-dimensional nondisk equality case, after the boundary-spectrum reduction, and let (f(A)x=2y) be the extremal singular pair from item 15.  Put
   \[
   \mathcal H_x=\operatorname{span}\{A^kx:0\le k<N\}.
   \]
   This is (A)-invariant and contains (y=f(A)x/2).  If it were proper, the restriction (A|_{\mathcal H_x}) would still satisfy (\|f(A|_{\mathcal H_x})\|=2).  Peel off any of its reducing boundary eigenvalues; the norm-(2) block remains.  The intrinsic and relative-to-(K) calculus constants of that smaller block are both (2) by the universal upper bound.  Crouzeix's strict relative-domain lemma forces its numerical range to equal (K), and induction then makes (K) a disk, a contradiction.  Hence
   \[
   \boxed{x\text{ is cyclic for }A.}
   \]
   Applying the same argument to (A^*) and the extremal right singular vector (y) gives
   \[
   \boxed{y\text{ is cyclic for }A^*.}
   \]
   Since equality extraction gives (f(A)y=0), one has (f(A)^2x=0).  The operator (f(A)^2) commutes with (A), and (x) is cyclic, so
   \[
   \boxed{f(A)^2=0\text{ on the whole space}.}
   \]
   Consequently (W(f(A))=\overline{\mathbb D}): for any square-zero matrix (R), the orthogonal decomposition ((\ker R)^\perp\oplus\ker R) writes it as a single off-diagonal block and gives (W(R)=\overline D(0,\|R\|/2)).  Further exact identities are
   \[
   \operatorname{ran}f(A)=\operatorname{span}\{A^ky:0\le k<N\},\qquad
   \operatorname{ran}f(A)^*=\operatorname{span}\{(A^*)^kx:0\le k<N\}.
   \]
   Thus a least counterexample is a cyclic (nonderogatory) matrix, observable from (y), whose extremal image is globally square-zero, not merely nilpotent.

   This still does not make the extremal plane invariant for (A).  The genuine disk equality examples supplied by every higher Crabb--Choi--Crouzeix block already have (x) cyclic for (A), (y) cyclic for (A^*), (f(A)^2=0), and a non-(A)-invariant endpoint plane.  Therefore cyclicity cannot by itself close the higher-degree case; the missing step must promote these endpoint data to the full CCC chain using numerical-range geometry.

17. **Presumptively-false audit of items 15--16 (no fatal gap found; exact dependencies isolated).**

   - *Boundary peeling and the induction require two distinct peeling stages.*
     Suppose disk rigidity is known below dimension \(N\), let \(K=W(A)\), and
     suppose \(A\) has a boundary eigenvalue.  Iterating the reducing-eigenvector
     argument gives
     \[
       A=D\oplus B,
     \]
     where \(D\) is diagonal with entries in \(\partial K\),
     \(\sigma(B)\subset K^\circ\), and \(\dim B<N\).  Choose polynomials \(p_j\)
     with \(\|p_j\|_K=1\) and \(\|p_j(A)\|\to2\).  Since
     \(\|p_j(D)\|\le1\), one has \(\|p_j(B)\|\to2\).  Thus the relative
     constant of \(B\) on \(K\) and its intrinsic constant are both \(2\)
     (the reverse upper bounds are the universal theorem), and induction makes
     \(L:=W(B)\) a closed disk of positive radius.

     It is **not yet legitimate** to compare \(L^\circ\) strictly with
     \(K^\circ\), because \(\sigma(B)\) may meet \(\partial L\).  Peel those
     eigenvalues a second time:
     \[
       B=E\oplus C,
     \]
     with \(E\) diagonal on the finite set
     \(\Lambda=\sigma(B)\cap\partial L\) and
     \(\sigma(C)\subset L^\circ\).  The same polynomial sequence has
     \(\|p_j(C)\|\to2\), because \(\|p_j(E)\|\le1\).  Hence the relative
     constants of \(C\) on both \(K^\circ\) and \(L^\circ\) equal \(2\).
     Moreover
     \[
       L=W(B)=\operatorname{conv}(\Lambda\cup W(C)).
     \]
     Every point of the boundary circle of \(L\) is extreme; every extreme point
     of the convex hull of a compact set belongs to that set.  Thus
     \(\partial L\setminus\Lambda\subset W(C)\), and closedness of \(W(C)\)
     gives \(\partial L\subset W(C)\).  Convexity then gives \(W(C)=L\).
     (In particular \(C\ne0\); finitely many scalar points cannot have a disk as
     their convex hull.)  Now \(\sigma(C)\subset L^\circ\), so strict domain
     monotonicity applies.  If \(L\subsetneq K\), it gives
     \[
       2=\psi_{L^\circ}(C)>\psi_{K^\circ}(C)=2,
     \]
     a contradiction.  Therefore \(K=L\) is the same disk.  This argument uses
     only an asymptotically extremizing polynomial sequence and never assumes a
     maximizing polynomial.
   - *Invariant restrictions.*  For (\mathcal H_x=\operatorname{alg}(A)x), invariance is enough: holomorphic functional calculus restricts as (f(A)|_{\mathcal H_x}=f(A|_{\mathcal H_x})), and (x,y\in\mathcal H_x), so the restricted norm is at least (2).  Since its numerical range lies in (K), the universal relative bound makes both the intrinsic and (K)-relative constants exactly (2).
   - *Strict domain monotonicity.*  If bounded open convex domains satisfy (\sigma(C)\subset\Omega_0\subsetneq\Omega_1), then
     \[
       \psi_{\Omega_0}(C)>\psi_{\Omega_1}(C)
       \quad\text{whenever }\psi_{\Omega_0}(C)>1.
     \]
     Here is the exact equality audit.  Let the two constants be equal to
     \(c>1\), and choose a norm-one extremizer \(g\) for \(\Omega_1\).
     Finite Hermite--Nevanlinna--Pick theory says that **every** norm-one
     extremizer is a finite Blaschke product relative to its domain.  If
     \(r=\|g\|_{\Omega_0}<1\), then \(g/r\) is admissible on \(\Omega_0\) and
     gives a value \(c/r>c\), impossible.  Hence \(r=1\), and the restriction
     of \(g\) is also an extremizer on \(\Omega_0\); it too is a finite
     Blaschke product.  Convexity supplies a point
     \(z_0\in\partial\Omega_0\cap\Omega_1\): take the first exit from
     \(\Omega_0\) along a segment joining a point of \(\Omega_0\) to a point
     of \(\Omega_1\setminus\Omega_0\).  Smaller-domain innerness gives
     \(|g(z_0)|=1\), whereas the nonconstant larger-domain Schur function
     satisfies \(|g(z_0)|<1\) by the maximum principle.  This contradiction
     proves strictness.  The qualification \(c>1\) is indispensable, since a
     constant extremizer gives value \(1\) on every domain.  This is precisely
     Crouzeix (2004), Lemma 2.2, and its proof uses no universal Crouzeix bound.
   - *Nonsmooth double layer.*  A convex boundary is rectifiable and has an outward normal almost everywhere; (d\sigma=i n\,ds) holds almost everywhere.  Since the spectrum is a positive distance from the boundary, all resolvent integrands are continuous and bounded.  The positivity, Cauchy identities, and isometry in item 15 therefore require no smoothness.  For a general (H^\infty) function, apply the argument to radial dilates through a Riemann map and pass to the spectral jets.  The equality extremizer itself is finite Blaschke and continuous on the closure, so the exact (not limiting) boundary model applies.
   - *Equality in the dilation lemma.*  At (\kappa=2), the telescoping lower bound gives (2m_1\ge-\|u\|^2), while the terminal estimate gives (\|u\|^2\le-2m_1); hence both are equalities.  The weighted sum of nonnegative individual slacks is zero, so every slack vanishes.  From (\rho(T)<1) one obtains (u=0) and (T^*x=0), not merely an asymptotic statement.  Applying the independently valid reflected model to (A^*) and the right singular vector (y) gives (Ty=0).  No step assumes that the original polynomial supremum is attained.
   - *Remaining dependency.*  The final document must reproduce (i) the finite Nevanlinna--Pick extremizer theorem (including “every extremizer is a finite Blaschke product”), or an equivalent finite-jet proof; (ii) polynomial approximation of that closure-continuous extremizer; and (iii) the elementary Lorist--Schwenninger telescoping lemma.  Subject to those explicitly reproducible ingredients, the universal bound, equality extraction, peeling, strict-domain comparison, cyclicity, and global square-zero conclusion are logically sound.

18. **The abstract dilation lemma, in the exact self-contained form needed.**  Suppose (V) is an isometry, (Q) a contraction, and
   \[
   E_n=2V^*Q^{*n}V-T^{*n}
   \]
   are uniformly bounded and commute with (T).  Then (\|T\|\le2).  Indeed the displayed identity first makes all powers of (T) uniformly bounded.  Put (\kappa=\|T\|>1), choose (T^*Tx=\kappa^2x) with (\|x\|=1), and set
   \[
   m_n=\operatorname{Re}\langle E_nT^nx,x\rangle,\qquad
   u=Q^*VTx-\kappa Vx.
   \]
   Direct substitution, using (E_nT=TE_n), gives
   \[
   \begin{aligned}
   \kappa m_n-m_{n+1}
   &=
   \kappa(\kappa-1)
   \left\|T^{*n}x-\frac{V^*Q^{*n}u}{\kappa(\kappa-1)}\right\|^2
   -\frac{\|V^*Q^{*n}u\|^2}{\kappa(\kappa-1)}\\
   &\ge-\frac{\|u\|^2}{\kappa(\kappa-1)}.
   \end{aligned}
   \]
   Since (m_n) is bounded, multiplication by (\kappa^{-n+1}) and telescoping yield
   \[
   \kappa m_1\ge-\frac{\|u\|^2}{(\kappa-1)^2}. \tag{D1}
   \]
   On the other hand contractivity of (Q), the isometry property, and
   \(E_1=2V^*Q^*V-T^*\) give
   \[
   \|u\|^2
   \le2\kappa^2-\kappa m_1-\kappa^3. \tag{D2}
   \]
   Combining (D1)--(D2),
   \[
   \|u\|^2\left(1-\frac1{(\kappa-1)^2}\right)
   \le\kappa^2(2-\kappa).
   \]
   For (\kappa>2) the left side is nonnegative and the right side negative, a contradiction.  This proves the universal constant-(2) conclusion once item 15 constructs (V,Q,E_n).  At (\kappa=2), retaining equality rather than discarding it gives exactly the saturation analysis in items 15 and 17.

19. **One curved exposed arc and the endpoint relations collapse the extremal to a rational function.**  After the boundary-spectrum induction, let (T=f(A)) and retain only the endpoint relations
   \[
   Tx=2y,\quad Ty=0,\quad T^*x=0,\quad T^*y=2x.
   \]
   For (R(z)=(zI-A)^{-1}) define scalar rational functions
   \[
   a=x^*Rx,\qquad b=x^*Ry,\qquad c=y^*Rx,\qquad d=y^*Ry.
   \]
   Since (R) commutes with (T), applying (RT=TR) between the endpoint vectors gives identically
   \[
   b=0,\qquad d=a.
   \]
   No cyclicity or global square-zero conclusion is needed here.  A polygonal numerical
   range is already impossible after the boundary-spectrum reduction: at a polygon vertex,
   two independent supporting directions and equality in the two Hermitian Rayleigh
   quotients solve to give (Ax=\lambda x) and (A^*x=\bar\lambda x), a forbidden boundary
   eigenvalue.  Every nonpolygonal finite-matrix numerical range has an open analytic,
   regular, strictly exposed boundary arc (use the analytic eigenbranches of its support
   function as recorded below).  At almost every point (z) of this arc the vector
   \(q=R(y-fx)\) lies in the maximal support eigenspace, whose numerical value is the unique supported point (z).  Hence
   \[
   (y-fx)^*R(y-fx)=0.
   \]
   Using (|f|=1) on the boundary and multiplying by (f) gives
   \[
   c f^2-(a+d)f+b=0.
   \]
   Substitution of (b=0,d=a), boundary analytic continuation, and nonconstancy yield the exact identity
   \[
   \boxed{f(z)=\frac{2\,x^*\operatorname{adj}(zI-A)x}
   {\,y^*\operatorname{adj}(zI-A)x\,}.}
   \]
   Thus a least counterexample has a **rational** proper map from (K^\circ) onto the disk; its boundary is a convex component of a rational lemniscate.  Possible pole cancellations are harmless: item 20 reduces the quotient before locating all zeros and poles.  CCC blocks show that rationality is compatible with genuine disk equality, so the full-level/self-consistency argument, rather than square-zero alone, is essential.

20. **Audit of the positive state, transfer quotient, and full rational lemniscate.**

   - For every (h) with (\operatorname{Re}h\ge0), the one-sided Schur variation (f_t=fe^{-th}) gives
     \[
     \left.\frac d{dt}\right|_{0+}\|f_t(A)x\|^2
     =-2\operatorname{Re}\bigl(x^*T^*Th(A)x\bigr)
     =-8\operatorname{Re}L(h)\le0.
     \]
     Hence (L(1)=1) and positivity imply (\|L\|=1): apply positivity to
     \(1-e^{i\theta}h\) for (\|h\|\le1).  A norm-preserving Hahn--Banach extension to the boundary algebra is represented by a complex measure of total variation (1) and total mass (1); equality in the triangle inequality makes it a positive probability measure.  After conformal transfer to the circle this representing probability is unique, because its nonnegative Fourier moments determine the negative ones by conjugation.
   - Write
     \[
     m(z)=\det(zI-A),\quad
     A_0(z)=x^*\operatorname{adj}(zI-A)x,\quad
     C_0(z)=y^*\operatorname{adj}(zI-A)x.
     \]
     Then (A_0) is monic of degree (N-1), while (\deg C_0\le N-2) because (y^*x=0), and (C_0\not\equiv0).  The transfer (C_0/m=y^*(zI-A)^{-1}x) has no pole cancellation with (m).  A self-contained proof is: if its reduced denominator were a polynomial (q) of degree below (N), its Laurent coefficients would give
     \(y^*A^kq(A)x=0\) for every (k); cyclicity of (y) for (A^*) gives (q(A)x=0), and cyclicity of (x) for (A) gives (q(A)=0), contradicting that the minimal polynomial of cyclic (A) has degree (N).
   - Let (G=\gcd(A_0,C_0)) and reduce the rational extremizer from item 19 as
     \[
     f=P/Q,\qquad P=2A_0/G,\quad Q=C_0/G.
     \]
     Then (\deg P>\deg Q), so (f(\infty)=\infty).  The Cauchy transform
     \[
     \frac{A_0(z)}{m(z)}
       =x^*(zI-A)^{-1}x
       =\int_{\partial K}\frac{d\mu(\zeta)}{z-\zeta}
     \]
     has no zero outside the convex set (K): a strict separating line rotates every
     \(1/(z-\zeta)\) into the open right half-plane.  Hence all zeros of (A_0), and therefore all zeros of the reduced numerator (P), lie in (K).  Because (f) is inner on the boundary, its noncancelled zeros are actually in (K^\circ).  All zeros of the reduced denominator (Q) lie outside (K), since (f) is holomorphic in the interior and continuous and finite on the boundary.
   - Put (U=\{z\in\mathbb C:|f(z)|<1\}).  It is bounded because (\deg P>\deg Q).  Every connected component of (U) contains a zero of (f): the restriction to a component is a proper holomorphic map to the disk, or equivalently, if it had no zero then (\log|f|) would be harmonic with zero boundary values and strictly negative inside.  The original domain (K^\circ) is one component of (U), and every zero of (f) lies in it.  Therefore there are no other components:
     \[
     \boxed{K^\circ=\{z:|f(z)|<1\}.}
     \]
     Finally every point with (|f|=1) is a boundary point of (U) by the open mapping theorem (including critical points).  Thus the **full** rational lemniscate, not merely one oval or an arc, is
     \[
     \boxed{\partial K=\{z:|P(z)|=|Q(z)|\}.}
     \]
     These placement and connectedness assertions survive all cancellations and are the exact geometric input available for the remaining classification.

21. **Full-lemniscate hyperbolicity forces a circle (generic-contact proof; no Pluecker count needed).**
    Retain the least-counterexample setting of items 16--20, and write the reduced rational extremizer as
    \(f=P/Q\), with \(\deg P=n>\deg Q\).  Item 20 proves
    \[
       K^\circ=\{|f|<1\},\qquad \Gamma:=\partial K=\{|f|=1\}.
    \]
    The second equality is the **full** level set, not just one component.  It first implies that
    \(f'(z)\ne0\) for every \(z\in\Gamma\): otherwise, after taking a local logarithm of
    \(f/f(z_0)\), the zero set of its real part at a critical point of order \(m\ge2\)
    has \(2m\ge4\) local rays, whereas a Jordan curve has only two.  Hence \(\Gamma\)
    is a nonsingular real-analytic oval.

    Let
    \[
       H(x,y)=P(x+iy)P^\#(x-iy)-Q(x+iy)Q^\#(x-iy),
    \]
    and choose the complex irreducible factor \(p\) which vanishes on an open arc of
    \(\Gamma\).  It is unique along the whole oval: if the factor changed, two factors
    would vanish at a transition point and \(H=0\) would be singular there.  Conjugation
    makes \(p\) real up to a scalar.  Since every real zero of \(p\) is a zero of \(H\),
    the full-level identity gives
    \[
       C(\mathbb R)=\Gamma
    \]
    for the projective curve \(C=\{p=0\}\); there are no real points at infinity because
    the top form of \(H\) is a nonzero multiple of \((x^2+y^2)^n\).

    Let \(q(w,u,v)\) define the irreducible dual curve \(C^*\).  Every tangent line to
    \(\Gamma=\partial W(A)\) is a support line, so its line coordinates lie on
    \[
       h_A(w,u,v)=\det(wI+u\operatorname{Re}A+v\operatorname{Im}A)=0.
    \]
    Zariski density of the real dual arc gives \(q\mid h_A\).  Since
    \(h_A(1,0,0)=1\), one has \(q(1,0,0)\ne0\), and, for every real \((u,v)\),
    the polynomial \(q(\,\cdot\,,u,v)\) has only real roots because it divides the
    characteristic polynomial of a Hermitian matrix.  Thus \(C^*\) is hyperbolic with
    respect to the dual point representing the line at infinity.

    Choose a generic real normal direction \((u:v)\): the corresponding projective line
    through \((1:0:0)\) meets \(C^*\) transversely and avoids its finite singular set.
    Hyperbolicity makes all \(\deg C^*\) intersection points real.  At a smooth dual
    point the contact point on \(C\) is unique.  Indeed, for a local homogeneous
    parametrization \(r(t)\) of \(C\), its tangent line is
    \(\ell(t)=r(t)\times r'(t)\); both \(\ell(t)\) and \(\ell'(t)\) annihilate
    \(r(t)\), so the tangent to \(C^*\) at \(\ell(t)\) dualizes back to the unique
    point \(r(t)\).  A real smooth dual point therefore has a real contact point:
    conjugation gives another contact, and uniqueness identifies it with the first.
    Consequently all \(\deg C^*\) contacts in the generic direction lie on the sole
    real oval \(\Gamma\).  Since \(K\) is strictly convex, a fixed unoriented tangent
    direction occurs at exactly two boundary points.  Hence
    \[
       \deg C^*=2.
    \]

    The irreducible dual is therefore a conic, and biduality makes \(C\) itself a conic.
    Its real quadratic top form divides the top form \((x^2+y^2)^n\) of \(H\), so it is
    a nonzero multiple of \(x^2+y^2\).  Completing squares shows that \(\Gamma\) is a
    Euclidean circle; because it is the boundary of the compact convex set \(K\),
    \(K\) is the corresponding closed disk of positive radius.

    **Adversarial correction to the earlier Gauss-map route.**  Hyperbolicity of the
    dual does not, without qualification, say that every point in a Gauss-map fiber is
    real: a real line can be tangent at conjugate nonreal points.  The generic smooth-dual
    argument above is what makes the contact unique and hence real.  Also, the earlier
    formula \(\deg C^*=4n+2g-2-R\) tacitly assumes transverse pole fibers at infinity
    and is unsafe when \(P\) has repeated zeros.  Neither assertion is used in this proof.

    An exact degree-two stress test supports the generic-contact step.  For
    \[
       r(z)=\frac{z^2-a^2}{bz}\quad(a,b>0),\qquad t=b^2/a^2,
    \]
    the real level polynomial is
    \[
       F=(x^2+y^2)^2-(2a^2+b^2)x^2+(2a^2-b^2)y^2+a^4.
    \]
    Horizontal tangencies satisfy
    \(F_x=2x(2(x^2+y^2)-2a^2-b^2)=0\).  At \(x=0\), the equation for
    \(Y=y^2\) has discriminant \(b^2(b^2-4a^2)\), so for \(0<t<4\) there
    are nonreal horizontal contacts.  Vertical tangencies satisfy
    \(F_y=2y(2(x^2+y^2)+2a^2-b^2)=0\).  On the second factor one obtains
    \[
       x^2=\frac{a^2t(4-t)}{16},\qquad
       y^2=\frac{a^2(t^2+4t-16)}{16};
    \]
    hence for \(t>4\) there are nonreal vertical contacts.  At the only remaining
    value \(t=4\),
    \[
       F=(x^2+y^2-a^2-2ax)(x^2+y^2-a^2+2ax),
    \]
    a reducible union of two circles.  Thus throughout this broad rational family a
    noncircular irreducible level fails dual hyperbolicity in an explicit real direction.

### Foundational facts (self-contained proof sketches checked)

1. (W(A)) is nonempty and compact: it is the continuous image of the compact unit sphere. It is convex by the Toeplitz–Hausdorff two-dimensional compression argument. Hence, if it has empty interior, it is either a singleton or a line segment.
2. If (W(A)=\{\gamma\}), then (A=\gamma I): for (B=A-\gamma I), (x^*Bx=0) for all (x); the complex polarization identity gives (y^*Bx=0) for all (x,y). Consequently ψ(A)=1, including the positivity convention in the prompt.
3. If (W(A)) lies in a line, then after a complex affine change (A) is Hermitian: the skew-Hermitian part has identically zero quadratic form and hence vanishes by polarization. Thus (A) is normal and ψ(A)=1. Therefore ψ(A)=2 automatically forces (N\ge2) and a numerical range with nonempty planar interior.
4. For (a\ne0,b\in\mathbb C), (W(aA+bI)=aW(A)+b) and ψ(aA+bI)=ψ(A); unitary similarity preserves both; (W(A^*)=\overline{W(A)}) and ψ(A*)=ψ(A), using (q(z)=\overline{p(\bar z)}). Constant nonzero polynomials always give ratio 1.
5. (W(A\oplus B)=\operatorname{conv}(W(A)\cup W(B))) and
   
   \[
   \psi(A\oplus B)\le \max\{\psi(A),\psi(B)\}.
   \]
   
   Equality need not hold because the denominator is taken on the enlarged convex hull.
6. The support function is
   (h_A(\theta)=\lambda_{\max}(\operatorname{Re}(e^{-i\theta}A))), and
   (W(A)=\bigcap_\theta\{z:\operatorname{Re}(e^{-i\theta}z)\le h_A(\theta)\}).
   A closed disk (D(\gamma,\rho)) is characterized by
   (h_A(\theta)=\operatorname{Re}(e^{-i\theta}\gamma)+\rho) for every θ. Merely having one circular boundary arc or one constant-curvature interval does not prove the set is a disk.
7. Boundary eigenvalue reduction: if (Ax=\lambda x), ‖x‖=1, and λ∈∂W(A), choose a supporting direction θ. Equality in the Rayleigh quotient for (H_\theta=\operatorname{Re}(e^{-i\theta}A)) gives (H_\theta x=h_A(\theta)x). Substituting (Ax=\lambda x) yields (A^*x=\bar\lambda x). Thus the eigenspace reduces (A), and iterating gives (A\simeq D\oplus B) with (D) diagonal on boundary eigenvalues and σ(B)⊂int W(A).

### Strict direct-sum obstruction (new symbolic lemma)

Let (r>0), (J_r=\begin{pmatrix}0&2r\\0&0\end{pmatrix}), so (W(J_r)=\overline D(0,r)). Let λ satisfy ∣λ∣>r and set (A=J_r\oplus[\lambda]). Then

\[
W(A)=\operatorname{conv}(\overline D(0,r)\cup\{\lambda\})
\quad\text{is not a disk},\qquad
\boxed{\psi(A)<2}.
\]

Uniform upper bound: for every polynomial (p), the disk inequality for the (2\times2) nilpotent block (proved directly by Schwarz–Pick below) gives
‖p(J_r)‖≤2 sup(_{|z|\le r}|p(z)|), while ∣p(λ)∣≤sup(_{W(A)}|p|); hence ‖p(A)‖≤2 sup(_{W(A)}|p|).

Strictness proof, including nonattainment. Suppose normalized polynomials (p_n), ∣p_n∣≤1 on (K=W(A)), satisfy ‖p_n(A)‖→2. Since the scalar block has norm ≤1, necessarily ‖p_n(J_r)‖→2. Montel gives a subsequence converging locally uniformly on int(K) to (f), ∣f∣≤1. Hence (p_n(0)\to f(0)), (p_n'(0)\to f'(0)), and ‖f(J_r)‖=2. Put (a=f(0)), (b=rf'(0)). Schwarz–Pick on (D(0,r)) gives ∣b∣≤1−∣a∣², while

\[
\left\|\begin{pmatrix}a&2b\\0&a\end{pmatrix}\right\|
=\sqrt{|a|^2+|b|^2}+|b|.
\]

This is at most 2, with equality only when (a=0, |b|=1): if ∣a∣>0 then
√(∣a∣²+(1−∣a∣²)²)<1+∣a∣², giving a strict total (<2). Equality in Schwarz's lemma therefore forces (f(z)=e^{it}z/r) on the disk, hence on all of connected int(K) by the identity theorem. But int(K) contains a point of modulus (>r), contradicting ∣f∣≤1. This proves a genuine strict gap without assuming the universal conjecture.

The same normal-family proof excludes any finite direct sum of (2\times2) extremal Jordan disk blocks and scalar blocks whenever their convex-hull numerical range is not one of the component disks: a subsequence must be driven by one Jordan block, and equality forces the limiting function to be the affine disk map on the whole enlarged interior.

### Equality extraction from the Lorist–Schwenninger dilation lemma (new, exact)

Assume an exact double-layer/Stinespring model is available for a normalized extremal (f): (T=f(A)), ‖T‖=2, (Q) contractive, (V) isometric,

\[
E_n=2V^*Q^{*n}V-T^{*n},\qquad E_nT=TE_n,
\]

and ρ(T)<1. Let (x) be a unit right singular vector, (T^*Tx=4x), put (y=Tx/2), and define (u=Q^*VTx-2Vx), (m_n=\operatorname{Re}\langle E_nT^nx,x\rangle). At κ=2 the proof of the dilation lemma gives

\[
d_n:=2m_n-m_{n+1}
=2\left\|T^{*n}x-\tfrac12V^*Q^{*n}u\right\|^2
-\tfrac12\|V^*Q^{*n}u\|^2
\ge-\tfrac12\|u\|^2.
\]

Telescoping yields (2m_1=\sum_{n\ge1}2^{-n+1}d_n\ge-\|u\|^2). The other terminal estimate is ‖u‖²≤−2m₁. Hence equality holds in both. Writing each summand's slack as

\[
2\left\|T^{*n}x-\tfrac12V^*Q^{*n}u\right\|^2
+\tfrac12(\|u\|^2-\|V^*Q^{*n}u\|^2),
\]

positive weights and zero total force both terms to vanish for every (n). Since ρ(T)<1 in finite dimension, (T^{*n}x\to0); therefore

\[
\boxed{u=0,\quad m_1=0,\quad T^*x=0.}
\]

With (y=Tx/2), (Q^*Vy=Vx). Since (x,y) and hence (Vx,Vy) are unit and (Q) is contractive, equality in Cauchy–Schwarz gives (Vy=QVx). In the boundary multiplication model this is the pointwise identity

\[
\boxed{P(\sigma)^{1/2}(y-f(\sigma)x)=0\quad\text{for a.e. }\sigma\in\partial W(A).}
\]

Applying the same argument to (A^*) and (q(z)=\overline{f(\bar z)}) gives (Ty=0). Thus (T) has a reducing (2J_2) singular block on \(\operatorname{span}\{x,y\}\), though its complementary block need not have numerical radius ≤1.

For any analytic (h), define

\[
L(h)=x^*h(A)x,\qquad \delta(h)=y^*h(A)x.
\]

Using (T=f(A)), (T^*x=0), (Tx=2y), and (T^*y=2x), one obtains exactly

\[
L(hf)=0,\qquad \delta(hf)=2L(h),\qquad
x^*h(A)y=0,\qquad y^*h(A)y=L(h).
\]

Therefore every analytic functional-calculus compression to \(S=\operatorname{span}\{x,y\}\) is equal-diagonal triangular:

\[
P_Sh(A)|_S=\begin{pmatrix}L(h)&0\\ \delta(h)&L(h)\end{pmatrix}
\quad\text{in the ordered basis }(x,y).
\]

### Complete rigidity when the extremal Blaschke degree is one (new theorem)

Let (K=W(A)) have interior, and suppose the equality extremizer (f:K^\circ\to\mathbb D) furnished above has Blaschke degree one, hence is a conformal bijection, with (f(z_0)=0). For every analytic (h), division by the simple zero gives (h=h(z_0)+fg). The preceding identities imply

\[
L(h)=h(z_0),\qquad \delta(h)=\frac{2h'(z_0)}{f'(z_0)}.
\]

Taking (h(z)=z), the compression of (A) to (S) has numerical range

\[
\overline D\!\left(z_0,\frac1{|f'(z_0)|}\right)\subset K.
\]

The radius on the left is the conformal radius of (K^\circ) at (z_0). Restrict (f) to this contained Euclidean disk and rescale it to a self-map of ℝ. Its derivative at the origin has modulus one, so equality in Schwarz's lemma makes it a rotation. The identity theorem then makes (f) affine on all of (K^\circ), and surjectivity onto ℝ gives

\[
\boxed{K=\overline D\!\left(z_0,1/|f'(z_0)|\right).}
\]

Thus the full assertion is proved for every equality case whose extremal finite Blaschke product has degree one. Higher-degree inner extremizers (which genuinely occur for disk/Crabb–Choi–Crouzeix examples) remain the substantive case.

### Further boundary equation under strict convexity

At a smooth boundary point σ with outward unit normal (n), support value (h=\operatorname{Re}(\bar n\sigma)), and (R=(\sigma I-A)^{-1}),

\[
P(\sigma)=\frac1\pi R^*\bigl(hI-\operatorname{Re}(\bar nA)\bigr)R.
\]

Hence the pointwise equality says (q=R(y-fx)) is a maximal support eigenvector. If (K) is strictly convex, its numerical value is the unique supported point σ, and therefore

\[
(y-f(\sigma)x)^*R(\sigma)(y-f(\sigma)x)=0.
\]

On ∂K, ∣f∣=1. Multiplying the expanded identity by (f(\sigma)\det(\sigma I-A)), then using the maximum principle, yields throughout (K^\circ)

\[
B(z)f(z)^2-C(z)f(z)+D(z)=0,
\]

where

\[
B=y^*\operatorname{adj}(zI-A)x,\quad
C=x^*\operatorname{adj}(zI-A)x+y^*\operatorname{adj}(zI-A)y,\quad
D=x^*\operatorname{adj}(zI-A)y.
\]

Thus a strictly-convex nondisk equality case would require its extremal inner function to be algebraic of degree at most two over \(\mathbb C(z)\). This strongly excludes generic numerical-range boundaries (e.g. the noncircular ellipse Riemann map is transcendental) but does not alone exclude convex algebraic/quadrature domains.

The quadratic conclusion actually collapses to a rational one after using the adjoint endpoint identity.  Since (Ty=0), for every holomorphic (h) we have
\[
x^*h(A)y=\tfrac12y^*Th(A)y=\tfrac12y^*h(A)Ty=0.
\]
Hence (x^*(zI-A)^{-1}y=0) identically, so
\[
D(z)=x^*\operatorname{adj}(zI-A)y\equiv0.
\]
The boundary equation therefore gives, by analytic continuation from any curved boundary arc,
\[
\boxed{
f(z)=\frac{C(z)}{B(z)}
=\frac{x^*\operatorname{adj}(zI-A)x+y^*\operatorname{adj}(zI-A)y}
{y^*\operatorname{adj}(zI-A)x}.}
\]
Thus every nonpolygonal equality case to which the exact boundary-kernel argument applies has a **rational** extremal proper map, rather than merely an algebraic one.  Moreover
\[
y^*(zI-A)^{-1}x=(y^*Ax)z^{-2}+O(z^{-3}),\qquad
x^*(zI-A)^{-1}x+y^*(zI-A)^{-1}y=2z^{-1}+O(z^{-2}),
\]
so the rational map has a simple pole at infinity whenever (y^*Ax\ne0).  This reduces the remaining curved-boundary candidates to rational lemniscate numerical ranges.  It does not by itself imply a disk: convex noncircular lemniscates exist (for example sufficiently round Cassini ovals).

**Global inverse-map warning.**  Kato, *Some Mapping Theorems for the Numerical Range*, https://doi.org/10.3792/pja/1195522286, Theorem 1 uses the convex kernel of the **full** rational preimage (f^{-1}(E')), not a selected univalent component.  Thus, for instance, from (W(C)\subset\overline{\mathbb D}) and a convex univalent polynomial (g(w)=w+aw^2) one cannot infer (W(g(C))\subset g(\overline{\mathbb D})): the other component of the full polynomial preimage makes Kato's convex-kernel hypothesis fail.  This blocks a tempting but invalid construction of higher-degree counterexamples.

### Removing boundary-regularity and polygon loopholes in the rational-collapse step

For a finite matrix, put
\[
h(\theta)=\lambda_{\max}\!\bigl(\operatorname{Re}(e^{-i\theta}A)\bigr).
\]
Rellich's theorem (or the characteristic polynomial plus analytic continuation) gives finitely many real-analytic eigenvalue branches; after identical branches are merged, (h) is their pointwise maximum and has only finitely many switching angles.  On an interval on which (h) is analytic, the exposed boundary point is
\[
\sigma(\theta)=e^{i\theta}(h(\theta)+ih'(\theta)),\qquad
\sigma'(\theta)=ie^{i\theta}(h+h'').
\]
Convexity gives (h+h''\ge0).  If this quantity vanishes identically on every analytic interval, (\sigma) is constant on each such interval and the numerical range is a polygon.  Otherwise analyticity gives an open subinterval on which (h+h''>0); this is a regular real-analytic strictly convex arc, and every supporting line there exposes the unique point (\sigma(\theta)).  Thus every nonpolygonal numerical range has the open arc needed for the rational-collapse argument.  The finitely many spectral points can be deleted from the arc.

The a.e. double-layer kernel identity is enough on that arc.  For almost every (\sigma) there, (q=(\sigma I-A)^{-1}(y-f(\sigma)x)) lies in the top support eigenspace.  Uniqueness of the exposed point gives (q^*Aq=\sigma\|q\|^2), hence ((y-fx)^*(\sigma I-A)^{-1}(y-fx)=0).  Continuity makes the resulting rational boundary identity valid on the whole subarc.  After (D\equiv0), the disk-algebra function (Bf-C) has zero boundary values on a nontrivial arc.  Composing with a Riemann map and using the elementary boundary uniqueness theorem for the disk algebra (Schwarz reflection across a zero boundary arc) gives (Bf-C\equiv0) in the interior.  No global smoothness or strict convexity is required.

The polygon case cannot support equality.  At every polygon vertex (\lambda), two independent supporting directions show that any unit vector with (x^*Ax=\lambda) satisfies both (Ax=\lambda x) and (A^*x=\bar\lambda x).  Iteration splits all boundary eigenvalues as a normal diagonal summand.  The remaining block has spectrum in the polygon interior and numerical range properly smaller than the polygon (it contains no vertex).  Split in turn its eigenvalues on the boundary of its own numerical range; the scalar summands contribute relative norm at most one.  For the surviving block (B), its spectrum lies in (W(B)^\circ\subsetneq K^\circ).  Crouzeix's strict domain monotonicity (2004, Lemma 2.2) and the now-proved universal bound give
\[
\psi_{K^\circ}(B)<\psi_{W(B)^\circ}(B)\le2
\]
unless the inner constant is one, in which case strictness is unnecessary.  Hence the direct sum has relative constant strictly below two.  Consequently an equality case is nonpolygonal and the rational formula above always applies.

### Hyperbolic-dual obstruction: a precise intermediate lemma

Let (\Gamma) be an irreducible real algebraic component of a rational lemniscate, let (X) be its normalization, and let (G:X\to\mathbb P^1) send a smooth point to its unoriented tangent direction.  If (\Gamma^*) divides a Hermitian characteristic determinant, then (\Gamma^*) is hyperbolic with respect to the dual point representing the line at infinity.  Equivalently, every fiber of (G) over (\mathbb RP^1) consists entirely of real points.  A local coordinate proof shows that (G) has no ramification on (X(\mathbb R)): a real ramification of order (>1) would give nearby real target values with nonreal inverse branches.  Thus (G|_{X(\mathbb R)}) is a covering.

If the unit level of a degree-(n) primitive rational map is regular, it has (r\le n) oval components (the positive covering degrees over a generic unimodular value sum to (n)).  Each oval has turning number one, so its unoriented tangent map has degree two.  Hyperbolicity would therefore force
\[
\deg(\Gamma^*)=2r\le2n.
\]
On the other hand, viewing the normalization as a bidegree-((n,n)) curve in (\mathbb P^1\times\mathbb P^1), the parametrized Pluecker formula gives
\[
\deg(\Gamma^*)=4n+2g-2-R,
\]
where (g) is the genus and (R) is the common ramification of the two coordinate projections.  Riemann--Hurwitz gives (R\le2g+2n-2), hence
\[
\deg(\Gamma^*)\ge2n.
\]
Therefore hyperbolicity can occur only in the equality case: every ramification point of either coordinate projection must be a common ramification point.  For an equation (r(z)r^\#(w)=1), this means that every fiber reciprocal to a critical value of (r) consists entirely of critical points.  The remaining theorem-strength task is to prove that, after passing to Cartwright's primitive rational generator of the lemniscate, this total-ramification equality forces degree (n=1) (the circle).  Reducible levels and singular real components must be included in that classification; without it, the hyperbolicity route is not yet complete.

### State positivity, minimal transfer realization, and the full rational lemniscate (independent audit)

Assume the least-counterexample reduction and the equality extraction above.  Thus
\(K=W(A)\) has nonempty interior \(\Omega\), \(\sigma(A)\subset\Omega\), the
normalized extremizer \(f\in A(K)\) is nonconstant and inner
(\(|f|=1\) on \(\partial K\)), and for orthonormal vectors \(x,y\)
\[
 T=f(A),\qquad Tx=2y,\qquad T^*y=2x.
\]
In the least-dimensional case, \(x\) is cyclic for \(A\) and \(y\) is cyclic
for \(A^*\).  The rational-collapse identity is
\[
 f(z)\,y^*(zI-A)^{-1}x=2x^*(zI-A)^{-1}x . \tag{20.1}
\]
The following checks close all analytic and cancellation qualifications in the
passage from (20.1) to a statement about the **full** rational lemniscate.

**Positivity of the extremal state.**  Define
\(L(h)=x^*h(A)x\) on \(A(K)\).  If \(\operatorname{Re}h\ge0\) on \(K\), then,
for \(t\ge0\),
\[
 f_t=f e^{-th}\in A(K),\qquad \|f_t\|_K\le1.
\]
The polynomial bound \(2\) extends from polynomials to \(A(K)\) by Mergelyan
approximation, so \(\|f_t(A)\|\le2\).  Since
\(y^*T=2x^*\),
\[
 y^*f_t(A)x
 =y^*T e^{-t h(A)}x
 =2x^*e^{-t h(A)}x
 =2\{1-tL(h)+O(t^2)\}.
\]
Taking absolute values and using \(|y^*f_t(A)x|\le2\) gives
\[
 \operatorname{Re}L(h)\ge0. \tag{20.2}
\]
This is a one-sided variation only; no assumption that the original polynomial
supremum is attained has entered.

For arbitrary \(h\in A(K)\), rotate so that
\(e^{-i\theta}L(h)=|L(h)|\).  Since
\(\|h\|_K-\operatorname{Re}(e^{-i\theta}h)\ge0\), (20.2) yields
\(|L(h)|\le\|h\|_K\).  Also \(L(1)=1\).  By the maximum principle the
restriction of \(A(K)\) to \(\partial K\) is isometric.  Extend \(L\), with
the same norm, to \(C(\partial K)\), and apply the Riesz representation theorem.
The resulting complex measure \(\nu\) has
\(\|\nu\|=\nu(\partial K)=1\).  Equality in the triangle inequality for the
polar decomposition of \(\nu\) forces its phase to be \(1\) almost everywhere.
Consequently there is a probability measure \(\mu\) on \(\partial K\) such that
\[
 L(h)=\int_{\partial K}h(\zeta)\,d\mu(\zeta)
 \quad(h\in A(K)). \tag{20.3}
\]

**The diagonal Cauchy transform has no zero off the convex body.**  Put
\[
 a(z)=x^*(zI-A)^{-1}x
     =\int_{\partial K}\frac{d\mu(\zeta)}{z-\zeta}
     \qquad(z\notin K). \tag{20.4}
\]
For \(z\notin K\), strict separation from the compact convex set \(K\) supplies
a unimodular \(\eta\) and \(\delta>0\) with
\(\operatorname{Re}(\eta(z-\zeta))\ge\delta\) for every \(\zeta\in K\).
Writing \(w=\eta(z-\zeta)\), one has
\[
 \operatorname{Re}\{\overline\eta a(z)\}
 =\int_{\partial K}\operatorname{Re}\frac1w\,d\mu(\zeta)
 =\int_{\partial K}\frac{\operatorname{Re}w}{|w|^2}\,d\mu(\zeta)>0.
\]
Thus
\[
 a(z)\ne0\qquad(z\notin K). \tag{20.5}
\]
Convexity and positivity are both essential in this argument.

**Polynomial degrees and cancellation.**  Let
\[
 m(z)=\det(zI-A),\quad
 A_0(z)=x^*\operatorname{adj}(zI-A)x,\quad
 C_0(z)=y^*\operatorname{adj}(zI-A)x.
\]
Then \(m\) is monic of degree \(N\), \(A_0\) is monic of degree \(N-1\),
and \(\deg C_0\le N-2\), because \(x^*x=1\) and \(y^*x=0\).
Moreover \(C_0\not\equiv0\), by (20.1).  Equation (20.1) is exactly
\[
 C_0 f=2A_0\quad\hbox{on }\Omega. \tag{20.6}
\]

The transfer function \(c=C_0/m=y^*(zI-A)^{-1}x\) is a minimal scalar
realization: \(\gcd(C_0,m)=1\).  Indeed, if cancellation gave
\(c=p/q\) with \(\deg q<N\), the polynomial identity
\[
 q(z)(zI-A)^{-1}=S_q(z,A)+(zI-A)^{-1}q(A)
\]
would show that \(y^*(zI-A)^{-1}q(A)x\) is both a polynomial and \(O(z^{-1})\),
hence zero.  Its Laurent coefficients give
\(y^*A^kq(A)x=0\) for all \(k\ge0\).  Cyclicity of \(y\) for \(A^*\) gives
\(q(A)x=0\), and cyclicity of \(x\) for \(A\) then gives \(q(A)=0\).
But a cyclic \(N\)-dimensional matrix has minimal polynomial of degree \(N\),
contradicting \(\deg q<N\).

Let \(G=\gcd(A_0,C_0)\), and reduce (20.6) as
\[
 P=2A_0/G,\qquad Q=C_0/G,
 \qquad f=P/Q\quad\hbox{on }\Omega. \tag{20.7}
\]
Then \(P,Q\) are coprime and
\[
 \deg P=N-1-\deg G>\deg Q, \tag{20.8}
\]
so the rational continuation tends to infinity at infinity.  Formula (20.5),
together with \(a=A_0/m\) and \(\sigma(A)\subset K\), says that every zero of
\(A_0\), hence every zero of \(P\), lies in \(K\).  Since (20.6) extends
continuously to \(K\), coprimeness shows that \(Q\) has no zero in \(K\).
Finally a zero of \(P\) on \(\partial K\) would give \(f=0\) there, contrary
to \(|f|=1\).  Therefore
\[
 \boxed{\text{all zeros of }P\text{ lie in }\Omega,
 \qquad\text{all finite poles (zeros of }Q\text{) lie outside }K.} \tag{20.9}
\]

**There are no unused lemniscate components.**  Set
\[
 U=\{z\in\mathbb C:|P(z)|<|Q(z)|\}.
\]
It is bounded by (20.8).  The inner property and (20.7) show that
\(\Omega\subset U\) and \(\partial K\cap U=\varnothing\), so the connected set
\(\Omega\) is one whole component of \(U\).

Every component \(V\) of \(U\) contains a zero of \(P\).  To see this without
any boundary regularity, the rational map \(r=P/Q\) is holomorphic on \(V\) and
defines a proper map \(V\to\mathbb D\): if \(r(z_j)\) stays in a compact subset
of \(\mathbb D\), boundedness of \(U\) gives a convergent subsequence; its limit
cannot be a pole and cannot lie on \(\partial V\), where continuity of
\(|P|-|Q|\) gives \(|r|=1\).  Hence the limit remains in \(V\).  The image
\(r(V)\) is open by the open mapping theorem and closed relative to
\(\mathbb D\) by properness.  It is therefore all of \(\mathbb D\), and in
particular \(V\) contains a preimage of zero.  By (20.9) every zero of \(P\)
already lies in the component \(\Omega\).  Thus
\[
 U=\Omega. \tag{20.10}
\]

Finally, coprimeness implies that \(Q\ne0\) at every point of
\(\{|P|=|Q|\}\).  The open mapping theorem applied locally to the nonconstant
rational function \(P/Q\) shows that every such point is approached both by
points with modulus below one and by points with modulus above one, even at a
critical point.  Conversely, continuity puts every boundary point of \(U\) on
the equality level.  Combining this with (20.10) gives the global identity
\[
 \boxed{\partial K=\partial\Omega
       =\{z\in\mathbb C:|P(z)|=|Q(z)|\}.} \tag{20.11}
\]
This is the entire rational lemniscate, not merely the oval traced by the
original conformal boundary map.  No attainment by a polynomial, smoothness of
\(\partial K\), or unproved assertion about other inverse-image components is
used.

## Failed claims and counterchecks

- (A=[1]\oplus\begin{psmallmatrix}0&\alpha\\0&0\end{psmallmatrix}) with (0<\alpha<2) has a manifestly nondisk numerical range and a conformal-strip test function giving (\pi/2), but its ratio is **strictly below (2)** by the conformal-radius estimate above.
- Adding any scalar or normal block outside an extremal Jordan disk enlarges the denominator; it does not preserve equality. If the added block stays inside the disk, the full numerical range remains the same disk.
- Finite nilpotent weighted shifts and CCC blocks do attain monomial factor (2), but rotational unitary similarity makes their numerical ranges disks. Cyclic weighted shifts with all weights nonzero are diagonalizable and therefore have (\psi<2); if a weight vanishes the numerical range reduces to the disk case.
- A symbolic disk-model search with (A=\begin{psmallmatrix}0&0&0\\-\sqrt2&0&1\\1&0&1/\sqrt2\end{psmallmatrix}) and (f(z)=z(z-1/\sqrt2)/(1-z/\sqrt2)) gives (f(A)=2e_{21}), but direct support-function calculation gives (W(A)=\overline{\mathbb D}). It is an exact polynomial-preimage prototype after rational approximation, not a nondisk counterexample.
- Natural block companions satisfying (p(A)=2J_2\oplus C) numerically approach ratio (2) only under singular/divergent similarities; finite well-conditioned instances stay strictly below (2). The dual-degree argument explains exact failure for the low-dimensional simple-root cases. This route is `blocked` beyond the degree threshold absent an explicit high-dimensional determinantal representation that also enforces the norm equality.

### Quadratic polynomial-preimage mechanism is impossible in every dimension (strengthened obstruction)

Let a normalized attained extremal be a quadratic polynomial.  After an affine change its boundary level curve is a noncritical connected Cassini oval
\[
 C:\quad ((x-c)^2+y^2)((x+c)^2+y^2)=R^2,
 \qquad c>0,\quad R>c^2.
\]
(The case (c=0) is a circle, while the critical/disconnected cases cannot be the boundary of a convex body with interior.)  The complex projective curve (C) is irreducible, hence so is its dual (C^*).  If an open arc of (C) is the boundary of a finite matrix numerical range, the corresponding open dual arc lies in the Kippenhahn determinant
\[
 h_A(w,u,v)=\det(wI+u\operatorname{Re}A+v\operatorname{Im}A).
\]
Zariski density then forces the defining polynomial of (C^*) to divide (h_A).  Since (h_A(\,\cdot\,,u,v)) is the characteristic polynomial of a Hermitian matrix for real (u,v), every real factor with nonzero value at ((1,0,0)) must be hyperbolic with respect to ((1,0,0)).

But (C^*) is not hyperbolic.  Indeed
\[
 F_y=4y(x^2+y^2+c^2).
\]
Complex vertical tangencies with (y=0) satisfy
\[
 (x^2-c^2)^2=R^2.
\]
Besides the two real vertical tangencies (x=\pm\sqrt{c^2+R}), this gives
\[
 x=\pm i\sqrt{R-c^2}.
\]
Thus the dual polynomial specialized to vertical normal ((u,v)=(1,0)) has the nonreal roots (w=-x), contradicting hyperbolicity.  Consequently **no noncircular quadratic polynomial extremal can realize equality for a finite matrix, in any size**.  In particular this closes the commutant family
\[
 A=\begin{pmatrix}a&b&c_0\\0&a&0\\0&d&e\end{pmatrix},
 \qquad (z-a)(z-e)(A)=(b(a-e)+c_0d)e_{12},
\]
and all higher-dimensional quadratic companion variants, provided the polynomial really is an attained ratio-(2) extremal.  The hypothesis is essential: a general equality extremizer supplied by the finite-dimensional extremal theorem is (B\circ\varphi), not necessarily a polynomial, so this does not by itself settle the main assertion.

### Exact compression inside the defective three-dimensional candidate

For the defective family (A_t) from Åhag--Czyż--Perälä--Virtanen, in the real-symmetric model used in that paper put
\[
 u_t=(\sqrt{1-2t},i,-\sqrt{2t})^{\mathsf T},\quad
 x=\overline{u_t}/\sqrt2,\quad y=u_t/\sqrt2.
\]
Then (x,y) are orthonormal and direct multiplication gives
\[
 [x\ y]^*A_t[x\ y]=
 \begin{pmatrix}-t&0\\-2t&-t\end{pmatrix}.
\]
Hence the exact disk (\overline D(-t,t)) is contained in (W(A_t)).  Also
\[
 (A_t+tI)(A_t-(2t-1)I)=t(1-t)u_tu_t^{\mathsf T},
\]
so its normalized polynomial image is already a half-radial rank-one nilpotent.  This explains why the family is a genuine higher-Blaschke-degree candidate.  The contained-disk Schwarz--Pick bound is not strong enough to exclude equality: the necessary value
\[
 |f_t'(-t)|=\frac{|1-3t|}{t(1-t)}
\]
 is strictly below the elementary one-zero disk bound (1/t), and, when (2t-1\in D(-t,t)), also below the corresponding two-zero disk bound.  A quantitatively larger explicit subdomain or a new equality identity is required.

### The defective three-dimensional candidate is strictly below two (boundary-kernel closure)

The exact equality identity in item 15 supplies the missing mechanism.  Use the unitarily equivalent model
\[
 \widetilde A_t=\begin{pmatrix}
 0&i\mu&0\\ i\mu&0&i\sqrt2r\\0&i\sqrt2r&-1
 \end{pmatrix},\qquad
 \mu=t\sqrt{1-2t},\quad r=(1-t)\sqrt t,
\]
and put
\[
 u=(\sqrt{1-2t},i,-\sqrt{2t})^{\mathsf T},\qquad
 x=\overline u/\sqrt2,\quad y=u/\sqrt2.
\]
The polynomial identity above says that any normalized equality extremizer must satisfy (f(\widetilde A_t)=2yx^*).  On the relative interior of the flat boundary segment (\operatorname{Re}z=0), the outward normal is (n=1) and
\[
 H_z=\operatorname{Re}(zI-\widetilde A_t)=\operatorname{diag}(0,0,1).
\]
Writing (R(z)=(zI-\widetilde A_t)^{-1}), the double-layer kernel is (P(z)=\pi^{-1}R(z)^*e_3e_3^*R(z)).  Therefore
\(P(z)^{1/2}(y-f(z)x)=0) implies
\[
 f(z)=\frac{e_3^*R(z)y}{e_3^*R(z)x}
 =:R_t(z)
 =\frac{(z+t)(z+1-2t)}{(z-t)(z+2t-1)}
\]
for almost every point of that open segment.  The Riemann map, hence the finite-Blaschke extremizer, extends analytically across an open straight boundary segment by Schwarz reflection.  Thus continuity and the identity theorem force (f\equiv R_t) throughout the numerical-range interior.

This is impossible by exact arithmetic.  The poles (t) and (1-2t) lie in the open right half-plane, so (R_t) is holomorphic on the numerical range, but direct functional calculus gives
\[
 \boxed{R_t(\widetilde A_t)=yx^*,\qquad \|R_t(\widetilde A_t)\|=1,}
\]
whereas equality requires (f(\widetilde A_t)=2yx^*).  Equivalently,
\[
 R_t'(-t)=\frac{3t-1}{2t(t-1)},
\]
whose modulus is exactly one half of the necessary derivative.  The double-root value (t=1/3) follows by the same rational identity (and was independently excluded in the source).  Consequently
\[
 \boxed{\psi(A_t)<2\quad(0<t<1/2).}
\]
This closes the last defective (3\times3) family left open in Åhag--Czyż--Perälä--Virtanen and, combined with their exact reductions (or a self-contained reproduction of those reductions), proves disk rigidity in dimension three.

### General exclusion of flat boundary edges in a least counterexample

The preceding parameter calculation is subsumed by a general argument.  Let a least-dimensional nondisk equality case have an open boundary edge
\[
 \{z:\operatorname{Re}(\overline nz)=h\}\cap\partial W(A),
 \qquad
 H:=hI-\operatorname{Re}(\overline nA)\succeq0,
\]
where the outward normal (n) and hence (H) are constant along the edge.  Item 15 and the cyclic reduction give, almost everywhere on its relative interior,
\[
 H^{1/2}(zI-A)^{-1}(y-f(z)x)=0,
\]
or equivalently
\[
 H(zI-A)^{-1}y=f(z)H(zI-A)^{-1}x. \tag{F}
\]
The finite-Blaschke extremizer extends analytically across an open straight boundary arc by Schwarz reflection.  Both sides of (F) therefore extend across the edge; boundary agreement and the identity theorem make (F) valid throughout the numerical-range interior.

Let (g) be any function holomorphic near the numerical range.  Integrating (F) on a contour surrounding the spectrum gives
\[
 Hg(A)y=H(fg)(A)x.
\]
But (f(A)x=2y) and commutativity of the functional calculus make the right side equal to (2Hg(A)y).  Hence
\[
 Hg(A)y=0\qquad\text{for every }g.
\]
Taking (g(\zeta)=\zeta^k) first gives (HA^ky=0) for every (k).  Expanding the resolvent at infinity and then using rational continuation yields
\(H(zI-A)^{-1}y=0\) off the spectrum.  Equation (F) therefore gives
\(f(z)H(zI-A)^{-1}x=0\).  Since (f) is nonzero, analytic continuation and another expansion at infinity yield
\[
 Hg(A)x=0\qquad\text{for every }g.
\]
The maximizing vector (x) is cyclic for (A) by item 16, so these vectors span the whole space and force (H=0).  This says
\(\operatorname{Re}(\overline nA)=hI\), hence the entire numerical range lies on one line, contrary to (\psi(A)=2).  Therefore
\[
\boxed{\text{a least-dimensional nondisk equality case has no boundary line segment.}}
\]
Since a compact convex numerical range with interior is non-strictly convex exactly when its boundary contains a nontrivial segment, its boundary must be strictly convex.  This makes the quadratic boundary relation recorded above applicable globally at every regular support point.

### Conformal/operator failure modes

- **Invalid mapping inclusion.** The tempting assertion (w(\phi(A))\le1\) for a Riemann map \(\phi:W(A)^\circ\to\mathbb D\) is not an available numerical-range mapping theorem.  Combined with Berger plus Okubo–Ando and von Neumann, it would immediately imply the full constant-(2) theorem.  Treating it as elementary is circular.
- **A (2)-spectral disk bound plus \(\|T\|=2\) does not make (T) half-radial.** Nonnormal involutions (T^2=I) can be scaled/tuned so their disk polynomial bound and \(\|T\|\) are both (2), while (w(T)>1) and (W(T)) is a noncircular ellipse.  Thus from an extremizer (F=f(A)) one cannot infer (W(F)=\mathbb D\) merely from \(\|F\|=2\) and \(\|q(F)\|\le2\|q\|_{\mathbb D}\).
- **Orthogonal extremal singular vectors are insufficient.** Extremality gives \(\langle f(A)x,x\rangle=0\), but the half-radial characterization additionally needs (w(f(A))=1\); no such bound follows from orthogonality alone.
- **Configuration-constant direction is wrong for strict-(2).** Since (a(\Omega)\ge0\), (1+\sqrt{1+a(\Omega)}\ge2\).  Its strictness below (1+\sqrt2) cannot be repurposed as strictness below (2).
- **Domain-constant quantifier swap.** (C_\Omega(2)=2\Rightarrow\Omega\) disk does not say that a fixed higher-dimensional (A) with \(\psi(A)=2\) has disk numerical range.
- **No maximum-polynomial shortcut.** The polynomial supremum can be attained only after passing to the bounded-holomorphic normal-family compactification.  Equality arguments must apply to that limit and justify polynomial approximation back to the original definition.
- **Similarity versus scalar polynomial bound.** Okubo–Ando/Paulsen similarity constants control complete polynomial bounds; scalar polynomial bounds can be strictly smaller than the best similarity condition number already for (3\times3) matrices (Crouzeix–Gilfeather–Holbrook, https://perso.univ-rennes1.fr/michel.crouzeix/publis/cgh11.pdf).  Equality of \(\psi(A)\) cannot be converted automatically into equality in a similarity theorem.

- **False route: add an exterior scalar to an extremal Jordan block.** Although (J_r) alone has ψ=2 and the direct sum retains the elementary all-polynomial upper bound 2, the strict lemma above proves the enlarged nondisk hull has ψ<2. It also shows why an asymptotically extremizing polynomial sequence cannot evade the maximum principle.
- **False route: infer polynomial inequalities from a (2\times2) compression.** In general (p(PAP)\ne Pp(A)P). For (A=\begin{pmatrix}0&1\\1&0\end{pmatrix}) and projection (P) onto the first coordinate, ((PAP)^2=0) but (PA^2P=P). Only reducing summands support the needed functional-calculus comparison.
- **False route: use (W(p(A))\subset p(W(A))).** No such numerical-range spectral mapping theorem holds in general; if it did, ‖B‖≤2w(B) would immediately prove the former Crouzeix conjecture. Thus half-radial rigidity of (p(A)) cannot be invoked without separately proving (w(p(A))\le\max_{W(A)}|p|).
- **False converse:** a disk numerical range need not have ψ=2. Crouzeix–Greenbaum's weighted-shift example (M(2\sin\varphi,2\cos\varphi,0)) has unit-disk numerical range and ψ (=2\max(\sin\varphi,\cos\varphi,\sin2\varphi)), which is (<2) away from φ=0,π/4,π/2.
- **Equality-chain warning:** in Lorist–Schwenninger's sharp universal proof, substituting κ=2 into the decisive last inequality annihilates both sides. No equality condition follows from that chain; treating every intermediate inequality as equality would be invalid.
- **Geometric warning:** for compact convex numerical ranges, a boundary equal to a circle does imply the filled disk, but a single circular arc, disk containment, or equality of one support value does not. A boundary circle is never itself a numerical range unless interpreted together with its filled convex hull.

### Final independent audit of the equality and dual steps (2026-08-30)

- The sharp-dilation recurrence was rederived without importing an equality
  characterization.  From (E_nT=TE_n) and (T^*Tx=\kappa^2x), one gets
  exactly
  \[
  \kappa m_n-m_{n+1}=\kappa(\kappa-1)\|T^{*n}x\|^2
   -2\operatorname{Re}\langle \mathcal V^*\mathcal M^{*n}u,T^{*n}x\rangle.
  \]
  At \(\kappa=2\), the two terminal inequalities force equality, so the
  positive weighted sum of the displayed square-completion slacks is zero.
  The spectral-radius hypothesis then gives (u=0) and (T^*x=0).  Thus the
  boundary-kernel identity used later is a genuine equality consequence, not
  an inference from a vanishing final bound.
- Resolvent entries (a(z),c(z)) are meromorphic, not holomorphic, on the
  numerical-range interior.  The correct rational-collapse argument first
  proves (cf-2a=0) in a spectrum-free collar of the analytic boundary arc,
  and then uses connectedness of
  \(\Omega\setminus\operatorname{spec}(A)\) to obtain the meromorphic identity
  throughout \(\Omega\).  The final manuscript was amended accordingly.
- The dual-degree count was independently rederived with the two necessary
  genericity exclusions.  For a generic real normal, the specialization of
  the irreducible hyperbolic dual equation has its full degree in (s), has
  distinct roots, and avoids both the singular dual locus and the finitely
  many Gauss-critical images.  Every root is then a smooth real dual point;
  its real gradient is the unique primal contact.  Since the primal real
  locus is the one strictly convex oval, only the maximum and minimum support
  contacts occur.  Hence the dual degree is exactly two.  This avoids the
  false assertion that hyperbolicity alone makes contacts at singular real
  bitangents real, and it makes the earlier Pluecker/Harnack count unnecessary.

### Final resolution and deliverable (2026-08-30)

- The assertion is true in every finite size.  The self-contained proof,
  including the universal all-polynomial upper bound \(2\), nonattaining
  extremizing sequences, all numerical-range degeneracies, the two-stage
  boundary-spectrum induction, rational collapse, and the hyperbolic-dual
  circle argument, is in
  /home/server/Documents/DiskRigidity/LaTeX/disk_rigidity.tex.
- Three independent presumptively-false audits rederived the dilation
  recurrence and equality slacks, the Schur/Montel and strict-domain steps,
  the state/Cauchy-transform and full-level steps, and the generic real-contact
  count.  The only substantive defect found during the final pass was the
  initial treatment of resolvent entries as holomorphic across the spectrum;
  the deliverable uses the corrected meromorphic identity on the connected
  punctured domain.
