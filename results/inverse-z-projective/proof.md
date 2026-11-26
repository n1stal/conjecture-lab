# Line-preserving projective restrictions: research checkpoint

**Mathematical result:** Let \(M\) be a restriction of \(\mathrm{PG}(r-1,q)\) over a finite field of size \(q\), \(r\ge 2\), retaining at least two points of each projective line. The inverse \(Z\)-polynomial has positive, strictly log-concave coefficients. This is a restricted family, not the unrestricted Gao–Ruan–Xie conjecture. No novelty claim.

Write \([j]=(q^j-1)/(q-1)\), including \([-1]=-1/q\), and let \(d\) denote the number of deleted points. With \({r\brack i}_q\) the subspace count, the coefficient of \(t^i\) equals
\[
a_i g_i,\qquad a_i={r\brack i}_q\,q^{\binom i2+\binom{r-i}2},\qquad
g_i=1+\frac{d}{[r]}\left(\frac{[i-1][r-i-1]}{q^{r-2}}-1\right).
\]

**Proof.** Every subspace of dimension at least two is spanned by retained points: each point is on a line in that subspace and each such line is spanned by two retained points. Thus the restricted flat lattice is the full subspace lattice with the deleted atoms removed. The ordinary Möbius number on a full rank-gap \(s\) interval is \((-1)^s q^{\binom{s}2}\), from the q-binomial identity and the Möbius recurrence. Above any nonzero surviving flat the interval is unchanged. At the bottom of each positive dimensional flat \(F\), the signed Möbius value loses \(d_F q^{\binom{k-1}2}\), where \(k=\dim F\) and \(d_F\) is its deleted-point count; this follows by subtracting the two upper Möbius sums, which are zero for a positive-dimensional interval.

By the degree and symmetry characterization of inverse KL and inverse Z (Braden–Ferroni–Matherne–Nepal, Theorem 2.2, arXiv:2510.01086v2), the candidate inverse KL polynomial of a \(k\)-dimensional flat for \(k\ge2\) is
\[
q^{\binom{k}{2}}+d_F\left(-q^{\binom{k-1}{2}}+[k-2]q^{\binom{k-2}{2}}t\right);
\]
it is \(1\) in dimensions zero and one. The candidate satisfies the degree bound (its linear term vanishes for \(k=2\)). To check palindromicity, sum over flats \(F\), weighting by upper signed Möbius and multiplying by \(t^{r-k}\). For \(1\le i\le r-1\), the correction to the \(t^i\) coefficient comes from the constant term at \(k=r-i\) and the linear term at \(k=r-i+1\). Double count deleted points incident to these flats. The correction divided by \(d a_i\) is
\[
\frac{-[r-i]q^{i-1}+[i][r-i-1]}{[r]q^{r-2}}
=\frac{[i-1][r-i-1]-q^{r-2}}{[r]q^{r-2}}.
\]
The equality uses \([m]=[m-1]+q^{m-1}\). For the first term when \(k=1\) the correction instead removes the whole missing atom. The division-free Gaussian ratios used in this computation follow from counting incident point/subspace flags and from annihilator symmetry. The endpoint coefficients have the common factor \(1-d/q^{r-1}\) by the Möbius calculation. The result is symmetric, so by induction on \(r\) and uniqueness under the degree/symmetry characterization it is the true polynomial.

For strict log-concavity the consecutive ratios of \(a_i\) have successive quotient
\[
q^2\frac{q^{r-i}-1}{q^{r-i+1}-1}\frac{q^i-1}{q^{i+1}-1}<1 .
\]
The \(g_i\) are concave, since their only index-varying term is a nonpositive multiple of \(q^{i-1}+q^{r-i-1}\); their endpoints are positive because the lines through a retained point require at least \([r-1]\) distinct other retained points, so \(d<q^{r-1}\). A positive concave sequence is log-concave, and the product with the strictly log-concave \(a_i\) is strictly log-concave.

**Rank-five deletion obstruction.** For full \(\mathrm{PG}(4,2)\), \(Y=(1024,1984,2480,2480,1984,1024)\). After any one point deletion it is \(Y=(960,1920,2430,2430,1920,960)\). Thus adding a non-coloop can lower \(C-B\) from 510 to 496. This prevents a direct rank-four monotone-gap proof with that invariant, not all deletion methods.

**Lean status:** The end-to-end theorem is stated in ../../InverseZProjective/ProjectiveMain.lean as InverseZProjective.GaussianIncidence.represented_inverseZ_strict_logConcave. It uses the actual represented Mathlib matroid and Conjecture Lab's published matroidInverseZ. It assumes the standard line-preserving representative condition (two retained nonparallel vectors in each two-dimensional subspace). It proves positivity through rank and strict log-concavity at every interior coefficient. See the [audit](audit.md) and [verification instructions](../../docs/verification.md) for the source, attribution, and reproducible check. No claim of the unrestricted conjecture or publication priority is made.
