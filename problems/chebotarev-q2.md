# Chebotarev's even-order Laplacian height question

**Status:** General weighted question remains open in the sources checked on 2026-11-26. The family result below is a written proof, not Lean-verified; independent review and novelty are not established. The order-six unweighted height bound is checked by exhaustive integer arithmetic; the weighted and full-polygon searches remain exploratory.

[Chebotarev, arXiv:2610.14100v4, §7.3, Question 2](https://arxiv.org/html/2610.14100v4#S7.SS3) asks whether the maximum imaginary part of an eigenvalue of a standardized $n\times n$ digraph Laplacian at even $n$ is $n^{-1}\cot(\pi/n)$. Such an $L$ has $L_{ij}=-a_{ij}$ for $i\ne j$, $a_{ij}\in[0,1/n]$, and each row sums to zero. Order four is already settled in v4; earlier versions reporting it open are stale. The companion [arXiv:2611.02249, §7](https://arxiv.org/html/2611.02249#S7) reports local optimization at orders 6 and 8, and the original paper reports a second-order perturbative obstruction in the horizontal direction. Neither observation rules out a nonlocal counterexample.

## Partial theorem: all antipodal weights can vary

Let $n=2m\ge 4$. Start with **any** admissible circulant $L_0$ and replace the weights on the $n$ arcs $j\to j+m$ modulo $n$ by arbitrary independent numbers in $[0,1/n]$, adjusting the diagonal to keep zero row sums. The resulting $L$ satisfies

$$
\lvert\operatorname{Im}\lambda\rvert\le \frac1n\cot\frac{\pi}{n}
 \qquad(\lambda\in\sigma(L)).
$$

The uniform family bound is sharp, since the admissible circulant using steps $1,\dots,m-1$ at weight $1/n$ and all others at zero attains it.

**Proof.** Write $P$ for the cyclic shift $(Px)_j=x_{j+1}$. The perturbation is $D(I-P^m)$, where $D=\operatorname{diag}(d_0,\ldots,d_{n-1})$ and $d_j$ is the change in the corresponding weight (possibly negative). Use the orthonormal pair-symmetric and pair-antisymmetric bases $u_j=(e_j+e_{j+m})/\sqrt2$ and $v_j=(e_j-e_{j+m})/\sqrt2$ for $0\le j<m$. Since $L_0$ commutes with $P^m$, it is block diagonal in this splitting. The perturbation vanishes on the $+$ subspace, so $L$ is block upper triangular. Its upper-left block is $L_{0,+}$, and its lower-right block is

$$
L_{0,-}+\operatorname{diag}(d_j+d_{j+m})_{j=0}^{m-1}.
$$

Indeed, $D(I-P^m)v_j=2Dv_j=(d_j-d_{j+m})u_j+(d_j+d_{j+m})v_j$.

It remains to bound the skew-Hermitian part of each block. In Fourier mode $k$, the eigenvalue of $L_0=\sum_{s=1}^{n-1}a_s(I-P^s)$ has imaginary part $-\sum_s a_s\sin(2\pi ks/n)$. For $k=0$ this is zero. Otherwise let $q=n/\gcd(n,k)$. The sine terms are those of the $q$ uniformly spaced phases, each repeated $n/q$ times (one zero phase can be supplied by $s=0$). Since $0\le a_s\le 1/n$, the magnitude is bounded by the sum of the positive sine terms divided by $n$:

$$
 \frac1q\sum_{r=1}^{\lfloor(q-1)/2\rfloor}\sin\frac{2\pi r}{q}
 =\begin{cases}
 q^{-1}\cot(\pi/q),&q\text{ even},\\
 (2q)^{-1}\cot(\pi/(2q)),&q\text{ odd}.
 \end{cases}
$$

These identities follow by a finite geometric sum; the omitted order-one case was already zero. The real function $x\mapsto \cot(\pi/x)/x$ is increasing for $x\ge 2$: with $t=\pi/x$, the derivative of $t\cot t$ with respect to $t$ is $(\sin t\cos t-t)/\sin^2t<0$. For even $q$ use $q\le n$. For odd $q\mid n$ and $n$ even use $2q\le n$. The bound therefore applies to all Fourier eigenvalues of $L_0$.

The two blocks of $L_0$ are normal, being diagonal in their respective Fourier bases. The real diagonal perturbation leaves the Hermitian imaginary part $(B-B^*)/(2i)$ of the lower block unchanged. For any eigenvector $z$ of a block $B$ with eigenvalue $\lambda$, $\operatorname{Im}\lambda=z^*((B-B^*)/(2i))z/(z^*z)$, so its magnitude cannot exceed the largest magnitude of the original block's eigenvalue imaginary parts. Block triangularity now gives the assertion for $L$. The upper bound is attained by the specified half-circulant at Fourier mode $1$ or its conjugate. ∎

This rules out all counterexamples produced exclusively by changing the antipodal weights of a circulant. It does **not** control perturbations of other arcs, or prove the unrestricted conjecture.

## Computational scouting

Run from repository root with NumPy installed:

~~~sh
OPENBLAS_NUM_THREADS=1 python experiments/chebotarev_unweighted6.py
~~~

This enumerates 4,241,864 six-vertex unweighted digraph representatives (repetitions allowed). It first verifies that the 156 undirected skeleton representatives cover all $2^{15}$ unordered-edge masks under vertex permutations. For each skeleton it iterates every assignment of one direction or both directions per edge, with at most 15 directed arcs. Every excluded digraph has a complement with at most 15 arcs. On the quotient by constant vectors, the complementary Laplacian is $I-L$, so the quotient spectrum is reflected across real part $1/2$ (using conjugation symmetry); both the height test and the polygon are invariant under this operation. Thus a violation by *any* unweighted six-vertex digraph would occur in the screen, subject to numerical error. The maximum observed imaginary part was 0.28867513459481337, matching $\sqrt3/6$ to rounding. The maximal observed signed distance outside the polygon was only $2.4\cdot10^{-15}$, consistent with numerical roundoff. Chebotarev's v4 §6 reports the unweighted $n=6$ sweep only for maximum out-degree at most 2, so this coverage goes beyond the stated sample while still lacking exact spectral certification.

A separate seeded multistart experiment uses SciPy:

~~~sh
OPENBLAS_NUM_THREADS=1 python experiments/chebotarev_weighted.py
~~~

No height violation was found in 100 starts at each of $n=6,8,10,12,16$, including random matrices and perturbations of the half-circulant. This is exploratory evidence, not exhaustive coverage of weights. The full question still allows fractional weights.

## Exact unweighted certificate at order six

The floating-point height screen above was independently replaced by integer arithmetic. The result is exact: every unweighted six-vertex digraph has standardized Laplacian eigenvalues satisfying $|\operatorname{Im}\lambda|\le\sqrt3/6$. The bound is attained by the half-circulant in the theorem above. Exact certification of *all the other sides of the polygon* is not claimed.

~~~sh
g++ -O3 -std=c++17 -Wall -Wextra experiments/chebotarev_exact6.cpp -o /tmp/chebotarev-exact6
set -o pipefail
/tmp/chebotarev-exact6 | python experiments/chebotarev_verify6.py
~~~

Expected output: 4,241,864 representatives with repetitions, 44,729 distinct quotient characteristic polynomials, and nonnegative strip-test coefficients for all 44,729. Compilation excluded, the pipeline ran in about 3.3 seconds locally.

Here the quotient Laplacian is **unscaled**, with matrix $Q_{ij}=L_{ij}-L_{5j}$ for $0\le i,j<5$ in the quotient basis of the first five coordinate vectors. The missing constant eigenvector contributes only a zero. The generator independently re-enumerates the undirected skeletons, their orientations with at most 15 arcs, and computes each quotient characteristic polynomial from matrix-power traces via the Newton identities. For overflow bounds: the infinity norm of $Q$ is at most 15, so entries of the computed powers (up to fifth) and traces are small. The original unscaled Laplacian has Gershgorin eigenvalue magnitude at most 10, so $|c_k|\le \binom5k10^k$ for the characteristic coefficients and $|\operatorname{tr}(Q^k)|\le5\cdot10^k$. The largest possible running absolute sum in the trace-to-coefficient conversion is therefore at most $5\cdot10^5(1+5+10+10+5)=15{,}500{,}000$. No solver, floating-point calculation, or external enumeration data is used.

For a quotient characteristic polynomial with roots $\lambda_1,\ldots,\lambda_5$, counted with multiplicity, the verifier computes the exact coefficients of

$$
 G(t)=\prod_{i<j}\bigl(t+12+(\lambda_i-\lambda_j)^2\bigr).
$$

If $|\operatorname{Im}\lambda_i|\le\sqrt3$ for all $i$, every constant term $12+(\lambda_i-\lambda_j)^2$ has nonnegative real part, since $|\operatorname{Im}(\lambda_i-\lambda_j)|\le2\sqrt3$. Pair the nonreal constant terms with their conjugates: each resulting quadratic, and each remaining real linear factor, has nonnegative coefficients. Conversely, if the height bound fails, an eigenvalue $a+ib$ and its conjugate produce a factor $t+12-4b^2$ with a positive zero. A monic polynomial with all coefficients nonnegative cannot have a positive real zero. The two conditions are therefore equivalent.

The verifier computes power sums $p_\ell=\sum_i\lambda_i^\ell$ by Newton identities. For $k>0$, the power sum of the squared differences is $\frac12\sum_{\ell=0}^{2k}(-1)^\ell\binom{2k}{\ell}p_{\ell}p_{2k-\ell}$, by binomial expansion (the diagonal contributes zero). A second binomial expansion shifts the squared differences by 12 and negates them; a second Newton pass computes the coefficients of $G$. Python integers are unbounded. The finite result still does not control fractional arc weights or higher orders.
