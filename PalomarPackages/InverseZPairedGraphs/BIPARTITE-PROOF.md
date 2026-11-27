# Strict ordinary inverse-Z log-concavity for every K_{2,n}

For every n≥1, the cycle matroid L_n=M(K_{2,n}) has rank n+1 and its ordinary inverse Z-polynomial has positive coefficients in every degree 0 through n+1, with every interior adjacent minor strictly positive. The n=0 empty-edge matroid has Y=1 and vacuous strict log-concavity. This is unbounded rank and nonpaving for n≥4 (4-circuit). This is not arbitrary matroids or arbitrary K_{m,n}.

## Source and exact flat formula

Use the signed flat sum in [Braden–Ferroni–Matherne–Nepal, Theorem 2.2](https://arxiv.org/html/2510.01086v2), equivalently the defining ordinary inverse Z sum of [Gao–Ruan–Xie](https://arxiv.org/abs/2507.01332v1). In this sum the weight at F is abs(Möbius(F,E)) t^(r−r(F)) Q(M|F). Write T_n=M(K_{1,1,n}), with spine between the two hubs. [Gao–Yun Li–Xie, Corollary 4.3, Eq. (40)](https://arxiv.org/html/2510.11322v1) gives Q(L_k)=Q(T_k)+(k−1)t−1 for every k≥1. Their Corollary 5.4 proves log-concavity of Q(L_n), **not** inverse-Z log-concavity. Targeted exact searches by complete bipartite, thagomizer deletion, parallel two-edge theta paths, and inverse Z found the Q and ordinary Z results, but no exact prior Y strict-LC theorem. This is an audit, not an assertion of historical priority.

Flats of L_n have either separated hubs or joined hubs; closure adds all original edges within each connected component. In the joined case there must be ≥1 double-spoked leaf, and all active leaves have both spokes. With k≥1 such leaves, the rank is k+1, the restriction is L_k, and the simplified contraction is free on n−k leaves (two parallel edges from each outside leaf to the common hub before simplification). There are binom(n,k) such flats. In the separated case there are k assigned leaves with one spoke each and the remaining leaves isolated, so there are 2^k binom(n,k) flats of rank k with free restriction. For k≥1, each assigned leaf contributes an opposite spoke between the two hubs after contraction. These simplified contractions are T_{n−k}, with |μ|=2^(n−k); for k=0 the contraction is L_n itself. The last absolute value is 2^n−1, by characteristic-polynomial deletion/contraction at the nonloop noncoloop spine of T_n, with T_n/spine simplifying to a free matroid of rank n. (The T_n value follows equally by its two flat classes and the Möbius sum; include k=0 in both types there.) Thus

    Y(L_n) = 2^n t(1+t)^n − t^(n+1) + Σ_{k=1}^n binom(n,k) t^(n−k) Q(L_k).

For T_n, omit the negative t^(n+1) term and start the sum at k=0 with Q(T_0)=1. Substitution of the Q deletion identity and binomial differentiation give

    Y(T_n) − Y(L_n) = (1+t)^(n+1) − n t(1+t)^(n−1).

## Exact coefficients and all-rank minor

Let b_i=binom(n,i) (0 outside [0,n]), Tail_i=Σ_{k≥i} b_k, Prefix_i=Σ_{k≤i} b_k. The thagomizer row is a_i=b_i Tail_i+b_(i−1) Prefix_i: the joined-flat sum counts Motzkin prefixes with two neutral horizontal colors (one of degree one), since one installs the marked horizontal steps in positions complementary to the unmarked Q prefix. Encode the steps as pairs of simultaneous bits (up=01, down=10, unmarked/marked horizontals=00/11), and count first-path ones for degree. For total ones i≤k of the two bit sequences, the bad pairs biject to all pairs with totals (i−1,k+1), by swapping prefixes up to the first height −1, inverted at +1. Sum b_i b_k−b_(i−1)b_(k+1) over k≥i and add 2^n b_(i−1), yielding the formula.

The correction above has coefficient b_i+b_(i−1)−i b_i, by i b_i=n binom(n−1,i−1). Therefore c_i=[t^i]Y(L_n) is exactly

    c_i = b_i (Tail_i − 1 + i) + b_(i−1)(Prefix_i − 1), 0≤i≤n+1.

At the two ends c_0=c_(n+1)=2^n−1. At interior degrees b_i>0 and Tail_i−1+i>0.

At an interior i, set p=i, q=n−i+1, b=b_i, A=(Tail_i−1)/b, H=(Prefix_(i−1)−1)/b, z=1/b, r=p/q, v=(q−1)/(p+1), s=p(p−1)/(q(q+1)). Both A,H≥0. The neighbors, normalized by b², are exactly

    L = r A + r² + s H + z (p−1) r,
    C = A + r(H+1) + zp,
    R = v A + H + 1 + z(p+1)v.

This follows by expanding the preceding coefficient formula and using the three binomial ratios. At i=n use b_(n+1)=0 (thus v=0); the purely formal shift of the next tail by b_n when it is empty is multiplied by that zero. At i=1 s=0 similarly matches b_(−1)=0. Expanding yields

    C² − LR = (p+q)[ A²/(q(p+1)) + 2pAH/(q(p+1)(q+1))
                   + pA/(q²(p+1)) + p(H²+H)/(q²(q+1))
                   + 2pAz/(q(p+1)) + 2pHz/(q(q+1)) + pz/q² ]
              + p(p+q−1)z²/q.

Every displayed term is nonnegative and the final term is strictly positive, for all i and n in scope.

## Verification scope

Pinned Lean 4.35.0-rc2, import Std only, verified the denominator-cleared identity, strictness, and exact binomial-row `row_minor` and `row_positive` for all n, not bounded. File `CompleteBipartiteRows.checked.lean`, exact SHA-256 d0193c570967b34879d39176186d3e24c0d868df0dd8ce6400b712325192932a. Axioms are the usual propext, Classical.choice, and Quot.sound only. The staged paired Solution also kernel-checks the exact finite graph-flat sum to row and both endpoint inequalities. The universal comparison to a general Mathlib Matroid API is not claimed. The independent `verify_graph_flats.py` spot check enumerates *actual* graph closures, sums the finite Möbius recurrence, and uses the published Q formula — not the proposed coefficient identity — through n=7. It agreed at all 42 coefficients, including 2,314 flats for n=7.
