# Strict inverse-Z log-concavity for all edge-glued pairs of cycles

Let C_(a,b) be the cycle matroid of two simple cycles of arbitrary lengths a,b≥3 glued along one common edge. Then all coefficients of the ordinary inverse Z polynomial are positive in its rank range and all adjacent interior minors are strictly positive. Put r=a−2,s=b−2, N=r+s+1; N is exactly the matroid rank. No statement is made here for more than two cycles or for theta graphs without a spine.

## Exact primary scope and priority

[Braden–Ferroni–Matherne–Nepal, arXiv:2510.01086v2 (22 October 2026), Proposition 4.2](https://arxiv.org/html/2510.01086v2), and the [journal article](https://ems.press/journals/jca/articles/14300136) prove the exact inverse Z formula used below, not these log-concavity inequalities. Deleting the common edge gives C_(a+b−2)=U_(N,N+1), not C_(a+b−1) as mistyped in the sentence introducing §4.2. The proposition's uniform indices and its proof use the correct length. Contracting the common edge gives U_(r,r+1) direct-sum U_(s,s+1). The only possible nonzero corrections come from the two single-cycle flats: the top contracted restriction is disconnected, and any other eligible restriction contracted through the spine has an additional coloop, hence zero tau. [Gao–Ruan–Xie, Theorem 1.1](https://arxiv.org/abs/2507.01332v1) supplies the ordinary uniform inverse Z coefficients. The 27 November 2026 targeted search across glued/parallel cycles, theta matroids, inverse Z/ordinary Z/inverse KL terminology found the published coefficient formula and other invariants, not the exact all-pair strict result. That is not an assertion of first priority.

## Positive formula and synchronization

Let A_r denote the inverse Z polynomial of U_(r,r+1), positive and symmetric of degree r. Its coefficient for j≤r/2 is binom(r+1,j)(r−j). Let D_r=0 if r is even; if r=2m−1, let D_r=τ_r t^m, with τ_r=binom(2m,m)/(m+1) by BFMN Proposition 4.1 and the displayed uniform tau formula. Write W_r=(1+t)A_r−2D_r. BFMN Proposition 4.2 becomes

    2Y(C_(a,b)) = 2A_N + W_r A_s + A_r W_s.       (1)

For r≥2, W_r is positive and symmetric of degree r+1. This is automatic if r is even. If r=2m−1, m≥2, the two central A_r coefficients both equal X=m binom(2m,m−1), and τ_r/X=1/m²; W_r replaces its central coefficient 2X by 2X(1−1/m²)>0, leaving everything else unchanged. If r=1, W_1=1+t² is not a positive row across the full degree; the prior triangle+cycle proof handles precisely that case (and s=1 by symmetry). Formula (1) is a positive symmetric decomposition for arbitrary r,s≥2.

For a positive finite row a_0,…,a_R, define its degree-R normalized adjacent defect for j=1,…,R by

    δ_j(a)=j a_j/a_(j−1) − (R+1−j).

If positive rows a and b have all defects bounded in absolute value by ε and η, respectively, then their convolution c has defects bounded by ε+η. Indeed, setting i+h=j−1 and extending coefficients by 0, exactly

    j c_j = Σ_(i+h=j−1) [(i+1)a_(i+1)b_h + (h+1)a_i b_(h+1)].

For any included pair with positive product a_i b_h, the two normalized terms have base R−i and S−h and individual defect δ_(i+1)(a), δ_(h+1)(b), with defect defined as 0 when the corresponding index exceeds the support. Thus δ_j(c) is a weighted mean of sums of the old defects, with weights a_i b_h divided by c_(j−1). The same-degree positive sum rule holds as well: the new defect is the weighted mean of component defects with weights equal to their previous coefficients (including any fixed positive multipliers).

For A_r a direct binomial ratio at a lower-half index j gives

    j (A_r)_j/(A_r)_(j−1) = (r+1−j) − 1/(r+1−j).

In the reverse ratio at k=r+1−j, symmetry gives defect j/(k²−1). Here j≤k−1, so the magnitude of this reverse defect is at most 1/(k+1). If r is odd, the sole intervening central ratio is 1 and its defect is 0. Consequently

    |δ_j(A_r)| ≤ ε_r := 1/(ceil(r/2)+1)   (for r≥2).

For W_r with r even, convolving with the degree-one binomial (defect zero) gives the same bound. For r=2m−1 odd, m≥2, only k=m,m+1 change from the undented convolution, which is already bounded by ε_r. For k=m−1 and m+1 the W_r coefficient is X(1+ρ), where ρ=(m−1)(m+1)/(m(m+2)); at m it is 2X(1−1/m²). Therefore the two changed defects are, in order,

    −3(m+1)/(2m²+2m−1),  +3m/(2(m−1)(m+2)).

The first magnitude dominates the second because after positive cross-multiplication the numerator difference is 2m²−m−4>0 for m≥2. It also dominates ε_r=1/(m+1), since 3(m+1)²>2m²+2m−1. Thus write η_r=ε_r for even r and η_(2m−1)=3(m+1)/(2m²+2m−1) for odd r≥3. For m≥4 this last number is at most 5/13: cross-multiplication reduces to 10m²−29m−44=(m−4)(10m+11)≥0.

The two products in (1) have bounds η_r+ε_s and ε_r+η_s. Both are ≤1 except possibly the following eight unordered parameter pairs: (3,s) for s=2,…,8, and (2,5). To verify this exhaustive reduction, even r always has η_r≤1/2; odd r≥7 has η_r≤5/13<1/2. The exceptional odd r=3 has η_r=9/11, acceptable with s≥9 where ε_s≤1/6; odd r=5 has η_r=12/23, acceptable with s≥3 where ε_s≤1/3. Also ε_s≤1/2 for every s≥2. The uniform term A_N has max defect strictly below 1 with positive weight at every index. Therefore once both product bounds are ≤1, the same-degree positive sum rule yields **strict** |δ_j(Y)|<1 at every index.

To turn this into strict log-concavity, compare two successive ratios at each interior k in the left half:

    Y_k/Y_(k−1) > (N−k)/k ≥ (N−k+1)/(k+1) > Y_(k+1)/Y_k.

The middle weak inequality is exactly 2k≤N, and the outer inequalities are the strict defect bounds. The symmetric right half follows by reflection. This proves the claimed inequalities for unbounded varying r and s. The omitted triangle case r=1 or s=1 is handled by the separately checked triangle+cycle proof. The eight exceptional pairs pass the exact finite certificate below and require no inference from a numerical search.

## Verification

The proof is checked from the exact unscaled source formula in `Palomar/GluedCyclesInverseZ/Solution.lean`. It includes the integer Cauchy derivative and window lemmas, binomial and dent estimates for all ranks, all eight residual cases by kernel computation of the published coefficients, and the triangle boundary at either side. The BFMN identification and uniform-cycle formula belong to the cited mathematics; no formal statement about a general Mathlib matroid API is claimed. The triangle boundary subproof is included in the same Lean source, independently of any hosted version.

The terminal paths have lengths 1, a−1, b−1. Removing the length-one path leaves one simple cycle; contracting it identifies the two terminals and leaves the other paths as two cycles intersecting only at that vertex. For a flat containing the common edge to stop being a flat upon removing that edge, at least one side path must be complete, since only then are the endpoints still connected. Both complete is the top flat; the restriction after contracting the common edge is then the above direct sum. If only one side is complete, any selected edges on the other side form a forest and are coloops in the contracted restriction; if none are selected this is exactly one cycle flat. For that surviving flat, contraction leaves the other side as its cycle. Accordingly the two source exponents are (a−1)/2 and (b−1)/2 (at odd r or s only), and the quotient rows are A_s and A_r. This is the explicit graph-to-formula correspondence used by the formal coefficient proof.
