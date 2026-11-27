# Exact four-terminal distance-packing bound

Source: Artem Hak and Sergiy Kozerenko, [*Triameter, distance packings, and vertex connectivity*, §7, Question 3](https://arxiv.org/html/2611.17259v1#S7). This treats the packing question for exactly four distinct terminals. The finite extremum for at least five terminals and the sharp graph-separation question are separate. The paper's Theorem 1.1 is credited; the Lean project proves its numerical cap anew from shortest geodesics rather than assuming it.

Let k ≥ 1 and let p ≥ 1 be the maximum number of graph vertices whose pairwise distances exceed k, with the graph finite, simple and connected. Give four distinct terminals a, b, c, d nonnegative integer weights; write W for total weight, M for the sum of products over the six unordered pairs, and C for the maximum of w(A)(W−w(A)) over bipartitions of the four terminals. Then the exact maximum weighted sum of their six distances is

**k M + (k+1)(p−1) C.**

For unit weights the maximum is **6k + 4(k+1)(p−1)**.

## Upper bound

Set R=(k+1)(p−1). Geodesic spacing gives dᵢⱼ≤k+R. Theorem 1.1 of Hak–Kozerenko gives triangle perimeter ≤3k+2R. For each pair let xᵢⱼ=max(0,dᵢⱼ−k). Then xᵢⱼ≤R and each triangle has x-perimeter at most 2R. Indeed, if all three excesses are positive subtract 3k from the perimeter bound; otherwise there are at most two nonzero terms each at most R.

Increase each of the six edges once, in any order, to the maximal value ≤R allowed by its two triangle caps. Constraints are preserved; any triangle made tight remains tight because later increases are nonnegative. At the end the resulting y≥x is saturated: each edge is at R or is in a tight triangle. It also satisfies lower triangle inequalities. If yᵢⱼ>yᵢℓ+yⱼℓ, then yᵢℓ and yⱼℓ are below R and the triangle i,j,ℓ is not tight. With m the fourth vertex, tightness must be in i,ℓ,m and j,ℓ,m respectively. Adding those two equalities and using yℓₘ≤R gives yᵢₘ+yⱼₘ≥2R−yᵢℓ−yⱼℓ. The i,j,m cap now contradicts the strict lower-triangle violation.

For R>0, y/R is a mixture of the eight cuts fixing a on its first side. Here is a direct verification without polytope enumeration. Put p_i=y_ai/R and q_ij=(y_ai+y_aj−y_ij)/(2R) for i,j among b,c,d. These are desired first and pair moments of three side bits. The eight masses, as a function of the triple moment u, are
- u for 111;
- q_ij−u for the three atoms with two ones;
- p_i−q_ij−q_iℓ+u for the three atoms with one one;
- 1−sum p_i+sum q_ij−u for 000.

Take u=max(0, q_bc+q_bd−p_b, q_bc+q_cd−p_c, q_bd+q_cd−p_d). Every lower limit here is at most every upper limit q_ij and 1−sum p_i+sum q_ij. This follows from the triangle inequalities and perimeter caps for y: q_ij≥0; q_ij≤p_i,p_j; each cross-comparison q_ij+q_iℓ−p_i≤q_jℓ is the lower triangle inequality y_jℓ≤y_ij+y_iℓ; the 000 upper limit is nonnegative by the b,c,d perimeter cap; comparing q_ij+q_iℓ−p_i to that upper limit is the a,j,ℓ perimeter cap. The masses sum to one, and their cut marginals are y/R by direct substitution. For integral graph distances the Lean certificate clears denominators and uses integer masses summing to 2R. If R=0, x=0 directly.

The weights are nonnegative, so the weighted excess of x is no more than that of y, which is at most R times the largest cut cost C. This proves the claimed upper bound.

## A graph attaining it

Choose a maximum-cost cut with both sides nonempty. If a trivial cut maximizes, its value is zero and every cut has nonnegative cost, so any nontrivial cut works. Write k=2h+e with e=0 or 1, and let H=h+e>0. If p=1 take a common root, L=0. Otherwise take an L-edge path with
L=R−e=2h+1+(k+1)(p−2).
Attach one H-edge arm per terminal, with each arm based at the endpoint assigned by the chosen cut. If e=1, join the depth-one vertices of distinct arms at the same anchor by edges. The terminals are the four tips.

Index trunk vertices by 0 through L and branch vertices by an arm label and their positive depth. Two trunk vertices have the absolute difference of coordinates as distance. A trunk vertex and an arm vertex have coordinate-to-anchor distance plus the arm depth. Two vertices on the same arm have absolute depth difference. On different arms, their distance is the sum of depths plus the absolute anchor-coordinate difference, minus e if the anchors coincide. For each formula there is a path of that length: along the trunk, along the arm, through the anchors, or by one odd first-layer shortcut. The displayed distances also satisfy the triangle inequality, by considering whether the middle vertex is in the trunk, on the same arm as an endpoint, or on a distinct arm. They are one on edges, so no walk is shorter; this argument is checked directly in Lean. Thus same-side tips are at distance 2H−e=k, and when p≥2 opposite tips are at distance L+2H=k+R. When p=1 all tip distances equal k. In all cases the weighted score is at the bound.

The graph has packing number exactly p. For p=1 all vertices are in a single cap of diameter at most k. For p≥2, at each trunk endpoint take all its arms and trunk vertices within h of that endpoint. A cap has diameter at most k: the different-arm maximum is 2H−e=k, the arm-to-trunk maximum H+h=k, and the trunk-to-trunk maximum 2h≤k. The remaining (k+1)(p−2) interior trunk vertices partition into p−2 consecutive blocks of k+1 vertices each, each of diameter at most k. So no packing has more than p vertices. Along any opposite-tip geodesic, whose length is k+R, taking every (k+1)st vertex up to distance R yields p vertices at pairwise distances exceeding k. This proves exact attainment.

The integer-weight theorem and unit-weight formula use native Lean graph definitions (actual shortest walks and actual maximum packing). The integer cut certificate proves the same argument for arbitrary real nonnegative weights on paper, but no Lean real-weight theorem is claimed.

## Prior special case

F. R. K. Chung's [*The average distance and the independence number*](https://doi.org/10.1002/jgt.3190120213) implies the unweighted k=1 upper bound for every even terminal count r, including r=4 here. To see this, replace each selected vertex by a clique of m true twins. The independence number stays p because an independent set takes at most one vertex from each clique and projects to an independent set of the original graph. Between different cliques the original terminal distances are preserved. As m tends to infinity the average vertex distance converges to 1/r+2S/r², where S is the sum of the original unordered terminal-pair distances. Chung's bound gives S≤(p r²−r)/2, exactly the claimed upper bound when r=4 and k=1. This special case is not claimed as new.
