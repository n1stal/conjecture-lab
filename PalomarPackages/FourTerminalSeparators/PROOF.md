# Proof: sharp vertex and edge separator packing for four prescribed vertices

Let G be a finite connected simple graph with four distinct marked vertices T. Write S for the sum of their six distances and c for the maximum size of a pairwise disjoint family of vertex T-separators. A separator avoids all of T and separates at least one pair of its vertices, following the definition in [Hak–Kozerenko, §2.1 and Lemma 6.1](https://arxiv.org/html/2611.17259v1#S6). We prove S ≤ 4c + 10 and attain the resulting ceiling bound **max(0, ⌈(S − 10)/4⌉)** at every integer S ≥ 6.

The result is the four-terminal vertex-separator part of [their Question 3](https://arxiv.org/html/2611.17259v1#S7). It does not claim the analogous result for five or more terminals.

## 1. Three graph tools for the vertex lower bound

**Triple restriction and precise rounding.** By the authors’ [Lemma 6.1](https://arxiv.org/html/2611.17259v1#S6), if three distinct terminals have perimeter P, G has floor((P−3)/2) disjoint vertex separators avoiding those three. Since they are disjoint, at most one contains a specified fourth terminal. All others are four-terminal separators: they still separate two of the original triple and now avoid all four. Thus floor((P−3)/2)≤c+1, or P≤2c+6, for each of the four triples. The perimeter sum is 2S, hence S≤4c+12.

**Exact fixed-pair cost with all terminals excluded.** On the complete graph on T put nonnegative edge lengths w(s,t)=d_G(s,t)−1 for s≠t. Its shortest-path closure w* has the following exact interpretation: w*(s,t) is the maximum number of pairwise disjoint vertex sets, each avoiding all of T and separating the fixed pair s,t. Indeed let f(v) be the minimum number of nonterminal vertex occurrences on a walk from s to v (including v if it is a nonterminal). Since costs are nonnegative, a minimizing path exists. On a path from s to t, decompose at every encountered terminal in order; each terminal-to-terminal segment of length ℓ accounts for ℓ−1 nonterminals and ℓ≥d_G between those endpoints. Thus f(t)≥w*(s,t). Conversely concatenate actual geodesics along a shortest complete-terminal route; each segment counts at most d_G−1 nonterminals (it can contain extra terminals), so f(t)≤w*(s,t).

For every 1≤j≤f(t), use the set S_j={v∉T:f(v)=j}. On an edge xy, f(y)≤f(x)+[y∉T]. Every path from s at level zero to t at level f(t) must first enter level at least j at a nonterminal vertex with f=j. Each S_j is therefore nonempty and separates s and t, and the sets are disjoint. Conversely any family separating s,t must meet a path minimizing f(t) in one distinct nonterminal per separator. This proves the exact formula and in particular c≥w*(s,t) for every pair. A minimum route on four terminals can be chosen simple even if some weights are zero, hence uses one, two or three edges.

**Four ball layers plus pair-group layers.** Opposite distance pairs are the three perfect matchings of K4. Sort their minimum entries as a≤b≤d, and let the matching corresponding to a pair the terminals into A and B (each a 2-set). Every terminal pair is at distance at least a, and the minimum cross distance between A and B is b, because the cross pairs comprise exactly the two other opposite matchings. Set t=floor((a−1)/2). Around each of the four terminals, take BFS layers j=1,…,t. Each is a nonempty T-separator (it isolates its own terminal from every other terminal); it is disjoint from T because t<a. All four closed radius-t balls are disjoint by triangle inequality, since 2t<a, and layers in each are disjoint.

Next take layers of g(v)=min_{u∈A}d_G(u,v) at levels t+1,…,b−t−1. Each is a nonempty T-separator avoiding T (vertices of A have level zero, vertices of B have levels at least b, and g is 1-Lipschitz). Each is disjoint from the preceding ball cuts: g≤t throughout A-side balls, while g≥b−t throughout B-side balls by triangle inequality. These extra layers are disjoint from each other. Their number is b−2t−1≥0, including the case of an empty range. Total c≥4t+(b−2t−1)=b+2t−1≥a+b−3.

## 2. Finish the sharp vertex inequality

Suppose S≥4c+11. From the triple bound, S∈{4c+11,4c+12}. For any opposite pair of distances x=d(i,j), x'=d(l,m), their difference is the sum of the perimeters of the two triples containing ij, minus S. Each of the four triple perimeters is at most 2c+6 and their sum is 2S. If S=4c+12, all these upper bounds are equalities, so all opposite differences are zero. If S=4c+11, total deficit of the four perimeters from 2c+6 is two, so each signed opposite difference is 1 minus the sum of two nonnegative deficits, hence lies in [−1,1]. Let δ count the opposite pairs differing by one. Then
- S=4c+12 gives δ=0 and a+b+d=2c+6;
- S=4c+11 gives δ=1 or 3 by parity, and a+b+d=2c+5 or 2c+4 respectively.
Write D for the actual maximum terminal distance.

If D≥c+3, let s,t be a diametral terminal pair. A one-edge complete-terminal route costs D−1 in w. A two-edge route costs at least D−2 by triangle inequality. A three-edge route necessarily has as its middle edge the distance opposite D, at least D−1. Its first and last distances are each at least 1, so its w-length is at least D−2 as well. Thus w*(s,t)≥c+1, contradiction.

Now D≤c+2. The four ball and group layers already contradict maximality if a+b≥c+4. Otherwise a+b≤c+3.
- δ=0 is impossible: a+b+d=2c+6 and d≤c+2.
- δ=1 forces d=c+2 and a+b=c+3. Both entries of the largest-minimum opposite pair equal c+2, because the smaller is d and D≤c+2. Use one as the terminal pair s,t. A one-edge w-route costs c+1. In any two-edge route the two distances are in the other two opposite matchings, and each is at least its matching minimum, so route cost is at least a+b−2=c+1. In any three-edge route the middle edge is opposite s,t, hence distance c+2, and the other two add at least two, so the w-cost is at least c+1.
- δ=3 forces d≤c+1 (every pair has entries differing by one and D≤c+2). Then d=c+1 and a+b=c+3 by the sum. Choose s,t given by the larger entry d+1=c+2. One- and two-edge costs are at least c+1 as above. In a three-edge route the middle distance is d=c+1, and the first and last distances form an opposite pair differing by one, so positive entries have sum at least three. Subtracting the three unit terms again gives cost at least c+1.

In the last two cases w*(s,t)≥c+1 also contradicts maximality. Thus S≤4c+10, proving the universal lower bound.

**Exact vertex witnesses.** For a tree, every nonterminal vertex on the minimal subtree spanning T is a singleton separator, and every separator must meet this subtree, so its count is exactly those nonterminals. For a path marked in order with consecutive gaps x,y,z, S=3x+4y+3z and c=x+y+z−3. For c≥3 and j=0,1,2,3 use gaps (1,c+1−j,1+j), giving S=4c+10−j. For c=2 the same gaps with j≤2 give S=16,17,18; S=15 uses a four-arm tree with leaf terminals and arm lengths (2,1,1,1), whose two nonterminals are the center and the other point on the long arm. For c=1, S=13,14 come from gaps (1,1,2) and (1,2,1), S=12 from the four-leaf star, and S=11 by adding an edge between two of that star's terminal leaves. In the latter graph the only nonterminal (center) is a separator. For c=0, use graphs on exactly the four designated vertices: K4 (S6), K4−edge (S7), C4 (S8), three-leaf star (S9), and P4 (S10). This covers every integer S≥6.


## Vertex Lean correspondence

The Challenge is the actual finite graph model, ordinary shortest-walk distances, literal separator relations, and the two compared minimum theorems; Lean-proven unit paths are used in the Solution. The source proof of Lemma 6.1 is credited. The formalization proves its needed claim independently with disjoint balls: odd perimeter uses the three half-integral arm radii rounded down, with pair distances one larger than sums of their radii; even perimeter uses each integer arm radius minus one. If an arm is zero no central set is needed, otherwise the complement of the three reduced balls is an additional disjoint separator, since there are no edges between those balls. The fourth marked terminal can hit at most one original separator.

The charged-distance argument counts only nonterminal vertices at an entering endpoint. A minimizing charged walk gives a complete-terminal route. The finite four-marked-vertex potential removes repetitions in the relevant cost bound without assuming the walk was simple; a contradiction is reduced to the five explicit one-, two- and three-edge terminal routes. The arithmetic then uses the four triple bounds and the actual disjoint-ball/group bound. Finally the attaining graph is a parametric path for all large S and one of ten literal finite certificates for S=6 through 15. Each certificate constructs a genuine shortest walk by a decreasing next-hop distance, not an imposed metric.

## 3. Edge separators: exact lower bound

Here a separator is a set of undirected edges such that, after deleting it, some two of the four terminals are disconnected. Terminals are not forbidden as endpoints of deleted edges. Let e be the maximum number of pairwise edge-disjoint such sets.

We first reprove the three-terminal statement of Hak and Kozerenko's [Remark 6.2](https://arxiv.org/html/2611.17259v1#S6): a triple with perimeter P guarantees floor(P/2) edge separators. Write its three pair distances as x+y, x+z, y+z, with nonnegative arm lengths x, y, z given by triangle inequality, and all arms either integers or half-integers. Choose nonnegative integral radii r, s, t with each pair sum at most its pair distance and total floor(P/2). For integral arms, use the arms. For half-integral arms, round each down and then increase any one of the rounded values by one. No pair of radii increases above its original sum.

At a terminal of radius r take the r BFS boundaries between distances j and j+1 for 0≤j<r; each disconnects it from a different terminal because every other terminal in this triple has distance at least r. The boundaries around each individual terminal are disjoint. Boundaries from different terminal centers cannot share an edge: both endpoints of such an edge would have distance at most the relevant radius from each of those centers, and at least one endpoint would be strictly closer to the first center than its radius. That endpoint would give a route between centers shorter than the sum of the radii, contradicting the selected radii. So there are exactly r+s+t=floor(P/2) separate boundaries. Each is still a separator for the full four-terminal set; unlike with vertex separators, one need not discard a boundary incident to the fourth terminal.

Thus every triple satisfies floor(P/2)≤e, equivalently P≤2e+1. Summing over all four triples gives 2S≤8e+4, so e≥ceil((S−2)/4). The natural-number Lean expression is `(S+1)/4`.

## 4. Edge separators: sharp graphs for every sum

Take two caps, each with a designated root, joined by a path of length L. If L=0 identify the roots. Each cap carries two terminals. The three available caps and their local distances are:

| Cap | Two chosen terminals | Distances to root | Pair distance | Cut budget |
| --- | --- | --- | --- | --- |
| Triangle | Two nonroot vertices | 1, 1 | 1 | 1 |
| Pentagon | An adjacent-to-root vertex and the vertex two steps away in the other direction | 2, 1 | 2 | 2 |
| Single edge | Both endpoints, one being the root | 0, 1 | 1 | 1 |

Within a cap, excursions through the rest of the graph cannot shorten local distances: the only point of attachment is its root. Each cross distance is the sum of the two distances to roots and L. Thus total S is 4L plus both intrapair distances plus twice the sum of the four arm-to-root distances.

Any separating edge set must delete a trunk edge, disconnect a single-edge cap by deleting its only edge, or delete at least two edges from a cycle cap. Indeed otherwise the trunk and each cap remain connected, hence so do all terminals. Charge each separating set to one such resource. Among pairwise disjoint sets, the charges on the trunk consume distinct edges, and charges to one cycle consume at least two distinct edges each. This proves the maximum number of disjoint cuts is at most L plus both cap budgets, even when L=0.

For S≥11 let e=floor((S+1)/4), so e≥3 and S is one of 4e+2, 4e+1, 4e, 4e−1. Use:

| S | Caps | L | Cap budgets + L |
| --- | --- | ---: | ---: |
| 4e+2 | Triangle, triangle | e−2 | e |
| 4e+1 | Triangle, pentagon | e−3 | e |
| 4e | Triangle, single edge | e−2 | e |
| 4e−1 | Pentagon, single edge | e−3 | e |

The left cap is never a single edge, so its terminals are distinct from both right terminals even when the roots coincide.

For S=10 take two triangles with common root. On vertices 0 through 4, the six edges are 01, 02, 12, 23, 24, 34, and the four terminals are 0, 1, 4, 3. For S=9, 8, 7 add successively edges 03, 04, 13; each lowers exactly one cross distance from 2 to 1. Adding edges cannot increase the maximum number of disjoint separators: restrict any disjoint family in the new graph to original edges, and it still blocks every original walk for its respective marked pairs. Therefore all four of these graphs have the required upper bound two.

Finally for S=6 take K4. If one edge cut separates two vertices, take the vertices reachable from one of them after the deletion. Every original edge of the complete bipartite graph between that shore and the other shore belongs to the first cut. It survives any disjoint second cut and connects all four vertices. Thus two disjoint separators are impossible and the bound one is attained.

## Edge Lean correspondence

The orientation-symmetric families `edgeRings` formalize the BFS boundaries: their support is inside the edge balls above. The formal upper bound for realizing graphs follows actual routes after deleting a cut, going forward along the trunk and either forward or backward around a cycle cap. A cap-label injection and a finite disjoint-resource count give the trunk-plus-cap upper bound, independently of the four terminal distances. The distances follow from the genuine unit-edge shortest walks, with the two trunk gates forced on every cross walk. The dense small witnesses use kernel-checked adjacency, distance and next-hop tables, while the complete-graph proof uses the reachable-shore argument. There are no additional trusted assumptions.
