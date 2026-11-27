# Parallel-pair, support-star, and double-star obstructions in Erdős #617

Jaime Nistal, responsible author. Codex (OpenAI), AI co-author for proof development and Lean formalization.

These are conditional structural results for [Erdős–Gyárfás, Conjecture 1](https://www.renyi.hu/~gyarfas/Cikkek/92_splitandbalanced.pdf#page=2), i.e. [Erdős Problem 617](https://www.erdosproblems.com/617), not a proof of that conjecture. A balanced r-coloring is an edge coloring in which every r+1 distinct vertices see all r colors. Fix one target color; a hole is a non-target edge. The model of independent anchors, private rows and exactly two-supported exceptional vertices is from the [earlier two-support normalization](https://erdosproblems.ai/wiki/research/erdos_617/two_support_normalization), which is an assumption here.

## 1. The pair bound

The earlier formalized result is included unchanged. If two rows of deficits d,e≥3 have μ shared exceptions, r≥12, and d+e≤r−3 in the displayed scoped normalized core, then μ≤d+e−2. [PAIR-PROOF.md](PAIR-PROOF.md) gives the full proof, including the credited prior bound μ≤d+e−1 and its even-order argument. The strengthened pair bound is not a new claim of this enhanced package.

## 2. Choosing rows for the exceptions on a single spoke

Let h=d+e−μ, m=2r−h−5, S=⌊(h−1)²/4⌋+1, and assume the two original rows are target-color cliques. For the refined spoke test assume

- S+1<⌊m/2⌋ and both original row lengths are greater than S+3;
- d+e+3<r;
- S<(K+1)² for a nonnegative integer K.

Every exception can simultaneously choose one of its two supporting rows. There is a choice in which every exception has at most one hole to its chosen row except possibly one exception, with at most K+1 holes. This is an assignment to the two true rows; it does not impose a quota between them.

To see this, use the missing-target graph F on the two rows and their μ exceptions. Its order is 2r−h. It is triangle-free by the scoped independence cap: a triangle of holes substitutes three target-independent vertices for the two anchors in this pair. Its independence number is at most r−1 because the scoped target graph has no K_r. Each hue has at least n−r edges in any n-vertex induced set; removing one endpoint of each edge leaves an independent set, and balance bounds its size by r. Hence F has at least (r−1)(r−h) edges. The pair bound gives h≥2.

If no exception has a hole to both rows, assign every exception to a zero-hole row. Otherwise choose an exception x and hole-neighbors u in the first row and v in the second. With p and q the two anchors, the actual support words give the cycle
`p — q — u — x — v — p` in F. It has five distinct vertices, is induced by triangle-freeness, and is a shortest odd cycle. Importantly, x is its only exception: it has both anchors and one additional vertex from each private row. An outsider has at most two neighbors on this cycle.

On the remaining m vertices there are therefore at least ⌊m²/4⌋−S edges, by the exact ledger identity
`⌊m²/4⌋+2m+5 = (r−1)(r−h)+S`. A triangle-free nonbipartite graph on m vertices has at most ⌊m²/4⌋−⌊m/2⌋+1 edges: a shortest odd cycle of length l≥5 is induced, each outsider has at most two neighbors on it by shortestness, and Mantel on the exterior gives at most `2m−l+⌊(m−l)²/4⌋` edges, largest at l=5. Mantel itself follows by counting edges with respect to a maximum-degree independent neighborhood. The strict gap test therefore gives a bipartite exterior with at most S missing crossings.

Each private row's exterior vertices lie in a single bipartition side. Otherwise its row independence in F would cost at least its exterior size minus one in missing crossings, exceeding S by the row-length test. The two private exterior rows lie on opposite sides, since their union is larger than r−1. Assign each exterior exception to the row on its side. It has no hole to the exterior part of that row and sees both anchors in target color, so it has at most one hole into its original row. For x itself, its two sets of exterior hole-neighbors force the entire product rectangle between them missing from F by triangle-freeness. The product of their sizes is at most S, so one size is at most K. Assign x to that row; the nonanchor row vertex on the pentagon supplies at most one further hole. This proves the simultaneous assignment.

The [existing pointwise two-private-clique bound](https://erdosproblems.ai/wiki/research/erdos_617/two_supported_private_cliques) permits a hole count bounded by the receiving row's deficit. Here the subsequent palette ledger needs small *total* cost, and the all-but-one result gives it.

## 3. Coupling every spoke at the actual hub

The star data consist of an actual private hub clique of size r−D, a list of actual spoke records all with this hub, and their jointly distinct exceptions, all disjoint from the hub. A leaf with deficit e has a private clique of size r−e. Its spoke is a scoped normalized pair as above. The exact total of all exception counts is one plus the sum of all row deficits. The data arise from a support star under the two-support normalization; no claim is made that every counterexample must have this form.

For any reached target clique, assign each exception a debt of its hole count beyond the first (or 0 for no holes). If d+1 exceptions arrive at a row of deficit d, they complete the row to r+1 vertices. This set must have at least r−1 non-target edges. At most \(\binom{d+1}{2}\) occur within the chosen exceptions, and at most d+1 plus their total debt occur between them and the row. The row itself has no non-target edge. Thus a row with total incoming debt at most B cannot receive more than d exceptions when
\[
\binom{d+1}{2}+d+1+B<r-1.
\]
One may take exactly d+1 of an overfull set because debt is nonnegative. The proof counts the actual missing edges, not merely the row sizes.

Every exception chooses exactly one row using §2 for its spoke. The debt contribution of that spoke to either row is at most K. The refined-star theorem assumes the displayed strict palette test for each leaf, with B=K of its spoke, and for the hub, with B the sum of all spoke K values. The leaf capacities bound their aggregate arrivals by their deficit sum. The hub capacity bounds the remaining arrivals by D. This contradicts one excess in the normalized total. This proves the general compared star theorem.

## 4. A uniform family with heterogeneous leaves

Let D≥3. Assume every leaf has deficit 3≤e≤D and that its spoke has e+1 exceptions. With the one-overload normalization the number of spokes is exactly D+1. All spokes have residual h=D−1 and the same budget S=⌊(D−2)²/4⌋+1. Choose K=⌊(D−1)/2⌋. We have K≥1 and S≤K²+1<(K+1)²≤D². For r≥(D+1)², the gap and row conditions in §2 follow from these and the row lengths at least r−D. In particular r−D−3>S, 2D+3<r, and \(\lfloor(2r-(D-1)-5)/2\rfloor\ge r-D-2>S+1\).

Twice the hub palette upper bound is
\[
D(D+1)+2(D+1)+2(D+1)K
\le 2D^2+3D+1
< 2D^2+4D \le 2(r-1).
\]
A leaf's deficit and total debt are no larger than the corresponding hub estimates, so all its tests follow. The normalized star is impossible. This is an unbounded support family, not a fixed-r computation. The leaves need not all have equal deficits.

The prior normalized result on a double-edge star with unit-deficit leaves is a different regime. No claim is made for arbitrary stars, arbitrary graphs, or the unrestricted balanced-coloring conjecture.


## 5. Two hubs: exact leaf elimination and the central edge

Add a second private target-color hub joined to the first by a central exception bundle. Every other bundle is a leaf spoke incident with one of the hubs. The common hub identities, both normalized pair caps, actual row orders and exact anchor words are part of the data. All exceptions are distinct and disjoint from both hubs. The total exception count is one more than the sum of all row deficits. Each leaf of deficit e has more than e incident exceptions on its spoke: the usual proper-set capacity after removing that leaf implies this strict surplus. No graph partition or spoke routing is presumed.

For a spoke with μ exceptions, remove exactly e exceptions and retain the other s=μ−e as arrivals at its hub. We prove that these retained arrivals can all be made to have at most one hole into that hub, with no excess-hole debt. If no exception has positive hole counts into both rows, assign all exceptions to a zero-hole side. The actual leaf palette cap bounds its arrivals by e, so retain any s of the hub arrivals.

Otherwise use the canonical pentagon p,q,u,x,v of §2. Its exterior has two independent sides in the missing-target graph, with the two original exterior private rows in opposite sides. The hub has deficit d; its exterior side has size r−d−2+y, where y counts exterior exceptions on its side. If y<s, this size is at most r−h−3 for h=d+e−μ. The opposite side, by the exact exterior order 2r−h−5, has size at least r−2. The product of the side sizes is at most (r−h−3)(r−2): moving the smaller side up to r−h−3 and the larger down to r−2 can only increase the product. But the pair palette floor is strictly greater than this maximum possible crossing count plus all cycle incidences and the five cycle edges:
\[
(r-1)(r-h)-\big[(r-h-3)(r-2)+2(2r-h-5)+5\big]=h-1>0.
\]
Thus y≥s. Every retained exterior exception has at most one hole, only to the nonanchor hub vertex on the pentagon. Removing all leaves this way leaves exactly one excess exception over the two hub deficits.

Suppose every row deficit is in [3,D] and
\[
r\ge \left\lceil 49D^2/64\right\rceil+6D+10.
\]
Use the following complete routing of the central bundle of multiplicity μ:

- If 4μ≤D, use the pointwise rectangle route. For one exception with hole counts p and q into the respective rows of deficits d and e, its two exterior neighbor lists force all pq private-row crossing pairs missing in the non-target graph, since that graph is triangle-free. Counting the palette on just the two private rows and this exception gives \((p-1)(q-1)\le(d-1)(e-1)+1\). As d,e≥3, some hole count is at most the corresponding deficit. Each exception goes to such a row, costing total excess-hole debt at most μD per hub.
- If 4μ>D, use the refined route of §2 with K=D. In this case the residual satisfies 4h≤7D. For the leaf spokes h≤D−1, so the same residual bound holds. Consequently each relevant budget satisfies 64S≤49D²+64, and the stated inequality in r supplies the strict exterior gap, two row-length bounds and d+e+3<r. The square root test S<(D+1)² follows from h≤2D−1. Each hub's central debt is at most D in this case.

The leaf arrivals contribute zero to either hub's debt. If 4μ≤D, four times the maximum hub palette bill is at most 3D²+6D+4, since 4μD≤D². If 4μ>D, twice its maximum is at most D²+5D+2. Both are strictly smaller than the corresponding multiples of r−1 under the radius bound; the smaller leaf palette bill also fits. Hence neither hub can receive more than its deficit. This contradicts the exact overload and proves the compared double-star theorem. It assumes a normalized double star with all deficits in the displayed range, not an arbitrary counterexample to Erdős #617.
