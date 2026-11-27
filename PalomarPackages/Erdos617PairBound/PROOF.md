# Proof: at most \(d_i+d_j-2\) shared exceptions between two high-deficit rows

Jaime Nistal, responsible author. Codex (OpenAI), AI co-author for proof development and Lean formalization.

## Exact setting

A balanced \(r\)-coloring assigns one of \(r\) colors to each unordered pair, with every \(r+1\) distinct vertices seeing each color. We work in one target color, whose graph on the normalized core has independence number at most the number \(a\) of its independent anchors and has no \(K_r\). Choose distinct anchors \(p,q\), with their respective private rows \(P,Q\) of sizes \(r-d,r-e\). A vertex of its private row is either the anchor itself or adjacent to it in the target color, and has no target neighbor among the other anchors. The list \(X\) may be any list of exceptions, which are vertices adjacent in the target color to exactly \(p,q\) among the anchors. These three lists are disjoint and have no repeats.

We prove, for \(r\ge12\), \(d,e\ge3\), \(d+e\le r-3\), that
\[
 |X|\le d+e-2.
\]
The pair-sum condition follows in the usual bounded-exception normalization: with at least four anchors, positive deficits, and total deficit \(b-1\le r-1\), at least two deficits on other rows lie outside the pair sum. The Lean theorem uses the pair-sum condition explicitly, along with the two scoped core caps, rather than asserting the normalization itself.

The original conjecture is [Erdős–Gyárfás 1999, Conjecture 1](https://www.renyi.hu/~gyarfas/Cikkek/92_splitandbalanced.pdf). The model and the earlier \(|X|\le d+e-1\) bound are recorded in [*Two support normalization*, especially §3](https://erdosproblems.ai/wiki/research/erdos_617/two_support_normalization#3-pair-capacities-and-additional-two-row-caps). The [earlier even-order odd-cycle argument](https://erdosproblems.ai/wiki/research/erdos_617/independent/growing_local_independence_range) is credited below. The new result excludes the one remaining boundary multiplicity when both deficits are at least three. No full-conjecture claim is made.

## 1. Two rows give a triangle-free missing-target graph

For \(Y\subseteq X\), let \(U=P\cup Q\cup Y\), and let \(F\) be the graph on \(U\) whose edges have non-target color. It is triangle-free: an \(F\)-triangle would be three target-independent vertices, all distinct from and nonadjacent in target color to the \(a-2\) remaining anchors. Together those vertices would make a target-independent \((a+1)\)-set in the core. Also \(\alpha(F)\le r-1\) because the target graph on the core has no \(K_r\).

Each color has independence number at most \(r\) in the ambient graph. On any \(n\)-vertex set its edges number at least \(n-r\): removing one endpoint of every edge leaves an independent set of size at least \(n\) minus the edge count. The \(r-1\) non-target colors are disjoint as edge sets, so
\[
 e(F)\ge (r-1)(|U|-r).
\]

## 2. Recover the earlier cap at even order

Suppose \(|X|\ge d+e\) and choose exactly \(d+e\) exceptions. Then \(|U|=2r\) and \(e(F)\ge r(r-1)\). Every neighborhood in a triangle-free graph is independent, so every degree of \(F\) is at most \(r-1\). Double-counting degrees gives that every degree is exactly \(r-1\).

Since \(\alpha(F)\le r-1\) and \(|U|=2r\), \(F\) cannot be bipartite. Take its shortest odd cycle \(C\), of length \(\ell\ge5\). It has no chord, because a chord splits it into two shorter cycles, exactly one odd. If an outside vertex saw three cycle vertices, their three cyclic gaps would have length at least two by triangle-freeness. At least one gap would be odd, and closing that gap through the outside vertex would give a shorter odd cycle. Thus every outsider has at most two neighbors on \(C\), and
\[
 \ell(r-1)=\sum_{u\in C}\deg_F(u)
 \le 2\ell+2(2r-\ell)=4r.
\]
But \(5(r-1)>4r\) for \(r\ge6\). This recovers the earlier \(|X|\le d+e-1\) bound. The formalization derives the shortest odd cycle using walks: an absence of odd closed walks permits a consistent parity labeling via a reachability root in each component, and a shortest odd closed walk cannot repeat a vertex.

## 3. Rigidity at order \(2r-1\)

It remains to exclude \(|X|=d+e-1\). Take \(Y=X\). Now \(|U|=2r-1\) and \(e(F)\ge(r-1)^2\). The independence cap still precludes bipartiteness. Let \(C\) be a shortest odd cycle of length \(\ell\). Mantel's bound on the graph induced by the vertices outside \(C\), together with the previous incidence bound, gives
\[
 e(F)\le\ell+2(2r-1-\ell)+\frac{(2r-1-\ell)^2}{4}.
\]
The right side decreases with \(\ell\). At \(\ell=7\) it is \(r^2-4r+7<(r-1)^2\). Hence \(C\) is a pentagon. Put \(R=r-3\), so that there are \(2R\) outsiders. The maximum possible expression above at \(\ell=5\) is \((r-1)^2+1\). Thus the outsider graph loses at most one unit in total from \(R^2\) possible outsider edges and two cycle-neighbor incidences per outsider.

Here is the exact outsider classification. In their induced graph take a maximum-degree vertex of degree \(\Delta\), with independent neighborhood \(A\), and let \(B\) contain the other outsiders. Summing degrees over \(B\) shows
\[
 R^2-1\le e(F[U\setminus C])
 \le \Delta(2R-\Delta)-e(F[B])
 =R^2-(R-\Delta)^2-e(F[B]).
\]
If \(B\) had an edge, then \(\Delta=R\) and \(B\) would have just one edge. The endpoints of that edge have disjoint neighborhoods in \(A\), costing at least \(R\) possible crossings. The resulting upper bound \(R^2-R+1\) is too small. Therefore both sides are independent. There are just two size patterns: balanced sizes \(R,R\), with at most one crossing missing, or sizes \(R-1,R+1\), with every crossing present. There is only one unit of loss: it cannot be spent on both an absent crossing and a missing cycle incidence.

Label the pentagon by residues modulo 5. A full outsider has two cycle neighbors, which must be the neighbors of a unique pentagon label \(j\); call \(j\) its type. Adjacent full outsiders have disjoint cycle-neighbor pairs, so their types are adjacent in the pentagon. If two nonempty families of types are completely cross-adjacent, at least one of the two families is uniform: two different types have at most one common neighbor in a pentagon.

In the imbalanced case both parts have all crossings and all outsiders are full. Fix one type \(t\) on the smaller side. Every larger-side type is one of \(t-1,t+1\). The corresponding two pentagon vertices \(t-1,t+1\) are nonadjacent to each other and to every vertex on the larger side. They extend that side to an independent set of size \(R+3=r\), impossible. Only balanced sizes remain.

## 4. A large class of equal neighborhoods

With balanced sides, there are three possibilities.

1. **All crossings present, all outsiders full.** At least one side has a uniform type \(t\). Every vertex of that side, as well as the cycle vertex \(t\), has neighborhood exactly the opposite side and the two cycle neighbors \(t-1,t+1\). There are \(R+1\) such vertices, of degree \(R+2\).
2. **All crossings present, one outsider weak.** Temporarily omit that vertex. If the opposite, full-sized side is uniform, its \(R\) vertices already have equal neighborhoods and degree \(R+2\). Otherwise the \(R-1\) full vertices on the weak vertex's side are uniform of some type \(t\). The cycle vertex \(t\) sees the entire opposite side. It cannot see the weak vertex, since the weak vertex also sees the entire opposite side and this would form a triangle. So \(t\) joins the \(R-1\) uniform vertices, again giving \(R\) vertices of degree \(R+2\) with equal neighborhoods.
3. **Exactly one crossing absent, all outsiders full.** Let its endpoints be \(u,v\). If their types are adjacent, the type families are completely cross-adjacent, so one side is uniform of type \(t\). Omit the endpoint of the absent crossing on that side and include the cycle vertex \(t\), giving \(R\) equal neighborhoods of degree \(R+2\). If the endpoint types coincide, both ordinary sides would have their types in the same two-element neighbor set of that type, where no cross-adjacent pair exists. This is impossible. Otherwise the endpoint types are distinct and nonadjacent; relabel the pentagon to make them \(0,2\). The ordinary side opposite the exceptional endpoint of type \(2\) has types in \(\{1,3\}\), and the other ordinary side has types in \(\{1,4\}\). Their only adjacent type pair is \((3,4)\). The \(R-1\) ordinary vertices of type \(3\), together with cycle vertex \(3\), therefore have the same neighborhood: the opposite part and the cycle vertices \(2,4\). They have degree \(R+2\).

In every case \(F\) has at least \(R=r-3\) false twins (vertices with identical open neighborhoods), of degree \(R+2=r-1\).

## 5. The anchor words rule out the boundary

With respect to the ordered pair \((p,q)\), adjacency words in \(F\) are \((0,1)\) on \(P\), \((1,0)\) on \(Q\), and \((0,0)\) on \(X\); the diagonal bit is zero. All false twins have the same word, so all lie in one of these three sets. They cannot lie in \(X\), because
\[
 |X|=d+e-1\le r-4<r-3.
\]
Each private row has at most \(r-3\) vertices. Thus if the twins lie in \(P\), they equal \(P\), including the anchor \(p\). The degree of \(p\) in \(F\) is exactly \(|Q|=r-e\), by the same three anchor words. The twin degree \(r-1\) would force \(e=1\), contrary to hypothesis. The case of \(Q\) is symmetric. This excludes the boundary and proves \(|X|\le d+e-2\).

The compared Lean endpoint assumes no cycle witness, missing-target density, auxiliary graph classification, or older pair cap; all are derived from the stated normalized data and balanced coloring. The finite pentagon type checks are evaluated by Lean's kernel, with no external solver or nonstandard axiom. This is a partial bound on pairs in the original conjecture, not an exclusion of all normalized cores.
