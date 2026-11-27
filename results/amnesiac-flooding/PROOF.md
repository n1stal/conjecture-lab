# A counterexample to Turau's amnesiac flooding conjecture for every $k\ge4$

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author

## Statement

For every integer $k\ge4$, there is a connected, non-bipartite simple graph $G_k$ on $6k$ vertices such that
$
\operatorname{Rad}(G_k)=\left\lfloor\frac{5k}{2}\right\rfloor,
\qquad
\operatorname{Flood}_k(G_k)\le3 .
$
Here $\operatorname{Flood}_k$ is the minimum number of nonempty synchronous rounds before termination, over all sets of $k$ initial sources. This contradicts the inequality
$
k\,\operatorname{Flood}_k(G)\ \ge\ \operatorname{Rad}(G)+k-1
$
posed in [Section 8 of Turau's preprint](https://arxiv.org/html/2002.10752v4#S8). The protocol and the round convention are those of [Algorithm 1 and Definition 1](https://arxiv.org/html/2002.10752v4#S4). The argument does not refute the weaker bound in Turau's Theorem 4.

## Construction

For $i=0,\ldots,k-1$, take a five-vertex path $a_i-b_i-c_i-d_i-e_i$, and add $x_i$ adjacent to $b_i,c_i,d_i$. For $0\le i<k-1$, add the edge $e_i a_{i+1}$. These are all the edges. The $5k$ path vertices form a single path, each $x_i$ is attached to it, and $b_i,c_i,x_i$ form a triangle. Thus $G_k$ is simple, connected and non-bipartite. Use $c_0,\ldots,c_{k-1}$ as the $k$ initial sources.

## The radius is exactly $\lfloor 5k/2\rfloor$

Label the path vertices in order by $0,\ldots,5k-1$. Give $x_i$ the same label $5i+2$ as $c_i$. Every edge changes the label by at most one. Therefore every walk between the two ends $a_0,e_{k-1}$ has length at least $5k-1$, and the displayed path attains that distance. By the triangle inequality, any vertex is at distance at least $\lceil(5k-1)/2\rceil=\lfloor5k/2\rfloor$ from one of the two ends.

Conversely, let $v$ be a middle vertex of the path and let $r=\lfloor5k/2\rfloor$. Every path vertex is within $r$ of $v$ along the path. Each $c_i$ is at least two path edges from both ends, so its path distance from $v$ is at most $r-2$. The edge $c_i x_i$ puts every added vertex within $r-1$ of $v$. Thus the radius is exactly $r$.

## The protocol stops after three nonempty rounds

A source sends to every neighbor in round 1. Thereafter a vertex that received a message in the previous round sends to all its neighbors **except** the neighbors that sent to it in that round. A vertex that received nothing sends nothing. In the table, vertex letters without subscripts refer to the same block.

| Round | Directed transmissions inside each block | Across a link $e_i a_{i+1}$ |
|---|---|---|
| 1 | $c\to b,\ c\to d,\ c\to x$ | None |
| 2 | $b\to a,\ b\to x,\ d\to e,\ d\to x,\ x\to b,\ x\to d$ | None |
| 3 | $b\to a,\ b\to c,\ d\to e,\ d\to c,\ x\to c$ | Both directions |
| 4 | None | None |

In round 2 only $b,d,x$ were activated by round 1, each by a message from $c$, so each excludes $c$. In round 3, $b$ and $d$ exclude $x$, and $x$ excludes $b,d$. The vertices $a,e$ were activated by their sole within-block neighbors. They exclude those neighbors and send across their link if they have one. This gives both directions on each link.

After round 3, only $a,c,e$ have received anything. The vertex $c$ received from all three of its neighbors. The vertices $a,e$ each received from their within-block neighbor and, where applicable, their across-link neighbor. In every case there is no eligible recipient for round 4. An empty round is followed by another empty round, so the protocol remains silent. All vertices were reached: $b,d,x$ in round 1, $a,e$ in round 2, and the $c_i$ were the sources. The final empty round is not counted.

Thus the displayed choice of sources gives $\operatorname{Flood}_k(G_k)\le3$. It also reproduces the 24-vertex example at $k=4$: the nonempty rounds have $12,24,26$ transmissions, followed by zero, and the radius is 10.

## The inequality fails

For $k\ge4$,
$
\operatorname{Rad}(G_k)+k-1-3k
=\left\lfloor \frac{k}{2}\right\rfloor-1\ge1 .
$
Together with $k\operatorname{Flood}_k(G_k)\le3k$, this proves the strict reverse inequality for each $k\ge4$. The proof needs an upper bound on the minimum flooding time, not an enumeration of all source sets.

## Verification and sources

The [Lean family proof](../../Proofs/AmnesiacFamily.lean) formalizes the same block graph, transition table, exact radius, and comparison with the minimum over source sets. Its final declaration is `FloodFamily.refutes_turau_for_each`. See the [finite example](../../Proofs/Amnesiac.lean), [audit and prior-work discussion](audit.md), and [Palomar record](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000065&version=1).
