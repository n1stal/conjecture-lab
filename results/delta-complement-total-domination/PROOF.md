# Pinhe Chen’s total-domination conjecture for the δ-complement

For a graph (G) with no isolated vertices, let (gamma_t(G)) be the minimum size of a vertex set that gives **every** vertex a selected neighbor. This includes the selected vertices themselves. The (delta)-complement (G_delta) toggles the adjacency of each pair of distinct vertices of equal degree in (G), and keeps the adjacency of every pair with unequal degrees.

**Theorem (Chen’s Conjecture 4).** If (G) has (n) vertices in (k) degree classes, and neither (G) nor (G_delta) has an isolated vertex, then
[
  gamma_t(G)+gamma_t(G_delta)le n+2k.
]

We prove the following stronger statement: given two isolate-free graphs (A,B) on the same finite vertex set partitioned into (k) nonempty parts, the same bound holds whenever the two induced graphs on each part are ordinary complements. No relation between the cross-part edges is needed.

### The ordinary-complement bound

We first give a direct proof of the inequality from Cockayne, Dawes, and Hedetniemi that will be used inside a part. Suppose both (H) and its ordinary complement are isolate-free, and (H) has (r) vertices. At a vertex (v) of degree (d) in (H), select (v) and one neighbor of every vertex outside its open neighborhood. These choices totally dominate (H) and use at most (r-d+1) vertices. If (v-u-w) is an induced path with endpoint (v), the witness (u) can serve for both (v) and (w), saving one vertex.

Fix (v) and choose a neighbor (u) in (H) and a neighbor (w) in the complement. If (uw) is an edge of (H), then (v-u-w) is an induced path of (H); otherwise (v-w-u) is an induced path of the complement. So at the same root (v), one graph allows the saving and the other allows the plain bound. Since the two degrees of (v) sum to (r-1), the two total dominating sets have combined size at most (r+2).

### Cover a part, not necessarily from within it

For each part (C) of size (r), select sets (S_A(C), S_B(C)) of vertices, allowed to come from anywhere in the respective graph, that give every vertex of (C) a selected neighbor.
- If (r=1), choose one neighbor in each graph. The total cost is (2).
- If both induced graphs on (C) are isolate-free, the ordinary-complement bound supplies these sets with total cost at most (r+2).
- Otherwise (rge2) and, by symmetry, (A[C]) has an isolated vertex (x). The vertex (x) is universal in (B[C]): select (x) and any other vertex of (C) to cover (C) in (B). In (A), select all vertices of (C) that have a neighbor within (C), and one global neighbor for each remaining vertex of (C). An internally nonisolated vertex has an internally nonisolated neighbor; an internally isolated vertex gets its chosen external neighbor, which exists because (A) is isolate-free. At most (r) vertices are selected in (A). The total cost is again at most (r+2).

Take the unions of the selected sets separately in (A) and (B). Every vertex is dominated from the cover of its own part, including any external witness chosen while covering a different part. The sum of the sizes of the unions is at most the sum of the local costs, hence at most (n+2k). Taking the degree partition of (G), (A=G) and (B=G_delta) gives the conjecture. (square)

### Prior work and scope

- [Pinhe Chen, *Refined Nordhaus–Gaddum-Type Bounds for Roman and Total Domination on δ-Complement Graphs*](https://doi.org/10.3390/math14111797), *Mathematics* **14**(11):1797, 22 May 2026, Conjecture 4. Theorem 6 covers the case when every induced degree-class pair is isolate-free. The step permitting external witnesses handles the remaining cases. The paper’s Example 3 already gives sharpness of the conjectured bound.
- [E. J. Cockayne, R. M. Dawes, and S. T. Hedetniemi, *Total domination in graphs*](https://doi.org/10.1002/net.3230100304), *Networks* **10** (1980), 211–219. We reprove only their ordinary-complement upper bound here, not the equality characterization.
- Targeted searches for Chen’s exact title, DOI, and conjecture statement did not identify a later full proof. This is a statement about the sources found, not a guarantee of priority.
