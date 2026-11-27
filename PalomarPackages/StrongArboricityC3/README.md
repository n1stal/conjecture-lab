# Strong arboricity can exceed the coloring number

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author

[Bartnicki, Czerwiński, Grytczuk and Miechowicz, Conjecture 3](https://link.springer.com/article/10.1007/s00373-025-02934-5) asks whether the strong arboricity of every graph is at most its coloring number. A strongly woody edge coloring forbids a monochromatic broken cycle, the path obtained by deleting a single edge of a simple cycle.

Start with an edge (xy) and three independent common neighbors (u_1,u_2,u_3). For each of the three pairs (u_i,u_j), add two new vertices adjacent to both members of the pair and to no one else. This gives 11 vertices and 19 edges. The order (x,y,u_1,u_2,u_3), followed by the six new vertices, has at most two earlier neighbors at each vertex. The coloring number is therefore at most 3.

Suppose there were a strongly woody coloring with three colors. Every triangle is rainbow: two equally colored edges would themselves form a monochromatic broken triangle. Consequently only two ordered color pairs are possible on (xu_i,yu_i); two of the three common neighbors have the same pair. Call them (u,v). The paths (u-x-v) and (u-y-v) are monochromatic in distinct colors.

Let (z,w) be the two vertices attached to the pair (u,v). Neither edge of (u-z-v) can use either of the two path colors. Otherwise that edge and the corresponding path through (x) or (y) form a monochromatic path of length three closed by the other edge incident with (z). Thus both edges at (z) have the third color. There is now a monochromatic path of length two from (u) to (v) in every color. Whichever color (uw) uses, it extends the corresponding path to a monochromatic broken four-cycle closed by (vw), a contradiction.

The Lean theorem uses actual edges of the displayed simple graph, checks its ordering and forbids a strongly woody three-coloring under precisely the path-with-closing-edge rule. It does not assert a smallest witness, refute the paper's planar conjecture, or use the distinct ordinary-arboricity bound in Conjecture 2. No human review or source-author endorsement is claimed.
