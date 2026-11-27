# Sharp vertex and edge separator bounds for four prescribed vertices

Choose four distinct terminals in a finite connected simple graph and let S be the sum of the six distances between them. Then:

| Separator type | Exact guaranteed count |
| --- | --- |
| Pairwise disjoint vertex sets, each avoiding all four terminals | max(0, ⌈(S − 10)/4⌉) |
| Pairwise disjoint undirected edge sets; edges may be incident to a terminal | ⌈(S − 2)/4⌉ |

Each set separates at least one pair of terminals. For each integer S ≥ 6, each bound has a realizing graph; the vertex and edge realizing graphs need not be the same. The bound is not about the size of a single cut or about all the cuts separating one fixed pair.

The vertex theorem answers the four-terminal separator branch of [Hak and Kozerenko's Question 3](https://arxiv.org/html/2611.17259v1#S7); the edge theorem extends their three-terminal analogue in [Remark 6.2](https://arxiv.org/html/2611.17259v1#S6). The source's three-terminal results are credited and reproved. This does not resolve the case of five or more terminals and does not include the separate distance-packing branch. [PROOF.md](PROOF.md) gives both arguments and sharp examples for all S.

The comparator checks two declarations: `HakKozerenkoSeparatorGraph.sharp_four_vertex_separator_bound` and `HakKozerenkoEdgeSeparator.sharp_four_edge_separator_bound`. Both use an actual symmetric loopless graph and unit-edge walks; exact shortest distances include a walk and a proof of minimality for every vertex pair. The Challenge imports only bundled Std and contains the self-contained model and two intended theorem holes. The Solution and support modules never import Challenge. Lean 4.35.0-rc2 with bundled Std is the sole toolchain dependency.

Jaime Nistal is the responsible author; Codex (OpenAI) is credited for AI-assisted mathematical reasoning, exact checks and Lean formalization.
