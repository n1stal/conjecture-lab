# A counterexample to Turau’s amnesiac flooding conjecture

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author

Volker Turau’s [arXiv preprint, §8](https://arxiv.org/html/2002.10752v4#S8)
asks whether every finite connected non-bipartite graph satisfies
`k · Floodₖ(G) ≥ Rad(G) + k − 1`. A graph on 24 vertices violates it:
`Flood₄(G) ≤ 3` but `Rad(G) = 10`, so that `12 < 13`.

## Witness

Take a path on twenty vertices, split into four consecutive blocks of five.
In each block, add one vertex adjacent to the middle three path vertices.
Use the four middle path vertices as simultaneous sources. This graph is
connected and contains a triangle. Label every added vertex with the
position of its block’s center. Along an edge the labels differ by at most
one, so the two original endpoints are distance nineteen and force radius
at least ten. A central path vertex reaches all vertices in at most ten
steps.

The first four synchronous rounds contain respectively 12, 24, 26 and 0
directed transmissions. In round four, every recipient from round three
has already received from all its neighbors. The final empty round is not
counted, as in the first-round complete-graph example in Turau’s
[Algorithm 1 and Definition 1](https://arxiv.org/html/2002.10752v4#S4).

The [Lean file](../../Proofs/Amnesiac.lean) checks the graph, connectivity,
non-bipartiteness, radius, exact transition rule and the counterexample. It
checks the original rule directly, not via a proxy or an assumed parity lemma.
The proven weaker lower bound in Turau’s Theorem 4 is not refuted.

## Prior-work audit (2026-11-26)

- [Turau, SOFSEM 2021](https://doi.org/10.1007/978-3-030-67731-2_5) studies
  the same synchronized multi-source problem. The precise conjecture we
  refute is pinned to the arXiv v4 statement above.
- [Hussak and Trehan 2023](https://doi.org/10.1007/s00446-023-00448-y)
  prove termination for general finite graphs and give bounds involving the
  eccentricity of the starting set, not this minimization inequality.
- [Austin et al., DISC 2025](https://doi.org/10.4230/LIPIcs.DISC.2025.10)
  study stateless termination and robustness to message loss, not the
  stated radius inequality in the unmodified synchronous protocol.

A bounded search for the exact inequality and variants under “amnesiac
flooding,” “multi-source,” “k-flooding,” and “radius,” and searches for the
arXiv identifier in public Lean catalogs and GitHub, located no matching
prior counterexample or formalization. This is not a priority claim.
