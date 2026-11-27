# A high-deficit parallel-pair bound for Erdős Problem 617

**Jaime Nistal** is the responsible author. **Codex (OpenAI)** is credited as the AI co-author for proof development and Lean formalization.

In a balanced \(r\)-coloring, every set of \(r+1\) vertices sees all \(r\) colors. In the normalized two-support core for one target color, an exception can have exactly two of the core anchors as its neighbors. This result bounds how many exceptions can share the same pair.

**Result.** For \(r\ge12\), if the two corresponding private rows have deficits \(d_i,d_j\ge3\), then the number of exceptions supported on precisely those two anchors is at most \(d_i+d_j-2\). The previously known bound is \(d_i+d_j-1\). The result assumes the exact normalized-core hypotheses, including the scoped target independence and clique caps and \(d_i+d_j\le r-3\). It does not resolve [Erdős Problem 617](https://www.erdosproblems.com/617), prove that a given support multigraph is realizable, or improve any known fixed-case classification.

[PROOF.md](PROOF.md) gives the full argument. If the older cap were attained, the missing-target graph on the two rows and their exceptions would have \(2r-1\) vertices. Its shortest odd cycle and tight density force at least \(r-3\) vertices with the same neighborhood and degree \(r-1\). Their adjacencies to the two anchors put all of them in one private row. That row then equals the set of twins, forcing the other row to have \(r-1\) vertices, a contradiction.

Sources: [Erdős–Gyárfás, *Split and balanced colorings of complete graphs*, Conjecture 1](https://www.renyi.hu/~gyarfas/Cikkek/92_splitandbalanced.pdf); [prior normalization and minus-one bound, §§1–3](https://erdosproblems.ai/wiki/research/erdos_617/two_support_normalization); [prior even-order argument and five-cycle boundary example](https://erdosproblems.ai/wiki/research/erdos_617/independent/growing_local_independence_range).

The only compared declaration is **ParallelMantel.Pentagon.NormalizedPair.high_parallel_multiplicity_bound**. Challenge imports only Std; the separately compiled Solution does not import Challenge. The pinned Lean release is 4.35.0-rc2. No external library, network dependency, or nonstandard axiom is used.

- Run the proof with **lake build**.
- Run isolated Challenge and strict Solution with **./replay.sh** on the pinned toolchain. The single stub in Challenge is intentional.
- For official statement comparison, run **lake comparator --config comparator.json** in an environment supporting its bubblewrap sandbox.
