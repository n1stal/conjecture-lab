# Conjecture Lab · Lean-checked proofs in discrete mathematics

Four sources flood a 24-vertex graph in three rounds. Turau’s conjecture predicts that the number of sources times the flooding time is at least 13 for this graph, but **4 × 3 = 12 < 13**.

[Full catalogue](results/README.md) · [Palomar registrations](#palomar-registrations) · [Verification](docs/verification.md)

<!-- BEGIN GENERATED RESULTS -->

## Results checked on main

| Problem | What we proved |
| --- | --- |
| [Turau’s amnesiac flooding conjecture](results/amnesiac-flooding/README.md) | The construction gives a counterexample for every number of sources k ≥ 4. |
| [Ordered spectral proximity (Problem 21)](results/spectral-rank-problem-21/README.md) | For a simple graph on 3n vertices (n ≥ 3), adjacency rank is at most five if its ordered adjacency spectrum lies at squared distance < 2/3 from the balanced tripartite profile. |
| [Inverse Z-polynomials through rank four](results/inverse-z-rank-four/README.md) | Positivity and log-concavity for every finite matroid of rank at most four. |
| [Inverse Z-polynomials on projective restrictions](results/inverse-z-projective/README.md) | Strict log-concavity in every rank when at least two projective points remain on every line. |
| [Van Cott–Zhang’s coin systems](results/van-cott-zhang-521/README.md) | The target prefix pattern occurs at every length ≥ 11. At lengths 14, 17, 20, …, systems with that pattern exist outside both proposed families. |

**Checked baseline** · [Property P: the finite witness {1, 2}](results/property-p-baseline/audit.md). Its reciprocal sum is 3/2.

## Palomar registrations

Each registration links the exact statement, source commit and verification report.

| Registered | Result |
| --- | --- |
| 2026-11-27 | [Sharp distance packing for four prescribed terminals](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000051&version=1) |
| 2026-11-27 | [Counterexample to Cazenave's second spectral graph conjecture](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000045&version=1) |
| 2026-11-27 | [Reflection of exceptional breakpoints for k-wise independent bits](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000041&version=1) |
| 2026-11-27 | [Seven-denomination case of Van Cott–Zhang Conjecture 5.2(1)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000034&version=1) |
| 2026-11-27 | [Chen's total-domination conjecture for the delta complement](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000025&version=1) |
| 2026-11-27 | [Ordered spectral proximity forces adjacency rank at most five](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000004&version=1) |
| 2026-11-27 | [Van Cott–Zhang prefix patterns for every length at least eleven](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000001&version=1) |
| 2026-11-26 | [A counterexample and infinite family for Turau's amnesiac flooding conjecture](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000065&version=1) |
| 2026-11-26 | [Inverse Z-polynomial log-concavity through rank four](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000061&version=1) |

<details>
<summary>Research branches and preflight packages</summary>

These source snapshots include experiments, preflights and earlier versions of published work.

| Branch | Source commit |
| --- | --- |
| <code>palomar/preflight-beka-c511</code> | [61547c5](https://github.com/n1stal/conjecture-lab/tree/61547c5decdee20dd8b049fbc28c45b75caaacd6) |
| <code>palomar/preflight-cazenave-c2</code> | [2a5b608](https://github.com/n1stal/conjecture-lab/tree/2a5b608164c4579d7816f2fc9e15332b0321527f) |
| <code>palomar/preflight-chen-c4</code> | [519eaf6](https://github.com/n1stal/conjecture-lab/tree/519eaf69d1aa38f53663759817c66aee8f105698) |
| <code>palomar/preflight-coin-family</code> | [2be8139](https://github.com/n1stal/conjecture-lab/tree/2be8139b53f316fe27e6dab873febeaae28b4908) |
| <code>palomar/preflight-coin-family-v2</code> | [8e6457d](https://github.com/n1stal/conjecture-lab/tree/8e6457de04c0712a02123c07af9594ac5a6509d2) |
| <code>palomar/preflight-coin-seven</code> | [65752dd](https://github.com/n1stal/conjecture-lab/tree/65752ddca94f0e646e4e807cb821bfe540946fee) |
| <code>palomar/preflight-erdos617-pair-bound</code> | [90304d3](https://github.com/n1stal/conjecture-lab/tree/90304d37dd3d5478054e5c3227465a9817fe297d) |
| <code>palomar/preflight-erdos617-pair-star</code> | [ffd0c62](https://github.com/n1stal/conjecture-lab/tree/ffd0c62d08aa36ec491dce19720ad707dc1536df) |
| <code>palomar/preflight-erdos617-pair-star-double</code> | [581978b](https://github.com/n1stal/conjecture-lab/tree/581978b88cb7651e02715678c6e073dfc5776748) |
| <code>palomar/preflight-four-terminal-packing</code> | [a82e9bf](https://github.com/n1stal/conjecture-lab/tree/a82e9bfeaf6622cf3cfcbaffe29c8cdfda3ee3f7) |
| <code>palomar/preflight-four-terminal-separators</code> | [99f1d53](https://github.com/n1stal/conjecture-lab/tree/99f1d53ebec3ea23f41e2f3a26b7b11a16b36423) |
| <code>palomar/preflight-inverse-z-glued-cycles</code> | [0171bab](https://github.com/n1stal/conjecture-lab/tree/0171bab02e610a7f6ccc679903b6157c152dc5b6) |
| <code>palomar/preflight-inverse-z-paired-graphs</code> | [c520189](https://github.com/n1stal/conjecture-lab/tree/c520189840961d63786893e54031b08dd81a7100) |
| <code>palomar/preflight-problem-21</code> | [20eac3f](https://github.com/n1stal/conjecture-lab/tree/20eac3fcc461798315a036e3bc4a540840f3db07) |
| <code>palomar/preflight-projective-inverse-z</code> | [fb5a667](https://github.com/n1stal/conjecture-lab/tree/fb5a6676d72eab20b0ddbc3e9aafd4f68f18af3b) |
| <code>palomar/preflight-strong-arboricity-c3</code> | [d60d653](https://github.com/n1stal/conjecture-lab/tree/d60d653b0066d5bce4c1556abce7b14bc705f1e7) |
| <code>palomar/preflight-thagomizer-inverse-z</code> | [3a47d1a](https://github.com/n1stal/conjecture-lab/tree/3a47d1ad438850fcf4d69c247fbfc52b71bd04e1) |
| <code>palomar/preflight-thagomizer-inverse-z-v2</code> | [f70a4b9](https://github.com/n1stal/conjecture-lab/tree/f70a4b985d29f539adcd51e93b9707d2a31e355b) |
| <code>palomar/preflight-turau</code> | [d77d114](https://github.com/n1stal/conjecture-lab/tree/d77d1144fa33ee24ced91f8873f4a1d56567abe3) |
| <code>palomar/preflight-walk-maple-degree-four</code> | [21ea097](https://github.com/n1stal/conjecture-lab/tree/21ea097cf2b99f311e068f983f0b661997f8728a) |
| <code>palomar/preflight-walk-maple-quartic</code> | [703cfeb](https://github.com/n1stal/conjecture-lab/tree/703cfeb62c92ba58ac9545c963c63788263d79e1) |
| <code>palomar/preflight-walk-maple-quartic-v2</code> | [10fc3a9](https://github.com/n1stal/conjecture-lab/tree/10fc3a93b8840e9004c6dd37850b5bc567dcd8a8) |
| <code>palomar/preflight-weighted-terminal-packing</code> | [0f3cd2b](https://github.com/n1stal/conjecture-lab/tree/0f3cd2bd4eb1a3825e16527d9eee81ec95e7a965) |
| <code>palomar/preflight-weighted-terminal-packing-v2</code> | [8285dfb](https://github.com/n1stal/conjecture-lab/tree/8285dfb7d714c5ebcb43052a33eb9cf0e0e59017) |
| <code>results/delta-complement-total-domination</code> | [4c7e0ef](https://github.com/n1stal/conjecture-lab/tree/4c7e0efd1d7c34c99a9fb4e1a7845cbc9cc6ad76) |
| <code>results/spectral-conjecture-20</code> | [c634850](https://github.com/n1stal/conjecture-lab/tree/c63485076f9cc5d5026151184a2f3ec81a6aa781) |
| <code>results/spectral-conjecture-20-squared</code> | [505a52b](https://github.com/n1stal/conjecture-lab/tree/505a52b9fa98f8ea66bf26406e12a009a6f604de) |
| <code>results/van-cott-zhang-seven</code> | [184d450](https://github.com/n1stal/conjecture-lab/tree/184d450db881cada3875b05cc4774e6424b58876) |
| <code>verification/amnesiac-flooding</code> | [a282890](https://github.com/n1stal/conjecture-lab/tree/a282890470a9900a0eb3822227b7c49d31a42d45) |
| <code>verification/inverse-z-rank-four</code> | [fba1c28](https://github.com/n1stal/conjecture-lab/tree/fba1c28396deea5482f5f38f077c6117c49dbf8e) |
| <code>verification/palomar-preflight</code> | [b3f8427](https://github.com/n1stal/conjecture-lab/tree/b3f84276ee45b7820ada843aa81b13543bd99211) |

</details>

<!-- END GENERATED RESULTS -->

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author. [Attribution and citation](docs/provenance.md) · [Prior-work policy](docs/research-process.md) · [Apache 2.0](LICENSE)
