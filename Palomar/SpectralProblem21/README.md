# Palomar statement: spectral Problem 21

For n ≥ 3, a simple undirected graph on 3n vertices whose decreasing
ordered adjacency spectrum has a **sum of squared** differences less
than 2/3 from (2n, 0, …, 0, −n, −n) has real adjacency rank at most five.
This includes disconnected graphs and answers
[Jovanović–Sedlar–Škrekovski, Problem 21](https://arxiv.org/html/2610.18636v2#S5).
It does not address the nearest-graph and uniqueness claims in Conjecture 20.

The Challenge imports only pinned Mathlib. The Solution uses the same
statement and calls the repository's substantive proof in
[SpectralRank/SpectralTop.lean](../../SpectralRank/SpectralTop.lean).
See the [written proof and audit](../../results/spectral-rank-problem-21/proof.md)
and [formalization metadata](formalization.yaml), including AI attribution.

Run from the repository root with the pinned Lean toolchain:

```sh
lake build --wfail SpectralProblem21Solution
lake comparator --config Palomar/SpectralProblem21/comparator.json
```

For Palomar use the repository root as the Lake project, explicitly select
`Palomar/SpectralProblem21/comparator.json` and
`Palomar/SpectralProblem21/formalization.yaml`, and use the full reviewed
commit SHA. The intentional theorem hole is confined to the Challenge.
