# Ordered spectral proximity forces adjacency rank at most five

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author

For a simple graph on $3n$ vertices with $n\ge3$, order its adjacency eigenvalues from largest to smallest. If the sum of their squared differences from $(2n,0,\ldots,0,-n,-n)$ is strictly below $2/3$, its adjacency matrix has rank at most five.

This answers Problem 21 of Jovanović, Sedlar and Škrekovski. Their separate Conjecture 20 asks which graphs minimize a spectral distance.

[Original problem, §5](https://arxiv.org/html/2610.18636v2#S5) · [Written proof and finite certificates](proof.md) · [Source and prior-work audit](audit.md)

Lean checks [`SpectralRank.problem_21`](../../SpectralRank/SpectralTop.lean). [Reproduce the check](../../docs/verification.md) · [Palomar registration](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000004&version=1)
