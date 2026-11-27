# Strict inverse Z log-concavity for line-preserving projective restrictions

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author

Take a finite projective geometry and retain at least two points on every line. In every rank, the inverse Z-polynomial of the resulting restriction has positive coefficients through its rank. At each interior degree they satisfy $a_i^2 > a_{i-1}a_{i+1}$.

The proof factors the coefficients into a strictly log-concave Gaussian-binomial factor and a positive log-concave factor accounting for the deleted points. The audit credits earlier formulas for projective geometries and overlapping deletion results. [Original conjecture](https://arxiv.org/html/2507.01332v1) · [Written proof](proof.md) · [Source and prior-work audit](audit.md)

Lean checks [`InverseZProjective.GaussianIncidence.represented_inverseZ_strict_logConcave`](../../InverseZProjective/ProjectiveMain.lean). [Reproduce the check](../../docs/verification.md)
