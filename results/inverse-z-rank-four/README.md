# Inverse Z-polynomials through rank four

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author

Gao, Ruan and Xie conjectured that the coefficients of the inverse Z-polynomial are log-concave. For every matroid on a finite ambient type of rank at most four, the coefficients are positive from degree zero through the rank and vanish above it. Each interior coefficient satisfies $a_i^2 \ge a_{i-1}a_{i+1}$. Higher ranks remain outside this theorem.

At rank four the coefficients have the form $(A,B,C,B,A)$. Bounds on the successive differences $B-A$ and $C-B$ give the two interior inequalities. [Original conjecture](https://arxiv.org/html/2507.01332v1) · [Written proof](PROOF.md) · [Source and prior-work audit](audit.md)

Lean checks [`ConjectureLab.Submission.inverse_z_rank_at_most_four`](../../Solution.lean) using [`InverseZ.matroidInverseZ_rank_at_most_four`](../../InverseZProofs/Main.lean). [Reproduce the check](../../docs/verification.md) · [Palomar registration](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000061&version=1)
