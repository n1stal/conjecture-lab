# Source, scope, and prior-work audit

- Exact target: C. A. Van Cott and Q. Zhang, *The Change-Making Problem for Six Coin Values and Beyond*, §5, Conjecture 5.2(1), [arXiv version 2](https://arxiv.org/html/2303.00078v2#S5) and [journal DOI](https://doi.org/10.1016/j.disc.2025.114669).
- Scope: The 13-denomination witness refutes the general ban for length $3r+1$ ($r\ge2$). It does not settle the separate assertions for 7 or 10 denominations, or parts (2) and (3). The separately reported 17-denomination example concerns part (3); it is not used or claimed here.
- Prior work: On 26 November 2026, searches by the exact witness, by the paper title and authors, and by conjecture number and prefix-pattern terminology found no earlier match for this witness or resolution. This is a bounded search, not a claim of priority.
- Verification: [Full proof](PROOF.md) and [Lean source](../../Proofs/VanCottZhang.lean). The mathematical argument reduces all-amount optimality to a finite residue check; there is no cap on the amounts in the theorem. Lean 4.35.0-rc2 checks `CoinOrder.vanCottZhangConjecture521_false`, with only `propext` and `Quot.sound`.
