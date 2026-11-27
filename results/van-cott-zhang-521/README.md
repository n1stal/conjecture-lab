# Counterexamples to Van Cott–Zhang Conjecture 5.2(1) and (3)

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author

```text
1, 2, 4, 5, 7, 8, 10, 12, 15, 18, 23, 26, 34
```

Greedy change is optimal for every amount using the first one, two, three, or all thirteen denominations. It is not optimal for every amount using any of the nine intermediate prefixes. This refutes the general length $3r+1$ prohibition in Conjecture 5.2(1).

- [Full written proof](PROOF.md)
- [Lean source](../../Proofs/VanCottZhang.lean)
- [Original conjecture](https://arxiv.org/html/2303.00078v2#S5)
- [Scope and prior-work audit](audit.md)

## Stronger follow-up

[Full family proof](FAMILY-PROOF.md): the pattern exists at every length at least 11. The general ban in part (1) fails at every length 13, 16, 19, …; the two-family classification in part (3) fails at every length 14, 17, 20, … . A separate [registered proof for seven denominations](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000034&version=1) establishes the prohibition at length 7. Length 10 and the length-9 classification in part (2) lie outside both results.

[Lean statement](../../Palomar/CoinFamily/Challenge.lean) · [Lean solution](../../Palomar/CoinFamily/Solution.lean) · [Length-14 audit](LENGTH14-AUDIT.md)

Lean checks `CoinOrder.vanCottZhangConjecture521_false` for the witness and `CoinOrder.Family.every_length_ge_eleven`, `CoinOrder.Family.general_prohibition_fails`, `CoinOrder.Family.classification_fails`, and `CoinOrder.Family.conjecture523_false` for the family. [Reproduce the check](../../docs/verification.md) · [Palomar family registration](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000001&version=1)
