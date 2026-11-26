# Van Cott–Zhang Conjecture 5.2(1) is false

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

[Full family proof](FAMILY-PROOF.md): the pattern exists at every length at least 11. The general ban in part (1) fails at every length 13, 16, 19, …; the two-family classification in part (3) fails at every length 14, 17, 20, … . The 7- and 10-denomination cases and the length-9 classification in part (2) are not settled here.

[Lean statement](../../Palomar/CoinFamily/Challenge.lean) · [Lean solution](../../Palomar/CoinFamily/Solution.lean) · [Length-14 audit](LENGTH14-AUDIT.md)
