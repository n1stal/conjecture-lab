# Property P: sharp reciprocal bound

**Result:** The maximum reciprocal sum for Property P subsets of $\{1,\ldots,300\}$ is $3/2$, attained by $\{1,2\}$. This is an exact finite optimum, not a proof for arbitrary positive integers.

[Exact search and proof of coverage](#why-the-exact-search-covers-every-subset-in-the-interval) · [Raw reports](../results/README.md) · [Reproduce](../docs/verification.md#property-p-reciprocal-sums)

**Status:** Finite exact evidence and exploratory results; no global proof or novelty claim.

**Statement under test:** For every finite subset (A) of the positive integers with no distinct (a<b<c) in (A) such that (amid b+c), is (sum_{ain A}1/a le 3/2)? If true, ({1,2}) is sharp. A finite counterexample refutes the bound. Conversely, an all-finite bound also bounds infinite sets by monotone convergence.

**Prior art:** [Erdős Problem 12](https://www.erdosproblems.com/12) asks about the reciprocal sum. Howe, Huffman, Kohlmeyer and Kruer [claim a uniform bound in Theorem 1.3](https://hexagonmath.org/2611.00765v1). Treat proving existence of *some* constant as a different task from determining the best one. The linked proof has not been independently audited here. Literature search on the sharp constant remains incomplete.

## Experiments

| Search | Outcome | What it establishes |
|---|---|---|
| Exact 1–200 | 3/2, {1, 2}, 62,108 nodes | Finite optimum |
| Exact 1–300 | 3/2, {1, 2}, 951,769 nodes | Finite optimum |
| Exact 2–150 | 40154231/36716372 ≈ 1.09363, 351,639 nodes | Finite optimum, without 1 |
| Greedy 2–5000, seed 20261126 | 2,000 trials, no improvement on starter | No global or finite upper bound |

The without-1 witness is `{3, 5, 6, 8, 11, 20, 23, 26, 56, 71, 143, 146}`. It beats `{2,3,4}` (13/12). Its validity and weight can be checked independently; the same exact solver replays optimality, and an independent direct enumeration cross-checks small instances.

## Why the exact search covers every subset in the interval

The search enumerates in increasing order. Adding (b) to a valid prefix creates only new constraints involving some earlier (a<b), the newly selected middle element (b), and a potential future (c>b). Remove exactly the eligible (c) with (cequiv-bmod a). Constraints involving two already selected elements were applied when the second one was added. Every valid set has one sorted construction, so no valid set is excluded except by the objective bound. The sum of all remaining candidate weights is an upper bound on any extension, so pruning cannot remove an improvement. Weights are integers scaled by an exact common multiple of the denominators. A capped search explicitly reports `witness_only`.

## Next attacks

- If (1in A), there can be at most one other element, so the exact maximum is (3/2). If (2=min A), at most one larger even and one larger odd can occur, so the exact bound is (13/12). This leaves (min Age3).
- A fixed minimum (m) prohibits simultaneously using two opposite non-self-inverse residues modulo (m) above the minimum; each of the self-inverse residues can occur at most once. Develop this as a computable bound and see whether constraints from additional small elements strengthen it enough. A one-modulus argument alone does not control the reciprocal tail.
- Look for constructions with better reciprocal mass, and verify any candidate exceeding (3/2) independently before attempting a proof or claiming a counterexample.
