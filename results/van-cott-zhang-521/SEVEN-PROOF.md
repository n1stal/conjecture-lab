# Van Cott–Zhang Conjecture 5.2(1): seven denominations

**Jaime Nistal.** OpenAI Codex assisted with the proof search, formalization, and verification.

## Statement

There is no increasing list of seven positive integer denominations beginning at 1 whose first three prefixes and full system are orderly, while its prefixes of lengths four, five, and six are not. A system is *orderly* if greedy change always uses the smallest possible number of coins.

This proves the seven-denomination assertion of [Conjecture 5.2(1)](https://arxiv.org/html/2303.00078v2#S5). It does not prove the ten-denomination assertion. The broader prohibition for all lengths of the form (3r+1) is false, as shown by the separate [counterexample-family proof](FAMILY-PROOF.md).

## Proof

Write the denominations as (1<a<b<c<d<e<f). The full orderly system makes every prefix *tight*: below the last denomination of that prefix, later coins cannot occur in any representation and do not affect greedy change.

Call a two-coin sum (s) a *fit* at (m) if (s=m+r) and (r) is zero or a denomination at most (m). If (m) is the largest available coin at most (s), this is exactly the condition that greedy uses at most two coins. Thus a sum of two earlier coins between (e) and (f-1) must fit at (e), and one at least (f) must fit at (f). The all-amount property of the full system implies these constraints; they are not an assumption about which amounts suffice to test orderliness.

Apply the tight-prefix counterexample lemma to the prefixes of lengths five and six. There is a pair (x,y ∈ {a,b,c,d}) with (x+y>e) that does not fit at (e). Consequently (x+y ≥ f). The lemma follows the argument of [Cai, Theorem 11](https://arxiv.org/abs/0809.0400), restated as Theorem 2.15 by Van Cott and Zhang, and is proved from the greedy and optimal-representation definitions in the checked source. Also, the first three coins being orderly implies (b ≥ 2a−1): if (a<b<2a-1), greedy uses (b) and at least two pennies at (2a), which loses to two copies of (a).

If (c ≤ 2b), the `m = 2` four-coin case of the One Point Theorem shows that (2b) cannot fit at (c), since the four-coin prefix is nonorderly. The checked proof derives that specialization from the greedy residue criterion. If (c>2b), no analogous extra premise is needed for the arithmetic contradiction.

For completeness, the remaining arithmetic certificate consists of the two cases (c ≤ 2b) and (c>2b), each crossed with the ten unordered choices of (x,y) from ({a,b,c,d}) with repetition. In each case the inequalities above and the required fits split into linear constraints: a fit is a finite disjunction (s=m+r), one equality per possible residue. An explicit case tree checks incompatibility at every leaf by integer arithmetic. Its splits were selected with solver assistance, but they and their arithmetic consequences are independently checked by Lean. The variables have no upper bounds.

## Verification

The exact theorem over arbitrary ascending lists is [`CoinOrder.vanCottZhang_no_seven`](../../Proofs/CoinSeven/NoSeven.lean). The tight-prefix lemma is [`CoinOrder.Bridge.compact_cai`](../../Proofs/CoinSeven/Bridge.lean); the four-coin specialization is [`CoinOrder.four_orderly_of_residue`](../../Proofs/CoinSeven/OnePoint.lean). The [arithmetic cases](../../Proofs/CoinSeven/Arithmetic.lean) and their [assembly](../../Proofs/CoinSeven/Obstruction.lean) are also included.

With the checked Lean 4.35.0-rc2 toolchain installed, run from the project root:

```sh
lake build --wfail +Proofs.CoinSeven.NoSeven
```

The theorem uses only `propext`, `Classical.choice`, and `Quot.sound`. It does not rely on Z3 at replay, native evaluation, or proof placeholders.
