# Van Cott–Zhang’s prefix pattern at every length at least 11

Jaime Nistal, with OpenAI Codex assistance  
Follow-up to the [original 13-coin proof](https://github.com/n1stal/conjecture-lab/blob/4bf25fe2b3d1ae65cbc6edaec3a541009e5bf7f8/results/van-cott-zhang-521/PROOF.md).

Let an increasing coin system, starting at 1, have the *target pattern* if the first three prefixes and the full system are greedy-optimal for every amount, and every other proper prefix is not. [Van Cott and Zhang’s Conjecture 5.2](https://arxiv.org/html/2303.00078v2#S5) prohibits this at lengths 3r+1 and predicts that families D and G are exhaustive at lengths 3r+2.

**Theorem.** Every length n≥11 admits the target pattern. For lengths n=13 and n≥15 a single formula works:
```
L = 3n-17
A = {1,4,7,...,L} ∪ {2,5,8,14} ∪ {L+6}.
```
In particular, the prohibition fails at every length 3r+1≥13. The exclusivity prediction fails at every length 3r+2≥14. This does not decide the separate questions at lengths 7 and 10 or part (2) at length 9.

## Why all the proper prefixes have the stated pattern

The first three denominations are 1, 2 and 4; each prefix is orderly by the residue criterion below (or binary carrying). For prefixes 4 through 9, the following amounts take three greedy coins while the displayed two-coin alternatives are available:

| Prefix length | Amount | Greedy | Better |
| ---: | ---: | --- | --- |
| 4 | 8 | 5+2+1 | 4+4 |
| 5 | 10 | 7+2+1 | 5+5 |
| 6 | 11 | 8+2+1 | 4+7 |
| 7 | 13 | 10+2+1 | 5+8 |
| 8 | 16 | 13+2+1 | 8+8 |
| 9 | 17 | 14+2+1 | 4+13 |

Every remaining proper prefix has largest coin J in 16,19,…,L. At amount J+11 its greedy representation is J+10+1, since J>11 and 10 is the largest coin at most 11; but (J−3)+14 uses two coins, both present.

## Why the full system is greedy-optimal

Put M=L+6 and let g(x) count greedy coins. For 0≤x<M,
- g(0)=0;
- g(x)=1 when x is a coin;
- g(L+3)=3;
- g(x)=2 otherwise.

To see this for 0<x≤L, the largest ladder coin no greater than x is at most two below x. The largest available coin no greater than x leaves a remainder at most two as well; both 1 and 2 are coins. For L<x<M the first coin is L, leaving 1,2,3,4 or 5; only 3 requires two coins.

The [residue criterion](https://github.com/n1stal/conjecture-lab/blob/4bf25fe2b3d1ae65cbc6edaec3a541009e5bf7f8/results/van-cott-zhang-521/PROOF.md) says that to prove full orderliness it is enough to show g(c+r)≤1+g(r) for every coin c and residue 0≤r<M. Greedy first takes copies of M, so g(qM+r)=q+g(r); this extends the inequality to every amount. Adding the coins of any competing representation one at a time then proves optimality.

The case c=M follows immediately from the shift identity. Otherwise:

1. **No wrap (c+r<M).** For r=0 there is equality; for g(r)≥2 the bound follows from g(c+r)≤3. If r is a coin, the only possible failure is c+r=L+3. Every coin below M is 1 or 2 modulo 3, and L+3 is 1 modulo 3, so both c and r must belong to B={2,5,8,14}. Their sum is at most 28, below L+3 for L≥28. For L=22, no two coins of B sum to 25.
2. **Wrap (c+r≥M).** Put s=c+r−M. It suffices to show g(s)≤g(r). Since s<c≤L, g(s)≤2, which handles noncoin r (r=0 is impossible). If r is a coin, then for two coins 1 modulo 3, s is 1 modulo 3 and no greater than L−6, so it is a ladder coin. For a mixed pair, s is 2 modulo 3 and at most 8, hence one of 2,5,8. A pair from B cannot wrap if L≥28; if L=22 only 14+14 wraps and s=0.

This gives the target pattern at n=13 (L=22) and all n≥15, as claimed.

## Lengths 11, 12, and 14

| Length | Denominations | Source |
| ---: | --- | --- |
| 11 | 1,2,4,5,7,9,12,14,17,22,27 | Already in Van Cott–Zhang §5 (their family G) |
| 12 | 1,2,4,5,7,8,10,11,13,16,19,22 | Explicit certificate; existence at 12 already shown in §5 |
| 14 | 1,2,4,5,7,8,10,13,15,18,21,26,29,37 | Explicit certificate; outside both suggested families |

The companion certificates apply the same residue criterion to the full systems and exhibit a better representation for each middle prefix.

## Why D and G do not exhaust the possibilities

The length-14 system and every construction above of length 3r+2≥17 have the same first eight coins, (1,2,4,5,7,8,10,13). In the relevant range a matching member of D ([Theorem 4.3](https://arxiv.org/html/2303.00078v2#S4)) would have parameter a=2 because its third coin is a+2, but its eighth coin is then 11. In G ([Definition 5.1](https://arxiv.org/html/2303.00078v2#S5)), the sixth coin is 9, not 8. Thus none of these systems belongs to either suggested family. A separately reported length-17 witness against part (3) predates this follow-up in our conversation and is not claimed here. We make no priority claim.

## Machine verification

The [Palomar statement](../../Palomar/CoinFamily/Challenge.lean) and [solution](../../Palomar/CoinFamily/Solution.lean) use the same elaborated theorem types and model definitions. The proof modules are under [Proofs/CoinFamily](../../Proofs/CoinFamily). Lean 4.35.0-rc2 checks all four theorem entry points with only the standard axioms. The particular length-14 counterexample has a [separate certificate and audit](LENGTH14-AUDIT.md). The [dynamic-programming replay](replay.py) is a separate finite sanity check, not a premise of the universal proof.
