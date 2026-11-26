# Van Cott–Zhang scope and small-length check

The primary source is [arXiv:2303.00078v2 §5](https://arxiv.org/html/2303.00078v2#S5), Conjecture 5.2(3), with [Theorem 4.3](https://arxiv.org/html/2303.00078v2#S4) defining D and Definition 5.1 defining G. The claim asserts that all systems of length 3r+2 with the +++--…-+ pattern are members of D or G (and conversely). One system with that length and pattern outside both families refutes the claim.

**Length 14 witness (r=4):** 1, 2, 4, 5, 7, 8, 10, 13, 15, 18, 21, 26, 29, 37.

Theorem 4.3 has first three denominations 1,2,a+2, so matching the witness forces a=2. At r=4, its eighth denomination is 5+3a=11, whereas the witness has 13. Definition 5.1 gives g6=9 and the witness has 8. The same comparison applies to the proposed infinite family for every length 3r+2 ≥17.

Full greediness below 37, in residue order: 0, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 3, 2, 1, 2, 2, 1, 2, 2, 3, 2, 2, 3, 2. For each c in the witness, the maximum over 0≤r<37 of floor((c+r)/37)+R[(c+r) mod 37]−R[r] is exactly 1 (518 residue checks). As in the published 13-coin proof, shift by multiples of 37 and induct on the length of any competing coin representation. This establishes optimality for every amount, not just amounts below 37. The first three prefixes are identical to those in the published witness.

| k | amount | greedy output | better output |
|---:|---:|---|---|
| 4 | 8 | 5+2+1 | 4+4 |
| 5 | 10 | 7+2+1 | 5+5 |
| 6 | 11 | 8+2+1 | 4+7 |
| 7 | 13 | 10+2+1 | 5+8 |
| 8 | 16 | 13+2+1 | 8+8 |
| 9 | 18 | 15+2+1 | 5+13 |
| 10 | 21 | 18+2+1 | 8+13 |
| 11 | 30 | 21+8+1 | 15+15 |
| 12 | 29 | 26+2+1 | 8+21 |
| 13 | 41 | 29+10+2 | 15+26 |

**Verified small lengths.** [VanCottZhangSmall.lean](../../Proofs/CoinFamily/VanCottZhangSmall.lean) imports the original coin formalization and the prefix model; its bridge `CoinOrder.every_small_length_family` checks the source's G witness at 11, our alternate witness at 12, the published 13 witness, and the new 14 witness. Lean 4.35.0-rc2 warnings-as-errors passes with only propext and Quot.sound.

**Novelty.** Targeted searches for the exact 14 tuple and Van Cott–Zhang + Conjecture 5.2(3) yielded the original article and no external match. The original discusses examples at lengths 8, 11 (for the G family) and 12 (no conjecture), not this length 14 witness. Do not claim priority.

**Other finite evidence.** Original paper's searches found no 7-denomination witness with all values <100 and no 10-denomination witness with all values <50. The search using Pearson and necessary early-prefix tightness completed all 7-denomination systems with maximum at most 200 without finding a witness, a bounded result only. For 10, do not infer unbounded nonexistence even from a completed bounded search.
