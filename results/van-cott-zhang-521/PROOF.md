# A counterexample to Van Cott–Zhang Conjecture 5.2(1)

**Jaime Nistal**  
**Proof development and Lean formalization:** with OpenAI Codex assistance.

Cornelia A. Van Cott and Qiyu Zhang call a coin system *orderly* if greedy change uses the fewest coins for every amount. Their paper [*The Change-Making Problem for Six Coin Values and Beyond*](https://arxiv.org/html/2303.00078v2#S5), Conjecture 5.2(1), proposes that no system of length $3r+1$, for $r\ge2$, has the prefix pattern $+++-\cdots-+$: the first three prefixes and the complete system are orderly, but every prefix in between is not.

**Theorem.** The denominations
```
1, 2, 4, 5, 7, 8, 10, 12, 15, 18, 23, 26, 34
```
have that pattern. Since $13=3\cdot4+1$, the general prohibition is false.

## 1. A finite test that covers every amount

Write $G_A(v)$ for the number of coins used by greedy change for amount $v$ in a system $A$ containing 1. Greedy takes as many copies of the largest available denomination as possible, then repeats with the remainder and the smaller denominations. Its output always represents $v$ because the last denomination is 1. If $M$ is the largest denomination, greedy first takes $\lfloor v/M\rfloor$ copies of $M$, so
$$G_A(v+qM)=G_A(v)+q\qquad(v,q\ge0).$$

**Lemma.** Suppose for each denomination $c\in A$ and each residue $0\le r<M$ we have
$$G_A(c+r)\le 1+G_A(r).\tag{1}$$
Then $A$ is orderly.

**Proof.** Given $v\ge0$, write $v=qM+r$ with $0\le r<M$. Add $q$ to both sides of (1) and use the shift identity. This gives $G_A(c+v)\le1+G_A(v)$ for every $v\ge0$. For any representation $v=c_1+\cdots+c_k$ with each $c_i\in A$, apply this inequality once per coin. Since $G_A(0)=0$, we get $G_A(v)\le k$. Thus greedy is optimal against every representation of every amount. $\square$

## 2. The first three prefixes and the complete system

For a given $A$, set $R=(G_A(0),\ldots,G_A(M-1))$. The quantity checked for each $c$ is
$$D_A(c)=\max_{0\le r<M}\left(\left\lfloor\frac{c+r}{M}\right\rfloor+R_{(c+r)\bmod M}-R_r\right).$$
This is exactly the maximum of $G_A(c+r)-G_A(r)$, so (1) holds if every entry of $D_A$ is at most 1.

| System | $R$ | $D_A$ in increasing denomination order |
| --- | --- | --- |
| $(1)$ | $(0)$ | $(1)$ |
| $(1,2)$ | $(0,1)$ | $(1,1)$ |
| $(1,2,4)$ | $(0,1,1,2)$ | $(1,1,1)$ |
| Full system | See below | $(1,1,1,1,1,1,1,1,1,1,1,1,1)$ |

For the full system, the zero-indexed residue table is:

```text
r =  0.. 9:  0, 1, 1, 2, 1, 1, 2, 1, 1, 2
r = 10..19:  1, 2, 1, 2, 2, 1, 2, 2, 1, 2
r = 20..29:  2, 3, 2, 1, 2, 2, 1, 2, 2, 3
r = 30..33:  2, 2, 3, 2
```

Here is a literal replay of the entire finite calculation (Python 3, standard library only):

```python
C = [1, 2, 4, 5, 7, 8, 10, 12, 15, 18, 23, 26, 34]

def greedy_count(A, v):
    count = 0
    for c in reversed(A):
        q, v = divmod(v, c)
        count += q
    return count

for A in (C[:1], C[:2], C[:3], C):
    M = A[-1]
    R = [greedy_count(A, r) for r in range(M)]
    D = [max((c+r)//M + R[(c+r) % M] - R[r]
             for r in range(M)) for c in A]
    assert D == [1] * len(A)
```

The lemma now proves that each of the four systems is orderly for *all* amounts. In particular, the 442 residue checks for the full system are not an assumption about an upper limit on the amount.

## 3. The nine middle prefixes

Each row compares the greedy output in the indicated prefix (the first $k$ denominations, and no others) with an available two-coin representation of the same amount.

| Prefix length $k$ | Amount | Greedy output | Two coins |
| ---: | ---: | --- | --- |
| 4 | 8 | $5+2+1$ | $4+4$ |
| 5 | 10 | $7+2+1$ | $5+5$ |
| 6 | 11 | $8+2+1$ | $7+4$ |
| 7 | 13 | $10+2+1$ | $8+5$ |
| 8 | 15 | $12+2+1$ | $10+5$ |
| 9 | 18 | $15+2+1$ | $10+8$ |
| 10 | 24 | $18+5+1$ | $12+12$ |
| 11 | 26 | $23+2+1$ | $18+8$ |
| 12 | 35 | $26+8+1$ | $23+12$ |

Thus each middle prefix is nonorderly. Together with §2 and $r=4$, this proves the theorem. $\square$

## Verification and scope

The companion Lean file [`VanCottZhang.lean`](../../Proofs/VanCottZhang.lean) proves `CoinOrder.vanCottZhangConjecture521_false`. The proof includes the finite-to-all-amounts lemma and does not assume a change-making bound from the literature. Replayed with Lean 4.35.0-rc2 and `-DwarningAsError=true`; the main theorem depends only on `propext` and `Quot.sound`.

The counterexample refutes the general $3r+1$ prohibition. It does not settle the separate 7- and 10-denomination assertions, and does not address parts (2) or (3). The separately reported 17-denomination counterexample to part (3) is not part of this proof. A targeted prior-work search on 26 November 2026 found no earlier match for this witness or refutation; this is not a priority claim.

**Reference.** C. A. Van Cott and Q. Zhang, [*The Change-Making Problem for Six Coin Values and Beyond*](https://doi.org/10.1016/j.disc.2025.114669), §5, Conjecture 5.2(1); [arXiv:2303.00078v2](https://arxiv.org/html/2303.00078v2#S5).

