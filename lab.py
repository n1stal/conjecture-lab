#!/usr/bin/env python3
"""Search the sharp reciprocal sum bound for Erdős Property P."""
import argparse
import json
import math
import random
from functools import lru_cache
from fractions import Fraction
from pathlib import Path

THRESHOLD = Fraction(3, 2)
STARTERS = ((1, 2), (2, 3, 4), (3, 5, 6, 8, 11, 20, 23, 26, 56, 71, 143, 146))


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()
        mask ^= bit


def bans(a, b, n):
    return sum(1 << (c - 1) for c in range(b + 1 + (-(2*b + 1)) % a, n+1, a))


def optimize(n, low, budget):
    denominator = math.lcm(*range(low, n+1))
    weights = [0] * low + [denominator // i for i in range(low, n+1)]
    best = max((s for s in STARTERS if low <= s[0] and s[-1] <= n),
               key=lambda s: sum(weights[a] for a in s), default=())
    score = sum(weights[a] for a in best)
    nodes = 0
    complete = True
    mask = (1 << n) - (1 << (low-1))
    cache = lru_cache(maxsize=100_000)(lambda a, b: bans(a, b, n))

    # Partition the mask into byte-sized chunks to get a cheap exact bound.
    tables = []
    for j in range(0, n, 8):
        w = (weights[j+1:j+9] + [0]*8)[:8]
        table = [0] * 256
        for m in range(1, 256):
            k = m & -m
            table[m] = table[m ^ k] + w[k.bit_length()-1]
        tables.append(table)

    def weight(m):
        upper = 0
        j = 0
        while m:
            upper += tables[j][m & 255]
            j += 1
            m >>= 8
        return upper

    def visit(prefix, candidates, value):
        nonlocal best, score, nodes, complete
        if nodes == budget:
            complete = False
            return
        nodes += 1
        if value > score:
            score, best = value, prefix
        remainder = weight(candidates)
        while candidates and value + remainder > score:
            bit = candidates & -candidates
            candidates ^= bit
            b = bit.bit_length()
            remainder -= weights[b]
            remaining = candidates
            for a in prefix:
                remaining &= ~cache(a, b)
            visit(prefix+(b,), remaining, value+weights[b])
            if not complete:
                return

    visit((), mask, 0)
    return best, Fraction(score, denominator), nodes, complete


def explore(n, low, budget, seed):
    """Randomized greedy search. Each trial starts fresh; no global claim."""
    rng = random.Random(seed)
    best = max((s for s in STARTERS if low <= s[0] and s[-1] <= n),
               key=lambda s: sum(Fraction(1, a) for a in s), default=())
    score = sum((Fraction(1,a) for a in best), Fraction())
    cache = lru_cache(maxsize=100_000)(lambda a, b: bans(a, b, n))
    for _ in range(budget):
        current = []
        candidates = (1 << n) - (1 << (low-1))
        # Always advance in increasing order. Usually take a small next
        # element, but vary the window to sample different residue patterns.
        width = rng.choice((1, 2, 3, 4, 8, 16))
        while candidates:
            window = []
            for x in bits(candidates):
                window.append(x)
                if len(window) == width:
                    break
            b = rng.choice(window)
            candidates &= -1 << b
            for a in current:
                candidates &= ~cache(a, b)
            current.append(b)
        value = sum((Fraction(1,a) for a in current), Fraction())
        if value > score:
            best, score = tuple(current), value
        if score > THRESHOLD:
            return best, score, _+1, False
    return best, score, budget, False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=["exact", "explore"], default="exact")
    parser.add_argument("--n", type=int, default=150)
    parser.add_argument("--min-element", type=int, default=1)
    parser.add_argument("--budget", type=int, default=500_000, help="maximum DFS nodes or greedy trials")
    parser.add_argument("--seed", type=int, default=20261126)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    max_n, max_budget = (500, 3_000_000) if args.mode == "exact" else (5000, 10_000)
    if not 1 <= args.min_element <= args.n <= max_n or not 1 <= args.budget <= max_budget:
        parser.error(f"require 1 <= min-element <= n <= {max_n}, 1 <= budget <= {max_budget}")
    if args.mode == "exact":
        witness, score, work, complete = optimize(args.n, args.min_element, args.budget)
    else:
        witness, score, work, complete = explore(args.n, args.min_element, args.budget, args.seed)
    record = dict(schema=1, conjecture="property-p-sharp", mode=args.mode, n=args.n,
                  min_element=args.min_element, budget=args.budget, seed=args.seed, work=work,
                  complete=complete, witness=list(witness), score=str(score),
                  exceeds_target=score > THRESHOLD,
                  status="finite_optimum" if complete else "witness_only")
    payload = json.dumps(record, indent=2, sort_keys=True)+"\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    print(payload, end="")


if __name__ == "__main__":
    main()
