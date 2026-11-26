"""Exact finite test of Erdős #982 on square and triangular lattice patches."""
import argparse
from itertools import combinations


def turn(a, b, c):
    return (b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0])


def strictly_convex(points):
    if len(points) <= 2:
        return True
    pts = sorted(points)

    def half(seq):
        out = []
        for p in seq:
            while len(out) >= 2 and turn(out[-2], out[-1], p) <= 0:
                out.pop()
            out.append(p)
        return out

    return len(half(pts)) + len(half(reversed(pts))) - 2 == len(pts)


def dist(a, b, lattice):
    x, y = a[0]-b[0], a[1]-b[1]
    return x*x + y*y + (x*y if lattice == 'triangular' else 0)


def census(side, order=8, lattice='square'):
    pts = [(x,y) for x in range(side) for y in range(side)]
    D = [[1 << dist(a,b,lattice) for b in pts] for a in pts]
    limit = order//2 - 1
    nodes = [0]*(order+1)
    witness = None

    def visit(ids, masks, start):
        nonlocal witness
        nodes[len(ids)] += 1
        if len(ids) == order:
            witness = [pts[i] for i in ids]
            return True
        for i in range(start, len(pts)-(order-len(ids))+1):
            # Translate min x to zero; only the first point needs checking.
            if not ids and pts[i][0] != 0:
                break
            bits = [D[i][j] for j in ids]
            last = 0
            for bit in bits:
                last |= bit
            if last.bit_count() > limit:
                continue
            new_masks = [old | bit for old,bit in zip(masks,bits)]
            if any(m.bit_count() > limit for m in new_masks):
                continue
            if not strictly_convex([pts[j] for j in (*ids,i)]):
                continue
            if len(ids)+1 == order and min(pts[j][1] for j in (*ids,i)) != 0:
                continue
            if visit((*ids,i), (*new_masks,last), i+1):
                return True
        return False

    visit((), (), 0)
    if witness:
        # Independent convexity test: every pair that defines a supporting
        # line is an edge exactly when all other vertices are strictly to one side.
        support = 0
        for a,b in combinations(witness,2):
            signs = [turn(a,b,c) for c in witness if c not in (a,b)]
            support += all(s>0 for s in signs) or all(s<0 for s in signs)
        assert support == order
        assert all(len({dist(a,b,lattice) for b in witness if b!=a}) <= limit for a in witness)
    return nodes, witness


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--side", type=int, default=8, choices=range(3,21))
    p.add_argument("--order", type=int, default=8, choices=range(4,13))
    p.add_argument("--lattice", choices=["square", "triangular"], default="square")
    args = p.parse_args()
    print(census(args.side,args.order,args.lattice))
