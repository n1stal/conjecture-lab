# Erdős #982: the convex octagon case

**Status:** General octagon case open in the sources checked 2026-11-26.
Finite grid experiments below. Candidate partial proof for two perpendicular
reflection axes; not independently reviewed, formally verified, or claimed novel.

A strictly convex octagon is sought in which each vertex sees at most three
distinct distances to the other seven vertices. One verified example would
disprove the octagon case of [Erdős #982](https://www.erdosproblems.com/982);
an exhaustive check of a grid alone does not decide it. See the [literature
summary](https://erdosproblems.ai/wiki/problems/distance_problems/E0982).
The related nonconvex result in #1082 is not an octagon counterexample here.

## Reproduce the exact grid search

```sh
python experiments/erdos_982_grid.py --side 10
python experiments/erdos_982_grid.py --side 10 --lattice triangular
```

Neither patch has a counterexample. The 10-by-10 square grid had 1,055
surviving depth-five prefixes and no depth-six prefixes; the corresponding
triangular lattice patch had 13,901 depth-five and 64 depth-six prefixes, but
no depth-seven prefixes. These are search-tree counts, not isomorphism counts.
A prefix can be discarded if any vertex already sees a fourth squared distance,
or if not all its points are extreme: neither failure can be reversed by
adding vertices. Translation normalizes the minimum of each lattice coordinate
to zero. The triangular metric is the exact integer form x²+xy+y².

## Candidate proof for perpendicular reflection axes

**Claim.** A strictly convex octagon invariant under reflection in two
perpendicular lines has a vertex seeing at least four distances.

Place the axes at the coordinate axes. An off-axis orbit consists of the
four points (±a, ±b), with a,b positive. Each axis has at most two vertices
(the extremes), and the origin is not a vertex by central symmetry. Thus the
orbit sizes are 4+4 or 4+2+2. Work with squared distances.

**Two four-point orbits.** Write p=(a,b), q=(c,d) for the first-quadrant
representatives. From p to q's orbit the four squared distances are
C ± 2ac ± 2bd, where C=a²+b²+c²+d². Because ac,bd are positive, these can
have at most three different values only if ac=bd, in which case their set
is {C−4ac,C,C+4ac}. This is also the set from q to p's orbit.

If one orbit is square, ac=bd forces both square, and the smaller concentric
square cannot supply vertices. Otherwise the three distances within each
orbit are distinct: for p they are 4a²,4b²,4(a²+b²), and analogously for q.
Each triple must equal the cross-orbit triple. Comparing the maxima gives
a²+b²=c²+d². But then the middle cross-orbit value is 2(a²+b²),
strictly smaller than the middle within-orbit value 4 max(a²,b²). Contradiction.

**One four-point orbit and four axis vertices.** Write the axes' vertices as
(±c,0),(0,±d). Extremality implies c>a and d>b: otherwise an axis point
lies in the rectangle spanned by p's orbit. At p, write the squared distances
to the two x-axis vertices as X₋=(c−a)²+b² and X₊=(c+a)²+b²,
and those to the y-axis vertices as Y₋=a²+(d−b)² and Y₊=a²+(d+b)².

If a≠b, both pairs must use values in the three-value within-orbit set.
Since X₊−X₋=4ac>4a² and X₊≤4(a²+b²), X₋<4b². The only possible
within-orbit value is 4a², forcing a<b. Swapping the axes gives b<a.

If a=b, scale to a=b=1. The within-orbit set is {4,8}; there must be
one further value t, since X₊−X₋>4. If 4<t<8 the three-value set has
diameter 4, impossible. If t>8, both X₋ and Y₋ must be at least 4
(as all three allowable values are at least 4). Thus c,d≥1+√3>2.
Then (1,1) is inside the triangle with vertices (0,0),(c,0),(0,d),
contrary to extremality. Finally if t<4, both near distances must equal t,
and both far distances 8: a near distance ≥4 cannot have a far distance
more than 4 larger, and a near distance t>0 cannot have far distance 4.
It follows that c=d=√7−1. At (c,0) the four distinct values are
t<4, 2c²∈(4,8), 8, and 4c²>8. Contradiction.

The case split is exhaustive under the stated symmetries. Earlier
[search notes](https://lemmapark.com/programs/erdos-open/challenges/Lemma.erdos_982)
include numerical tests of these orbit types; we have not ruled out prior
analytic treatments. Next: independent line-by-line proof review, followed
by the larger class with 180° rotational symmetry only.

## Extension: central symmetry alone

**Claim.** Every centrally symmetric strictly convex octagon has a vertex
seeing at least four distances.

Suppose otherwise, center at the origin, and write the four antipodal
pairs as ±v and ±w₁, ±w₂, ±w₃, choosing v of largest norm r.
The distance from v to −v is 2r, strictly greater than that to any other
vertex by the triangle inequality and its equality case. The six remaining
distances from v therefore have at most two different squared values.

The lines spanned by the four antipodal pairs are distinct: otherwise
one pair on the same line is between the vertices of another pair and
cannot be extreme. At most one wᵢ is perpendicular to v. For every pair
not perpendicular to v, the two squared distances from v are distinct
and hence must be exactly the same two values as for every other such
pair. Their average is r²+‖wᵢ‖², and their absolute difference is
4|v·wᵢ|. Consequently all nonperpendicular pairs have the same radius
and the same nonzero absolute projection onto the line of v. These
conditions allow at most two lines through the origin, and if two
occur they are interchanged by reflection across the line of v.
There are at least two such pairs, so there are exactly two, and the
third pair is perpendicular to v.

Thus reflection across the line of v fixes its own pair, preserves
the perpendicular pair, and interchanges the remaining two pairs.
Central symmetry then gives reflection across the perpendicular axis
as well. This reduces to the previous claim, a contradiction.

This extends the argument beyond the previous numerical search for
centrally symmetric octagons. It does not handle a single reflection
axis without central symmetry, or a fully asymmetric octagon.
