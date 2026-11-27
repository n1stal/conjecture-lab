# Exact weighted terminal sum through packing number five

Private paper proof. This is a stronger case of the packing branch of Question 3 of Artem Hak and Sergiy Kozerenko, [*Triameter, distance packings, and vertex connectivity*, arXiv:2611.17259v1 §7](https://arxiv.org/html/2611.17259v1#S7). It does not settle p≥6 on arbitrary graphs or the separator branch, and no discovery or priority is claimed for a prior special case. It complements the unrestricted-p theorem for four terminals rather than superseding that result.

Fix k≥1 and put a=k+1. Let G be a connected finite simple graph whose largest set of vertices at all mutual distances greater than k has size p. Let r terminals be distinct vertices and w_i≥0 their weights; arbitrary real weights are allowed in this written proof. Define

- M = sum of w_i w_j over unordered terminal pairs,
- C = max_A w(A) w(Aᶜ),
- R = (k+1)(p−1).

For p≤5, the exact maximum of the weighted sum of terminal distances is **kM+RC** for every k,r and weight vector. The attaining graph does not depend on any upper-bound compression; it can realize every terminal bipartition and have exact p. Separately, the formula holds for all p on any class including the extremal block graphs and in which the k-th power has clique-cover number equal to its independence number.

## 1. Remove neighboring positive-excess representatives

For any terminal pair put x_ij=max(0,d_ij−k), with x_ii=0. Then S≤kM+E, where E=Σ_{i<j} x_ij w_i w_j. Maintain one nonnegative mass at each original terminal position, each mass carrying the block of original weights it now represents. Initially every positive-weight original terminal is its own block. If two active positions u,v have x_uv=0, move all their combined mass to whichever of u,v has the larger current weighted degree, where the degree is Σ_z x_tz w_z. Since x_uv=x_uu=x_vv=0, transferring the mass from v to u changes E by w_v times (weighted degree of u minus weighted degree of v) and cannot decrease E. The statement in the opposite direction is analogous. Active count falls. At termination surviving active positions form a k-packing Q with at most p vertices. Each cut of those positions lifts to a cut of the original terminal labels by taking complete blocks, so its product mass is at most C. Discarding original zero-weight labels is harmless.

This reduction is valid for all p. It never changes graph distances or pretends that abstract clipped matrices are graph-realizable.

## 2. Pair and triangle caps

The d-diameter bound follows by taking points every k+1 along one geodesic: d≤(k+1)p−1=k+R. By [Hak–Kozerenko Theorem 1.1](https://arxiv.org/html/2611.17259v1), every terminal triangle has d-perimeter ≤3k+2R. Thus 0≤x≤R and each clipped triangle has perimeter ≤2R. Indeed if all three excesses are positive subtract 3k; otherwise at most two nonzero terms are individually ≤R.

If p=1, R=0 and E=0. If the compressed set Q has at most four vertices and R>0, the normalized x/R belongs to BIP(K4) after padding unused labels with zero excess and zero mass. The [Galli–Letchford facet description](https://doi.org/10.1016/j.orl.2010.05.004), §2 and Table 1, says that the box and triangle inequalities suffice for BIP(K4). Equivalently use the existing constructive four-point proof. A bipartite subgraph extends to a cut, so every nonnegative weighted cost of a point of BIP is at most the maximum cut cost. Hence E≤RC whenever the compressed support has size ≤4.

Only p=5 and |Q|=5 remains. In the following all d are actual graph distances between the five packed centers and x_ij=d_ij−k>0.

## 3. Necessary center geometry: connected low graph and geodesic windows

Every graph vertex lies within k of some center in Q, since otherwise it extends Q. With arbitrary center assignments to graph vertices, adjacent graph vertices have assigned centers at distance ≤2k+1. Each center itself must be assigned to itself. Since G is connected, the graph on Q containing the pairs of distance ≤2k+1 is connected. Pick a spanning tree T of it. Its four edges have x≤a, and now R=4a.

For any centers s,t, let v_0,...,v_D be a shortest s-to-t walk, D=d(s,t), and choose a covering center q_i of v_i. Every such assignment has q_0=s, q_D=t, consecutive q_i equal or a low edge, and the two window inequalities
|d(s,q_i)−i|≤k,  |d(t,q_i)−(D−i)|≤k.
These follow from the two exact subgeodesic lengths and the triangle inequality.

## 4. All five-point facets are satisfied

**Total sum.** In the complement of T some three labels form a triangle: the larger independent side of the bipartition of T has at least three vertices. The four T-excesses total at most 4a=R; the three complementary triangle terms total at most 2R; the other three terms total at most 3R. Hence Σ x≤6R.

**Every five-cycle.** Let C_5 be any Hamiltonian cycle on the five labels.

- If C_5 contains at least two T edges, its excess is at most 2a+3R≤4R.
- If it contains exactly one, the other three T edges lie in the complementary cycle. Two of those share an endpoint. Their other endpoints have distance at most 2(2k+1), hence excess ≤3k+2≤3a, and their connecting edge belongs to C_5 because the complementary cycle is chordless. This is a distinct C_5 edge from the unique T edge in C_5, since otherwise T would contain a triangle. Thus cycle excess ≤a+3a+3R=4R.
- If it contains no T edge, T is the complementary cycle minus one edge. Label the resulting path 0–1–2–3–4. The cycle edges are 02,03,13,14,24. The two-step distances are at most 4a−2 by the low path edges; the three-step distances are at most 5a−1 by diameter. Write
  d02=4a−2−x, d13=4a−2−y, d24=4a−2−z,
  d03=5a−1−u, d14=5a−1−v,
  with nonnegative deficits. The cycle excess equals 17a−3−(x+y+z+u+v). If it exceeds 4R=16a, the sum of deficits is less than a−3, in particular a≥4. All five of these pairs have d>2a−1=2k+1. The sixth nonpath pair 04 also does, since d04≥d03−d34≥3a−u>2a−1. Hence the low center graph is precisely T. Along the actual 0-to-3 geodesic, its covering-center walk must transition from 1 to 2 at some step i→i+1. The window with the terminal 3 at i gives i≤d03−d13+k=2a+y−u. The window with terminal 0 at i+1 gives i+1≥d02−k=3a−1−x. Therefore x+y≥a−2+u, contradicting x+y<a−3.

Consequently x/R satisfies every inequality in the complete [Galli–Letchford BIP(K5) description](https://www.lancaster.ac.uk/people/letchfoa/articles/2010-bipartite-subgraph.pdf), §§2–3/Table 1: box, triangles, five-cycles and all ten edges. As before, its nonnegative weighted cost is at most the maximum cut cost of the five packed positions, which is at most C by the block lift. This gives S≤kM+RC.

## 5. Attainment

Choose a cut of the terminal weights realizing C. Put k=2h+e with e=0 or 1, and arm height H=h+e>0. For p=1 attach all terminal arms to a common root. For p≥2 use a trunk of length L=R−e=2h+1+(k+1)(p−2), with each terminal arm attached at its chosen cut-side endpoint. To ensure a cross-tip geodesic even if the cut is trivial, attach one extra arm at each side, with its tip not counted among the prescribed terminals. For odd k join all distinct depth-one vertices at each anchor by edges. Same-anchor terminal distances are 2H−e=k; crossings for p≥2 are L+2H=k+R. These are literal shortest distances: the only links between distinct arms at an anchor are through that anchor or their depth-one edge; switching between trunk ends requires traversing the trunk.

For p=1 the graph has diameter ≤k. For p≥2, partition into the two anchor caps (all attached arms plus the h-nearest trunk positions to each anchor), and p−2 consecutive trunk blocks of k+1 interior vertices. All pieces have diameter ≤k, so packing size≤p; equally spaced vertices along an opposite-tip geodesic give size≥p. Thus the exact score is kM+RC and the graph is a block graph (for odd k each anchor's first layer plus anchor is a clique, all other blocks are edges). This construction is independent of the bound p≤5.

## 6. Next exact boundary and priors

The normalized upper triangle/box inequalities alone do not imply BIP(K5): constant 2/3 on all edges violates the all-edge bound. Even adding a low spanning tree and ordinary metric lower triangles is not enough to imply the cycle bound. For every k≥3, a=k+1, consider five-point distances d along path-label order 0..4: consecutive pairs 2a−1, all two-step pairs 4a−2, the two three-step pairs 5a−1, and d04=3a. The distances satisfy ordinary metric and the source pair and perimeter caps for p=5; the path is low, but the complementary five-cycle excess is 17a−3>16a. This matrix is not graph-realizable at p=5, by the geodesic transition proof above. It is an obstruction to a relaxation, not a counterexample to the formula. The p=6 case would additionally need the six-point hypermetric inequality in Galli–Letchford Table 1 and suitable five-subset control when a sixth covering center can bridge a low path.

Laura Galli and Adam N. Letchford, *Small bipartite subgraph polytopes*, Operations Research Letters 38 (2010), 337–340, DOI [10.1016/j.orl.2010.05.004](https://doi.org/10.1016/j.orl.2010.05.004), supply the finite facet theorem, not the graph packing verification. The graph triangle cap is credited to Hak–Kozerenko. [F. R. K. Chung's average-distance theorem](https://doi.org/10.1002/jgt.3190120213) gives the unit-weight k=1 bound for even r and also for odd r when p≤2, by the true-clique cloning argument and integer rounding. No broader priority assertion is made.


## Complementary theorem: four prescribed terminals and arbitrary positive p

With only four original labels, weight compression is unnecessary and there is no restriction on the packing number. The same diameter and credited three-point caps give 0≤x≤R and all three-edge upper caps≤2R. Pad the four labels by one zero coordinate. The explicit four-point cut distribution in the formal proof dominates the clipped excesses with denominator two. It uses the box and triangle caps only: raise each of the six coordinates to a saturated value, use the lower-triangle consequence of saturation, and then specify the first/pair moments of three side bits and choose their triple moment within the Fréchet bounds. The four-label cuts lift to the original four weights. This gives the same upper bound kM+RC for all positive p. The trunk-and-arms family in §5 attains it for every such p. This complements rather than subsumes the arbitrary-number-of-terminals theorem at p≤5; together they do not imply the exact maximum for r≥5 and p≥6.
