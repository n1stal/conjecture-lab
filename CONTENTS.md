# Results catalogue

Evidence levels refer to a stated result, not the name of the broader conjecture. See the [verification guide](docs/verification.md) for commands and definitions.

## Digraph Laplacian spectra

- **Exact computation:** [All order-six unweighted standardized Laplacians have spectrum in the proposed polygon](problems/chebotarev-q2.md#exact-containment-in-the-entire-order-six-polygon). The [height/strip certificate](problems/chebotarev-q2.md#exact-unweighted-certificate-at-order-six) is a separate verifier.
- **Written partial proof:** [The height bound persists under arbitrary independent antipodal weight changes on an admissible even-order circulant](problems/chebotarev-q2.md#partial-theorem-all-antipodal-weights-can-vary). No separate review or formal verification claimed.
- **Exploratory:** [Floating-point unweighted and weighted experiments](problems/chebotarev-q2.md#computational-scouting). The unweighted result was superseded by the exact computation. The sampled weighted search is not a bound.

## Erdős #982: convex octagons

- **Written partial proof, separately AI-reviewed:** [Centrally symmetric strictly convex octagons](problems/erdos-982.md#extension-central-symmetry-alone), reduced to [the perpendicular-reflection case](problems/erdos-982.md#candidate-proof-for-perpendicular-reflection-axes). This is not the full octagon problem.
- **Exact finite search:** [No counterexample in the specified square and triangular lattice patches](problems/erdos-982.md#reproduce-the-exact-grid-search). These patches do not model arbitrary real coordinates.

## Property P: reciprocal sums

- **Exact finite search:** [Maximum 3/2 through 300, and maximum 40154231/36716372 through 150 when excluding 1](conjectures/property-p-sharp.md#experiments).
- **Exploratory:** [The capped 1–500 sweep and seeded 2–5000 greedy search](results/README.md) found no improvement over their respective incumbents. Neither result provides an upper bound.
- **Formalization source, build unverified locally:** [Lean witness checks](Proofs/PropertyP.lean). Not a proof of search completeness, finite optimality or any uniform bound.

## Reuse

[Source and attribution notes](docs/provenance.md) · [Raw report index](results/README.md) · [Verification](docs/verification.md)
