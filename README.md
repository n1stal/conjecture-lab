# Conjecture Lab

Reproducible experiments and partial proofs in discrete mathematics. Each result is paired with its exact scope, the source problem, and instructions to check it. None of the entries below claims to settle the corresponding general problem, and we have not established novelty.

## Results

| Result | Evidence | What remains |
| --- | --- | --- |
| [Six-vertex unweighted digraph Laplacians stay inside the spectral polygon](problems/chebotarev-q2.md#exact-containment-in-the-entire-order-six-polygon) | **Exact computation.** 4,241,864 representatives and 44,729 distinct quotient characteristic polynomials; integer checks on every supporting line. [Reproduce](docs/verification.md#six-vertex-spectral-polygon) | Fractional arc weights are not covered. The general weighted horizontal-edge question remains open in the sources checked. |
| [A centrally symmetric strictly convex octagon has a vertex that sees at least four distances](problems/erdos-982.md#extension-central-symmetry-alone) | **Written partial proof, separately AI-reviewed.** Also tested finite square and triangular lattice patches exactly. [Reproduce](docs/verification.md#erdős-982-convex-octagons) | Arbitrary strictly convex octagons are not covered. No Lean check or external referee report. |
| [The maximum Property P reciprocal sum is 3/2 through 300](conjectures/property-p-sharp.md) | **Exact finite search.** 951,769 nodes. Stored reports, witness checker, exact replay, and independent small-instance oracle. [Reproduce](docs/verification.md#property-p-reciprocal-sums) | The sharp bound for all positive integers remains unproved here. The run through 500 was capped. |

[Full catalogue](CONTENTS.md) · [Verification guide](docs/verification.md) · [Sources and citation](docs/provenance.md)

## Run another search

Python 3.10+ is enough for the default Property P experiments, with no packages or API keys needed.

```sh
python -m unittest discover -s tests -v
python lab.py --mode exact --n 300 --budget 3000000 --output runs/exact.json
python verify.py --replay runs/exact.json
```

On GitHub, use **Actions → Bounded research → Run workflow** to choose the search mode, interval, seed, and budget. It produces a JSON artifact and does not call a model API or commit results. The workflow uses standard GitHub Actions runner minutes and has an eight-minute timeout. It is manual, not scheduled.

For a new problem, use the [intake template](templates/conjecture.md), [bounded research prompt](templates/agent-run.md), and [run log](templates/run.md). Save counterexamples and negative results as well as successful proofs. Use exact arithmetic for checkable claims and state what each test or formalization does not cover.
