# Conjecture Lab

A private experimental-math workbench. A run should produce a reproducible witness, a bounded exact result, a proof draft, or a useful failed lead. They are different outcomes.

## Run it

Requires Python 3.10+ (CI uses 3.12), with no external Python packages or API keys.

```sh
python -m unittest discover -s tests -v
python lab.py --mode exact --n 300 --budget 3000000 --output runs/exact.json
python lab.py --mode explore --n 5000 --min-element 2 --budget 2000 --seed 20261126 --output runs/explore.json
python verify.py runs/exact.json runs/explore.json
python verify.py --replay runs/exact.json
```

On GitHub: **Actions → Bounded research → Run workflow**. Choose the search mode, limit, minimum element, seed, and node/trial cap. The run stops at its cap; the workflow also has an eight-minute timeout. Download the JSON artifact or view the Actions summary. This dispatch is opt-in, does not call a model API or push commits, and uses standard GitHub Actions runner minutes. There is no scheduled job or automatic publication.

**Verify** runs Python tests, checks the stored witnesses, replays exact results, and builds the Lean proof package. If using Lean locally, install [elan](https://lean-lang.org/install/) and run `lake build --wfail`; the toolchain is pinned. The concrete Lean theorems verify *witnesses* and exact arithmetic, not the search completeness or the all-integers claim.

## Active targets

[Property P sharp reciprocal bound](conjectures/property-p-sharp.md). New exact computation: **3/2 through 300** (951,769 nodes). A 2,000-trial search through 5,000 without 1 found no improvement over the known witness for that restricted search. This heuristic result is not a bound. Raw reports are in [results/](results/).

[Erdős #982: distances in convex octagons](problems/erdos-982.md). Includes an exact lattice search and a proof draft for the case with two perpendicular reflection axes.

## Research loop

1. **Intake:** Write the exact statement and quantifiers, source paper/page, known bounds, and what is actually unresolved. Check recent papers and formalization repos before treating a target or variant as open. [Template](templates/conjecture.md)
2. **Attack:** Start with the cheapest falsification or special case. Keep deterministic seeds, caps, and exact arithmetic. For model-assisted reasoning, use the [research prompt](templates/agent-run.md); record model and budget only if known. A promising answer is a candidate, not a proof.
3. **Verify independently:** Test the witness against the original definition using a different method. For exact optimization, record evidence of completeness, independently brute-force tractable sizes, and keep a replay. For an all-size proof, audit the quantifiers, assumptions, imported results, and every reduction; formalize the exact statement in Lean. No placeholders or unacknowledged axioms.
4. **Promote only the proved scope:** Label results `exploratory`, `witness-verified`, `finite-exact`, `proof-draft`, or `formalized`; include the verified statement and audit limits. [Experiment log template](templates/run.md) Keep failed approaches with evidence. Publishing and spending on APIs are separate decisions, not workflow defaults.

### Additional active target

- [Chebotarev's even-order digraph Laplacian question](problems/chebotarev-q2.md):
  candidate proof for circulant bases with independently weighted antipodal
  arcs; an unweighted six-vertex census is numerical, not an exact proof.
- The octagon note now also covers the reviewed partial proof for central symmetry
  alone (no reflection symmetry assumption). The general problem remains open.
- `results/attempt-n500.json` records a three-million-node search stopped by
  its budget. No larger witness was found; this does **not** certify optimality
  through 500.
