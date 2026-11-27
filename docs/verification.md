# Verification

Install the Lean toolchain pinned by this repository and use Python 3:

```sh
lake build --wfail
python3 scripts/check_publication.py
```

CI regenerates both catalogue views before running the same proof and metadata checks on pushes and pull requests. The script requires a
catalogue entry to have named Lean declarations, an audit file citing its
sources, existing result-page links, matching generated catalogue and root README sections, and a kernel-checked axiom receipt. Regenerate the two views after registry edits with `python3 scripts/check_publication.py --write-catalogue --metadata-only`.
Only the standard foundational axioms `propext`, `Classical.choice`, and
`Quot.sound` are allowed. The gate is not a novelty detector or a substitute
for checking that the written claim means exactly what the Lean theorem says.

## Inverse Z-polynomial

With Elan and Python 3 installed, run:

```sh
./scripts/cache-imports.sh
lake build --wfail
python3 scripts/check_publication.py
```

For registry comparison on Linux with bubblewrap and user namespaces:

```sh
./check-comparator.sh
```

This runs Lean Comparator and the bundled Nanoda and Con-Ron kernels.
`Challenge.lean` is the intentionally unproved statement given to the
checker, not a proof dependency or a public result. `Solution.lean` proves
the exact matching statement. The default build checks the proof without
building the statement-only Challenge.
