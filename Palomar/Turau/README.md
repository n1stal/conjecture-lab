# Palomar package: Turau's amnesiac flooding conjecture

This package covers the explicit counterexample and infinite family in
the [result page](../../results/amnesiac-flooding/README.md) and its
[proof and source audit](../../results/amnesiac-flooding/audit.md).
It addresses the conjectured inequality in [Turau's Section 8,
arXiv:2002.10752v4](https://arxiv.org/html/2002.10752v4#S8), not his
weaker proved bound in Theorem 4.

- [Challenge](Challenge.lean): standalone definitions and three declarations,
  importing only Lean, with exactly three deliberate theorem holes.
- [Solution](Solution.lean): proves the same declarations by importing the
  existing checked finite witness and infinite family. No proof copy and
  no import of the Challenge.
- [Comparator configuration](comparator.json) and [metadata](formalization.yaml).
  Both are separately addressed under the root Lake project. The proof package
  shares the root toolchain, pinned manifest, and Apache-2.0 license.

## Verify locally

Run from the repository root:

```sh
./scripts/check-turau-palomar.sh
./check-comparator.sh Palomar/Turau/comparator.json
```

The first command checks both elaborated statement surfaces and the Solution
proof axioms. The second uses the official template's Comparator shape and
Lean's bundled independent kernels; it requires bubblewrap on a supported
host. The manually dispatched **Turau Palomar preflight** GitHub workflow
provides that host configuration using the same pinned workflow actions as
the [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate/tree/2891de4c48955af824969a263d31b25e7a9a1406).
Neither command submits or registers anything. Local checks are distinct from
Palomar verification, editorial review, or registry publication.

## Intake paths

For a separately authorized Palomar verification, use the public repository
`n1stal/conjecture-lab` at a full commit containing this package, the default
root Lake project (leave project path blank), Comparator configuration
`Palomar/Turau/comparator.json`, and formalization metadata
`Palomar/Turau/formalization.yaml`. The root Comparator configuration and
metadata are unrelated and are not part of this package.
