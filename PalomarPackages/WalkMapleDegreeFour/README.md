# Minimum degree of the Section 6.2 excursion series

The unweighted three-letter excursion series in [de Panafieu and Wallner,
Section 6.2](https://arxiv.org/html/2311.03234v2#S6.SS2) has algebraic degree
exactly four over Q(t). The authors' exact Maple quartic annihilates it,
and no nonzero cubic (or lower-degree equation) does.

- PROOF.md: source attribution, upper bound, and the four-conjugate lower bound.
- Palomar/WalkMapleDegreeFour/Challenge.lean: literal word count, Cauchy
  arithmetic, author coefficients, and cleared arbitrary rational cubic.
  Imports only Std and contains one intentional proof hole.
- Palomar/WalkMapleDegreeFour/Solution.lean: independent proof with only
  Lean core imports. It does not import the Challenge, the other quartic
  package, or Mathlib.
- comparator.json: exact theorem and standard axiom allowlist.
- formalization.yaml: scope and author/AI attribution.

Lean pin: leanprover/lean4:v4.35.0-rc2. From the package root run
bash replay.sh for isolated Lean checks. Run lake comparator --config
comparator.json in a supported environment for the separate mechanical
comparison. No hosted run, registration, endorsement, or peer review
is claimed here.

Human author and maintainer: Jaime Nistal. Codex (OpenAI) is credited for
mathematical reasoning, proof development, and formalization.
