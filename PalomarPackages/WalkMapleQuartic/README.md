# The Maple quartic for three nondeterministic steps

This package proves the exact equation left open in
[de Panafieu and Wallner, Section 6.2](https://arxiv.org/html/2311.03234v2#S6.SS2):
the length-generating series of nondeterministic excursions on
{−1}, {−1,+1}, and {−2,+1} satisfies the author companion's quartic.

- PROOF.md: readable source statement and proof.
- Palomar/WalkMapleQuartic/Challenge.lean: literal source word count,
  rational Cauchy series, and the exact polynomial. It imports only Std.
- Palomar/WalkMapleQuartic/Solution.lean: complete independent proof,
  importing only Lean core. It does not import Challenge.
- comparator.json: exact theorem and standard axioms.
- formalization.yaml: source attribution and scope.

Lean toolchain: leanprover/lean4:v4.35.0-rc2. No packages, CAS or
toolchain downloads are required once this Lean toolchain is present.
The fixed Solution contains all polynomial data. From the package root,
run bash replay.sh for isolated local Lean checks. The Challenge's one
intentional proof hole should produce one warning. The Solution has no
holes and is checked with warnings as errors. Run lake comparator
--config comparator.json in a supported bubblewrap environment for the
independent mechanical comparison. No registration or peer review is
claimed here.

Author and responsible maintainer: Jaime Nistal. Codex (OpenAI) is
credited for significant AI-assisted mathematical work and formalization.
