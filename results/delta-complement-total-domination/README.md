# Proof of the δ-complement total-domination conjecture

This is a Lean formalization and [written proof](PROOF.md) of Pinhe Chen’s [Conjecture 4](https://doi.org/10.3390/math14111797): the sum of total-domination numbers of a graph and its δ-complement is at most its order plus twice the number of degree classes, provided both graphs have no isolated vertices.

The final Lean theorem is `DeltaNordhaus.conjecture4` in [DeltaConjecture4.lean](DeltaConjecture4.lean). [DeltaClasses.lean](DeltaClasses.lean) proves a stronger partition theorem, and [DeltaNordhaus.lean](DeltaNordhaus.lean) proves the classical ordinary-complement bound internally. The minimum in the definition of total domination is both achieved and certified to be no larger than the size of any total dominating set.

## Replay

Use the checked-in toolchain and dependency lock. With the dependencies and Mathlib cache installed:

```sh
lake exe cache get
./replay.sh
sha256sum -c SHA256SUMS
```

The serial replay uses Lean 4.35.0-rc2 at commit `11acb17ec6b07a8f9e9173e6845197929540936b` and Mathlib at commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The final theorem reports only `[propext, Classical.choice, Quot.sound]`. No finite graph enumeration or conjecture-specific axiom is used.
