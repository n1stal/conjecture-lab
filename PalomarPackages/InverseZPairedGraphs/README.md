# Strict inverse-Z log-concavity for two graphic families

The ordinary inverse Z-polynomials of the cycle matroids of `K_{1,1,n}` and `K_{2,n}` have positive coefficients throughout their rank and strictly positive interior log-concavity minors, for every n. The empty `K_{2,0}` has inverse Z-polynomial 1.

The checked theorem is `InverseZ.BothFamilies.strict_and_positive` and compares two literal finite graph-flat coefficient definitions. Read [THAGOMIZER-PROOF.md](THAGOMIZER-PROOF.md) and [BIPARTITE-PROOF.md](BIPARTITE-PROOF.md) for the mathematical source correspondence and proof. Both use ordinary inverse Z, not ordinary Z or inverse KL; the latter is the input Q polynomial.

The formalization uses Std only, Lean 4.35.0-rc2, and explicit graph ranks, flat codes and Möbius factors. It does not claim that Mathlib's generic matroid API imports these definitions. The Solution has no holes and uses only `propext`, `Classical.choice`, and `Quot.sound`. Official Comparator status is not asserted by this source receipt.
