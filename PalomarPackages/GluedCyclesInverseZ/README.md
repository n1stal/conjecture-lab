# Strict inverse-Z log-concavity for two cycles glued along one edge

For any two simple cycles of lengths at least three, identify one edge and its endpoints. The ordinary inverse Z-polynomial of the resulting graphic matroid has positive coefficients throughout its rank range and is strictly log-concave at every interior degree. Both cycle lengths vary independently without a bound.

Lean compares the exact coefficient expression `InverseZ.GluedCycleBounds.sourceCoeff` from Braden–Ferroni–Matherne–Nepal Proposition 4.2, and checks `InverseZ.GluedCycleBounds.sourceCoeff_strict_and_positive`. The expression has the published deletion and contraction terms and both correction terms. The graph-to-formula identification uses the cited theorem, not a formalization of generic KLS theory. See [PROOF.md](PROOF.md) for the graph correspondence and ratio argument.

Pinned to Lean 4.35.0-rc2 with Std only. Build `GluedCyclesInverseZChallenge` and `GluedCyclesInverseZSolution` separately. The Challenge has one intentional theorem hole, and the complete Solution uses only Lean’s standard axioms. The private receipt does not claim an official Comparator run or registry listing.
